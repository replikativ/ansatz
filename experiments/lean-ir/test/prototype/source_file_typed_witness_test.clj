(ns prototype.source-file-typed-witness-test
  "Bounded mixed local-B/imported-A file-install regression. The typed witness
   is a pinned native Lean DAG/oracle. The tiny guest environment/getters and
   finalizer boundary are explicit models; production source/finalize performs
   real Java kernel checking and creates the receipt. This does not execute the
   complete Lean frontend/finalizer or attest their whole environment."
  (:require [clojure.test :refer [deftest is]]
            [prototype.eval-const :as eval]
            [prototype.eval-const-typed-ir-test :as native]
            [prototype.eval-const-resolution-test :as resolution]
            [prototype.import-ir :as ir]
            [prototype.ir-value :as typed]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]
            [prototype.source-import :as source]
            [prototype.source-import-test :as source-fixture]
            [prototype.source-import-authorization-test :as authority]
            [prototype.module-import :as module-import]
            [prototype.kernel-bridge-test :as guest]
            [ansatz.kernel.name :as name]))

(def module-a ["str" ["anonymous"] "PreludeIdentity"])
(def module-b ["str" ["anonymous"] "MixedSecond"])
(def second-name ["str" ["anonymous"] "second"])
(def imported-name ["str" ["str" ["anonymous"] "answer"] "_redArg"])
(def witness-helper ["str" ["anonymous"] "nativeMixedWitness"])

(defn declaration [row module local?]
  (let [lowered (second (ir/lower-declaration (assoc row :runtime {:role "ordinary" :initializer nil})))]
    (assoc row :kind "decl" :runtime {:role "ordinary" :initializer nil}
               :sourceModule (when local? module) :sourceLocal local?
               :dependencies (vec (ir/static-targets (:body lowered))))))
(defn bundle [rows module root boxed imports]
  {:declarations (into {} (map (juxt :name identity)) rows)
   :manifests [(-> (first (:manifests resolution/fixture))
                   (assoc :requestedRoots [root] :entryPoints [{:name root :boxedTarget boxed}])
                   (assoc-in [:initializationPlan :module] module)
                   (assoc-in [:initializationPlan :imports] imports))]})
(def helpers
  {(:root module-import/helpers) (authority/getter 0)
   (:constant-map module-import/helpers) (authority/root-field-getter 0)
   (:quot-init? module-import/helpers) {:params [1] :body [:return [:imm 1]]}
   witness-helper
   {:params [1 2 3]
    :body [:let 4 [:project [:var 1] 1]
           [:inc [:var 4] 1 [:dec [:var 1] 1 [:dec [:var 2] 1
            [:let 5 [:ctor 0 [[:var 4]]] [:return [:var 5]]]]]]]}})

(defn checked-identity-declaration [world]
  ;; A safe closed identity at Sort 0, with the same erased runtime argument
  ;; shape as the native identity IR. No axiom or unchecked Java CI is seeded.
  (let [[world prop] (guest/ctor world 3 [guest/nil-tag] 8)
        [world alpha] (guest/guest-name world "α")
        [world x] (guest/guest-name world "x")
        [world zero] (guest/ctor world 0 [0] 8)
        [world one] (guest/ctor world 0 [1] 8)
        [world inner-type] (guest/ctor world 7 [x zero one] 9)
        [world type] (guest/ctor world 7 [alpha prop inner-type] 9)
        [world inner-body] (guest/ctor world 6 [x zero zero] 9)
        [world body] (guest/ctor world 6 [alpha prop inner-body] 9)]
    (guest/declaration world "answer" type body)))

(defn setup [backend change-witness change-bundle]
  (let [loaded @native/native-data
        mixed (nth @native/expected 3)
        original-a (nth @native/expected 2)
        a (bundle (mapv #(declaration % module-a true) (:declarations original-a))
                  module-a (:name original-a) (:boxedTarget original-a) [])
        b (bundle (mapv #(declaration % module-b (:sourceLocal %)) (:declarations mixed))
                  module-b (:name mixed) (:boxedTarget mixed) [{:module module-a :meta false}])
        admitted (eval/install-bundle (assoc (:world loaded) :functions helpers) a
                                     {:catalogue a :trusted-functions helpers})
        world (:world admitted) digest (:unit-digest admitted)
        unit (get-in world [:eval-const-authorizations :units digest])
        [world ci] (checked-identity-declaration world)
        [world name] (guest/guest-name world "answer")
        [world names] (m/allocate world :array 246 [name])
        [world constants] (m/allocate world :array 246 [ci])
        [world empty-array] (m/allocate world :array 246 [])
        [world data] (guest/ctor (m/retain world empty-array 2) 0
                                 [empty-array names constants empty-array empty-array] 1)
        world (assoc-in world [:source-modules module-a]
                        {:module module-a :profile :standalone :data data :unit unit :unit-digest digest})
        [world state] (m/allocate world :ctor 0 [])
        [world imports] (m/allocate world :array 246 [])
        requests [{:module module-a :importAll false :isExported true :isMeta false}]
        delegate (source-fixture/final-invoke [ci] requests 1)
        invoke-final
        (fn [world target args]
          (if (= target (:finalize source/helpers))
            (let [[state imports] args
                  world (-> world (m/release state 1) (m/release imports 1))]
              (source-fixture/final-result world [ci]))
            (delegate world target args)))
        finished (source/finalize {:world world :state state :imports imports
                                  :module module-a :requested-imports requests}
                                 invoke-final 0 {:kernel-policy {}})
        world (:world finished) environment (:environment finished)
        payload (nth (:roots loaded) 3)
        world (change-witness world payload)
        node (m/node world environment)
        world (m/replace-node (m/retain world payload 1) environment
                              (assoc node :fields (conj (:fields node) payload)))
        [world root] (guest/guest-name world "second")
        [world roots] (m/allocate world :array 246 [root])
        active (atom (raw/open-functions (:functions world) {} {:backend backend :fuel 1000000}))
        invoke (fn [world target args]
                 (let [called (raw/call @active world target args)]
                   (reset! active (:session called)) [(:state called) (:value called)]))]
    {:world world :environment environment :roots roots :payload payload
     :finished finished :session active :invoke invoke :bundle (change-bundle b)
     :options {:witness witness-helper :witness-format :typed-ir :catalogue a
               :trusted-functions helpers :authorize-source-import source/authorize-imported-row}}))

(defn install [{:keys [world environment roots invoke bundle options]}]
  (eval/install-file-bundle {:invoke invoke} world environment roots bundle options))
(defn change-origin [value]
  (fn [world payload]
    (let [rows (nth (:fields (m/node world payload)) 7)
          row (last (:fields (m/node world rows)))
          [world option]
          (if (= value :missing) [world 0]
            (let [[world name] (guest/guest-name world "WrongModule")]
              (m/allocate world :ctor 1 [name])))]
      (assoc-in world [:heap (:id row) :fields 2] option))))

(deftest native-mixed-typed-file-witness-installs-and-calls-through-checked-source-receipt
  (doseq [backend [:reference :mutable :jvm]]
    (let [input (setup backend (fn [w _] w) identity)
          before (:world input) finished (:finished input)
          installed (install input) after (:world installed)
          root (get-in installed [:boxed-entrypoints second-name])
          session (raw/open-functions (:functions after) {} {:backend backend :fuel 1000000})
          called (raw/call session after root [m/erased 42])
          receipt (:source-import-receipt finished)]
      (is (= :ok (:status finished)))
      (is (= 1 (count (:constants receipt))))
      (is (empty? (get-in finished [:certificate :axioms])))
      (is (identical? (:checked-env receipt) (get-in finished [:certificate :env])))
      (is (identical? (get-in receipt [:projected (name/from-string "answer")])
                      (.lookup ^ansatz.kernel.Env (:checked-env receipt) (name/from-string "answer"))))
      (is (= (nth @native/expected 3) (typed/project-witness before (:payload input))))
      (is (= 42 (:value called)))
      (is (= [] (:pending-local-initializers installed)))
      (is (identical? (get-in before [:functions imported-name]) (get-in after [:functions imported-name])))
      (is (identical? (get-in before [:eval-const-authorizations :declarations imported-name])
                      (get-in after [:eval-const-authorizations :declarations imported-name])))
      (is (true? (get-in after [:eval-const-authorizations :declarations imported-name :sourceLocal])))
      (is (identical? (:source-modules before) (:source-modules after)))
      (doseq [ref [(:environment input) (:roots input) (:payload input)
                   (first (:fields (m/node before (:roots input))))]]
        (is (= (:rc (m/node before ref)) (:rc (m/node after ref)))))
      (is (= (:heap before) (:heap after))))))

(deftest missing-origin-wrong-module-changed-ir-and-runtime-remain-rejected
  (doseq [backend [:reference :mutable :jvm]
          [change-witness change-bundle expected]
          ;; The first case removes typed origin; it does not execute the old
          ;; archived three-field JSON producer. Runtime drift is rejected by
          ;; existing-declaration admission, since native witnesses omit runtime.
          [[(change-origin :missing) identity #"Source import witness differs from admitted source unit"]
           [(change-origin :wrong) identity #"Source import witness differs from admitted source unit"]
           [(fn [w _] w) #(assoc-in % [:declarations imported-name :ir :fdecl :body] ["unreachable"])
            #"File output differs from actual interpreter import witness"]
           [(fn [w _] w) #(assoc-in % [:declarations imported-name :runtime :role] "value")
            #"evalConst selected IR differs from authorized declaration"]]]
    (let [input (setup backend change-witness change-bundle)
          error (try (install input) nil (catch clojure.lang.ExceptionInfo e e))]
      (is (some? error))
      (is (and error (re-find expected (.getMessage error)))))))

(deftest real-receipt-is-required-despite-identical-native-witness-and-ir
  (let [input (setup :reference (fn [w _] w) identity)
        foreign (update-in input [:world :source-modules module-a] dissoc :imports)
        failure (try (install foreign) nil (catch clojure.lang.ExceptionInfo e e))]
    (is (some? failure))
    (is (re-find #"checked module installation authority" (.getMessage failure)))))
