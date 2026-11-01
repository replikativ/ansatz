(ns prototype.cases-on-preparation-test
  "Host-only preparation models. The original extern is an actual pinned CAS
   row; the helper is deliberately a nonexecuted model, not Lean construction
   or kernel/frontend admission evidence."
  (:require [clojure.test :refer [deftest is]]
            [clojure.java.io :as io]
            [clojure.data.json :as json]
            [prototype.cases-on-preparation :as cases]
            [prototype.declaration-store :as declarations]
            [prototype.resident-init-prefix :as prefix]
            [prototype.machine :as m]
            [prototype.program-install :as install]
            [prototype.checkpoint-wire :as wire]
            [prototype.runtime-abi :as abi]
            [prototype.raw-interop :as raw]))

(def original-bytes
  (with-open [input (io/input-stream (io/resource "fixtures/cases-on-preseal/original-extern.json"))]
    (.readAllBytes input)))
(def original (json/read-str (wire/utf8-string original-bytes) :key-fn keyword))
(def target (:name original))
(def other ["str" ["anonymous"] "unrelated"])
(def manifest
  {:kind "manifest" :schema "lean-ir-probe/1" :leanVersion "4.33.1"
   :leanCommit "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
   :runtimeProfile {:target "x86_64-unknown-linux-gnu" :wordBits 64}
   :modules [] :exports []
   :initializationPlan {:kind "initialization-plan" :schema "lean-init-plan/1"
                        :moduleSystem false :module ["str" ["anonymous"] "Model"]
                        :imports [] :actions []}})
(def helper-row
  {:kind "decl" :name cases/helper :dependencies [] :runtime {:role "ordinary" :initializer nil}
   :sourceLocal true :sourceModule ["str" ["anonymous"] "Model"]
   :ir {:fdecl {:f cases/helper :info {} :type "object"
                :xs [{:x {:idx 1} :ty "object" :borrow false}
                     {:x {:idx 2} :ty "tobject" :borrow true}]
                :body ["ret" {:var {:id {:idx 1}}}]}}})
(defn artifact
  ([] (artifact manifest helper-row))
  ([m r]
   (let [source (.getBytes "-- Nonexecuted host-only model" "UTF-8")
         ir (.getBytes (str (json/write-str m) "\n" (json/write-str r) "\n") "UTF-8")]
     {:source-bytes source :source-sha256 (wire/sha256 source)
      :ir-bytes ir :ir-sha256 (wire/sha256 ir)
      :max-bytes 65536 :max-declarations 100})))
(defn fixture
  ([] (fixture true))
  ([independent?]
   (let [trap (second (abi/lower-deferred original))
         unrelated {:params [] :body [:return [:imm 0]]}
         functions {target trap other unrelated}
         trusted (if independent? functions {other unrelated})
         binding {:signature {:params [] :return-type "object"}
                  :handler (fn [& _] (throw (AssertionError. "NO GUEST EXECUTION")))}
         bindings {"model" binding}
         catalogue {:declarations {target original} :manifests []}
         support {:session (raw/open-functions trusted bindings {:backend :reference :fuel 100})
                  :catalogue catalogue}
         world {:functions functions :status :done :frames [] :heap {} :globals {}
                :native-imports [:model] :kernel-environments {}
                :eval-const-authorizations {:functions {target trap}} :stats {:steps 0}}
         candidate {:world world :session (raw/open-functions functions bindings {:backend :reference :fuel 100})
                    :catalogue catalogue :trusted-functions trusted :support support}
         configuration {:catalogue catalogue :trusted-functions trusted :trusted-bindings bindings
                        :cases-on-original-row-bytes original-bytes
                        :cases-on-original-function (when independent? trap)}]
     {:candidate candidate :configuration configuration :artifact (artifact)})))
(defn prepare [f] (cases/prepare (:candidate f) (:configuration f) (:artifact f)))

(deftest authentic-row-and-new-consumer-branch
  (is (= cases/original-row-sha256 (wire/sha256 original-bytes)))
  (doseq [independent? [true false]]
    (let [f (fixture independent?) result (prepare f)
          next (:candidate result) config (:configuration result)
          functions (get-in next [:world :functions]) replacement (get functions target)]
      (is (= {:params [1 2] :export-redirect cases/helper
              :body [:tail [:direct cases/helper] [[:var 1] [:var 2]]]}
             replacement))
      (is (identical? replacement (get-in config [:trusted-functions target])))
      (is (identical? replacement (get-in next [:world :eval-const-authorizations :functions target])))
      (is (identical? (get-in f [:candidate :world :functions other]) (get functions other)))
      (is (identical? (get-in f [:candidate :session :bindings]) (get-in next [:session :bindings])))
      (is (identical? (:trusted-functions config) (get-in next [:support :session :functions])))
      (is (identical? functions (get-in next [:session :functions])))
      (doseq [key [:heap :globals :kernel-environments :native-imports :stats]]
        (is (identical? (get-in f [:candidate :world key]) (get-in next [:world key]))))
      (is (= original (get-in f [:configuration :catalogue :declarations target])))
      (is (= original (get-in config [:catalogue :declarations target])))
      (is (= original ((get-in config [:catalogue :read-declaration]) target)))
      (is (= [target replacement] (abi/lower-catalogue (:catalogue config) original)))
      (is (= [target replacement] ((:lower-extern result) original)))
      (is (identical? (:lower-extern result) (:consumer-extern-lower config)))
      (is (nil? ((:lower-extern result) helper-row)))
      (is (= [target replacement]
             (abi/lower-catalogue
              (declarations/overlay (:catalogue config) {:declarations {} :manifests []}) original)))
      (is (some? (get-in f [:candidate :world :functions target :deferred-extern])))
      (is (= [target] (get-in result [:profile :relinked])))
      (is (false? (get-in result [:profile :guest-executed])))
      (is (= 0 (get-in result [:profile :new-initialization-actions]))))))

(defn rejected! [f]
  (let [error (try (prepare f) nil (catch Throwable error error))]
    (is (instance? clojure.lang.ExceptionInfo error))
    (when error
      (is (identical? (:candidate f) (:cases-on-preparation-entry (ex-data error))))
      (is (identical? (:configuration f) (:cases-on-preparation-configuration (ex-data error))))
      (is (some? (.getCause ^Throwable error))))))

(deftest reject-sealed-incoherent-or-widened-inputs
  (doseq [f [(assoc-in (fixture) [:candidate :prefix] :sealed)
             (assoc-in (fixture) [:configuration :frontend-configuration :install-options] {})
             (assoc-in (fixture) [:candidate :world :frames] [:active])
             (assoc-in (fixture) [:candidate :world :eval-const-authorizations :units "user"] {})
             (update (fixture) :candidate dissoc :support)
             (update (fixture) :configuration dissoc :cases-on-original-function)
             (assoc-in (fixture) [:configuration :cases-on-original-function] nil)
             (assoc-in (fixture false) [:configuration :cases-on-original-function] {})
             (assoc-in (fixture) [:configuration :cases-on-original-row-bytes] (.getBytes "{}" "UTF-8"))
             (assoc-in (fixture) [:candidate :world :eval-const-authorizations :functions target] {})
             (assoc-in (fixture) [:candidate :world :functions other] {:params [] :body [:return [:imm 0]]})
             (assoc-in (fixture) [:configuration :trusted-bindings "model"] {})
             (assoc-in (fixture) [:configuration :catalogue :declarations target :pretty] "drift")]]
    (rejected! f)))

(deftest reject-helper-digest-abi-and-initialization-drift
  (doseq [a [(assoc (artifact) :ir-sha256 (apply str (repeat 64 "0")))
             (artifact manifest (assoc-in helper-row [:ir :fdecl :xs 0 :borrow] true))
             (artifact manifest (assoc-in helper-row [:ir :fdecl :xs 1 :ty] "object"))
             (artifact manifest (assoc-in helper-row [:ir :fdecl :type] "tobject"))
             (artifact (assoc-in manifest [:initializationPlan :actions] [{:kind "initialize"}]) helper-row)
             (artifact manifest (assoc helper-row :name target))]]
    (rejected! (assoc (fixture) :artifact a))))

(deftest future-lowering-and-overlay-cannot-change-consumer-capability
  (let [catalogue (get-in (prepare (fixture)) [:configuration :catalogue])
        key :prototype.runtime-abi/consumer-redirects]
    (doseq [r [(assoc original :name other)
               (assoc-in original [:ir :extern :xs 0 :borrow] true)
               (assoc original :dependencies [other])
               (assoc original :redirect {:name other})]]
      (is (thrown? clojure.lang.ExceptionInfo (abi/lower-catalogue catalogue r))))
    (is (thrown? clojure.lang.ExceptionInfo
          (abi/lower-catalogue
           (assoc-in catalogue [:manifests 0 :exports]
                     [{:symbol "lean_mk_cases_on" :name other}]) original)))
    (is (thrown? clojure.lang.ExceptionInfo
          (declarations/overlay catalogue
            {:declarations {} :manifests []
             key {"lean_mk_cases_on" {:original-row original :target other}}})))
    (is (thrown? clojure.lang.ExceptionInfo
          (abi/with-consumer-redirects catalogue
            {"lean_mk_cases_on" {:original-row original :target other}})))))

(deftest consumer-capability-is-not-silently-serialized-as-producer-evidence
  (let [catalogue (get-in (prepare (fixture)) [:configuration :catalogue])]
    (is (thrown? clojure.lang.ExceptionInfo (declarations/checkpoint! catalogue)))
    (is (thrown? clojure.lang.ExceptionInfo (declarations/with-declaration! catalogue helper-row)))))

(deftest existing-source-profile-captures-issued-lowering-policy
  (let [seen (atom []) fallback (fn [r] (swap! seen conj r) nil)
        result (prepare (assoc-in (fixture) [:configuration :consumer-extern-lower] fallback))
        config (:configuration result) lower (:consumer-extern-lower config)
        limits {:max-constants 100 :name-limits {:max-nodes 64 :max-chars 4096}
                :max-nodes 1000 :max-edges 2000 :max-bytes 65536 :max-units 10 :max-declarations 1000}
        graph {:max-modules 10 :max-roots 10 :max-edges 20 :max-depth 10 :max-names 100
               :max-name-nodes 64 :max-name-bytes 4096 :max-total-name-bytes 65536
               :max-key-bytes 4096 :max-total-key-bytes 65536}
        created (prefix/prepare-source-graph-profile
                 ["model-exporter"] {:witness ["model-witness"]
                                     :catalogue (:catalogue config)
                                     :trusted-functions (:trusted-functions config) :lower-extern lower}
                 {:limits limits :graph-limits graph :host-limits {:max-heap-entries 1000}})
        captured (get-in created [:install-options :lower-extern])]
    (is (identical? lower captured))
    (is (= [target (get-in result [:candidate :world :functions target])] (captured original)))
    (is (nil? (captured helper-row)))
    (is (= [helper-row] @seen))
    (is (false? (get-in created [:install-options :initialize?])))
    (is (fn? (get-in created [:eval-binding :handler])))))

(def installed-root ["str" ["anonymous"] "consumerInstallModel"])
(def install-callback ["str" ["anonymous"] "consumerHostCallback"])
(defn install-bundle []
  {:manifests [(assoc manifest :producer "RuntimeCompileShim.exportCompiled"
                       :initializationPlanScope "all-local-declarations"
                       :requestedRoots [installed-root]
                       :entryPoints [{:name installed-root :boxedTarget installed-root}]
                       :missingDependencies [])]
   :declarations
   {installed-root
    (-> helper-row
        (assoc :name installed-root :dependencies [target])
        (assoc-in [:ir :fdecl :f] installed-root)
        (assoc-in [:ir :fdecl :body]
                  ["vdecl" {:idx 3} "object"
                   {:fap {:c target :ys [{:var {:id {:idx 1}}} {:var {:id {:idx 2}}}]}}
                   ["ret" {:var {:id {:idx 3}}}]]))}})

(deftest actual-host-installation-preserves-custom-and-catalogue-policies
  ;; Execute installation and its generated direct call through the real raw
  ;; callback boundary. The helper is still a labelled identity model; no Lean
  ;; construction/admission claim follows from this runtime policy regression.
  (doseq [backend [:reference :mutable :jvm] route [:custom :catalogue]]
    (let [prepared (prepare (fixture)) config (:configuration prepared)
          observed (atom [])
          custom (fn [r] (swap! observed conj (:name r)) ((:consumer-extern-lower config) r))
          installer {:signature cases/signature
                     :handler
                     (fn [{:keys [install-compiled! invoke]} world args]
                       (let [[world installed]
                             (install-compiled! world (install-bundle)
                               (cond-> {:catalogue (:catalogue config)}
                                 (= route :custom) (assoc :lower-extern custom)))]
                         (is (= installed-root (get (:boxed-entrypoints installed) installed-root)))
                         (invoke world installed-root args)))}
          bindings {"consumer-model-install" installer}
          callback-row (-> original (assoc :name install-callback)
                           (assoc-in [:ir :extern :f] install-callback)
                           (assoc-in [:ir :extern :ext :entries 0 :standard :fn] "consumer-model-install"))
          functions {install-callback (second (raw/lower bindings callback-row))}
          session (raw/open-functions functions bindings {:backend backend :fuel 10000})
          [parent value] (m/resource (m/world functions) :consumer-model-owner)
          result (raw/call session parent install-callback [value 0]) state (:state result)]
      (is (= value (:value result)))
      (is (= 1 (:rc (m/node state value))))
      (is (= (if (= route :custom) [target] []) @observed))
      (is (= cases/helper (get-in state [:functions target :export-redirect])))
      (is (nil? (get-in parent [:functions target])))
      (is (identical? (get functions install-callback) (get-in state [:functions install-callback])))
      (is (identical? (:functions state) (get-in result [:session :functions])))
      (is (not (contains? (:heap (m/release state value 1)) (:id value)))))))

(deftest compiler-output-cannot-issue-or-replace-consumer-policy
  (let [catalogue (get-in (prepare (fixture)) [:configuration :catalogue])
        key :prototype.runtime-abi/consumer-redirects
        capability (get catalogue key)
        forged (assoc (install-bundle) key capability)]
    (is (thrown? clojure.lang.ExceptionInfo
          (install/install (m/world {}) forged {:catalogue (dissoc catalogue key)})))
    (let [bad (assoc-in (install-bundle) [:manifests 0 :exports]
                        [{:symbol "lean_mk_cases_on" :name installed-root}])]
      (is (thrown? clojure.lang.ExceptionInfo
            (install/install (m/world {}) bad {:catalogue catalogue}))))
    (let [bad (assoc-in (install-bundle) [:declarations target]
                        (assoc-in original [:ir :extern :xs 0 :borrow] true))]
      (is (thrown? clojure.lang.ExceptionInfo
            (install/install (m/world {}) bad {:catalogue catalogue}))))))
