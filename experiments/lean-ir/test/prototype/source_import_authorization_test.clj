(ns prototype.source-import-authorization-test
  "Authorization contracts with strictly checked Java constants and a SMALL
   guest root-getter IR MODEL. Receipt storage models completed finalization;
   these tests do not execute Lean's real finalizer or establish native coverage."
  (:refer-clojure :exclude [name])
  (:require [clojure.test :refer [deftest is]]
            [prototype.source-import :as source]
            [prototype.module-import :as module-import]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]
            [ansatz.kernel.env :as kernel]
            [ansatz.kernel.expr :as expr]
            [ansatz.kernel.level :as level])
  (:import [ansatz.kernel Env Name]))

(def module ["str" ["anonymous"] "SourceA"])
(def name ["str" ["anonymous"] "answer"])
(def kernel-name (Name/fromString "answer"))
(def digest (apply str (repeat 64 "a")))
(def root-helper (:root module-import/helpers))
(def map-helper (:constant-map module-import/helpers))
(def quot-helper (:quot-init? module-import/helpers))
(defn getter [index]
  {:params [1] :body [:let 2 [:project [:var 1] index] [:inc [:var 2] 1 [:return [:var 2]]]]})
(defn root-field-getter [index]
  {:params [1] :body [:let 2 [:project [:var 1] 0]
                     [:let 3 [:project [:var 2] index] [:inc [:var 3] 1 [:return [:var 3]]]]]})
(defn fixture []
  (let [constant (kernel/mk-axiom kernel-name [] (expr/sort' level/zero))
        checked (kernel/check-constant (kernel/empty-env) constant)
        extra (kernel/mk-axiom (Name/fromString "later") [] (expr/sort' level/zero))
        descendant (kernel/check-constant checked extra)
        f {:params [] :body [:return [:imm 42]]}
        local {:name name :sourceLocal true :sourceModule module :ir {:fdecl {:f name :xs [] :type "object" :body []}}}
        unit {:actions [] :declarations [name] :manifest {:initializationPlan {:module module :actions [] :imports []}}}
        functions {root-helper (getter 0) map-helper (root-field-getter 0)
                   quot-helper (root-field-getter 1) name f}
        [world published-map] (m/allocate (m/world functions) :ctor 0 [])
        [world published-root] (m/allocate world :ctor 0 [published-map 0])
        [world published-env] (m/allocate (m/retain world published-root 1) :ctor 0 [published-root])
        [world target-map] (m/allocate world :ctor 0 [42])
        [world target-root] (m/allocate world :ctor 0 [target-map 0])
        [world target-env] (m/allocate (m/retain world target-root 1) :ctor 0 [target-root])
        receipt {:anchor published-root :checked-env checked :projected {kernel-name constant}
                 :constants {} :unit-digest digest}
        world (assoc world
                     :kernel-environments {(:id published-root) {:anchor published-root :env checked
                                                                 :constant-map published-map :quot-init? false}
                                           (:id target-root) {:anchor target-root :env descendant
                                                              :constant-map target-map :quot-init? false}}
                     :eval-const-authorizations {:units {digest unit} :unit-digests {name digest}
                                                :declarations {name local} :functions functions})
        before world
        entry {:module module :unit unit :unit-digest digest :imports {(:id published-root) receipt}}
        world (assoc-in world [:source-modules module] entry)]
    {:world world :before before :published-root published-root :published-env published-env
     :target-root target-root :target-map target-map :environment target-env
     :constant constant :checked checked :descendant descendant
     :local local :unit unit :receipt receipt
     :row (assoc local :sourceLocal false)}))
(defn authorize [backend {:keys [world environment row local unit]}]
  (let [session (raw/open-functions (:functions world) {} {:backend backend})
        invoke (fn [state target args]
                 (let [result (raw/call session state target args)] [(:state result) (:value result)]))]
    (source/authorize-imported-row world
      {:invoke invoke
       :check-trusted-functions!
       (fn [state roots]
         ;; These modeled getters have no static callees; production uses the
         ;; full transitive trusted/admitted executable closure checker.
         (doseq [root roots]
           (when-not (identical? (get-in state [:functions root])
                                 (get-in state [:eval-const-authorizations :functions root]))
             (throw (ex-info "Model trusted getter identity mismatch" {:root root})))))}
      environment row local unit)))

(deftest exact-checked-constant-inheritance-authorizes-without-changing-owners-or-receipts
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [world before target-root published-root environment] :as input} (fixture)
          [after accepted] (authorize backend input)]
      (is (true? accepted))
      (is (= (:heap world) (:heap after)))
      (is (identical? (:source-modules world) (:source-modules after)))
      (is (identical? (:eval-const-authorizations world) (:eval-const-authorizations after)))
      (is (= [2 2 1] (mapv #(:rc (m/node after %)) [target-root published-root environment])))
      (is (nil? (:source-modules before)))
      (is (false? (second (authorize backend (assoc input :world before))))))))

(deftest same-shaped-constant-replacement-missing-constant-and-unassociated-target-reject
  (let [{:keys [world target-root checked] :as input} (fixture)
        equivalent (kernel/mk-axiom kernel-name [] (expr/sort' level/zero))
        independently-checked (kernel/check-constant (kernel/empty-env) equivalent)]
    (is (not (identical? (:constant input) equivalent)))
    (doseq [backend [:reference :mutable :jvm]
            changed [(assoc-in world [:kernel-environments (:id target-root) :env] independently-checked)
                     (assoc-in world [:kernel-environments (:id target-root) :env] (Env.))
                     (update world :kernel-environments dissoc (:id target-root))
                     (assoc-in world [:kernel-environments (:id target-root) :anchor] (:published-root input))]]
      (let [[after accepted] (authorize backend (assoc input :world changed))]
        (is (false? accepted))
        (is (= (:heap changed) (:heap after)))))
    (is (identical? (:constant input) (.lookup ^Env checked kernel-name)))))

(deftest missing-or-mismatched-publication-unit-module-receipt-and-flags-reject
  (let [{:keys [world published-root] :as input} (fixture)
        receipt-path [:source-modules module :imports (:id published-root)]]
    (doseq [changed [(assoc input :world (update world :source-modules dissoc module))
                     (assoc input :row (dissoc (:row input) :sourceModule))
                     (assoc input :row (assoc (:row input) :sourceModule ["str" ["anonymous"] "Other"]))
                     (assoc input :row (assoc (:row input) :sourceLocal true))
                     (assoc input :row (dissoc (:row input) :sourceLocal))
                     (assoc input :unit (into {} (:unit input)))
                     (assoc input :local (into {} (:local input)))
                     (assoc input :world (assoc-in world [:eval-const-authorizations :unit-digests name] "different"))
                     (assoc input :world (assoc-in world (conj receipt-path :unit-digest) "different"))
                     (assoc input :world (assoc-in world (conj receipt-path :checked-env) (Env.)))
                     (assoc input :world (assoc-in world [:source-modules module :imports] {}))
                     (assoc input :world (update world :kernel-environments dissoc (:id published-root)))]]
      (let [[after accepted] (authorize :reference changed)]
        (is (false? accepted))
        (is (= (:heap (:world changed)) (:heap after)))))))

(deftest helper-authority-is-required-and-replacement-cannot-redirect-the-target-root
  (doseq [backend [:reference :mutable :jvm]
          helper [root-helper map-helper quot-helper]]
    (let [{:keys [world environment row local unit] :as input} (fixture)
          invoked (atom false)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"trusted helper closure checking"
            (source/authorize-imported-row world {:invoke (fn [& _] (reset! invoked true))}
                                          environment row local unit)))
      (is (false? @invoked))
      (let [functions (assoc (:functions world) helper (getter 1))
            changed (assoc input :world (assoc world :functions functions))]
        ;; Even a same-named, shape-correct projection must not replace the
        ;; identity-authorized accessor for the actual target Environment.
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"getter identity mismatch"
              (authorize backend changed)))
        (is (= 2 (:rc (m/node (:world changed) (:target-root input)))))
        (is (identical? (get-in world [:functions root-helper])
                        (get-in world [:eval-const-authorizations :functions root-helper])))))))

(defn- header-view [world constants quot]
  (let [[world root] (m/allocate (m/retain world constants 1) :ctor 0 [constants quot])
        [world environment] (m/allocate world :ctor 0 [root])]
    [world environment root]))

(deftest header-only-source-view-inherits-protected-map-with-one-new-root-owner
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [world target-map descendant] :as input} (fixture)
          [world environment root] (header-view world target-map 0)
          before-map-rc (:rc (m/node world target-map))
          [after accepted] (authorize backend (assoc input :world world :environment environment))
          association (get-in after [:kernel-environments (:id root)])
          [again accepted-again] (authorize backend (assoc input :world after :environment environment))
          released (m/release again environment 1)]
      (is (true? accepted))
      (is (true? accepted-again))
      (is (identical? descendant (:env association)))
      (is (= root (:anchor association)))
      (is (= target-map (:constant-map association)))
      (is (false? (:quot-init? association)))
      (is (nil? (get-in world [:kernel-environments (:id root)])))
      (is (= 1 (:rc (m/node world root))))
      (is (= 2 (:rc (m/node after root)) (:rc (m/node again root))))
      (is (= before-map-rc (:rc (m/node after target-map)) (:rc (m/node again target-map))))
      (is (identical? (:source-modules world) (:source-modules after)))
      (is (identical? (:eval-const-authorizations world) (:eval-const-authorizations after)))
      ;; The ledger's owner survives releasing the caller Environment. Merely
      ;; observing a live root while the caller still owns it would miss a leak
      ;; of authority onto a borrowed, eventually dangling anchor.
      (is (nil? (get-in released [:heap (:id environment)])))
      (is (= 1 (:rc (m/node released root))))
      (is (= before-map-rc (:rc (m/node released target-map)))))))

(deftest unprotected-header-maps-quotients-and-anchors-cannot-create-authority
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [world target-root target-map published-root descendant] :as input} (fixture)
          [world equal-map] (m/allocate world :ctor 0 [42])
          [world empty-map] (m/allocate world :ctor 0 [])]
      (doseq [[state constants quot]
              [[world equal-map 0]
               [world empty-map 0]
               [world target-map 1]
               [(assoc-in world [:kernel-environments (:id target-root) :anchor] published-root) target-map 0]
               [(assoc-in world [:kernel-environments (:id target-root) :env] (.enableQuot ^Env descendant)) target-map 0]
               [(update-in world [:kernel-environments (:id target-root)] dissoc :constant-map) target-map 0]]]
        (let [[state environment root] (header-view state constants quot)
              [after accepted] (authorize backend (assoc input :world state :environment environment))]
          (is (false? accepted))
          (is (= (:heap state) (:heap after)))
          (is (= (:kernel-environments state) (:kernel-environments after)))
          (is (nil? (get-in after [:kernel-environments (:id root)]))))))))

(deftest derived-header-still-requires-original-source-constant-identities
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [world target-root target-map] :as input} (fixture)
          equivalent (kernel/mk-axiom kernel-name [] (expr/sort' level/zero))
          independent (kernel/check-constant (kernel/empty-env) equivalent)
          world (assoc-in world [:kernel-environments (:id target-root) :env] independent)
          [world environment root] (header-view world target-map 0)
          [after accepted] (authorize backend (assoc input :world world :environment environment))]
      (is (false? accepted))
      ;; The target has a protected checked map, but that independently checked
      ;; CI cannot inherit this source unit's installation receipt.
      (is (identical? independent (get-in after [:kernel-environments (:id root) :env])))
      (is (identical? (:source-modules world) (:source-modules after))))))
