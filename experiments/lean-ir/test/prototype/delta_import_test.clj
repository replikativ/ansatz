(ns prototype.delta-import-test
  "Bounded helper-boundary/ownership tests using native 17-CI fixture and real
   Java checking. These models do not claim native finalizer/frontend coverage."
  (:require [clojure.test :refer [deftest is]]
            [prototype.checked-delta :as delta]
            [prototype.delta-import :as import]
            [prototype.module-import :as strict]
            [prototype.module-import-test :as finalizer]
            [prototype.imported-kernel :as kernel]
            [prototype.imported-kernel-test :as fixture]
            [prototype.kernel-bridge-test :as guest]
            [prototype.machine :as m])
  (:import [ansatz.kernel Env]))

(defn environment [world values]
  (let [world (reduce #(m/retain %1 %2 1) world values)
        [world array] (m/allocate world :array 246 values)
        [world root] (m/allocate world :ctor 0 [array])]
    (m/allocate world :ctor 0 [root])))
(defn completed [world values]
  (let [[world env] (environment world values)]
    (m/allocate world :ctor 0 [env])))
(defn issue []
  (let [loaded (fixture/loaded) values (fixture/values loaded)
        functions (into {} (map (fn [target] [target {:params [1] :body [:return [:var 1]]}]))
                        (vals (select-keys strict/helpers [:root :constants :constant-map :quot-init?])))
        world (assoc (:world loaded) :functions functions)
        certificate (kernel/verify-constants world values fixture/policy)
        [world env] (environment world values)
        calls (atom [])
        context {:invoke (finalizer/helper-model calls []) :trusted-functions functions
                 :bindings {} :trusted-bindings {}}
        world (kernel/associate-checked context world env strict/helpers certificate)
        [world cap] (delta/capture-base context world env strict/helpers certificate)]
    (reset! calls [])
    {:world world :cap cap :context context :values values :certificate certificate
     :refs (fixture/by-name loaded) :calls calls :base-environment env}))
(defn add-definition [world refs label body-name]
  (let [cv (first (:fields (m/node world (fixture/payload world (get refs "A")))))
        type (nth (:fields (m/node world cv)) 2)
        [world body] (guest/constant world body-name)]
    (guest/declaration world label type body)))
(defn exception [thunk]
  (try (thunk) nil (catch clojure.lang.ExceptionInfo e e)))

(deftest actual-completed-result-checks-only-new-groups-and-associates-final-map
  (let [{:keys [world context values cap refs certificate calls]} (issue)
        [world a] (add-definition world refs "deltaImportFirst" "aliasA")
        [world b] (add-definition world refs "deltaImportSecond" "deltaImportFirst")
        [before wrapper] (completed world (into values [b a]))
        result (with-redefs [kernel/verify-constants (fn [& _] (throw (ex-info "Whole base checked again" {})))]
                 (import/finish-finalization context before wrapper cap))
        world (:world result) env (:environment result)
        root (first (:fields (m/node world env)))
        map-root (get-in world [:kernel-environments (:id root) :constant-map])]
    (is (= :ok (:status result)))
    (is (= 19 (count (get-in result [:certificate :constants]))))
    (is (= ["deltaImportFirst" "deltaImportSecond"]
           (mapv #(str (second %)) (get-in result [:certificate :new-order]))))
    (doseq [[name ci] (:projected certificate)]
      (is (identical? ci (.lookup ^Env (get-in result [:certificate :env]) name))))
    (is (identical? (get-in result [:certificate :env])
                    (get-in world [:kernel-environments (:id root) :env])))
    (is (= 1 (:rc (m/node world env))))
    (is (= 2 (:rc (m/node world root))))
    (is (= 2 (:rc (m/node world map-root))))
    (is (not (contains? (:heap world) (:id wrapper))))
    (is (= 1 (:rc (m/node before wrapper))))
    (is (not-any? #(= (:finalize strict/helpers) (first %)) @calls))))

(deftest real-io-error-is-returned-unchanged-without-helper-work
  (let [{:keys [world context cap calls]} (issue)
        [world error] (m/resource world "delta-io-error")
        [world wrapper] (m/allocate world :ctor 1 [error])
        result (import/finish-finalization context world wrapper cap)]
    (is (= :io-error (:status result)))
    (is (identical? world (:world result)))
    (is (= wrapper (:io-result result)))
    (is (empty? @calls))
    (is (= [[:released "delta-io-error"]] (:events (m/release world wrapper 1))))))

(deftest changed-base-fails-after-actual-helper-progress-and-keeps-array-owner
  (let [{:keys [world context cap values refs certificate calls]} (issue)
        [world replacement] (guest/constant world "Tiny")
        payload (fixture/payload world (get refs "aliasA"))
        world (assoc-in world [:heap (:id payload) :fields 1] replacement)
        [world wrapper] (completed world values)
        context (update context :invoke
                        (fn [invoke]
                          (fn [world target args]
                            (let [[world scratch] (m/allocate world :ctor 0 [])
                                  world (m/release world scratch 1)]
                              (invoke world target args)))))
        error (exception #(import/finish-finalization context world wrapper cap))
        {:keys [checkpoint stage finalizer-result finalization-entry finalization-owners temporary-owners]} (ex-data error)
        constants (:constants finalization-owners) env (:environment finalization-owners)
        root (first (:fields (m/node checkpoint env)))]
    (is (some? error))
    (is (= :inherited-shapes stage))
    (is (> (:next-id checkpoint) (:next-id world)))
    (is (= [constants] temporary-owners))
    (is (= 1 (:rc (m/node checkpoint constants))))
    (is (= 1 (:rc (m/node checkpoint env))))
    (is (identical? checkpoint (:checkpoint finalization-owners)))
    (is (identical? world (:checkpoint finalizer-result)))
    (is (= wrapper (:io-result finalizer-result)))
    (is (= env (:environment finalization-entry)))
    (is (nil? (get-in checkpoint [:kernel-environments (:id root)])))
    (is (= 17 (count (:constants certificate))))
    (is (not-any? #(= (:finalize strict/helpers) (first %)) @calls))))

(deftest invalid-new-proof-reaches-real-checker-and-never-anchors-final-root
  (let [{:keys [world context cap values refs]} (issue)
        proof (get refs "identityProof") payload (fixture/payload world proof)
        [constant _ _] (:fields (m/node world payload))
        [world bad-value] (guest/constant world "A")
        [world bad-name] (guest/guest-name world "deltaInvalidProof")
        [world all] (guest/ctor world 1 [bad-name guest/nil-tag] 0)
        [world cv] (guest/ctor world 0 (assoc (:fields (m/node world constant)) 0 bad-name) 0)
        [world payload] (guest/ctor world 0 [cv bad-value all] 0)
        [world bad] (guest/ctor world 2 [payload] 0)
        [world wrapper] (completed world (conj values bad))
        error (exception #(import/finish-finalization context world wrapper cap))
        {:keys [checkpoint stage finalization-owners temporary-owners]} (ex-data error)
        env (:environment finalization-owners) root (first (:fields (m/node checkpoint env)))]
    (is (some? error))
    (is (= :check (first stage)))
    (is (= [(:constants finalization-owners)] temporary-owners))
    (is (nil? (get-in checkpoint [:kernel-environments (:id root)])))))

(deftest helper-failure-preserves-latest-session-and-all-owner-aliases
  (let [{:keys [world context cap values]} (issue)
        [world wrapper] (completed world values)
        calls (atom 0) token (Object.)
        ;; First constants call gives this layer its temporary owner; the base
        ;; root call fails after allocating a distinct diagnostic IO.Result.
        context (update context :invoke
                        (fn [invoke]
                          (fn [world target args]
                            (if (= target (:root strict/helpers))
                              (let [_ (swap! calls inc)
                                    [world error] (m/resource world "delta-helper-error")
                                    [world io] (m/allocate world :ctor 1 [error])]
                                (throw (ex-info "injected helper failure"
                                                {:checkpoint world :checkpoint-session token
                                                 :witness-raw-result io :host-boundaries [:kept]})))
                              (invoke world target args)))))
        error (exception #(import/finish-finalization context world wrapper cap))
        {:keys [checkpoint checkpoint-session session finalization-owners finalizer-result
                temporary-owners witness-raw-result host-boundaries] :as packet} (ex-data error)
        constants (:constants finalization-owners)]
    (is (= 1 @calls))
    (is (and (identical? token checkpoint-session) (identical? checkpoint-session session)))
    (is (= [:kept] host-boundaries))
    (is (= [constants] temporary-owners))
    (is (= 1 (:rc (m/node checkpoint constants))))
    (is (= 1 (:rc (m/node checkpoint (:environment finalization-owners)))))
    (is (= 1 (:rc (m/node checkpoint witness-raw-result))))
    (is (= 1 (:rc (m/node (:checkpoint finalizer-result) wrapper))))
    (is (not (contains? packet :environment)))
    (is (not (contains? (:heap checkpoint) (:id wrapper))))))

(deftest selected-final-helper-closure-and-raw-bindings-require-independent-authority
  (let [{:keys [world context cap values calls]} (issue)
        target ["different-final-constants"] leaf ["different-final-leaf"]
        executable {:params [1] :runtime-dependencies [leaf] :body [:return [:var 1]]}
        leaf-code {:params [1] :body [:return [:var 1]]}
        world (-> world (assoc-in [:functions target] executable) (assoc-in [:functions leaf] leaf-code))
        [world wrapper] (completed world values)
        options {:helpers {:constants target}}
        assert-preflight (fn [context world]
                           (let [error (exception #(import/finish-finalization context world wrapper cap options))
                                 packet (ex-data error)]
                             (is (some? error))
                             (is (= :helper-authority (:stage packet)))
                             (is (identical? world (:checkpoint packet)))
                             (is (= wrapper (:io-result packet)))
                             (is (= 1 (:rc (m/node (:checkpoint packet) wrapper))))
                             (is (empty? @calls))))]
    ;; A selected helper and each transitive leaf need independent registry entries.
    (assert-preflight context world)
    (let [authorized (update context :trusted-functions assoc target executable leaf leaf-code)
          changed (assoc-in world [:functions leaf] (assoc leaf-code :changed true))]
      (assert-preflight authorized changed))
    (let [symbol "different-final-raw-leaf"
          raw-leaf (assoc leaf-code :raw-extern {:symbol symbol})
          world (assoc-in world [:functions leaf] raw-leaf)
          binding {:handler identity} different {:handler (fn [x] x)}
          authorized (-> context
                         (update :trusted-functions assoc target executable leaf raw-leaf)
                         (assoc :bindings {symbol binding} :trusted-bindings {symbol different}))]
      (assert-preflight authorized world))))

(deftest late-association-failure-preserves-association-owners-after-array-release
  (let [{:keys [world context cap values]} (issue)
        before world
        [world wrapper] (completed world values)
        quot-calls (atom 0) token (Object.)
        context (update context :invoke
                        (fn [invoke]
                          (fn [world target args]
                            (if (and (= target (:quot-init? strict/helpers))
                                     (= 2 (swap! quot-calls inc)))
                              (let [[world error] (m/resource world "delta-association-error")
                                    [world io] (m/allocate world :ctor 1 [error])]
                                (throw (ex-info "injected late association failure"
                                                {:checkpoint world :checkpoint-session token
                                                 :witness-raw-result io})))
                              (invoke world target args)))))
        error (exception #(import/finish-finalization context world wrapper cap))
        {:keys [checkpoint association-temporary-owners temporary-owners
                finalization-owners witness-raw-result session]} (ex-data error)
        [root constants] association-temporary-owners]
    (is (some? error))
    (is (= 2 @quot-calls))
    (is (= 2 (count association-temporary-owners)))
    (is (= association-temporary-owners temporary-owners))
    (is (not (contains? finalization-owners :constants)))
    (is (= 1 (:rc (m/node checkpoint (:environment finalization-owners)))))
    (is (= 2 (:rc (m/node checkpoint root))))
    (is (= 1 (:rc (m/node checkpoint constants))))
    (is (= 1 (:rc (m/node checkpoint witness-raw-result))))
    (is (identical? token session))
    (is (nil? (get-in checkpoint [:kernel-environments (:id root)])))
    (let [cleaned (reduce #(m/release %1 %2 1) checkpoint
                          (concat [witness-raw-result] association-temporary-owners
                                  [(:environment finalization-owners)]))]
      (is (= (:heap before) (:heap cleaned))))))

(deftest attestation-failures-pair-actual-checkpoints-with-returned-text-owners
  ;; Helper models only: invalid header validation happens after text release;
  ;; malformed JSON fails while the returned text still has its owner.
  (doseq [[text released?] [["{}" true] ["{" false]]]
    (let [{:keys [world context cap values]} (issue)
          target ["delta-finalizer-header"]
          function {:params [1] :body [:return [:var 1]]}
          world (assoc-in world [:functions target] function)
          before world
          [world wrapper] (completed world values)
          seen (atom nil) calls (atom 0)
          context (-> context
                      (update :trusted-functions assoc target function)
                      (update :invoke
                              (fn [invoke]
                                (fn [world helper args]
                                  (if (= target helper)
                                    (let [_ (swap! calls inc)
                                          [world value] (m/allocate world :string 249 [])
                                          world (assoc-in world [:heap (:id value) :text] text)]
                                      (reset! seen value) [world value])
                                    (invoke world helper args))))))
          options {:finalizer-attestation {:requested-imports [] :header-helper target}}
          error (exception #(import/finish-finalization context world wrapper cap options))
          {:keys [checkpoint finalizer-temporary-owners temporary-owners finalization-owners]} (ex-data error)
          env (:environment finalization-owners)]
      (is (some? error))
      (is (= 1 @calls))
      (is (not (contains? finalization-owners :constants)))
      (is (= (if released? [] [@seen]) finalizer-temporary-owners))
      (is (= finalizer-temporary-owners temporary-owners))
      (is (= released? (not (contains? (:heap checkpoint) (:id @seen)))))
      (is (= 1 (:rc (m/node checkpoint env))))
      (when-not released?
        (is (= 1 (:rc (m/node checkpoint @seen)))))
      (let [cleaned (reduce #(m/release %1 %2 1) checkpoint
                            (concat finalizer-temporary-owners [env]))]
        (is (= (:heap before) (:heap cleaned)))))))

(deftest child-owner-ledgers-do-not-erase-prior-helper-owners-or-alias-occurrences
  (doseq [child-kind [:empty :new :alias]]
    (let [{:keys [world context cap values]} (issue)
          before world [world wrapper] (completed world values)
          root-owner (atom nil) child-owner (atom nil)
          context (update context :invoke
                          (fn [invoke]
                            (fn [world target args]
                              (cond
                                (= target (:root strict/helpers))
                                (let [[world root] (invoke world target args)]
                                  (reset! root-owner root) [world root])
                                (= target (:quot-init? strict/helpers))
                                (let [[world child] (case child-kind
                                                      :empty [world nil]
                                                      :new (m/resource world "delta-child-error")
                                                      :alias [(m/retain world @root-owner 1) @root-owner])]
                                  (reset! child-owner child)
                                  (throw (ex-info "child helper failed with its own owner packet"
                                                  {:checkpoint world :temporary-owners (if child [child] [])})))
                                :else (invoke world target args)))))
          error (exception #(import/finish-finalization context world wrapper cap))
          {:keys [checkpoint temporary-owners checked-delta-helper-owners finalization-owners]} (ex-data error)
          expected (cond-> [@root-owner] @child-owner (conj @child-owner))
          expected (conj expected (:constants finalization-owners))]
      (is (some? error))
      (is (= [@root-owner] checked-delta-helper-owners))
      (is (= expected temporary-owners))
      (let [cleaned (reduce #(m/release %1 %2 1) checkpoint
                            (conj temporary-owners (:environment finalization-owners)))]
        (is (= (:heap before) (:heap cleaned)))))))
