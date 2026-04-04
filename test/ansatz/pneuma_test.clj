(ns ansatz.pneuma-test
  "Integration tests for Pneuma spec compilation on Ansatz.
   Tests the full pipeline: spec data → kernel declarations → verified proofs."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.pneuma :as pneuma]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

;; ============================================================
;; Environment setup
;; ============================================================

(def ^:private init-medium-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (let [st (parser/parse-ndjson-file f)
              env (:env (replay/replay (:decls st)))]
          env)))))

(defn- require-env []
  (or @init-medium-env
      (throw (ex-info "test-data/init-medium.ndjson not found" {}))))

(defn- with-env [f]
  (let [env (require-env)]
    (reset! a/ansatz-env env)
    (binding [a/*verbose* false]
      (f))))

(use-fixtures :once with-env)

;; ============================================================
;; Minimal statechart test
;; ============================================================

(deftest test-minimal-statechart
  (testing "2-state on/off statechart"
    (let [env @a/ansatz-env
          result (pneuma/compile-statechart! env "Mini"
                                             {:states #{:on :off}
                                              :transitions [{:source :off :event :toggle :target :on}
                                                            {:source :on :event :toggle :target :off}]})]
      (reset! a/ansatz-env (:env result))

      (is (= ["off" "on"] (:state-names result)))
      (is (= ["toggle"] (:event-names result)))
      (is (= [] (:sink-theorems result))
          "No sink states — both have outgoing transitions")

      ;; Verify declarations exist
      (let [e (:env result)]
        (is (some? (env/lookup e (name/from-string "MiniState"))))
        (is (some? (env/lookup e (name/from-string "MiniEvent"))))
        (is (some? (env/lookup e (name/from-string "MiniDelta"))))
        (is (some? (env/lookup e (name/from-string "instDecidableEqMiniState"))))
        (is (some? (env/lookup e (name/from-string "instDecidableEqMiniEvent"))))))))

;; ============================================================
;; Statechart with sink states
;; ============================================================

(deftest test-statechart-sink-theorem
  (testing "Statechart with terminal/sink state proves sink theorem"
    (let [env @a/ansatz-env
          result (pneuma/compile-statechart! env "Sink"
                                             {:states #{:active :done}
                                              :transitions [{:source :active :event :finish :target :done}]})]
      (reset! a/ansatz-env (:env result))

      (is (= ["SinkDelta_done_sink"] (:sink-theorems result))
          "done is a sink state — no outgoing transitions")
      (is (some? (env/lookup (:env result)
                             (name/from-string "SinkDelta_done_sink")))))))

;; ============================================================
;; Effect signature test (with completeness theorem)
;; ============================================================

(deftest test-effect-signature
  (testing "Effect signature generates Op type, AllOps list, and completeness theorem"
    (let [env @a/ansatz-env
          result (pneuma/compile-effect-signature! env "Eff"
                                                   {:operations {:read {} :write {} :delete {}}})]
      (reset! a/ansatz-env (:env result))

      (is (= ["delete" "read" "write"] (:op-names result)))
      (is (some? (env/lookup (:env result) (name/from-string "EffOp"))))
      (is (some? (env/lookup (:env result) (name/from-string "EffAllOps"))))
      (is (some? (env/lookup (:env result) (name/from-string "instDecidableEqEffOp"))))
      (is (= "EffAllOps_complete" (:all-ops-complete result)))
      (is (some? (env/lookup (:env result) (name/from-string "EffAllOps_complete")))
          "AllOps_complete theorem should exist"))))

;; ============================================================
;; Capability set test
;; ============================================================

(deftest test-capability-set
  (testing "Capability set generates dispatch predicate"
    (let [env @a/ansatz-env
          ;; First need an Op type
          es (pneuma/compile-effect-signature! env "Cap"
                                               {:operations {:op-a {} :op-b {} :op-c {}}})
          env (:env es)
          result (pneuma/compile-capability-set! env "Cap" "Phase"
                                                 (:op-type es) (:op-names es)
                                                 {:dispatch #{:op-a :op-c}})]
      (reset! a/ansatz-env (:env result))

      (is (= "CapPhaseDispatch" (:dispatch-pred result)))
      (is (some? (env/lookup (:env result)
                             (name/from-string "CapPhaseDispatch")))))))

;; ============================================================
;; Existential morphism test
;; ============================================================

(deftest test-existential-morphism
  (testing "Existential morphism proves boundary theorem"
    (let [env @a/ansatz-env
          es (pneuma/compile-effect-signature! env "Morph"
                                               {:operations {:x {} :y {} :z {}}})
          env (:env es)
          cap (pneuma/compile-capability-set! env "Morph" "Test"
                                              (:op-type es) (:op-names es)
                                              {:dispatch #{:x :z}})
          env (:env cap)
          result (pneuma/compile-existential-morphism! env "Morph" :test->ops
                                                       (:dispatch-pred cap) (:op-type es))]
      (reset! a/ansatz-env (:env result))

      (is (= "Morphtest->ops_boundary" (:theorem result)))
      (is (some? (env/lookup (:env result)
                             (name/from-string "Morphtest->ops_boundary")))))))

;; ============================================================
;; Type schema test
;; ============================================================

(deftest test-type-schema
  (testing "Type schema generates TypeId inductive with completeness"
    (let [env @a/ansatz-env
          result (pneuma/compile-type-schema! env "TS"
                                              {:types {:ConfigKey :keyword
                                                       :ConfigValue :any
                                                       :UnitResult :nil}})]
      (reset! a/ansatz-env (:env result))

      (is (= "TSTypeId" (:type-id-type result)))
      (is (= ["ConfigKey" "ConfigValue" "UnitResult"] (:type-names result)))
      (let [e (:env result)]
        (is (some? (env/lookup e (name/from-string "TSTypeId"))))
        (is (some? (env/lookup e (name/from-string "TSAllTypeIds"))))
        (is (some? (env/lookup e (name/from-string "TSAllTypeIds_complete")))
            "Completeness theorem should exist")
        (is (some? (env/lookup e (name/from-string "instDecidableEqTSTypeId"))))))))

;; ============================================================
;; Structural morphism test
;; ============================================================

(defn- mk-list
  "Build a List.{0} term (test helper)."
  [type-expr terms]
  (let [u0 lvl/zero
        list-cons-nm (name/from-string "List.cons")
        list-nil-nm (name/from-string "List.nil")]
    (reduce (fn [acc t]
              (e/app* (e/const' list-cons-nm [u0]) type-expr t acc))
            (e/app (e/const' list-nil-nm [u0]) type-expr)
            (reverse terms))))

(deftest test-structural-morphism
  (testing "Structural morphism maps operations to type identifiers"
    (let [env @a/ansatz-env
          es (pneuma/compile-effect-signature! env "Str"
                                               {:operations {:read {:output :Data}
                                                             :write {:output :Result}
                                                             :delete {:output :Result}}})
          env (:env es)
          ts (pneuma/compile-type-schema! env "Str"
                                          {:types {:Data :any :Result :any}})
          env (:env ts)
          ;; Build allTypeIds list term
          tid-const (e/const' (name/from-string (:type-id-type ts)) [])
          all-tids-list (mk-list
                         tid-const
                         (mapv (fn [n] (e/const' (name/from-string (str (:type-id-type ts) "." n)) []))
                               (:type-names ts)))
          op-output-map {"delete" "Result" "read" "Data" "write" "Result"}
          result (pneuma/compile-structural-morphism!
                  env "Str" :ops->types
                  (:op-type es) (:op-names es)
                  (:type-id-type ts) (:type-names ts)
                  all-tids-list op-output-map)]
      (reset! a/ansatz-env (:env result))

      (is (= "Strops->types_map" (:map-fn result)))
      (is (= "Strops->types_map_valid" (:theorem result)))
      (let [e (:env result)]
        (is (some? (env/lookup e (name/from-string "Strops->types_map"))))
        (is (some? (env/lookup e (name/from-string "Strops->types_map_valid"))))))))

;; ============================================================
;; Containment morphism test
;; ============================================================

(deftest test-containment-morphism
  (testing "Containment morphism proves same boundary theorem as existential"
    (let [env @a/ansatz-env
          es (pneuma/compile-effect-signature! env "Cont"
                                               {:operations {:a {} :b {} :c {}}})
          env (:env es)
          cap (pneuma/compile-capability-set! env "Cont" "Phase"
                                              (:op-type es) (:op-names es)
                                              {:dispatch #{:a :b}})
          env (:env cap)
          result (pneuma/compile-containment-morphism! env "Cont" :phase->ops
                                                       (:dispatch-pred cap) (:op-type es))]
      (reset! a/ansatz-env (:env result))

      (is (some? (env/lookup (:env result)
                             (name/from-string "Contphase->ops_boundary")))))))

;; ============================================================
;; Ordering morphism test
;; ============================================================

(deftest test-ordering-morphism
  (testing "Ordering morphism proves chain index ordering"
    (let [env @a/ansatz-env
          ;; Prove that :init comes before :deploy in the chain
          result (pneuma/compile-ordering-morphism! env "Ord" :init-before-deploy
                                                    [:init :build :test :deploy]
                                                    :init :deploy)]
      (reset! a/ansatz-env (:env result))

      (is (= "Ordinit-before-deploy_order" (:theorem result)))
      (is (some? (env/lookup (:env result)
                             (name/from-string "Ordinit-before-deploy_order"))))))

  (testing "Ordering morphism rejects out-of-order pairs"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Ordering violation"
                          (pneuma/compile-ordering-morphism! @a/ansatz-env "Ord" :bad
                                                             [:a :b :c] :c :a))))

  (testing "Adjacent elements in chain"
    (let [env @a/ansatz-env
          result (pneuma/compile-ordering-morphism! env "Adj" :step
                                                    [:first :second :third]
                                                    :first :second)]
      (reset! a/ansatz-env (:env result))
      (is (some? (env/lookup (:env result)
                             (name/from-string "Adjstep_order")))))))

;; ============================================================
;; Full integrant lifecycle spec
;; ============================================================

(def integrant-spec
  {:prefix "Intg"
   :statechart
   {:states #{:uninitialized :expanded :running :suspended :halted}
    :transitions [{:source :uninitialized :event :expand :target :expanded}
                  {:source :expanded :event :init :target :running}
                  {:source :uninitialized :event :init :target :running}
                  {:source :running :event :halt :target :halted}
                  {:source :running :event :suspend :target :suspended}
                  {:source :suspended :event :resume :target :running}
                  {:source :suspended :event :halt :target :halted}]}
   :effect-signature
   {:operations {:init-key    {:output :InitializedValue}
                 :halt-key    {:output :UnitResult}
                 :resume-key  {:output :InitializedValue}
                 :suspend-key {:output :UnitResult}
                 :resolve-key {:output :ResolvedValue}
                 :expand-key  {:output :ConfigMap}
                 :assert-key  {:output :UnitResult}}}
   :type-schema
   {:types {:ConfigKey :keyword
            :ConfigValue :any
            :ConfigMap :any
            :InitializedValue :any
            :ResolvedValue :any
            :UnitResult :nil}}
   :capability-sets
   {:init    {:dispatch #{:assert-key :expand-key :init-key :resolve-key}}
    :running {:query #{:resolve-key}}
    :suspend {:dispatch #{:suspend-key}}
    :resume  {:dispatch #{:resume-key :resolve-key :assert-key}}
    :halt    {:dispatch #{:halt-key}}}
   :morphisms
   {:init->ops {:type :existential
                :from [:capability-sets :init]
                :source-ref-kind :dispatch
                :to :effect-signature
                :target-ref-kind :operations}
    :running->ops {:type :existential
                   :from [:capability-sets :running]
                   :source-ref-kind :query
                   :to :effect-signature
                   :target-ref-kind :operations}
    :suspend->ops {:type :existential
                   :from [:capability-sets :suspend]
                   :source-ref-kind :dispatch
                   :to :effect-signature
                   :target-ref-kind :operations}
    :resume->ops {:type :existential
                  :from [:capability-sets :resume]
                  :source-ref-kind :dispatch
                  :to :effect-signature
                  :target-ref-kind :operations}
    :halt->ops {:type :existential
                :from [:capability-sets :halt]
                :source-ref-kind :dispatch
                :to :effect-signature
                :target-ref-kind :operations}
    :ops->types {:type :structural
                 :from :effect-signature
                 :to :type-schema
                 :source-ref-kind :operation-outputs
                 :target-ref-kind :type-ids}}})

(deftest test-integrant-full-spec
  (testing "Full integrant lifecycle spec compiles and verifies"
    (let [result (pneuma/compile-spec! integrant-spec)]

      ;; Statechart
      (is (some? (:statechart result)))
      (is (= 5 (count (get-in result [:statechart :state-names]))))
      (is (= 5 (count (get-in result [:statechart :event-names]))))
      (is (= ["IntgDelta_halted_sink"]
             (get-in result [:statechart :sink-theorems])))

      ;; Effect signature + completeness
      (is (some? (:effect-signature result)))
      (is (= 7 (count (get-in result [:effect-signature :op-names]))))
      (is (some? (get-in result [:effect-signature :all-ops-complete])))

      ;; Type schema + completeness
      (is (some? (:type-schema result)))
      (is (= 6 (count (get-in result [:type-schema :type-names]))))
      (is (some? (get-in result [:type-schema :all-type-ids-complete])))

      ;; Capability sets (all 5 phases)
      (is (some? (get-in result [:capability-sets :init :dispatch-pred])))
      (is (some? (get-in result [:capability-sets :running :query-pred])))
      (is (some? (get-in result [:capability-sets :suspend :dispatch-pred])))
      (is (some? (get-in result [:capability-sets :resume :dispatch-pred])))
      (is (some? (get-in result [:capability-sets :halt :dispatch-pred])))

      ;; Morphisms: 5 existential + 1 structural
      (is (some? (get-in result [:morphisms :init->ops :theorem])))
      (is (some? (get-in result [:morphisms :running->ops :theorem])))
      (is (some? (get-in result [:morphisms :suspend->ops :theorem])))
      (is (some? (get-in result [:morphisms :resume->ops :theorem])))
      (is (some? (get-in result [:morphisms :halt->ops :theorem])))
      (is (some? (get-in result [:morphisms :ops->types :theorem])))
      (is (some? (get-in result [:morphisms :ops->types :map-fn])))

      ;; Verify all key declarations exist in env
      (let [e @a/ansatz-env]
        (doseq [n ["IntgState" "IntgEvent" "IntgOp" "IntgDelta"
                   "IntgAllOps" "IntgAllOps_complete"
                   "IntgTypeId" "IntgAllTypeIds" "IntgAllTypeIds_complete"
                   "IntgInitDispatch" "IntgHaltDispatch"
                   "IntgRunningQuery" "IntgSuspendDispatch" "IntgResumeDispatch"
                   "IntgDelta_halted_sink"
                   "Intginit->ops_boundary" "Intghalt->ops_boundary"
                   "Intgrunning->ops_boundary" "Intgsuspend->ops_boundary"
                   "Intgresume->ops_boundary"
                   "Intgops->types_map" "Intgops->types_map_valid"
                   "instDecidableEqIntgState" "instDecidableEqIntgEvent"
                   "instDecidableEqIntgOp" "instDecidableEqIntgTypeId"]]
          (is (some? (env/lookup e (name/from-string n)))
              (str n " should exist in env")))))))

;; ============================================================
;; Name conversion
;; ============================================================

(deftest test-kw-to-ctor-name
  (testing "Keyword to constructor name conversion"
    (is (= "init_key" (pneuma/kw->ctor-name :init-key)))
    (is (= "halt_key" (pneuma/kw->ctor-name :halt-key!)))
    (is (= "running" (pneuma/kw->ctor-name :running)))
    (is (= "is_valid_q" (pneuma/kw->ctor-name :is-valid?)))
    (is (= "a_to_b" (pneuma/kw->ctor-name :a>b)))))
