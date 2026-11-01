(ns ansatz.tactic.instance-test
  "Tests for typeclass instance synthesis."
  (:require [ansatz.test-env :as test-env]
            [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.tactic.instance :as inst]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.config :as config]
            [ansatz.meta :as meta]
            [ansatz.state :as state])
  (:import [ansatz.kernel ConstantInfo]))

;; ============================================================
;; Environment setup
;; ============================================================

(def ^:private test-env test-env/checked-bundled-init-env)

(defn- require-env [] (or @test-env (throw (ex-info "bundled Init unavailable" {}))))

(def ^:private test-index
  (delay (inst/index-for (require-env))))

;; ============================================================
;; Basic instance lookup
;; ============================================================

(deftest test-get-instances
  (testing "Instance index has candidates for common classes"
    (let [idx @test-index]
      (is (seq (inst/get-instances idx (name/from-string "Add")))
          "Add should have instances")
      (is (seq (inst/get-instances idx (name/from-string "Decidable")))
          "Decidable should have instances")
      (is (seq (inst/get-instances idx (name/from-string "BEq")))
          "BEq should have instances"))))

;; ============================================================
;; Instance synthesis for Nat
;; ============================================================

(deftest test-synthesize-add-nat
  (testing "Synthesize Add Nat instance"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          nat (e/const' (name/from-string "Nat") [])
          goal (e/app (e/const' (name/from-string "Add") [lvl/zero]) nat)
          result (inst/synthesize* st env @test-index goal 0)]
      (is (some? result) "Should find Add Nat instance")
      (when result
        (is (e/const? (e/get-app-fn result))
            "Result should be a constant application")))))

(deftest test-synthesize-decidable-eq-nat
  (testing "Synthesize DecidableEq Nat"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          nat (e/const' (name/from-string "Nat") [])
          goal (e/app (e/const' (name/from-string "DecidableEq") [(lvl/succ lvl/zero)]) nat)
          result (inst/synthesize* st env @test-index goal 0)]
      (is (some? result) "Should find DecidableEq Nat instance"))))

;; ============================================================
;; TSV loading
;; ============================================================

(deftest test-load-instance-tsv
  (testing "Load instance registry from TSV"
    (let [tsv "resources/instances.tsv"]
      (when (.exists (java.io.File. tsv))
        (let [idx (inst/load-instance-tsv tsv)]
          (is (map? idx))
          (is (> (count idx) 1000) "TSV should have 1000+ classes")
          (is (seq (inst/get-instances idx (name/from-string "LE")))
              "LE should have instances from TSV"))))))

;; ============================================================
;; Negative tests
;; ============================================================

(deftest test-synthesize-nonexistent
  (testing "Synthesis fails for nonexistent class"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          goal (e/app (e/const' (name/from-string "NonexistentClass") [lvl/zero])
                      (e/const' (name/from-string "Nat") []))]
      (is (nil? (inst/synthesize* st env @test-index goal 0))
          "Should return nil for unknown class"))))

;; ============================================================
;; Lean's registry: order, selection, and which index a session uses
;; ============================================================

(deftest test-parse-instance-tsv-order
  (testing "Lean's try order: higher priority first, most recently declared first among equals"
    (let [idx (inst/parse-instance-tsv ["C\tearly\t1000" "C\tlow\t100" "C\tlate\t1000" "C\thigh\t2000"])]
      (is (= ["high" "late" "early" "low"]
             (mapv (comp str :name) (inst/get-instances idx (name/from-string "C")))))))
  (testing "a re-registered instance (a re-exporting module) is one instance, at its first registration"
    (let [idx (inst/parse-instance-tsv ["C\ta\t1000" "C\tb\t1000" "C\ta\t1000"])]
      (is (= ["b" "a"] (mapv (comp str :name) (inst/get-instances idx (name/from-string "C")))))))
  (testing "present? drops what the env does not have (a full-Init registry over a smaller tier)"
    (let [idx (inst/parse-instance-tsv ["C\ta\t1000" "C\tb\t1000" "D\tc\t1000"] #{"a" "c"})]
      (is (= ["a"] (mapv (comp str :name) (inst/get-instances idx (name/from-string "C")))))
      (is (= ["c"] (mapv (comp str :name) (inst/get-instances idx (name/from-string "D"))))))))

(deftest test-select-candidates-keys-on-the-carrier
  (let [env (require-env)
        of (fn [ns] (mapv (fn [n] {:name (name/from-string n) :priority 1000}) ns))
        goal (e/app* (e/const' (name/from-string "OfNat") [lvl/zero])
                     (e/const' (name/from-string "Nat") []) (e/lit-nat 5))
        select (fn [ns] (mapv (comp str :name) (inst/select-candidates env (of ns) goal)))]
    (testing "only instances for the goal's carrier plus the generic ones survive — Lean's
              DiscrTree selection, one level deep, whatever the list's size"
      (is (= ["instOfNatNat" "Zero.toOfNat0"]
             (select ["Fin.instOfNat" "instOfNatNat" "BitVec.instOfNat" "Zero.toOfNat0"])))
      (binding [config/*max-candidates* 2]
        (is (= ["instOfNatNat" "Zero.toOfNat0"]
               (select ["Fin.instOfNat" "instOfNatNat" "BitVec.instOfNat" "Zero.toOfNat0"])))))
    (testing "the carrier's own instances come FIRST, before the generic ones, whatever the
              registry order — `getUnify` returns star matches before keyed ones and
              SynthInstance consumes that array backwards, so at equal priority Lean tries the
              specific instance first. Registry order alone resolved `Add Int` to
              `Distrib.toAdd`, a term no Mathlib lemma is stated about."
      (is (= ["instOfNatNat" "Zero.toOfNat0"] (select ["Zero.toOfNat0" "instOfNatNat"]))))
    (testing "a goal with no constant carrier keeps every candidate (nothing to key on)"
      (let [open-goal (e/app* (e/const' (name/from-string "OfNat") [lvl/zero])
                              (e/bvar 0) (e/lit-nat 5))]
        (is (= 2 (count (inst/select-candidates env (of ["instOfNatNat" "Zero.toOfNat0"]) open-goal))))))))

(deftest test-index-for-reads-the-env-not-the-process
  (let [env (require-env)
        saved @state/ansatz-instance-index
        registry {(name/from-string "Nonempty") [{:name (name/from-string "instNonemptyOfInhabited") :priority 1000}]}]
    (try
      (is (identical? registry (inst/index-for (env/with-extension env :instances registry)))
          "the registry ON the env is the instance table — Lean's environment extension")
      (reset! state/ansatz-instance-index registry)
      (is (not (identical? registry (inst/index-for env)))
          "a process-global registry never answers for an env that does not carry it")
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"no instance registry"
                            (inst/index-for (env/with-extension env :instances nil))))
      (is (= {} (inst/index-for (env/with-extension env :instances {}))))
      (finally (reset! state/ansatz-instance-index saved)))))

(deftest test-add-instance-registers-on-the-env
  (let [env (env/with-extension (require-env) :instances nil)
        inst (name/from-string "instNonemptyOfInhabited")
        env' (inst/add-instance env inst)
        entries (inst/get-instances (inst/index-for env') (name/from-string "Nonempty"))]
    (is (= [{:name inst :priority 1000}] entries) "only the explicit registration is added")
    (is (= 1000 (:priority (first entries))) "Lean's default priority")
    (is (nil? (env/get-extension env :instances nil)) "the original env is untouched")
    (is (= [{:name inst :priority 10}]
           (filter #(= inst (:name %))
                   (inst/get-instances (inst/index-for (inst/add-instance env' inst :priority 10))
                                       (name/from-string "Nonempty"))))
        "re-registering replaces the entry with the requested priority")))

(deftest add-instance-orders-equal-priorities-newest-first
  (let [cls (name/from-string "Nonempty")
        older (name/from-string "instNonemptyOfInhabited")
        newer (name/from-string "instNonemptyOfMonad")
        base (env/with-extension (require-env) :instances {})
        registered (-> base
                       (inst/add-instance older :priority 1000)
                       (inst/add-instance newer :priority 1000))]
    (is (= [{:name newer :priority 1000} {:name older :priority 1000}]
           (inst/get-instances (inst/index-for registered) cls))
        "Lean tries the most recent registration first among equal priorities")
    (is (= [{:name older :priority 1000} {:name newer :priority 10}]
           (inst/get-instances (inst/index-for (inst/add-instance registered newer :priority 10)) cls))
        "re-registration changes priority without duplicating or dropping candidates")))

;; ============================================================
;; DecidableEq instances with arguments (Lean keys them by the unfolded conclusion)
;; ============================================================

(deftest test-synthesize-decidable-eq-with-arguments
  ;; `T : Nat → Type` with `instT : (n : Nat) → DecidableEq (T n)` — the shape of
  ;; `instDecidableEqFin`. Peeling instT's type through the `DecidableEq` alias used to
  ;; produce `Decidable (a = b)` with two extra binders, so neither goal below matched.
  (let [nm name/from-string
        c (fn [s & ls] (e/const' (nm s) (vec ls)))
        u1 (lvl/succ lvl/zero)
        type0 (e/sort' u1)
        T (fn [n] (e/app (c "T") n))
        env (-> (require-env)
                (.addConstant (env/mk-axiom (nm "T") [] (e/forall' "n" (c "Nat") type0 :default)))
                (.addConstant (env/mk-axiom (nm "instT") []
                                            (e/forall' "n" (c "Nat")
                                                       (e/app (c "DecidableEq" u1) (T (e/bvar 0)))
                                                       :default))))
        idx (inst/parse-instance-tsv ["DecidableEq\tinstT\t1000"])]
    (testing "DecidableEq (T 3) matches instT at its declared conclusion"
      (let [r (inst/synthesize* (tc/mk-tc-state env) env idx
                                (e/app (c "DecidableEq" u1) (T (e/lit-nat 3))) 0)]
        (is (= "(app (const instT []) (lit-nat 3))" (str r)))))
    (testing "Decidable (x = y) at T n is answered by the DecidableEq instance applied to x y"
      (let [n (e/fvar 900)
            st (tc/mk-tc-state-with-locals env {900 {:name "n" :type (c "Nat")}
                                                901 {:name "x" :type (T n)}
                                                902 {:name "y" :type (T n)}})
            goal (e/app (c "Decidable") (e/app* (c "Eq" u1) (T n) (e/fvar 901) (e/fvar 902)))
            r (inst/synthesize* st env idx goal 0)]
        (is (some? r))
        (is (= "instT" (str (e/const-name (e/get-app-fn r)))))
        (is (tc/is-def-eq st (tc/infer-type st r) goal))))))

(deftest test-instance-search-does-not-truncate
  (let [nm name/from-string
        c (fn [s] (e/const' (nm s) []))
        goal (e/app (c "CapClass") (c "Nat"))
        env (-> (require-env)
                (.addConstant (env/mk-axiom (nm "CapClass") []
                                            (e/forall' "α" (e/sort' (lvl/succ lvl/zero))
                                                       (e/sort' lvl/zero) :default)))
                (.addConstant (env/mk-axiom (nm "capBlocked") []
                                            (e/forall' "h" (c "False") goal :inst-implicit)))
                (.addConstant (env/mk-axiom (nm "capAnswer") [] goal)))
        idx {(nm "CapClass") [{:name (nm "capBlocked")} {:name (nm "capAnswer")}]}]
    (binding [config/*max-candidates* 1]
      (is (= (c "capAnswer") (inst/synthesize env idx goal))))))

(deftest test-instance-priority-precedes-specificity
  (let [env (require-env)
        goal (e/app* (e/const' (name/from-string "OfNat") [lvl/zero])
                     (e/const' (name/from-string "Nat") []) (e/lit-nat 0))
        candidates [{:name (name/from-string "instOfNatNat") :priority 1000}
                    {:name (name/from-string "Zero.toOfNat0") :priority 2000}]]
    (is (= ["Zero.toOfNat0" "instOfNatNat"]
           (mapv (comp str :name) (inst/select-candidates env candidates goal))))))

(deftest test-instance-errors-propagate
  (let [env (require-env)
        goal (e/app (e/const' (name/from-string "Add") [lvl/zero])
                    (e/const' (name/from-string "Nat") []))
        failure (NullPointerException. "injected synthesis bug")]
    (testing "candidate reduction does not turn bugs into another instance"
      ;; tryResolve's unification (a mismatch is nil or an ExceptionInfo; anything else is a bug)
      (with-redefs-fn {#'meta/is-def-eq (fn [& _] (throw failure))}
        #(is (thrown-with-msg? NullPointerException #"injected synthesis bug"
                               (inst/synthesize env @test-index goal)))))
    (testing "the synthPending hook propagates bugs"
      (with-redefs [inst/synthesize* (fn [& _] (throw failure))]
        (is (thrown-with-msg? NullPointerException #"injected synthesis bug"
                              (inst/synth-pending-instance nil (tc/mk-tc-state env) goal)))))
    (testing "depth exhaustion fails only that path, is recorded, and is named when the search fails"
      (binding [config/*max-synth-depth* 0
                inst/*depth-hits* (atom [])]
        (is (nil? (inst/synthesize* (tc/mk-tc-state env) env @test-index goal 1)))
        (is (= [goal] @inst/*depth-hits*)))
      (with-redefs [inst/synthesize* (fn [& _] (some-> inst/*depth-hits* (swap! conj goal)) nil)]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"\*max-synth-depth\*"
                              (inst/synthesize env @test-index goal)))))))

(deftest test-invalid-instance-priority-fails
  (is (thrown? NumberFormatException (inst/parse-instance-tsv ["C\tbroken\tnot-a-priority"]))))

(deftest test-incompatible-instance-universe-backtracks
  ;; Regression: valid Lean declarations; the Type candidate must not be applied to a Prop.
  (let [nm name/from-string
        c (fn [s] (e/const' (nm s) []))
        prop (e/sort' lvl/zero)
        type0 (e/sort' (lvl/succ lvl/zero))
        u (nm "u")
        add-ax (fn [en s ty] (env/check-constant en (env/mk-axiom (nm s) [] ty)))
        env (-> (env/empty-env)
                (env/with-extension :instances {})
                (env/check-constant
                 (env/mk-axiom (nm "RegrU") [u]
                               (e/forall' "A" (e/sort' (lvl/param u)) prop :default)))
                (add-ax "regrP" prop)
                (add-ax "regrTypeInst"
                        (e/forall' "A" type0
                                   (e/app (e/const' (nm "RegrU") [(lvl/succ lvl/zero)])
                                          (e/bvar 0)) :implicit))
                (add-ax "regrPropInst"
                        (e/forall' "A" prop
                                   (e/app (e/const' (nm "RegrU") [lvl/zero])
                                          (e/bvar 0)) :implicit)))
        goal (e/app (e/const' (nm "RegrU") [lvl/zero]) (c "regrP"))
        bad {:name (nm "regrTypeInst") :priority 1100}
        good {:name (nm "regrPropInst") :priority 1000}
        expected (e/app (c "regrPropInst") (c "regrP"))]
    (doseq [[label resolve] [["recursive" #(inst/synthesize* %1 env %2 goal 0)]
                             ["legacy tabled" #(inst/tabled-synthesize %1 env %2 goal)]]]
      (testing label
        (is (nil? (resolve (tc/mk-tc-state env) {(nm "RegrU") [bad]}))
            "an incompatible candidate is an ordinary mismatch")
        (let [st (tc/mk-tc-state env)
              result (resolve st {(nm "RegrU") [bad good]})]
          (is (= expected result) "search continues to the compatible candidate")
          (when result
            (is (tc/is-def-eq st (tc/infer-type st result) goal))
            (is (some? (env/check-constant
                        env (env/mk-thm (nm (str "regrChecked" label)) [] goal result)))
                "the successful proof passes kernel admission")))))))

(deftest test-direct-search-reports-depth-exhaustion
  ;; A direct synthesize* call whose search fails only because the depth bound cut a path is
  ;; exhausted, not negative: it names the bound (Lean checkSystem), while backtracking past
  ;; individual cuts still works.
  (let [env (require-env)
        goal (e/app (e/const' (name/from-string "Decidable") [])
                    (e/app* (e/const' (name/from-string "And") [])
                            (e/const' (name/from-string "True") []) (e/const' (name/from-string "True") [])))
        ;; an explicit index: the legacy name-scan index also lists Classical.propDecidable
        ;; (no subgoals), which would answer at depth 0 (backlog G19)
        dec (name/from-string "Decidable")
        idx {dec [{:name (name/from-string "instDecidableAnd") :priority 1000}
                  {:name (name/from-string "instDecidableTrue") :priority 1000}]}]
    (binding [config/*max-synth-depth* 0]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"exhausted the search depth bound"
                            (inst/synthesize* (tc/mk-tc-state env) env idx goal 0))))
    (is (some? (inst/synthesize* (tc/mk-tc-state env) env idx goal 0)))))

(deftest registered-instances-only
  (let [base (require-env)
        nat (e/const' (name/from-string "Nat") [])
        goal (e/app (e/const' (name/from-string "Add") [lvl/zero]) nat)
        empty-env (env/with-extension base :instances {})
        raw-env (env/with-extension base :instances nil)]
    (testing "declarations with instance-like names do not populate an empty registry"
      (is (some? (env/lookup base (name/from-string "instAddNat"))))
      (is (some? (inst/synthesize* (tc/mk-tc-state base) base (inst/index-for base) goal 0)))
      (is (nil? (inst/synthesize* (tc/mk-tc-state empty-env) empty-env {} goal 0))))
    (testing "synthesis without an environment registry fails loudly"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"no instance registry"
                            (inst/synthesize* (tc/mk-tc-state raw-env) raw-env @test-index goal 0))))
    (testing "scoped Classical instances are absent from the bundled global registry"
      (is (not-any? #(= "Classical.propDecidable" (str (:name %)))
                    (mapcat val (inst/index-for base)))))))
