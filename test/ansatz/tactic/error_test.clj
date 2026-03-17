(ns ansatz.tactic.error-test
  "Tests for tactic error handling, edge cases, and error message quality.
   Verifies that wrong tactics, unsolvable goals, and type errors
   produce actionable error messages."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.simp :as simp]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

(def ^:private test-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(defn- require-env [] (or @test-env (throw (ex-info "init-medium.ndjson not found" {}))))

(defn- mk-proof-state
  "Create a proof state for a goal type."
  [goal-type]
  (let [env (require-env)
        [ps _] (proof/start-proof env goal-type)]
    ps))

;; ============================================================
;; Apply error cases
;; ============================================================

(deftest test-apply-nonexistent-const
  (testing "Apply with nonexistent constant throws"
    (let [nat (e/const' (name/from-string "Nat") [])
          goal (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                       nat (e/lit-nat 0) (e/lit-nat 0))
          ps (mk-proof-state goal)]
      (is (thrown? Exception
                   (basic/apply-tac ps (e/const' (name/from-string "nonexistent_lemma") [])))))))

(deftest test-apply-wrong-result-type
  (testing "Apply with wrong result type gives informative error"
    (let [nat (e/const' (name/from-string "Nat") [])
          ;; Goal: 0 = 0
          goal (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                       nat (e/lit-nat 0) (e/lit-nat 0))
          ps (mk-proof-state goal)
          ;; Try to apply Nat.succ (returns Nat, not Eq)
          succ (e/const' (name/from-string "Nat.succ") [])]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"result type does not match goal"
                            (basic/apply-tac ps succ))))))

;; ============================================================
;; Rfl error cases
;; ============================================================

(deftest test-rfl-not-eq
  (testing "Rfl on non-Eq goal throws"
    (let [nat (e/const' (name/from-string "Nat") [])
          ps (mk-proof-state nat)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not an Eq"
                            (basic/rfl ps))))))

(deftest test-rfl-not-defeq
  (testing "Rfl on Eq with non-def-eq sides throws"
    (let [nat (e/const' (name/from-string "Nat") [])
          ;; Goal: 0 = 1 — not reflexive
          goal (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                       nat (e/lit-nat 0) (e/lit-nat 1))
          ps (mk-proof-state goal)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not definitionally equal"
                            (basic/rfl ps))))))

;; ============================================================
;; Assumption error cases
;; ============================================================

(deftest test-assumption-empty-ctx
  (testing "Assumption with no hypotheses throws"
    (let [nat (e/const' (name/from-string "Nat") [])
          goal (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                       nat (e/lit-nat 0) (e/lit-nat 0))
          ps (mk-proof-state goal)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"No matching hypothesis"
                            (basic/assumption ps))))))

;; ============================================================
;; Intro error cases
;; ============================================================

(deftest test-intro-not-forall
  (testing "Intro on non-forall goal throws"
    (let [nat (e/const' (name/from-string "Nat") [])
          ps (mk-proof-state nat)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not a forall"
                            (basic/intro ps))))))

;; ============================================================
;; Simp error cases
;; ============================================================

(deftest test-simp-simplifies-to-false
  (testing "Simp on false equality simplifies to False and throws"
    (let [nat (e/const' (name/from-string "Nat") [])
          ;; Goal: succ 0 = 2 (i.e. 1 = 2) — simp detects this is False
          goal (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                       nat
                       (e/app (e/const' (name/from-string "Nat.succ") []) (e/lit-nat 0))
                       (e/lit-nat 2))
          ps (mk-proof-state goal)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"False"
                            (simp/simp ps []))))))

;; ============================================================
;; No goals error cases
;; ============================================================

(deftest test-tactic-on-solved
  (testing "Tactic on already-solved proof state throws"
    (let [nat (e/const' (name/from-string "Nat") [])
          goal (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                       nat (e/lit-nat 0) (e/lit-nat 0))
          ps (mk-proof-state goal)
          ps (basic/rfl ps)]
      ;; Proof is solved, another tactic should fail
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"No goals"
                            (basic/rfl ps))))))

;; ============================================================
;; Combinators
;; ============================================================

(deftest test-try-tac-catches-failure
  (testing "try-tac returns original state on failure"
    (let [nat (e/const' (name/from-string "Nat") [])
          ps (mk-proof-state nat)
          ;; Intro on Nat goal should fail, but try-tac catches
          result (basic/try-tac ps (fn [ps'] (basic/intro ps')))]
      (is (= (:goals result) (:goals ps))
          "Goals unchanged after failed try"))))

(deftest test-first-tac-all-fail
  (testing "first-tac with all failing tactics throws"
    (let [nat (e/const' (name/from-string "Nat") [])
          ps (mk-proof-state nat)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"all tactics failed"
                            (basic/first-tac ps
                                             (fn [ps'] (basic/intro ps'))
                                             (fn [ps'] (basic/rfl ps'))))))))
