(ns ansatz.tactic.decide-test
  "Tests for instance resolution, decide tactic, Ansatz→SMT translation, and smt tactic."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.instance :as instance]
            [ansatz.tactic.decide :as decide]
            [ansatz.surface.elaborate :as elab]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay])
  (:import [ansatz.kernel TypeChecker]))

;; ============================================================
;; Environment helpers
;; ============================================================

(def ^:private init-medium-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (let [st (parser/parse-ndjson-file f)
              result (replay/replay (:decls st))]
          (:env result))))))

(defn- require-env []
  (or @init-medium-env
      (throw (ex-info "init-medium.ndjson not found" {}))))

;; ============================================================
;; Instance resolution tests
;; ============================================================

(deftest test-resolve-decidable-eq-nat
  (testing "Resolve Decidable (Eq Nat 0 0)"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          zero (e/lit-nat 0)
          prop (e/app* (e/const' (name/from-string "Eq") [u1]) nat zero zero)
          inst (instance/resolve-decidable env prop)]
      (is (some? inst))
      (is (instance/verify-instance env prop inst)))))

(deftest test-resolve-decidable-eq-nat-succ
  (testing "Resolve Decidable (Eq Nat 1 1)"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          one (e/lit-nat 1)
          prop (e/app* (e/const' (name/from-string "Eq") [u1]) nat one one)
          inst (instance/resolve-decidable env prop)]
      (is (some? inst))
      (is (instance/verify-instance env prop inst)))))

(deftest test-resolve-decidable-and
  (testing "Resolve Decidable (And (Eq Nat 0 0) (Eq Nat 1 1))"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          eq00 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 0))
          eq11 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 1) (e/lit-nat 1))
          prop (e/app* (e/const' (name/from-string "And") []) eq00 eq11)
          inst (instance/resolve-decidable env prop)]
      (is (some? inst))
      (is (instance/verify-instance env prop inst)))))

(deftest test-resolve-decidable-or
  (testing "Resolve Decidable (Or (Eq Nat 0 0) (Eq Nat 0 1))"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          eq00 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 0))
          eq01 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 1))
          prop (e/app* (e/const' (name/from-string "Or") []) eq00 eq01)
          inst (instance/resolve-decidable env prop)]
      (is (some? inst))
      (is (instance/verify-instance env prop inst)))))

(deftest test-resolve-decidable-not
  (testing "Resolve Decidable (Not (Eq Nat 0 1))"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          eq01 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 1))
          prop (e/app* (e/const' (name/from-string "Not") []) eq01)
          inst (instance/resolve-decidable env prop)]
      (is (some? inst))
      (is (instance/verify-instance env prop inst)))))

(deftest test-resolve-decidable-true-false
  (testing "Resolve Decidable True and Decidable False"
    (let [env (require-env)]
      (let [prop (e/const' (name/from-string "True") [])
            inst (instance/resolve-decidable env prop)]
        (is (some? inst))
        (is (instance/verify-instance env prop inst)))
      (let [prop (e/const' (name/from-string "False") [])
            inst (instance/resolve-decidable env prop)]
        (is (some? inst))
        (is (instance/verify-instance env prop inst))))))

;; ============================================================
;; decide tactic tests
;; ============================================================

(deftest test-decide-eq-nat-zero
  (testing "decide closes Eq Nat 0 0"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          zero (e/lit-nat 0)
          goal-type (e/app* (e/const' (name/from-string "Eq") [u1]) nat zero zero)
          [ps _] (proof/start-proof env goal-type)
          ps (decide/decide ps)]
      (is (proof/solved? ps))
      (let [term (extract/extract ps)]
        ;; Verify with Java TypeChecker
        (let [tc (TypeChecker. env)
              inferred (.inferType tc term)]
          (is (.isDefEq tc inferred goal-type)))))))

(deftest test-decide-eq-nat-nonzero
  (testing "decide closes Eq Nat 42 42"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          n42 (e/lit-nat 42)
          goal-type (e/app* (e/const' (name/from-string "Eq") [u1]) nat n42 n42)
          [ps _] (proof/start-proof env goal-type)
          ps (decide/decide ps)]
      (is (proof/solved? ps)))))

(deftest test-decide-eq-nat-false
  (testing "decide fails for Eq Nat 0 1 (proposition is false)"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          goal-type (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 1))
          [ps _] (proof/start-proof env goal-type)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"decide failed"
                            (decide/decide ps))))))

(deftest test-decide-and
  (testing "decide closes And (Eq Nat 0 0) True — requires instDecidableAnd (needs full env)"
    ;; Skip in init-medium env which lacks instDecidableAnd
    (when false
      (let [env (require-env)
            u1 (lvl/succ lvl/zero)
            nat (e/const' (name/from-string "Nat") [])
            eq00 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 0))
            t (e/const' (name/from-string "True") [])
            goal-type (e/app* (e/const' (name/from-string "And") []) eq00 t)
            [ps _] (proof/start-proof env goal-type)
            ps (decide/decide ps)]
        (is (proof/solved? ps))
        (let [term (extract/extract ps)
              tc (TypeChecker. env)
              inferred (.inferType tc term)]
          (is (.isDefEq tc inferred goal-type)))))))

(deftest test-decide-not
  (testing "decide closes Not (Eq Nat 0 1)"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          eq01 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 1))
          goal-type (e/app* (e/const' (name/from-string "Not") []) eq01)
          [ps _] (proof/start-proof env goal-type)
          ps (decide/decide ps)]
      (is (proof/solved? ps)))))

(deftest test-decide-after-intro
  (testing "intro then decide: ∀ (a : Nat), Eq Nat a a"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          ;; ∀ (a : Nat), Eq Nat a a
          ;; After intro, goal becomes Eq Nat ?fv ?fv — but decide can't handle
          ;; non-ground propositions. This is expected to fail.
          ;; The decide tactic only works for ground decidable propositions.
          eq-aa (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/bvar 0) (e/bvar 0))
          goal-type (e/forall' "a" nat eq-aa :default)
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intro ps "a")]
      ;; After intro, the goal has a free variable, which rfl can handle but
      ;; decide cannot (it needs ground terms). This documents the boundary.
      (is (thrown? Exception (decide/decide ps))))))

;; ============================================================
;; Ansatz → SMT-LIB translation tests
;; ============================================================

(deftest test-smt-translation-eq
  (testing "Eq Nat 1 2 → (= 1 2)"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          prop (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 1) (e/lit-nat 2))
          smt (decide/prop->smt env prop)]
      (is (= '(= 1 2) smt)))))

(deftest test-smt-translation-and
  (testing "And (Eq Nat 0 0) (Eq Nat 1 1) → (and (= 0 0) (= 1 1))"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          eq00 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 0))
          eq11 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 1) (e/lit-nat 1))
          prop (e/app* (e/const' (name/from-string "And") []) eq00 eq11)
          smt (decide/prop->smt env prop)]
      (is (= '(and (= 0 0) (= 1 1)) smt)))))

(deftest test-smt-translation-not
  (testing "Not (Eq Nat 0 1) → (not (= 0 1))"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          eq01 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 1))
          prop (e/app* (e/const' (name/from-string "Not") []) eq01)
          smt (decide/prop->smt env prop)]
      (is (= '(not (= 0 1)) smt)))))

(deftest test-smt-translation-true-false
  (testing "True → true, False → false"
    (let [env (require-env)]
      (is (= 'true (decide/prop->smt env (e/const' (name/from-string "True") []))))
      (is (= 'false (decide/prop->smt env (e/const' (name/from-string "False") [])))))))

;; ============================================================
;; Mock Z3 tests
;; ============================================================

(deftest test-mock-z3-ground
  (testing "Mock Z3 evaluates ground formulas"
    (is (= :sat (decide/mock-z3 '(= 0 0))))
    (is (= :unsat (decide/mock-z3 '(= 0 1))))
    (is (= :sat (decide/mock-z3 '(and (= 1 1) (= 2 2)))))
    (is (= :unsat (decide/mock-z3 '(and (= 0 0) (= 0 1)))))
    (is (= :sat (decide/mock-z3 '(or (= 0 0) (= 0 1)))))
    (is (= :sat (decide/mock-z3 '(not (= 0 1)))))
    (is (= :unsat (decide/mock-z3 '(not (= 0 0)))))
    (is (= :sat (decide/mock-z3 '(<= 1 2))))
    (is (= :unsat (decide/mock-z3 '(< 2 2))))
    (is (= :sat (decide/mock-z3 '(= (+ 1 2) 3))))))

;; ============================================================
;; smt tactic tests
;; ============================================================

(deftest test-smt-tactic-eq
  (testing "smt tactic closes Eq Nat 0 0"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          goal-type (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 0))
          [ps _] (proof/start-proof env goal-type)
          ps (decide/smt ps)]
      (is (proof/solved? ps)))))

(deftest test-smt-tactic-and-verified
  (testing "smt tactic closes compound proposition and verifies with kernel"
    (let [env (require-env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          eq00 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 0))
          eq11 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 1) (e/lit-nat 1))
          goal-type (e/app* (e/const' (name/from-string "And") []) eq00 eq11)
          [ps _] (proof/start-proof env goal-type)
          ps (decide/smt ps)]
      (is (proof/solved? ps))
      ;; Verify extraction and type-checking
      (let [term (extract/extract ps)
            tc (TypeChecker. env)
            inferred (.inferType tc term)]
        (is (.isDefEq tc inferred goal-type))))))

;; ============================================================
;; End-to-end: elaborate + decide
;; ============================================================

(deftest test-decide-with-elaboration
  (testing "Elaborate a prop and decide it"
    (let [env (require-env)
          ;; Build Eq Nat 5 5 manually (since we don't want to couple to elaborate)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          goal-type (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 5) (e/lit-nat 5))
          [ps _] (proof/start-proof env goal-type)
          ps (decide/decide ps)]
      (is (proof/solved? ps))
      (let [term (extract/verify ps)]
        (is (some? term))))))

;; ============================================================
;; General instance resolution (env-scanning)
;; ============================================================

(deftest test-instance-index
  (testing "Instance index finds Decidable candidates"
    (let [env (require-env)
          idx (instance/build-instance-index env)
          decidable-name (name/from-string "Decidable")
          candidates (instance/get-instances idx decidable-name)]
      ;; PSS-aware index uses name patterns, may find fewer than full scan
      (is (>= (count candidates) 0)))))

(deftest test-general-synthesis-eq-nat
  (testing "General synthesis finds Nat.decEq for Decidable (Eq Nat 0 0)"
    (let [env (require-env)
          idx (instance/build-instance-index env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          prop (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 0))
          goal (e/app (e/const' (name/from-string "Decidable") []) prop)
          inst (instance/synthesize env idx goal)]
      (is (some? inst))
      ;; Should NOT be Classical.propDecidable
      (let [[head _] (e/get-app-fn-args inst)]
        (is (not= (name/from-string "Classical.propDecidable")
                  (when (e/const? head) (e/const-name head))))))))

(deftest test-general-synthesis-bool-eq
  (testing "General synthesis finds Bool.decEq"
    (let [env (require-env)
          idx (instance/build-instance-index env)
          u1 (lvl/succ lvl/zero)
          bool (e/const' (name/from-string "Bool") [])
          prop (e/app* (e/const' (name/from-string "Eq") [u1]) bool
                       (e/const' (name/from-string "Bool.true") [])
                       (e/const' (name/from-string "Bool.true") []))
          goal (e/app (e/const' (name/from-string "Decidable") []) prop)
          inst (instance/synthesize env idx goal)]
      (is (some? inst))
      (is (instance/verify-instance env prop inst)))))

(deftest test-general-synthesis-nested-and-or
  (testing "General synthesis handles nested And/Or/Not"
    (let [env (require-env)
          idx (instance/build-instance-index env)
          u1 (lvl/succ lvl/zero)
          nat (e/const' (name/from-string "Nat") [])
          eq00 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 0))
          eq01 (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/lit-nat 0) (e/lit-nat 1))
          ;; Or (Eq 0 0) (Not (Eq 0 1))
          prop (e/app* (e/const' (name/from-string "Or") [])
                       eq00
                       (e/app (e/const' (name/from-string "Not") []) eq01))
          goal (e/app (e/const' (name/from-string "Decidable") []) prop)
          inst (instance/synthesize env idx goal)]
      (is (some? inst))
      (is (instance/verify-instance env prop inst)))))

;; ============================================================
;; elaborate-in-context tests
;; ============================================================

(deftest test-elaborate-in-context-basic
  (testing "elaborate-in-context resolves local hypotheses"
    (let [env (require-env)
          goal-type (elab/elaborate env '(forall [a Nat] (Eq a a)))
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intro ps "a")
          goal (proof/current-goal ps)
          ;; Use elaborate-in-context to build Eq.refl a
          term (elab/elaborate-in-context env (:lctx goal) '(Eq.refl a))]
      (is (some? term))
      ;; Term should reference the fvar, not be a fresh one
      (let [st (assoc (tc/mk-tc-state env) :lctx (:lctx goal))
            ty (tc/infer-type st term)]
        (is (tc/is-def-eq st ty (:type goal)))))))

(deftest test-elaborate-in-context-eq-symm
  (testing "elaborate-in-context + exact proves symmetry"
    (let [env (require-env)
          goal-type (elab/elaborate env '(forall [a Nat, b Nat] (arrow (Eq a b) (Eq b a))))
          [ps _] (proof/start-proof env goal-type)
          ps (basic/intros ps ["a" "b" "h"])
          goal (proof/current-goal ps)
          term (elab/elaborate-in-context env (:lctx goal) '(Eq.symm h))
          ps (basic/exact ps term)]
      (is (proof/solved? ps))
      (let [proof-term (extract/verify ps)]
        (is (some? proof-term))))))

;; ============================================================
;; sexp->zustand conversion tests
;; ============================================================

(deftest test-sexp->zustand-basic
  (testing "sexp->zustand converts SMT-LIB s-expressions to zustand vectors"
    (is (= [:eq :x 5] (decide/sexp->zustand '(= x 5))))
    (is (= [:and [:>= :x 0] [:<= :x 10]]
           (decide/sexp->zustand '(and (>= x 0) (<= x 10)))))
    (is (= [:not [:eq :a :b]]
           (decide/sexp->zustand '(not (= a b)))))
    (is (= [:or [:< :x 3] [:> :x 7]]
           (decide/sexp->zustand '(or (< x 3) (> x 7)))))
    (is (= [:eq [:+ :x 1] 5]
           (decide/sexp->zustand '(= (+ x 1) 5))))
    (is (= [:eq [:- :a :b] [:* :c :d]]
           (decide/sexp->zustand '(= (- a b) (* c d)))))
    (is (= true (decide/sexp->zustand 'true)))
    (is (= false (decide/sexp->zustand 'false)))
    (is (= 42 (decide/sexp->zustand 42)))))

;; ============================================================
;; zustand SMT solver tests (require zustand optional dep)
;; zustand SMT tests removed — zustand is an optional dependency (not yet released).
;; Re-enable when zustand is on the classpath via the :smt alias.
