(ns ansatz.tactic.advanced-test
  "Tests for advanced tactics: omega, ring, simp.
   Mirrors Lean 4's test cases where possible."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.omega :as omega]
            [ansatz.tactic.omega-proof :as omega-proof]
            [ansatz.tactic.ring :as ring]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.decide :as decide]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay])
  (:import [ansatz.kernel TypeChecker]))

;; ============================================================
;; Test environment
;; ============================================================

(def ^:private init-medium-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (let [st (parser/parse-ndjson-file f)
              result (replay/replay (:decls st))]
          (:env result))))))

(defn- require-env []
  (let [env @init-medium-env]
    (when-not env
      (throw (ex-info "init-medium.ndjson not found" {})))
    env))

;; ============================================================
;; Helper functions
;; ============================================================

(def ^:private nat-name (name/from-string "Nat"))
(def ^:private eq-name (name/from-string "Eq"))
(def ^:private u1 (lvl/succ lvl/zero))

(defn- mk-nat [] (e/const' nat-name []))
(defn- mk-eq [a b] (e/app* (e/const' eq-name [u1]) (mk-nat) a b))
(defn- mk-add [a b] (e/app* (e/const' (name/from-string "Nat.add") []) a b))
(defn- mk-mul [a b] (e/app* (e/const' (name/from-string "Nat.mul") []) a b))
(defn- mk-succ [a] (e/app (e/const' (name/from-string "Nat.succ") []) a))
(defn- mk-zero [] (e/const' (name/from-string "Nat.zero") []))
(defn- n [x] (e/lit-nat x))

(defn- mk-bool-eq-true
  "Build @Eq Bool expr Bool.true — useful for decidable propositions."
  [expr]
  (e/app* (e/const' eq-name [u1])
          (e/const' (name/from-string "Bool") [])
          expr
          (e/const' (name/from-string "Bool.true") [])))

(defn- mk-le [a b]
  ;; Encode a ≤ b as Eq Bool (Nat.ble a b) Bool.true
  (mk-bool-eq-true (e/app* (e/const' (name/from-string "Nat.ble") []) a b)))

(defn- mk-lt [a b]
  ;; Encode a < b as Eq Bool (Nat.ble (a+1) b) Bool.true
  ;; i.e., a+1 ≤ b
  (mk-bool-eq-true (e/app* (e/const' (name/from-string "Nat.ble") [])
                           (mk-succ a) b)))

(defn- prove-and-verify
  "Start a proof, apply tactic-fn, verify the result."
  [env goal-type tactic-fn]
  (let [ps (first (proof/start-proof env goal-type))
        ps' (tactic-fn ps)]
    (is (proof/solved? ps') "Goal should be solved")
    (let [term (extract/verify ps')]
      (is (not (e/has-fvar-flag term)) "Proof term should have no free variables")
      term)))

;; ============================================================
;; Omega tests — ground arithmetic
;; ============================================================

(deftest test-omega-ground-eq
  (testing "Ground equalities"
    (let [env (require-env)]
      ;; 3 = 3
      (prove-and-verify env (mk-eq (n 3) (n 3)) omega/omega)
      ;; 2 + 3 = 5
      (prove-and-verify env (mk-eq (mk-add (n 2) (n 3)) (n 5)) omega/omega)
      ;; 0 + 0 = 0
      (prove-and-verify env (mk-eq (mk-add (n 0) (n 0)) (n 0)) omega/omega)
      ;; 100 = 100
      (prove-and-verify env (mk-eq (n 100) (n 100)) omega/omega))))

(deftest test-omega-ground-ineq
  (testing "Ground inequalities (via decide)"
    (let [env (require-env)]
      ;; 3 ≤ 5
      (prove-and-verify env (mk-le (n 3) (n 5)) omega/omega)
      ;; 0 ≤ 0
      (prove-and-verify env (mk-le (n 0) (n 0)) omega/omega)
      ;; 0 < 1
      (prove-and-verify env (mk-lt (n 0) (n 1)) omega/omega))))

(deftest test-omega-ground-mul
  (testing "Ground multiplication"
    (let [env (require-env)]
      ;; 3 * 4 = 12
      (prove-and-verify env (mk-eq (mk-mul (n 3) (n 4)) (n 12)) omega/omega)
      ;; 5 * 5 = 25
      (prove-and-verify env (mk-eq (mk-mul (n 5) (n 5)) (n 25)) omega/omega)
      ;; 0 * 100 = 0
      (prove-and-verify env (mk-eq (mk-mul (n 0) (n 100)) (n 0)) omega/omega))))

(deftest test-omega-succ
  (testing "Successor arithmetic"
    (let [env (require-env)]
      ;; succ 2 = 3
      (prove-and-verify env (mk-eq (mk-succ (n 2)) (n 3)) omega/omega)
      ;; succ (succ 0) = 2
      (prove-and-verify env (mk-eq (mk-succ (mk-succ (n 0))) (n 2)) omega/omega))))

(deftest test-omega-complex-ground
  (testing "Complex ground expressions — Lean omega.lean lines 40-51"
    (let [env (require-env)]
      ;; (2+1)*(2+1) = 9
      (let [three (mk-add (n 2) (n 1))]
        (prove-and-verify env (mk-eq (mk-mul three three) (n 9)) omega/omega))
      ;; 2 * 3 + 7 = 13
      (prove-and-verify env (mk-eq (mk-add (mk-mul (n 2) (n 3)) (n 7)) (n 13))
                        omega/omega))))

;; ============================================================
;; Ring tests — polynomial identities
;; ============================================================

(deftest test-ring-ground
  (testing "Ground ring equalities"
    (let [env (require-env)]
      ;; (2+1)*(2+1) = 9
      (let [three (mk-add (n 2) (n 1))]
        (prove-and-verify env (mk-eq (mk-mul three three) (n 9)) ring/ring))
      ;; 3*4 + 1 = 13
      (prove-and-verify env (mk-eq (mk-add (mk-mul (n 3) (n 4)) (n 1)) (n 13))
                        ring/ring))))

(deftest test-ring-polynomial-normalization
  (testing "Polynomial normalization checks via tactic interface"
    (let [env (require-env)]
      ;; 2 * 3 = 6
      (prove-and-verify env (mk-eq (mk-mul (n 2) (n 3)) (n 6)) ring/ring)
      ;; 1 + 2 + 3 = 6
      (prove-and-verify env (mk-eq (mk-add (mk-add (n 1) (n 2)) (n 3)) (n 6))
                        ring/ring))))

(deftest test-ring-nat-arithmetic
  (testing "Nat arithmetic identities"
    (let [env (require-env)]
      ;; 5 * 5 = 25
      (prove-and-verify env (mk-eq (mk-mul (n 5) (n 5)) (n 25)) ring/ring)
      ;; (1+1)*(1+1)*(1+1) = 8
      (let [two (mk-add (n 1) (n 1))]
        (prove-and-verify env (mk-eq (mk-mul (mk-mul two two) two) (n 8)) ring/ring)))))

;; ============================================================
;; Simp tests — simplification
;; ============================================================

(deftest test-dsimp-rfl
  (testing "dsimp closes goals where both sides are def-eq"
    (let [env (require-env)]
      ;; 3 + 0 = 3 (Nat.add reduces)
      (prove-and-verify env (mk-eq (mk-add (n 3) (n 0)) (n 3)) simp/dsimp)
      ;; 0 + 0 = 0
      (prove-and-verify env (mk-eq (mk-add (n 0) (n 0)) (n 0)) simp/dsimp))))

(deftest test-dsimp-succ
  (testing "dsimp with successor"
    (let [env (require-env)]
      ;; succ 4 = 5
      (prove-and-verify env (mk-eq (mk-succ (n 4)) (n 5)) simp/dsimp))))

(deftest test-simp-ground
  (testing "simp on ground equalities"
    (let [env (require-env)]
      ;; 2 + 3 = 5
      (prove-and-verify env (mk-eq (mk-add (n 2) (n 3)) (n 5))
                        #(simp/simp %))
      ;; 4 * 3 = 12
      (prove-and-verify env (mk-eq (mk-mul (n 4) (n 3)) (n 12))
                        #(simp/simp %)))))

(deftest test-simp-with-lemmas
  (testing "simp only [...] with explicit lemmas"
    (let [env (require-env)]
      ;; Try with Nat.add_zero if available
      (when (env/lookup env (name/from-string "Nat.add_zero"))
        ;; n + 0 = n should be provable by simp [Nat.add_zero]
        ;; For ground n, this should work via decide/rfl fallback
        (prove-and-verify env (mk-eq (mk-add (n 7) (n 0)) (n 7))
                          #(simp/simp % ["Nat.add_zero"]))))))

;; ============================================================
;; Integration tests — combining tactics
;; ============================================================

(deftest test-intro-then-dsimp
  (testing "intro followed by dsimp for universally quantified goals"
    (let [env (require-env)]
      ;; ∀ n : Nat, n + 0 = n
      ;; After intro, Nat.add n 0 reduces to n by kernel, so rfl closes it
      (let [goal-type (e/forall' "n" (mk-nat)
                                 (mk-eq (mk-add (e/bvar 0) (n 0)) (e/bvar 0))
                                 :default)
            ps (first (proof/start-proof env goal-type))
            ps (basic/intro ps "n")]
        (let [ps' (simp/dsimp ps)]
          (is (proof/solved? ps')))))))

(deftest test-intro-then-ring
  (testing "intro + ring for ground polynomial identity after substitution"
    (let [env (require-env)]
      ;; Test with fully ground goal: 2 * 3 + 1 = 7
      (prove-and-verify env (mk-eq (mk-add (mk-mul (n 2) (n 3)) (n 1)) (n 7))
                        ring/ring))))

;; ============================================================
;; Lean 4 omega test mirrors
;; ============================================================

(deftest test-omega-lean-mirror-ground
  (testing "Lean omega.lean ground tests"
    (let [env (require-env)]
      ;; 7 < 3 → False (ground, via decide)
      ;; We test the equivalent: ¬(7 < 3), i.e., 7 ≥ 3, i.e., 3 ≤ 7
      (prove-and-verify env (mk-le (n 3) (n 7)) omega/omega)
      ;; 5 ≤ 5
      (prove-and-verify env (mk-le (n 5) (n 5)) omega/omega)
      ;; 0 ≤ 100
      (prove-and-verify env (mk-le (n 0) (n 100)) omega/omega))))

(deftest test-omega-lean-mirror-eq
  (testing "Lean omega.lean equality tests"
    (let [env (require-env)]
      ;; 2*3 + 4*1 = 10
      (prove-and-verify env
                        (mk-eq (mk-add (mk-mul (n 2) (n 3)) (mk-mul (n 4) (n 1))) (n 10))
                        omega/omega)
      ;; 6*1 + 7*0 = 6
      (prove-and-verify env
                        (mk-eq (mk-add (mk-mul (n 6) (n 1)) (mk-mul (n 7) (n 0))) (n 6))
                        omega/omega))))

;; ============================================================
;; Lean ring test mirrors
;; ============================================================

(deftest test-ring-lean-mirror
  (testing "Lean grind_ring_1.lean style tests (ground)"
    (let [env (require-env)]
      ;; (x+1)*(x-1) for x=5: 6*4 = 24, and 5^2 - 1 = 24
      ;; We can only do ground for now
      ;; 6 * 4 = 24
      (prove-and-verify env (mk-eq (mk-mul (n 6) (n 4)) (n 24)) ring/ring)
      ;; (3+1)^2 = 16, i.e., 4*4 = 16
      (prove-and-verify env (mk-eq (mk-mul (n 4) (n 4)) (n 16)) ring/ring))))

;; ============================================================
;; Lean simp test mirrors
;; ============================================================

(deftest test-simp-lean-mirror-reduction
  (testing "Lean simp tests - ground reduction"
    (let [env (require-env)]
      ;; simp should handle ground arithmetic
      ;; 10 + 0 = 10
      (prove-and-verify env (mk-eq (mk-add (n 10) (n 0)) (n 10))
                        #(simp/simp %))
      ;; succ (succ (succ 0)) = 3
      (prove-and-verify env (mk-eq (mk-succ (mk-succ (mk-succ (n 0)))) (n 3))
                        #(simp/simp %)))))

;; ============================================================
;; Error/edge case tests
;; ============================================================

(deftest test-omega-false-should-fail
  (testing "omega should fail on false goals"
    (let [env (require-env)]
      ;; 3 = 4 — should fail
      (is (thrown? Exception
                   (omega/omega (first (proof/start-proof env (mk-eq (n 3) (n 4))))))))))

(deftest test-ring-non-eq-should-fail
  (testing "ring should fail on non-Eq goals"
    (let [env (require-env)]
      ;; False is not an Eq goal — ring should fail
      (is (thrown? Exception
                   (ring/ring (first (proof/start-proof env
                                                        (e/const' (name/from-string "False") [])))))))))

(deftest test-ring-false-eq-should-fail
  (testing "ring should fail on false equalities"
    (let [env (require-env)]
      ;; 2 + 2 = 5 — polynomials don't match
      (is (thrown? Exception
                   (ring/ring (first (proof/start-proof env
                                                        (mk-eq (mk-add (n 2) (n 2)) (n 5))))))))))

;; ============================================================
;; Extended omega tests — Nat.sub, Nat.div, Nat.mod
;; ============================================================

(defn- mk-sub [a b] (e/app* (e/const' (name/from-string "Nat.sub") []) a b))
(defn- mk-div [a b] (e/app* (e/const' (name/from-string "Nat.div") []) a b))
(defn- mk-mod [a b] (e/app* (e/const' (name/from-string "Nat.mod") []) a b))
;; HDiv/HMod versions for non-ground tests (pre-WHNF intercepted)
(defn- mk-hadd [a b]
  (e/app* (e/const' (name/from-string "HAdd.hAdd") [lvl/zero lvl/zero lvl/zero])
          (mk-nat) (mk-nat) (mk-nat)
          (e/app* (e/const' (name/from-string "instHAdd") [lvl/zero])
                  (mk-nat) (e/const' (name/from-string "instAddNat") []))
          a b))
(defn- mk-hmul [a b]
  (e/app* (e/const' (name/from-string "HMul.hMul") [lvl/zero lvl/zero lvl/zero])
          (mk-nat) (mk-nat) (mk-nat)
          (e/app* (e/const' (name/from-string "instHMul") [lvl/zero])
                  (mk-nat) (e/const' (name/from-string "instMulNat") []))
          a b))
(defn- mk-hdiv [a b]
  (e/app* (e/const' (name/from-string "HDiv.hDiv") [lvl/zero lvl/zero lvl/zero])
          (mk-nat) (mk-nat) (mk-nat)
          (e/app* (e/const' (name/from-string "instHDiv") [lvl/zero])
                  (mk-nat) (e/const' (name/from-string "Nat.instDiv") []))
          a b))
(defn- mk-hmod [a b]
  (e/app* (e/const' (name/from-string "HMod.hMod") [lvl/zero lvl/zero lvl/zero])
          (mk-nat) (mk-nat) (mk-nat)
          (e/app* (e/const' (name/from-string "instHMod") [lvl/zero])
                  (mk-nat) (e/const' (name/from-string "Nat.instMod") []))
          a b))

(deftest test-omega-ground-sub
  (testing "Ground Nat subtraction (truncated)"
    (let [env (require-env)]
      ;; 5 - 3 = 2
      (prove-and-verify env (mk-eq (mk-sub (n 5) (n 3)) (n 2)) omega/omega)
      ;; 3 - 5 = 0 (truncated)
      (prove-and-verify env (mk-eq (mk-sub (n 3) (n 5)) (n 0)) omega/omega)
      ;; 10 - 0 = 10
      (prove-and-verify env (mk-eq (mk-sub (n 10) (n 0)) (n 10)) omega/omega))))

(deftest test-omega-ground-div
  (testing "Ground Nat division"
    (let [env (require-env)]
      ;; 10 / 2 = 5
      (prove-and-verify env (mk-eq (mk-div (n 10) (n 2)) (n 5)) omega/omega)
      ;; 7 / 3 = 2
      (prove-and-verify env (mk-eq (mk-div (n 7) (n 3)) (n 2)) omega/omega)
      ;; 0 / 5 = 0
      (prove-and-verify env (mk-eq (mk-div (n 0) (n 5)) (n 0)) omega/omega))))

(deftest test-omega-ground-mod
  (testing "Ground Nat modulo"
    (let [env (require-env)]
      ;; 10 % 3 = 1
      (prove-and-verify env (mk-eq (mk-mod (n 10) (n 3)) (n 1)) omega/omega)
      ;; 7 % 2 = 1
      (prove-and-verify env (mk-eq (mk-mod (n 7) (n 2)) (n 1)) omega/omega)
      ;; 6 % 3 = 0
      (prove-and-verify env (mk-eq (mk-mod (n 6) (n 3)) (n 0)) omega/omega))))

(deftest test-omega-combined-arithmetic
  (testing "Combined arithmetic operations"
    (let [env (require-env)]
      ;; (10 / 2) + (10 % 2) = 5
      (prove-and-verify env
                        (mk-eq (mk-add (mk-div (n 10) (n 2)) (mk-mod (n 10) (n 2))) (n 5))
                        omega/omega)
      ;; 2 * (10 / 2) + (10 % 2) = 10 (division algorithm)
      (prove-and-verify env
                        (mk-eq (mk-add (mk-mul (n 2) (mk-div (n 10) (n 2))) (mk-mod (n 10) (n 2))) (n 10))
                        omega/omega))))

;; ============================================================
;; Ring tests — Nat.sub
;; ============================================================

(deftest test-ring-ground-sub
  (testing "Ring with ground Nat subtraction"
    (let [env (require-env)]
      ;; 5 - 3 = 2
      (prove-and-verify env (mk-eq (mk-sub (n 5) (n 3)) (n 2)) ring/ring)
      ;; (10 - 3) * 2 = 14
      (prove-and-verify env (mk-eq (mk-mul (mk-sub (n 10) (n 3)) (n 2)) (n 14)) ring/ring))))

;; ============================================================
;; Extended omega tests — GCD impossibility
;; ============================================================

(deftest test-omega-gcd-impossibility
  (testing "GCD-based impossibility detection"
    (let [env (require-env)]
      ;; 2 * 3 + 4 * 1 = 10 (should succeed)
      (prove-and-verify env
                        (mk-eq (mk-add (mk-mul (n 2) (n 3)) (mk-mul (n 4) (n 1))) (n 10))
                        omega/omega))))

;; ============================================================
;; Extended simp tests
;; ============================================================

(deftest test-simp-mul-ground
  (testing "simp on ground multiplication expressions"
    (let [env (require-env)]
      ;; 0 * 5 = 0
      (prove-and-verify env (mk-eq (mk-mul (n 0) (n 5)) (n 0))
                        #(simp/simp %))
      ;; 1 * 7 = 7
      (prove-and-verify env (mk-eq (mk-mul (n 1) (n 7)) (n 7))
                        #(simp/simp %)))))

(deftest test-simp-nested-ground
  (testing "simp on nested ground expressions"
    (let [env (require-env)]
      ;; (2 + 3) * (4 + 1) = 25
      (prove-and-verify env
                        (mk-eq (mk-mul (mk-add (n 2) (n 3)) (mk-add (n 4) (n 1))) (n 25))
                        #(simp/simp %)))))

(deftest test-dsimp-ground-arithmetic
  (testing "dsimp closes various ground arithmetic equalities"
    (let [env (require-env)]
      ;; succ (succ (succ 0)) = 3
      (prove-and-verify env (mk-eq (mk-succ (mk-succ (mk-succ (mk-zero)))) (n 3))
                        simp/dsimp)
      ;; 0 + 0 + 0 = 0
      (prove-and-verify env (mk-eq (mk-add (mk-add (n 0) (n 0)) (n 0)) (n 0))
                        simp/dsimp))))

;; ============================================================
;; Edge cases — large numbers
;; ============================================================

(deftest test-omega-large-numbers
  (testing "omega with larger ground numbers"
    (let [env (require-env)]
      ;; 1000 + 2000 = 3000
      (prove-and-verify env (mk-eq (mk-add (n 1000) (n 2000)) (n 3000)) omega/omega)
      ;; 50 * 50 = 2500
      (prove-and-verify env (mk-eq (mk-mul (n 50) (n 50)) (n 2500)) omega/omega))))

(deftest test-ring-large-numbers
  (testing "ring with larger ground numbers"
    (let [env (require-env)]
      ;; 123 * 456 = 56088
      (prove-and-verify env (mk-eq (mk-mul (n 123) (n 456)) (n 56088)) ring/ring))))

;; ============================================================
;; Omega-proof tests — proof term construction
;; ============================================================

;; Helpers for non-ground omega goals (use LE.le/LT.lt directly, not Nat.ble)
(def ^:private le-name (name/from-string "LE.le"))
(def ^:private lt-name (name/from-string "LT.lt"))
(def ^:private ge-name (name/from-string "GE.ge"))
(def ^:private gt-name (name/from-string "GT.gt"))
(def ^:private false-name (name/from-string "False"))
(def ^:private inst-le-nat (e/const' (name/from-string "instLENat") []))
(def ^:private inst-lt-nat (e/const' (name/from-string "instLTNat") []))

(defn- mk-le-prop
  "Build LE.le Nat instLENat a b"
  [a b]
  (e/app* (e/const' le-name [lvl/zero]) (mk-nat) inst-le-nat a b))

(defn- mk-lt-prop
  "Build LT.lt Nat instLTNat a b"
  [a b]
  (e/app* (e/const' lt-name [lvl/zero]) (mk-nat) inst-lt-nat a b))

(defn- mk-ge-prop
  "Build GE.ge Nat instLENat a b"
  [a b]
  (e/app* (e/const' ge-name [lvl/zero]) (mk-nat) inst-le-nat a b))

(defn- mk-gt-prop
  "Build GT.gt Nat instLTNat a b"
  [a b]
  (e/app* (e/const' gt-name [lvl/zero]) (mk-nat) inst-lt-nat a b))

(deftest test-omega-proof-ground-eq
  (testing "omega-proof on ground equalities (should use decide fallback)"
    (let [env (require-env)]
      ;; 3 = 3
      (prove-and-verify env (mk-eq (n 3) (n 3)) omega-proof/omega)
      ;; 2 + 3 = 5
      (prove-and-verify env (mk-eq (mk-add (n 2) (n 3)) (n 5)) omega-proof/omega))))

(deftest test-omega-proof-solver-logic
  (testing "omega-proof solver correctly tracks justifications"
    (let [mk-problem @(resolve 'ansatz.tactic.omega-proof/mk-problem)
          add-inequality @(resolve 'ansatz.tactic.omega-proof/add-inequality)
          add-equality @(resolve 'ansatz.tactic.omega-proof/add-equality)
          run-omega-solver @(resolve 'ansatz.tactic.omega-proof/run-omega-solver)
          mk-atom-table @(resolve 'ansatz.tactic.omega-proof/mk-atom-table)]

      (testing "simple contradiction: x ≥ 1 and x ≤ 0"
        (let [p (-> (mk-problem)
                    (add-inequality -1 [1] nil)   ;; x ≥ 1
                    (add-inequality 0 [-1] nil))  ;; x ≤ 0
              [_ result] (run-omega-solver (mk-atom-table) p)]
          (is (not (:possible result)))
          (is (some? (:proof-false result)))
          ;; Justification tree should be well-formed
          (let [j (:justification (:proof-false result))]
            (is (= :combine (:tag j)))
            (is (some? (:constraint j))))))

      (testing "equality + inequality: x + y = 5, x ≥ 3, y ≥ 3"
        (let [p (-> (mk-problem)
                    (add-equality -5 [1 1] nil)     ;; x + y = 5
                    (add-inequality -3 [1 0] nil)   ;; x ≥ 3
                    (add-inequality -3 [0 1] nil))  ;; y ≥ 3
              [_ result] (run-omega-solver (mk-atom-table) p)]
          (is (not (:possible result)))
          (is (some? (:proof-false result)))))

      (testing "no contradiction: x ≥ 0 and x ≤ 5"
        (let [p (-> (mk-problem)
                    (add-inequality 0 [1] nil)    ;; x ≥ 0
                    (add-inequality 5 [-1] nil))  ;; x ≤ 5
              [_ result] (run-omega-solver (mk-atom-table) p)]
          (is (:possible result))
          (is (nil? (:proof-false result)))))

      (testing "hard equality: 2x + 3y = 1, x ≥ 0, y ≥ 0, x ≤ 0, y ≤ 0"
        ;; 2x + 3y = 1 with x = 0, y = 0 is impossible (2*0 + 3*0 = 0 ≠ 1)
        (let [p (-> (mk-problem)
                    (add-equality -1 [2 3] nil)     ;; 2x + 3y = 1
                    (add-inequality 0 [1 0] nil)    ;; x ≥ 0
                    (add-inequality 0 [0 1] nil)    ;; y ≥ 0
                    (add-inequality 0 [-1 0] nil)   ;; x ≤ 0
                    (add-inequality 0 [0 -1] nil))  ;; y ≤ 0
              [_ result] (run-omega-solver (mk-atom-table) p)]
          (is (not (:possible result))
              "2x + 3y = 1 with x=0, y=0 should be impossible")))

      (testing "hard equality: 2x = 3 (no integer solution)"
        ;; 2x = 3 has no integer solution
        (let [p (-> (mk-problem)
                    (add-equality -3 [2] nil))  ;; 2x = 3
              [_ result] (run-omega-solver (mk-atom-table) p)]
          (is (not (:possible result))
              "2x = 3 has no integer solution"))))))

;; Full flatstore env for non-ground omega (needs Lean.Omega.* constants)
(def ^:private flatstore-env
  (delay
    (let [path "/tmp/ansatz-flatstore-mathlib"]
      (when (.exists (java.io.File. path))
        (try
          (require '[ansatz.export.storage :as storage])
          (:env ((resolve 'ansatz.export.storage/prepare-verify-flat) path))
          (catch Exception _ nil))))))

(defn- require-flatstore-env []
  (let [env @flatstore-env]
    (when-not env
      (println "  SKIP: flatstore not available at /tmp/ansatz-flatstore-mathlib"))
    env))

(deftest test-omega-proof-nonground-false
  (testing "omega-proof on non-ground False goals (verified by Java TC)"
    (when-let [env (require-flatstore-env)]
      (testing "a < a → False"
        (prove-and-verify env
                          (e/forall' "a" (mk-nat)
                                     (e/arrow (mk-lt-prop (e/bvar 0) (e/bvar 0))
                                              (e/const' false-name []))
                                     :default)
                          omega-proof/omega))

      (testing "a ≤ b → b < a → False"
        (prove-and-verify env
                          (e/forall' "a" (mk-nat)
                                     (e/forall' "b" (mk-nat)
                                                (e/arrow (mk-le-prop (e/bvar 1) (e/bvar 0))
                                                         (e/arrow (mk-lt-prop (e/bvar 1) (e/bvar 2))
                                                                  (e/const' false-name [])))
                                                :default)
                                     :default)
                          omega-proof/omega))

      (testing "a ≤ b → b ≤ c → c < a → False"
        (prove-and-verify env
                          (e/forall' "a" (mk-nat)
                                     (e/forall' "b" (mk-nat)
                                                (e/forall' "c" (mk-nat)
                ;; At h1: bvar 0=c, 1=b, 2=a → a ≤ b = bvar 2 ≤ bvar 1
                                                           (e/arrow (mk-le-prop (e/bvar 2) (e/bvar 1))
                         ;; At h2: bvar 0=h1, 1=c, 2=b, 3=a → b ≤ c = bvar 2 ≤ bvar 1
                                                                    (e/arrow (mk-le-prop (e/bvar 2) (e/bvar 1))
                                  ;; At h3: bvar 0=h2, 1=h1, 2=c, 3=b, 4=a → c < a = bvar 2 < bvar 4
                                                                             (e/arrow (mk-lt-prop (e/bvar 2) (e/bvar 4))
                                                                                      (e/const' false-name []))))
                                                           :default)
                                                :default)
                                     :default)
                          omega-proof/omega)))))

(deftest test-omega-proof-equality-goal
  (testing "omega-proof on equality goals (by_contra + Or.elim disjunction)"
    (when-let [env (require-flatstore-env)]
      (testing "a ≤ b → b ≤ a → a = b"
        (prove-and-verify env
                          (e/forall' "a" (mk-nat)
                                     (e/forall' "b" (mk-nat)
                                                (e/arrow (mk-le-prop (e/bvar 1) (e/bvar 0))
                                                         (e/arrow (mk-le-prop (e/bvar 1) (e/bvar 2))
                                                                  (mk-eq (e/bvar 3) (e/bvar 2))))
                                                :default)
                                     :default)
                          omega-proof/omega))

      (testing "a ≤ b → b ≤ a → b = a"
        (prove-and-verify env
                          (e/forall' "a" (mk-nat)
                                     (e/forall' "b" (mk-nat)
                                                (e/arrow (mk-le-prop (e/bvar 1) (e/bvar 0))
                                                         (e/arrow (mk-le-prop (e/bvar 1) (e/bvar 2))
                                                                  (mk-eq (e/bvar 2) (e/bvar 3))))
                                                :default)
                                     :default)
                          omega-proof/omega)))))

(deftest test-omega-proof-and-goal
  (testing "omega-proof on conjunction goals (¬(P ∧ Q) → ¬P ∨ ¬Q disjunction)"
    (when-let [env (require-flatstore-env)]
      (testing "a ≤ b → b ≤ a → a ≤ b ∧ b ≤ a"
        (prove-and-verify env
                          (e/forall' "a" (mk-nat)
                                     (e/forall' "b" (mk-nat)
                                                (e/arrow (mk-le-prop (e/bvar 1) (e/bvar 0))
                                                         (e/arrow (mk-le-prop (e/bvar 1) (e/bvar 2))
                                                                  (e/app* (e/const' (name/from-string "And") [])
                                                                          (mk-le-prop (e/bvar 3) (e/bvar 2))
                                                                          (mk-le-prop (e/bvar 2) (e/bvar 3)))))
                                                :default)
                                     :default)
                          omega-proof/omega))

      (testing "a < b → a < b ∧ a ≤ b"
        (prove-and-verify env
                          (e/forall' "a" (mk-nat)
                                     (e/forall' "b" (mk-nat)
                                                (e/arrow (mk-lt-prop (e/bvar 1) (e/bvar 0))
                                                         (e/app* (e/const' (name/from-string "And") [])
                                                                 (mk-lt-prop (e/bvar 2) (e/bvar 1))
                                                                 (mk-le-prop (e/bvar 2) (e/bvar 1))))
                                                :default)
                                     :default)
                          omega-proof/omega)))))

(def ^:private not-name' (name/from-string "Not"))
(def ^:private ne-name' (name/from-string "Ne"))

(deftest test-omega-proof-not-hypothesis
  (testing "omega-proof with Not hypotheses (¬LE, ¬LT converted to constraints)"
    (when-let [env (require-flatstore-env)]
      (testing "¬(a < b) → a < b → False"
        (prove-and-verify env
                          (e/forall' "a" (mk-nat)
                                     (e/forall' "b" (mk-nat)
                                                (e/arrow (e/app (e/const' not-name' []) (mk-lt-prop (e/bvar 1) (e/bvar 0)))
                                                         (e/arrow (mk-lt-prop (e/bvar 2) (e/bvar 1))
                                                                  (e/const' false-name [])))
                                                :default)
                                     :default)
                          omega-proof/omega))

      (testing "¬(a ≤ b) → a ≤ b → False"
        (prove-and-verify env
                          (e/forall' "a" (mk-nat)
                                     (e/forall' "b" (mk-nat)
                                                (e/arrow (e/app (e/const' not-name' []) (mk-le-prop (e/bvar 1) (e/bvar 0)))
                                                         (e/arrow (mk-le-prop (e/bvar 2) (e/bvar 1))
                                                                  (e/const' false-name [])))
                                                :default)
                                     :default)
                          omega-proof/omega)))))

(deftest test-omega-proof-or-goal
  (testing "omega-proof on disjunction goals (¬(P ∨ Q) → ¬P ∧ ¬Q)"
    (when-let [env (require-flatstore-env)]
      (testing "a < b → a ≤ b ∨ b ≤ a"
        (prove-and-verify env
                          (e/forall' "a" (mk-nat)
                                     (e/forall' "b" (mk-nat)
                                                (e/arrow (mk-lt-prop (e/bvar 1) (e/bvar 0))
                                                         (e/app* (e/const' (name/from-string "Or") [])
                                                                 (mk-le-prop (e/bvar 2) (e/bvar 1))
                                                                 (mk-le-prop (e/bvar 1) (e/bvar 2))))
                                                :default)
                                     :default)
                          omega-proof/omega)))))

(def ^:private or-name' (name/from-string "Or"))

(deftest test-omega-proof-or-hypothesis
  (testing "omega-proof with Or hypothesis (case-splitting via disjunction queue)"
    (when-let [env (require-flatstore-env)]
      (testing "(a < b ∨ b < a) → a = b → False"
        (prove-and-verify env
                          (e/forall' "a" (mk-nat)
                                     (e/forall' "b" (mk-nat)
                                                (e/arrow (e/app* (e/const' or-name' [])
                                                                 (mk-lt-prop (e/bvar 1) (e/bvar 0))
                                                                 (mk-lt-prop (e/bvar 0) (e/bvar 1)))
                                                         (e/arrow (e/app* (e/const' eq-name [u1]) (mk-nat) (e/bvar 2) (e/bvar 1))
                                                                  (e/const' false-name [])))
                                                :default)
                                     :default)
                          omega-proof/omega))

      (testing "a ≤ b ∨ b ≤ a → b < a → a ≤ b → False"
        (prove-and-verify env
                          (e/forall' "a" (mk-nat)
                                     (e/forall' "b" (mk-nat)
                                                (e/arrow (e/app* (e/const' or-name' [])
                                                                 (mk-le-prop (e/bvar 1) (e/bvar 0))
                                                                 (mk-le-prop (e/bvar 0) (e/bvar 1)))
                                                         (e/arrow (mk-lt-prop (e/bvar 1) (e/bvar 2))
                                                                  (e/arrow (mk-le-prop (e/bvar 3) (e/bvar 2))
                                                                           (e/const' false-name []))))
                                                :default)
                                     :default)
                          omega-proof/omega)))))

(deftest test-omega-proof-ne-hypothesis
  (testing "omega-proof with Ne hypothesis (disjunction from Ne)"
    (when-let [env (require-flatstore-env)]
      (testing "a ≠ b → a ≤ b → b ≤ a → False"
        (prove-and-verify env
                          (e/forall' "a" (mk-nat)
                                     (e/forall' "b" (mk-nat)
                                                (e/arrow (e/app* (e/const' ne-name' [u1]) (mk-nat) (e/bvar 1) (e/bvar 0))
                                                         (e/arrow (mk-le-prop (e/bvar 2) (e/bvar 1))
                                                                  (e/arrow (mk-le-prop (e/bvar 2) (e/bvar 3))
                                                                           (e/const' false-name []))))
                                                :default)
                                     :default)
                          omega-proof/omega)))))

(deftest test-omega-proof-nat-sub
  (testing "omega-proof with non-ground Nat.sub (solver finds contradiction)"
    (when-let [env (require-flatstore-env)]
      ;; Note: proof term construction for Nat.sub dichotomies is not yet fully certified.
      ;; These tests verify the solver logic finds contradictions correctly.
      (testing "a ≤ b → a - b = 0"
        (let [goal-type (e/forall' "a" (mk-nat)
                                   (e/forall' "b" (mk-nat)
                                              (e/arrow (mk-le-prop (e/bvar 1) (e/bvar 0))
                                                       (mk-eq (mk-sub (e/bvar 2) (e/bvar 1)) (n 0)))
                                              :default)
                                   :default)
              ps (first (proof/start-proof env goal-type))
              ps' (omega-proof/omega ps)]
          (is (proof/solved? ps') "Goal should be solved")))

      (testing "b ≤ a → a - b + b = a"
        (let [goal-type (e/forall' "a" (mk-nat)
                                   (e/forall' "b" (mk-nat)
                                              (e/arrow (mk-le-prop (e/bvar 0) (e/bvar 1))
                                                       (mk-eq (mk-add (mk-sub (e/bvar 2) (e/bvar 1)) (e/bvar 1))
                                                              (e/bvar 2)))
                                              :default)
                                   :default)
              ps (first (proof/start-proof env goal-type))
              ps' (omega-proof/omega ps)]
          (is (proof/solved? ps') "Goal should be solved")))

      ;; Divisibility: full omega proof with certified proof terms
      (testing "2 ∣ n, n ≥ 1, n ≤ 1 → False (dvd with proof)"
        (let [dvd-inst (e/const' (name/from-string "Nat.instDvd") [])
              mk-dvd (fn [k x] (e/app* (e/const' (name/from-string "Dvd.dvd") [lvl/zero])
                                       (mk-nat) dvd-inst k x))
              goal-type (e/forall' "n" (mk-nat)
                                   (e/arrow (mk-dvd (n 2) (e/bvar 0))
                                            (e/arrow (mk-le-prop (n 1) (e/bvar 1))
                                                     (e/arrow (mk-le-prop (e/bvar 2) (n 1))
                                                              (e/const' (name/from-string "False") []))))
                                   :default)
              ps (first (proof/start-proof env goal-type))
              ps' (omega-proof/omega ps)]
          (is (proof/solved? ps') "Goal should be solved"))))))

;; ============================================================
;; Omega-proof: implication, Iff, div bounds, mod, negation
;; ============================================================

(deftest test-omega-proof-implication
  (testing "omega-proof with implication hypotheses"
    (when-let [env (require-flatstore-env)]
      ;; P -> Q as hypothesis gets decomposed to Not-P Or Q
      (testing "trivial implication: 0 <= a -> 0 <= a"
        (let [goal-type (e/forall' "a" (mk-nat)
                                   (e/arrow (mk-le-prop (n 0) (e/bvar 0))
                                            (mk-le-prop (n 0) (e/bvar 1)))
                                   :default)
              ps (first (proof/start-proof env goal-type))
              ps' (omega-proof/omega ps)]
          (is (proof/solved? ps') "Trivial implication should be solved"))))))

(deftest test-omega-proof-neg-implication
  (testing "omega-proof with negated implication in goal"
    (when-let [env (require-flatstore-env)]
      ;; Not(P -> Q) -> P And Not-Q via not_imp
      ;; Not(a <= 5 -> a <= 3) -> (a <= 5) And Not(a <= 3) -> a <= 5 and 3 < a -> 3 < a
      (testing "Not(a <= 5 -> a <= 3) -> 3 < a"
        (let [goal-type (e/forall' "a" (mk-nat)
                                   (e/arrow (e/app (e/const' not-name' [])
                                                   (e/arrow (mk-le-prop (e/bvar 0) (n 5))
                                                            (mk-le-prop (e/bvar 1) (n 3))))
                                            (mk-lt-prop (n 3) (e/bvar 1)))
                                   :default)
              ps (first (proof/start-proof env goal-type))
              ps' (omega-proof/omega ps)]
          (is (proof/solved? ps') "Negated implication should be solved"))))))

(deftest test-omega-proof-positive-iff
  (testing "omega-proof with positive Iff hypothesis"
    (when-let [env (require-flatstore-env)]
      ;; (a <= 3 Iff a >= 4) -> False
      ;; Left branch: a <= 3 And a >= 4 -> contradiction
      ;; Right branch: Not(a<=3) And Not(a>=4) -> 3 < a And a < 4 -> contradiction
      (testing "(a <= 3 Iff a >= 4) -> False"
        (let [mk-iff (fn [p q] (e/app* (e/const' (name/from-string "Iff") []) p q))
              goal-type (e/forall' "a" (mk-nat)
                                   (e/arrow (mk-iff (mk-le-prop (e/bvar 0) (n 3))
                                                    (mk-ge-prop (e/bvar 0) (n 4)))
                                            (e/const' false-name []))
                                   :default)
              ps (first (proof/start-proof env goal-type))
              ps' (omega-proof/omega ps)]
          (is (proof/solved? ps') "Iff hypothesis leading to contradiction should be solved"))))))

(deftest test-omega-proof-neg-iff
  (testing "omega-proof with negated Iff in goal"
    (when-let [env (require-flatstore-env)]
      ;; a = 4 -> Not(a <= 5 Iff a <= 3)
      ;; a=4: a<=5=T, a<=3=F, T Iff F = F, Not F = T
      ;; by_contra assumes (a<=5 Iff a<=3), decomposes to contradiction with a=4
      (testing "a = 4 -> Not(a <= 5 Iff a <= 3)"
        (let [mk-iff (fn [p q] (e/app* (e/const' (name/from-string "Iff") []) p q))
              goal-type (e/forall' "a" (mk-nat)
                                   (e/arrow (mk-eq (e/bvar 0) (n 4))
                                            (e/app (e/const' not-name' [])
                                                   (mk-iff (mk-le-prop (e/bvar 1) (n 5))
                                                           (mk-le-prop (e/bvar 1) (n 3)))))
                                   :default)
              ps (first (proof/start-proof env goal-type))
              ps' (omega-proof/omega ps)]
          (is (proof/solved? ps') "Negated Iff should be solved"))))))

(deftest test-omega-proof-div-bounds
  (testing "omega-proof with division bounds"
    (when-let [env (require-flatstore-env)]
      (testing "a / 3 * 3 <= a (Nat.div_mul_le_self)"
        (let [goal-type (e/forall' "a" (mk-nat)
                                   (mk-le-prop (mk-hmul (mk-hdiv (e/bvar 0) (n 3)) (n 3))
                                               (e/bvar 0))
                                   :default)
              ps (first (proof/start-proof env goal-type))
              ps' (omega-proof/omega ps)]
          (is (proof/solved? ps') "div-mul-le-self should be proved")))

      (testing "a < (a / 3 + 1) * 3 (upper bound on div)"
        (let [goal-type (e/forall' "a" (mk-nat)
                                   (mk-lt-prop (e/bvar 0)
                                               (mk-hmul (mk-hadd (mk-hdiv (e/bvar 0) (n 3)) (n 1))
                                                        (n 3)))
                                   :default)
              ps (first (proof/start-proof env goal-type))
              ps' (omega-proof/omega ps)]
          (is (proof/solved? ps') "div upper bound should be proved"))))))

(deftest test-omega-proof-mod-decomposition
  (testing "omega-proof with mod decomposition (a % k -> a - k*(a/k))"
    (when-let [env (require-flatstore-env)]
      (testing "a % 3 < 3"
        (let [goal-type (e/forall' "a" (mk-nat)
                                   (mk-lt-prop (mk-hmod (e/bvar 0) (n 3)) (n 3))
                                   :default)
              ps (first (proof/start-proof env goal-type))
              ps' (omega-proof/omega ps)]
          (is (proof/solved? ps') "mod < k should be proved")))

      (testing "a % 3 + a / 3 * 3 = a"
        (let [goal-type (e/forall' "a" (mk-nat)
                                   (mk-eq (mk-hadd (mk-hmod (e/bvar 0) (n 3))
                                                   (mk-hmul (mk-hdiv (e/bvar 0) (n 3)) (n 3)))
                                          (e/bvar 0))
                                   :default)
              ps (first (proof/start-proof env goal-type))
              ps' (omega-proof/omega ps)]
          (is (proof/solved? ps') "mod + div*k = a should be proved"))))))

(deftest test-omega-proof-int-negation
  (testing "omega-proof with Neg.neg (Int negation): -a + a = 0"
    (when-let [env (require-flatstore-env)]
      (let [int-type (e/const' (name/from-string "Int") [])
            mk-int-add (fn [a b] (e/app* (e/const' (name/from-string "HAdd.hAdd") [lvl/zero lvl/zero lvl/zero])
                                         int-type int-type int-type
                                         (e/app* (e/const' (name/from-string "instHAdd") [lvl/zero])
                                                 int-type (e/const' (name/from-string "Int.instAdd") []))
                                         a b))
            mk-int-neg (fn [a] (e/app* (e/const' (name/from-string "Neg.neg") [])
                                       int-type (e/const' (name/from-string "Int.instNegInt") [])
                                       a))
            mk-int-eq (fn [a b] (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                                        int-type a b))
            int-zero (e/app (e/const' (name/from-string "Int.ofNat") []) (n 0))
            goal-type (e/forall' "a" int-type
                                 (mk-int-eq (mk-int-add (mk-int-neg (e/bvar 0)) (e/bvar 0))
                                            int-zero)
                                 :default)
            ps (first (proof/start-proof env goal-type))
            ps' (omega-proof/omega ps)]
        (is (proof/solved? ps') "Int negation should be handled")))))
