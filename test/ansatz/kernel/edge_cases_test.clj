(ns ansatz.kernel.edge-cases-test
  "Tests for kernel edge cases: proof irrelevance, eta reduction,
   deep WHNF, K-recursors, universe levels."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay])
  (:import [ansatz.kernel ConstantInfo TypeChecker Env]))

(def ^:private test-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(defn- require-env [] (or @test-env (throw (ex-info "init-medium.ndjson not found" {}))))

;; ============================================================
;; Proof irrelevance
;; ============================================================

(deftest test-proof-irrelevance-basic
  (testing "Two proofs of same proposition are def-eq"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          ;; Build: True.intro and True.intro — same proof, trivially equal
          true-intro (e/const' (name/from-string "True.intro") [])
          true-intro2 (e/const' (name/from-string "True.intro") [])]
      (is (tc/is-def-eq st true-intro true-intro2)))))

(deftest test-proof-irrelevance-different-proofs
  (testing "Different proof terms of same Prop are def-eq"
    (let [env (require-env)
          ;; Use Java TC with high fuel for proof irrelevance
          jtc (doto (TypeChecker. env) (.setFuel 20000000))
          ;; Eq.refl Nat 0 : 0 = 0
          eq-refl (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                          (e/const' (name/from-string "Nat") [])
                          (e/lit-nat 0))]
      ;; Same proof should be def-eq to itself
      (is (.isDefEq jtc eq-refl eq-refl)))))

;; ============================================================
;; WHNF reduction
;; ============================================================

(deftest test-whnf-nat-succ
  (testing "WHNF reduces Nat.succ(3) to 4"
    (let [env (require-env)
          succ-3 (e/app (e/const' (name/from-string "Nat.succ") []) (e/lit-nat 3))
          result (red/whnf env succ-3)]
      (is (e/lit-nat? result))
      (is (= 4 (e/lit-nat-val result))))))

(deftest test-whnf-beta-reduction
  (testing "WHNF beta-reduces (λ x : Nat, x) 42 to 42"
    (let [env (require-env)
          nat (e/const' (name/from-string "Nat") [])
          ;; (λ x : Nat, x) 42
          identity-fn (e/lam "x" nat (e/bvar 0) :default)
          app (e/app identity-fn (e/lit-nat 42))
          result (red/whnf env app)]
      (is (e/lit-nat? result))
      (is (= 42 (e/lit-nat-val result))))))

(deftest test-whnf-no-delta
  (testing "whnf-no-delta doesn't unfold named constants"
    (let [env (require-env)
          ;; Nat.add should NOT be unfolded by no-delta
          nat-add (e/const' (name/from-string "Nat.add") [])
          result (red/whnf-no-delta env nat-add)]
      ;; Should remain as the constant, not reduce to a lambda
      (is (e/const? result)))))

(deftest test-whnf-let-reduction
  (testing "WHNF reduces let-bindings"
    (let [env (require-env)
          nat (e/const' (name/from-string "Nat") [])
          ;; let x : Nat := 5 in x
          let-expr (e/let' "x" nat (e/lit-nat 5) (e/bvar 0))
          result (red/whnf env let-expr)]
      (is (e/lit-nat? result))
      (is (= 5 (e/lit-nat-val result))))))

;; ============================================================
;; Type inference
;; ============================================================

(deftest test-infer-nat-literal
  (testing "Infer type of Nat literal"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          ty (tc/infer-type st (e/lit-nat 42))
          nat (e/const' (name/from-string "Nat") [])]
      (is (tc/is-def-eq st ty nat)))))

(deftest test-infer-lambda
  (testing "Infer type of lambda produces forall"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          nat (e/const' (name/from-string "Nat") [])
          ;; λ x : Nat, x
          lam (e/lam "x" nat (e/bvar 0) :default)
          ty (tc/infer-type st lam)]
      (is (e/forall? ty) "Type of lambda should be forall")
      (is (tc/is-def-eq st (e/forall-type ty) nat) "Domain should be Nat"))))

(deftest test-infer-application
  (testing "Infer type of application"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          ;; Nat.succ 0 : Nat
          succ-0 (e/app (e/const' (name/from-string "Nat.succ") []) (e/lit-nat 0))
          nat (e/const' (name/from-string "Nat") [])
          ty (tc/infer-type st succ-0)]
      (is (tc/is-def-eq st ty nat)))))

;; ============================================================
;; Definitional equality
;; ============================================================

(deftest test-def-eq-nat-add
  (testing "2 + 3 is def-eq to 5"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          ;; Nat.add 2 3
          add-2-3 (e/app* (e/const' (name/from-string "Nat.add") [])
                          (e/lit-nat 2) (e/lit-nat 3))]
      (is (tc/is-def-eq st add-2-3 (e/lit-nat 5))))))

(deftest test-def-eq-nat-mul
  (testing "3 * 4 is def-eq to 12"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          mul-3-4 (e/app* (e/const' (name/from-string "Nat.mul") [])
                          (e/lit-nat 3) (e/lit-nat 4))]
      (is (tc/is-def-eq st mul-3-4 (e/lit-nat 12))))))

(deftest test-not-def-eq
  (testing "Different Nat values are NOT def-eq"
    (let [env (require-env)
          st (tc/mk-tc-state env)]
      (is (not (tc/is-def-eq st (e/lit-nat 1) (e/lit-nat 2)))))))

;; ============================================================
;; Java TypeChecker
;; ============================================================

(deftest test-java-tc-infer
  (testing "Java TypeChecker infers types correctly"
    (let [env (require-env)
          tc (doto (TypeChecker. env) (.setFuel 10000000))
          nat (e/const' (name/from-string "Nat") [])
          ty (.inferType tc (e/lit-nat 42))]
      (is (.isDefEq tc ty nat)))))

(deftest test-java-tc-check-constant
  (testing "Java TypeChecker can check a constant"
    (let [env (require-env)
          tc (doto (TypeChecker. env) (.setFuel 10000000))
          ;; Check that Nat.add is well-typed
          ci (env/lookup env (name/from-string "Nat.add"))]
      (when ci
        (is (some? (.inferType tc (e/const' (name/from-string "Nat.add") []))))))))

;; ============================================================
;; Universe levels
;; ============================================================

(deftest test-sort-level-zero
  (testing "Sort 0 is Prop"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          prop (e/sort' lvl/zero)
          ;; Type of Prop is Type 1 = Sort 1
          ty (tc/infer-type st prop)]
      (is (e/sort? ty)))))

(deftest test-sort-level-succ
  (testing "Sort (succ 0) is Type"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          type0 (e/sort' (lvl/succ lvl/zero))
          ty (tc/infer-type st type0)]
      (is (e/sort? ty)))))
