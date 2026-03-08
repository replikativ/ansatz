(ns cic.surface.elaborate-test
  "Tests for the elaboration function."
  (:require [clojure.test :refer [deftest testing is]]
            [cic.kernel.env :as env]
            [cic.kernel.expr :as e]
            [cic.kernel.name :as name]
            [cic.kernel.level :as lvl]
            [cic.kernel.tc :as tc]
            [cic.surface.elaborate :as elab]
            [cic.export.parser :as parser]
            [cic.export.replay :as replay]))

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

(defn- require-init-medium []
  (or @init-medium-env
      (throw (ex-info "init-medium.ndjson not found" {}))))

;; ============================================================
;; Basic elaboration (no implicits needed)
;; ============================================================

(deftest test-elab-sort-shortcuts
  (testing "Prop and Type elaborate correctly"
    (let [env (env/empty-env)]
      (is (e/sort? (elab/elaborate env 'Prop)))
      (is (e/sort? (elab/elaborate env 'Type))))))

(deftest test-elab-literal
  (testing "Literals elaborate correctly"
    (let [env (env/empty-env)]
      (is (e/lit-nat? (elab/elaborate env 42)))
      (is (e/lit-str? (elab/elaborate env "hello"))))))

(deftest test-elab-constant
  (testing "Constant lookup with explicit levels"
    (let [env (require-init-medium)
          result (elab/elaborate env 'Nat)]
      (is (e/const? result))
      (is (= (name/from-string "Nat") (e/const-name result))))))

(deftest test-elab-forall-simple
  (testing "forall with no implicits"
    (let [env (env/empty-env)
          ;; ∀ (a : Prop), a → a -- no env constants needed
          result (elab/elaborate env '(forall [a Prop] (arrow a a)))]
      (is (e/forall? result))
      ;; Verify it type-checks
      (let [st (tc/mk-tc-state env)]
        (is (e/sort? (tc/infer-type st result)))))))

(deftest test-elab-lam-simple
  (testing "Lambda with Prop"
    (let [env (env/empty-env)
          result (elab/elaborate env '(lam [a Prop, h a] h))]
      ;; Should be λ (a : Prop) (h : a) => h
      (is (e/lam? result))
      (let [st (tc/mk-tc-state env)
            ty (tc/infer-type st result)]
        (is (e/forall? ty))))))

;; ============================================================
;; Implicit argument insertion
;; ============================================================

(deftest test-elab-eq-implicits
  (testing "Eq inserts implicit type argument and universe level"
    (let [env (require-init-medium)
          ;; Eq a a — Eq has one implicit arg {α : Sort u} plus universe level
          result (elab/elaborate env '(forall [a Nat] (Eq a a)))]
      ;; Should elaborate to: forall (a : Nat), @Eq.{1} Nat a a
      (is (e/forall? result))
      (let [body (e/forall-body result)
            ;; body should be @Eq.{1} Nat (bvar 0) (bvar 0) after abstraction
            [head args] (e/get-app-fn-args body)]
        (is (e/const? head))
        (is (= (name/from-string "Eq") (e/const-name head)))
        ;; 3 args: type, lhs, rhs
        (is (= 3 (count args)))
        ;; First arg should be Nat (the implicit type arg)
        (is (e/const? (first args)))
        (is (= (name/from-string "Nat") (e/const-name (first args))))))))

(deftest test-elab-eq-type-checks
  (testing "Elaborated Eq term type-checks"
    (let [env (require-init-medium)
          result (elab/elaborate env '(forall [a Nat] (Eq a a)))
          st (tc/mk-tc-state env)
          ty (tc/infer-type st result)]
      (is (e/sort? ty)))))

(deftest test-elab-eq-refl-implicits
  (testing "Eq.refl inserts implicit type and value arguments"
    (let [env (require-init-medium)
          ;; λ (a : Nat) => Eq.refl a
          ;; Eq.refl has type: {α : Sort u} → (a : α) → @Eq α a a
          ;; So Eq.refl a should elaborate to @Eq.refl.{1} Nat a
          result (elab/elaborate env '(lam [a Nat] (Eq.refl a)))
          st (tc/mk-tc-state env)
          ty (tc/infer-type st result)]
      ;; Type should be: ∀ (a : Nat), @Eq Nat a a
      (is (e/forall? ty)))))

(deftest test-elab-nat-succ
  (testing "Nat.succ application"
    (let [env (require-init-medium)
          result (elab/elaborate env '(Nat.succ 0))
          st (tc/mk-tc-state env)
          ty (tc/infer-type st result)]
      ;; Type should be Nat
      (is (e/const? ty))
      (is (= (name/from-string "Nat") (e/const-name ty))))))

;; ============================================================
;; Explicit levels still work
;; ============================================================

(deftest test-elab-explicit-levels
  (testing "Explicit levels override inference"
    (let [env (require-init-medium)
          ;; Use symbol with .{} for explicit levels — must construct manually
          ;; since Clojure reader chokes on {1} in symbols.
          ;; Eq.{1} still auto-inserts the implicit Nat arg, so just provide a a
          result (elab/elaborate env (list 'forall ['a 'Nat]
                                           (list (symbol "Eq.{1}") 'a 'a)))]
      (is (e/forall? result))
      (let [st (tc/mk-tc-state env)]
        (is (e/sort? (tc/infer-type st result)))))))

(deftest test-elab-at-explicit
  (testing "@-prefixed constants suppress implicit insertion"
    (let [env (require-init-medium)
          ;; @Eq.{1} Nat a a — fully explicit, no implicit insertion
          result (elab/elaborate env (list 'forall ['a 'Nat]
                                           (list (symbol "@Eq.{1}") 'Nat 'a 'a)))]
      (is (e/forall? result))
      (let [st (tc/mk-tc-state env)]
        (is (e/sort? (tc/infer-type st result)))))))

;; ============================================================
;; Error cases
;; ============================================================

(deftest test-elab-unknown-constant
  (testing "Unknown constant throws"
    (let [env (env/empty-env)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unknown constant"
            (elab/elaborate env 'NonexistentThing))))))

(deftest test-elab-type-mismatch
  (testing "Type mismatch with expected type"
    (let [env (require-init-medium)
          nat (e/const' (name/from-string "Nat") [])]
      ;; Prop is Sort 0, not Nat
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"mismatch|error"
            (elab/elaborate env 'Prop nat))))))

;; ============================================================
;; elaborate-check (full verification)
;; ============================================================

(deftest test-elaborate-check
  (testing "elaborate-check verifies via kernel"
    (let [env (require-init-medium)
          result (elab/elaborate-check env '(forall [a Nat] (Eq a a)))]
      (is (e/forall? result)))))

(deftest test-elaborate-check-lambda
  (testing "elaborate-check on lambda with implicits"
    (let [env (require-init-medium)
          result (elab/elaborate-check env '(lam [a Nat] (Eq.refl a)))]
      (is (e/lam? result)))))
