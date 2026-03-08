(ns cic.surface.lean-test
  "Tests for the Lean 4 syntax emitter."
  (:require [clojure.test :refer [deftest testing is]]
            [cic.kernel.expr :as e]
            [cic.kernel.name :as name]
            [cic.kernel.level :as lvl]
            [cic.surface.lean :as lean]))

;; ============================================================
;; Helpers
;; ============================================================

(def ^:private prop (e/sort' lvl/zero))
(def ^:private type0 (e/sort' (lvl/succ lvl/zero)))
(def ^:private nat-const (e/const' (name/from-string "Nat") []))
(def ^:private bi :default)

(defn- mk-const
  ([s] (e/const' (name/from-string s) []))
  ([s levels] (e/const' (name/from-string s) levels)))

;; ============================================================
;; 1. Simple constant
;; ============================================================

(deftest emit-simple-constant-test
  (testing "Nat constant emits @Nat"
    (is (= "@Nat" (lean/emit-term nat-const))))

  (testing "Bool constant emits @Bool"
    (is (= "@Bool" (lean/emit-term (mk-const "Bool"))))))

;; ============================================================
;; 2. Forall / Pi type
;; ============================================================

(deftest emit-forall-test
  (testing "dependent forall produces valid syntax"
    ;; forall (a : Nat), @Eq Nat a a
    (let [eq-const (mk-const "Eq" [(lvl/succ lvl/zero)])
          ;; body references bvar 0 (the bound 'a')
          body (e/app* eq-const nat-const (e/bvar 0) (e/bvar 0))
          pi (e/forall' "a" nat-const body bi)]
      (is (= "∀ (a : @Nat), @Eq.{1} @Nat a a"
             (lean/emit-term pi)))))

  (testing "forall with named binder"
    ;; forall (n : Nat), Nat
    (let [pi (e/forall' "n" nat-const nat-const bi)]
      ;; nat-const has bvar-range 0, so this is a non-dependent arrow
      (is (= "@Nat → @Nat" (lean/emit-term pi))))))

;; ============================================================
;; 3. Lambda
;; ============================================================

(deftest emit-lambda-test
  (testing "identity lambda produces fun syntax"
    ;; fun (a : Nat) => a
    (let [lam (e/lam "a" nat-const (e/bvar 0) bi)]
      (is (= "fun (a : @Nat) => a"
             (lean/emit-term lam)))))

  (testing "nested lambda"
    ;; fun (a : Nat) => fun (b : Nat) => a
    (let [inner (e/lam "b" nat-const (e/bvar 1) bi)
          outer (e/lam "a" nat-const inner bi)]
      (is (= "fun (a : @Nat) => fun (b : @Nat) => a"
             (lean/emit-term outer))))))

;; ============================================================
;; 4. Full theorem
;; ============================================================

(deftest emit-theorem-test
  (testing "emit-theorem produces a parseable theorem declaration"
    ;; theorem my_thm : forall (a : Nat), @Eq.{1} Nat a a :=
    ;;   fun (a : Nat) => @Eq.refl.{1} Nat a
    (let [eq-const (mk-const "Eq" [(lvl/succ lvl/zero)])
          refl-const (mk-const "Eq.refl" [(lvl/succ lvl/zero)])
          ;; type: forall (a : Nat), Eq Nat a a
          ty-body (e/app* eq-const nat-const (e/bvar 0) (e/bvar 0))
          ty (e/forall' "a" nat-const ty-body bi)
          ;; proof: fun (a : Nat) => Eq.refl Nat a
          pf-body (e/app* refl-const nat-const (e/bvar 0))
          pf (e/lam "a" nat-const pf-body bi)
          result (lean/emit-theorem "my_thm" ty pf)]
      (is (clojure.string/starts-with? result "theorem my_thm"))
      (is (clojure.string/includes? result ":="))
      (is (clojure.string/includes? result "∀ (a : @Nat), @Eq.{1} @Nat a a"))
      (is (clojure.string/includes? result "fun (a : @Nat) => @Eq.refl.{1} @Nat a")))))

;; ============================================================
;; 5. Round-trip structure test
;; ============================================================

(deftest emit-roundtrip-structure-test
  (testing "emitted output has valid Lean 4 structural elements"
    ;; def my_def : Nat := 42
    (let [result (lean/emit-def "my_def" nat-const (e/lit-nat 42))]
      (is (= "def my_def : @Nat :=\n  42" result))
      ;; Verify structural elements
      (is (clojure.string/starts-with? result "def "))
      (is (clojure.string/includes? result " : "))
      (is (clojure.string/includes? result " :="))
      (is (re-find #"^\S" result) "starts with a keyword, not whitespace")))

  (testing "let-expression round-trip"
    ;; let x : Nat := 42; x
    (let [lt (e/let' "x" nat-const (e/lit-nat 42) (e/bvar 0))
          result (lean/emit-term lt)]
      (is (= "let x : @Nat := 42; x" result)))))

;; ============================================================
;; 6. Universe levels
;; ============================================================

(deftest emit-universe-levels-test
  (testing "@Eq.{1} renders with universe level"
    (let [eq (mk-const "Eq" [(lvl/succ lvl/zero)])]
      (is (= "@Eq.{1}" (lean/emit-term eq)))))

  (testing "constant with no levels omits braces"
    (is (= "@Nat" (lean/emit-term nat-const))))

  (testing "Sort rendering"
    (is (= "Prop" (lean/emit-term prop)))
    (is (= "Type" (lean/emit-term type0)))
    (is (= "Sort 2" (lean/emit-term (e/sort' (lvl/succ (lvl/succ lvl/zero)))))))

  (testing "multiple universe levels"
    (let [c (mk-const "Prod" [(lvl/succ lvl/zero) (lvl/succ (lvl/succ lvl/zero))])]
      (is (= "@Prod.{1, 2}" (lean/emit-term c))))))

;; ============================================================
;; 7. Arrow type (non-dependent forall)
;; ============================================================

(deftest emit-arrow-type-test
  (testing "Nat -> Nat renders as arrow"
    (let [arr (e/arrow nat-const nat-const)]
      (is (= "@Nat → @Nat" (lean/emit-term arr)))))

  (testing "Nat -> Nat -> Nat chains arrows"
    (let [arr (e/arrow nat-const (e/arrow nat-const nat-const))]
      (is (= "@Nat → @Nat → @Nat" (lean/emit-term arr)))))

  (testing "complex domain gets parenthesized"
    ;; (Nat -> Nat) -> Nat
    (let [inner (e/arrow nat-const nat-const)
          arr (e/arrow inner nat-const)]
      ;; The inner forall as domain should be parenthesized
      (is (clojure.string/includes? (lean/emit-term arr) "→")))))

;; ============================================================
;; Additional edge cases
;; ============================================================

(deftest emit-string-literal-test
  (testing "string literal"
    (is (= "\"hello\"" (lean/emit-term (e/lit-str "hello"))))))

(deftest emit-projection-test
  (testing "projection emits @TypeName.idx struct"
    (let [p (e/proj (name/from-string "Prod") 0 nat-const)]
      (is (= "@Prod.0 @Nat" (lean/emit-term p))))))

(deftest emit-application-test
  (testing "application with complex args uses parens"
    ;; @f (fun (x : Nat) => x)
    (let [f (mk-const "f")
          lam (e/lam "x" nat-const (e/bvar 0) bi)
          ap (e/app f lam)]
      (is (= "@f (fun (x : @Nat) => x)" (lean/emit-term ap))))))
