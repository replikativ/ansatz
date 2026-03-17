(ns ansatz.surface.pp-test
  "Tests for Ansatz pretty-printer."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.surface.pp :as pp]))

;; ============================================================
;; Helpers
;; ============================================================

(def ^:private prop (e/sort' lvl/zero))
(def ^:private type0 (e/sort' (lvl/succ lvl/zero)))
(def ^:private type1 (e/sort' (lvl/succ (lvl/succ lvl/zero))))

(defn- mk-name [s] (name/from-string s))
(defn- mk-const [s] (e/const' (mk-name s) []))
(defn- mk-const-lvls [s lvls] (e/const' (mk-name s) lvls))

;; ============================================================
;; Sort rendering
;; ============================================================

(deftest pp-prop-test
  (testing "Sort 0 renders as Prop"
    (is (= "Prop" (pp/pp prop)))))

(deftest pp-type-test
  (testing "Sort 1 renders as Type"
    (is (= "Type" (pp/pp type0)))))

(deftest pp-type-n-test
  (testing "Sort 2 renders as Type 1"
    (is (= "Type 1" (pp/pp type1)))))

;; ============================================================
;; Constants
;; ============================================================

(deftest pp-const-test
  (testing "Constant with no levels"
    (is (= "Nat" (pp/pp (mk-const "Nat"))))))

(deftest pp-const-with-levels-test
  (testing "Constant with non-zero universe levels"
    (is (= "@Eq.{1}" (pp/pp (mk-const-lvls "Eq" [(lvl/succ lvl/zero)]))))))

(deftest pp-const-zero-levels-test
  (testing "Constant with all-zero levels omits level annotation"
    (is (= "Nat" (pp/pp (mk-const-lvls "Nat" [lvl/zero]))))))

;; ============================================================
;; Forall / dependent types
;; ============================================================

(deftest pp-forall-named-test
  (testing "∀ (a : Nat), a — named binder with bvar reference"
    (let [nat (mk-const "Nat")
          ;; ∀ (a : Nat), #0
          expr (e/forall' (mk-name "a") nat (e/bvar 0) :default)]
      (is (= "∀ (a : Nat), a" (pp/pp expr))))))

(deftest pp-non-dependent-arrow-test
  (testing "Prop → Prop renders with arrow notation"
    (let [;; ∀ (_ : Prop), Prop — body does not use bvar 0
          expr (e/forall' nil prop prop :default)]
      (is (= "Prop → Prop" (pp/pp expr))))))

(deftest pp-nested-forall-test
  (testing "Nested forall: ∀ (a : Nat) (b : Nat), @Eq.{1} Nat a b"
    (let [nat (mk-const "Nat")
          eq1 (mk-const-lvls "Eq" [(lvl/succ lvl/zero)])
          ;; inner: ∀ (b : Nat), Eq.{1} Nat a b
          ;; where a=#1, b=#0
          inner-body (e/app* eq1 nat (e/bvar 1) (e/bvar 0))
          inner (e/forall' (mk-name "b") nat inner-body :default)
          outer (e/forall' (mk-name "a") nat inner :default)]
      (is (= "∀ (a : Nat), ∀ (b : Nat), @Eq.{1} Nat a b" (pp/pp outer))))))

;; ============================================================
;; Lambda
;; ============================================================

(deftest pp-lambda-test
  (testing "fun (x : Prop) => x"
    (let [expr (e/lam (mk-name "x") prop (e/bvar 0) :default)]
      (is (= "fun (x : Prop) => x" (pp/pp expr))))))

(deftest pp-lambda-implicit-test
  (testing "fun {x : Prop} => x — implicit binder"
    (let [expr (e/lam (mk-name "x") prop (e/bvar 0) :implicit)]
      (is (= "fun {x : Prop} => x" (pp/pp expr))))))

;; ============================================================
;; Application and parenthesization
;; ============================================================

(deftest pp-app-simple-test
  (testing "f x — simple application, no parens needed"
    (let [f (mk-const "f")
          x (mk-const "x")
          expr (e/app f x)]
      (is (= "f x" (pp/pp expr))))))

(deftest pp-app-nested-arg-test
  (testing "f (g x) — application arg that is itself an application gets parens"
    (let [f (mk-const "f")
          g (mk-const "g")
          x (mk-const "x")
          expr (e/app f (e/app g x))]
      (is (= "f (g x)" (pp/pp expr))))))

(deftest pp-app-multi-test
  (testing "f a b — multi-arg application"
    (let [f (mk-const "f")
          a (mk-const "a")
          b (mk-const "b")
          expr (e/app* f a b)]
      (is (= "f a b" (pp/pp expr))))))

;; ============================================================
;; Literals
;; ============================================================

(deftest pp-lit-nat-test
  (testing "Natural literal renders as number"
    (is (= "42" (pp/pp (e/lit-nat 42))))))

(deftest pp-lit-str-test
  (testing "String literal renders as quoted string"
    (is (= "\"hello\"" (pp/pp (e/lit-str "hello"))))))

;; ============================================================
;; Free variables
;; ============================================================

(deftest pp-fvar-test
  (testing "Free variable renders as ?fv<id>"
    (is (= "?fv5" (pp/pp (e/fvar 5))))))

;; ============================================================
;; Let bindings
;; ============================================================

(deftest pp-let-test
  (testing "let x : Nat := 0 in x"
    (let [nat (mk-const "Nat")
          expr (e/let' (mk-name "x") nat (e/lit-nat 0) (e/bvar 0))]
      (is (= "let x : Nat := 0 in x" (pp/pp expr))))))

;; ============================================================
;; Projections
;; ============================================================

(deftest pp-proj-test
  (testing "Projection renders as expr.idx"
    (let [x (mk-const "x")
          expr (e/proj (mk-name "Prod") 0 x)]
      (is (= "x.0" (pp/pp expr))))))

;; ============================================================
;; Generated binder names
;; ============================================================

(deftest pp-anonymous-binder-test
  (testing "Anonymous binder gets generated name"
    (let [expr (e/forall' nil prop (e/bvar 0) :default)]
      (is (= "∀ (a : Prop), a" (pp/pp expr))))))

;; ============================================================
;; Two-arg pp (with env)
;; ============================================================

(deftest pp-with-env-test
  (testing "pp with env argument works"
    (is (= "Prop" (pp/pp nil prop)))))

;; ============================================================
;; Nested arrows
;; ============================================================

(deftest pp-nested-arrow-test
  (testing "Prop → Prop → Prop — right-associative arrows"
    (let [;; ∀ (_ : Prop), ∀ (_ : Prop), Prop
          inner (e/forall' nil prop prop :default)
          outer (e/forall' nil prop inner :default)]
      (is (= "Prop → Prop → Prop" (pp/pp outer))))))
