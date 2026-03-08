(ns cic.surface.term-test
  "Tests for the surface term builder."
  (:require [clojure.test :refer [deftest testing is]]
            [cic.kernel.env :as env]
            [cic.kernel.expr :as e]
            [cic.kernel.name :as name]
            [cic.kernel.level :as lvl]
            [cic.kernel.tc :as tc]
            [cic.surface.term :as cic]
            [cic.export.parser :as parser]
            [cic.export.replay :as replay])
  (:import [cic.kernel TypeChecker Env]))

;; ============================================================
;; Environment helpers
;; ============================================================

(def ^:private init-medium-env
  "Lazily loaded init-medium environment."
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
;; Sort shortcuts
;; ============================================================

(deftest test-prop-shortcut
  (testing "Prop resolves to Sort 0"
    (let [env (env/empty-env)
          result (cic/term env 'Prop)]
      (is (e/sort? result))
      (is (lvl/level-zero? (e/sort-level result))))))

(deftest test-type-shortcut
  (testing "Type resolves to Sort 1"
    (let [env (env/empty-env)
          result (cic/term env 'Type)]
      (is (e/sort? result))
      (is (= (lvl/succ lvl/zero) (e/sort-level result))))))

;; ============================================================
;; Literal
;; ============================================================

(deftest test-literal-nat
  (testing "Integer becomes lit-nat"
    (let [env (env/empty-env)
          result (cic/term env 42)]
      (is (e/lit-nat? result))
      (is (= 42 (e/lit-nat-val result))))))

;; ============================================================
;; Constant resolution
;; ============================================================

(deftest test-constant-resolution
  (testing "Nat resolves to the Nat constant from env"
    (let [env (require-init-medium)
          result (cic/term env 'Nat)
          expected (e/const' (name/from-string "Nat") [])]
      (is (e/const? result))
      (is (= (e/const-name expected) (e/const-name result))))))

;; ============================================================
;; Forall with bound variable
;; ============================================================

(deftest test-forall-bound-var
  (testing "(forall [a Nat] a) — a refers to bvar 0"
    (let [env (require-init-medium)
          result (cic/term env '(forall [a Nat] a))]
      (is (e/forall? result))
      ;; domain is Nat
      (is (e/const? (e/forall-type result)))
      ;; body is bvar 0
      (is (e/bvar? (e/forall-body result)))
      (is (= 0 (e/bvar-idx (e/forall-body result)))))))

;; ============================================================
;; Nested forall with correct de Bruijn indices
;; ============================================================

(deftest test-nested-forall
  (testing "(forall [a Nat] (forall [b Nat] (Eq Nat a b))) — correct de Bruijn"
    (let [env (require-init-medium)
          result (cic/term env '(forall [a Nat] (forall [b Nat] (Eq Nat a b))))]
      ;; Outer forall
      (is (e/forall? result))
      (let [inner (e/forall-body result)]
        ;; Inner forall
        (is (e/forall? inner))
        (let [body (e/forall-body inner)]
          ;; body should be (Eq Nat a b) = app(app(app(Eq, Nat), a), b)
          ;; a is bvar 1 (bound one level up), b is bvar 0 (innermost)
          (is (e/app? body))
          ;; Rightmost arg is b = bvar 0
          (is (e/bvar? (e/app-arg body)))
          (is (= 0 (e/bvar-idx (e/app-arg body))))
          ;; Second from right is a = bvar 1
          (let [inner-app (e/app-fn body)]
            (is (e/app? inner-app))
            (is (e/bvar? (e/app-arg inner-app)))
            (is (= 1 (e/bvar-idx (e/app-arg inner-app))))))))))

;; ============================================================
;; Multiple binders in one forall
;; ============================================================

(deftest test-multi-binder-forall
  (testing "(forall [a Nat, b Nat] (Eq Nat a b)) — multiple binders"
    (let [env (require-init-medium)
          result (cic/term env '(forall [a Nat, b Nat] (Eq Nat a b)))]
      ;; Should produce nested foralls same as explicit nesting
      (is (e/forall? result))
      (let [inner (e/forall-body result)]
        (is (e/forall? inner))
        (let [body (e/forall-body inner)]
          (is (e/app? body))
          ;; b = bvar 0, a = bvar 1
          (is (= 0 (e/bvar-idx (e/app-arg body))))
          (is (= 1 (e/bvar-idx (e/app-arg (e/app-fn body))))))))))

;; ============================================================
;; Lambda
;; ============================================================

(deftest test-lambda
  (testing "(lam [x Prop] x) — identity function on Prop"
    (let [env (env/empty-env)
          result (cic/term env '(lam [x Prop] x))]
      (is (e/lam? result))
      ;; binder type is Prop = Sort 0
      (is (e/sort? (e/lam-type result)))
      (is (lvl/level-zero? (e/sort-level (e/lam-type result))))
      ;; body is bvar 0
      (is (e/bvar? (e/lam-body result)))
      (is (= 0 (e/bvar-idx (e/lam-body result)))))))

;; ============================================================
;; Arrow
;; ============================================================

(deftest test-arrow
  (testing "(arrow Prop Prop) — Prop -> Prop"
    (let [env (env/empty-env)
          result (cic/term env '(arrow Prop Prop))
          expected (e/arrow (e/sort' lvl/zero) (e/sort' lvl/zero))]
      (is (e/forall? result))
      ;; Non-dependent: name is nil
      (is (nil? (e/forall-name result)))
      ;; domain and codomain are both Prop
      (is (= (e/sort' lvl/zero) (e/forall-type result)))
      (is (= (e/sort' lvl/zero) (e/forall-body result)))
      (is (= expected result)))))

;; ============================================================
;; Application within forall
;; ============================================================

(deftest test-application-in-forall
  (testing "(forall [a Nat] (Eq Nat a a)) — application of Eq"
    (let [env (require-init-medium)
          result (cic/term env '(forall [a Nat] (Eq Nat a a)))]
      (is (e/forall? result))
      (let [body (e/forall-body result)]
        ;; (Eq Nat a a) = app(app(app(Eq, Nat), bvar0), bvar0)
        (is (e/app? body))
        ;; Last arg: bvar 0
        (is (e/bvar? (e/app-arg body)))
        (is (= 0 (e/bvar-idx (e/app-arg body))))
        ;; Second-to-last arg: also bvar 0
        (let [f1 (e/app-fn body)]
          (is (e/app? f1))
          (is (e/bvar? (e/app-arg f1)))
          (is (= 0 (e/bvar-idx (e/app-arg f1)))))
        ;; Head should be (Eq Nat) where Eq is a const
        (let [head (e/get-app-fn body)]
          (is (e/const? head))
          (is (= (name/from-string "Eq") (e/const-name head))))))))

;; ============================================================
;; Full theorem type verified with TypeChecker
;; ============================================================

(deftest test-full-theorem-type
  (testing "(forall [a Nat] (Eq.{1} Nat a a)) type-checks as a valid Prop"
    (let [env (require-init-medium)
          ;; Build with surface syntax, using explicit universe level
          ;; Eq.{1} can't be written directly in quoted form (reader sees {} as map)
          ;; so we construct the symbol programmatically
          form (list 'forall ['a 'Nat] (list (symbol "Eq.{1}") 'Nat 'a 'a))
          result (cic/term env form)
          ;; Build manually for comparison
          nat (e/const' (name/from-string "Nat") [])
          u1 (lvl/succ lvl/zero)
          eq-aa (e/app* (e/const' (name/from-string "Eq") [u1]) nat (e/bvar 0) (e/bvar 0))
          manual (e/forall' "a" nat eq-aa :default)]
      ;; Structural equality
      (is (= manual result))
      ;; Type-check: should infer a Sort (this is a well-formed type)
      (let [tc (TypeChecker. ^Env env)
            inferred (.inferType tc result)]
        (is (e/sort? inferred))))))

(deftest test-default-level-params
  (testing "(forall [a Nat] (Eq Nat a a)) uses level params from env"
    (let [env (require-init-medium)
          result (cic/term env '(forall [a Nat] (Eq Nat a a)))]
      ;; Should produce valid structure with level params
      (is (e/forall? result))
      (let [body (e/forall-body result)
            head (e/get-app-fn body)]
        (is (e/const? head))
        ;; The Eq constant should have level params (not concrete levels)
        (let [levels (e/const-levels head)]
          (is (= 1 (count levels)))
          (is (lvl/param? (first levels))))))))

;; ============================================================
;; Unresolved symbol error
;; ============================================================

(deftest test-unresolved-symbol
  (testing "Unresolved symbol throws informative error"
    (let [env (env/empty-env)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo
                            #"Unresolved symbol"
                            (cic/term env 'NonExistent))))))

;; ============================================================
;; Colon syntax in binders
;; ============================================================

(deftest test-colon-binder-syntax
  (testing "(forall [a : Prop] a) — colon is ignored (constructed programmatically)"
    (let [env (env/empty-env)
          ;; Build the form with a colon symbol programmatically
          ;; since ': is not valid Clojure reader syntax
          form (list 'forall [(symbol "a") (symbol ":") 'Prop] 'a)
          result (cic/term env form)]
      (is (e/forall? result))
      (is (e/bvar? (e/forall-body result)))
      (is (= 0 (e/bvar-idx (e/forall-body result)))))))
