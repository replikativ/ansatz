(ns ansatz.tactic.grind-test
  "Tests for grind-lite tactic."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.grind :as grind]
            [ansatz.tactic.extract :as extract]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

(def ^:private zustand-available?
  (try (Class/forName "smt.EGraph") true (catch Exception _ false)))

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

(def ^:private nat (e/const' (name/from-string "Nat") []))
(def ^:private u1 (lvl/succ lvl/zero))
(defn- mk-eq [a b]
  (e/app* (e/const' (name/from-string "Eq") [u1]) nat a b))

;; ============================================================
;; Grind via rfl
;; ============================================================

(deftest test-grind-rfl
  (testing "grind solves a = a via rfl"
    (let [env (require-env)
          goal (e/forall' "a" nat (mk-eq (e/bvar 0) (e/bvar 0)) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intro ps "a")
          ps (grind/grind ps)]
      (is (proof/solved? ps))
      (let [term (extract/extract ps)]
        (is (some? term))
        (is (not (e/has-fvar-flag term)))))))

;; ============================================================
;; Grind via assumption
;; ============================================================

(deftest test-grind-assumption
  (testing "grind solves a = b from h : a = b via assumption"
    (let [env (require-env)
          h-type (mk-eq (e/bvar 2) (e/bvar 1))
          concl (mk-eq (e/bvar 3) (e/bvar 2))
          goal (e/forall' "a" nat
                          (e/forall' "b" nat
                                     (e/forall' "h" h-type concl :default) :default) :default)
          [ps _] (proof/start-proof env goal)
          ps (basic/intros ps ["a" "b" "h"])
          ps (grind/grind ps)]
      (is (proof/solved? ps)))))

;; ============================================================
;; Grind via congruence closure
;; ============================================================

(deftest test-grind-congruence
  (when-not zustand-available? (is true "skipped: zustand not available"))
  (when zustand-available?
    (testing "grind solves f(a) = f(b) from h : a = b via congruence closure"
      (let [env (require-env)
            nat-to-nat (e/arrow nat nat)
          ;; forall a b : Nat, forall f : Nat -> Nat, h : a = b |- f a = f b
            h-type (mk-eq (e/bvar 2) (e/bvar 1))
            concl (mk-eq (e/app (e/bvar 1) (e/bvar 3))
                         (e/app (e/bvar 1) (e/bvar 2)))
            goal (e/forall' "a" nat
                            (e/forall' "b" nat
                                       (e/forall' "f" nat-to-nat
                                                  (e/forall' "h" h-type concl :default) :default) :default) :default)
            [ps _] (proof/start-proof env goal)
            ps (basic/intros ps ["a" "b" "f" "h"])
            ps (grind/grind ps)]
        (is (proof/solved? ps))))))

(deftest test-grind-transitivity
  (when-not zustand-available? (is true "skipped: zustand not available"))
  (when zustand-available?
    (testing "grind solves a = c from h1 : a = b, h2 : b = c via CC"
      (let [env (require-env)
          ;; forall a b c : Nat, h1 : a = b, h2 : b = c |- a = c
            h1-type (mk-eq (e/bvar 2) (e/bvar 1))
            h2-type (mk-eq (e/bvar 2) (e/bvar 1))
            concl (mk-eq (e/bvar 4) (e/bvar 2))
            goal (e/forall' "a" nat
                            (e/forall' "b" nat
                                       (e/forall' "c" nat
                                                  (e/forall' "h1" h1-type
                                                             (e/forall' "h2" h2-type concl :default) :default) :default) :default) :default)
            [ps _] (proof/start-proof env goal)
            ps (basic/intros ps ["a" "b" "c" "h1" "h2"])
            ps (grind/grind ps)]
        (is (proof/solved? ps))))))

(deftest test-grind-deep-congruence
  (when-not zustand-available? (is true "skipped: zustand not available"))
  (when zustand-available?
    (testing "grind solves g(f(a)) = g(f(b)) from h : a = b via deep CC"
      (let [env (require-env)
            nat-to-nat (e/arrow nat nat)
          ;; forall a b : Nat, f g : Nat -> Nat, h : a = b |- g(f(a)) = g(f(b))
          ;; h binder (depth 4): a=#3, b=#2, f=#1, g=#0
            h-type (mk-eq (e/bvar 3) (e/bvar 2))
          ;; concl (depth 5): a=#4, b=#3, f=#2, g=#1
            concl (mk-eq (e/app (e/bvar 1) (e/app (e/bvar 2) (e/bvar 4)))
                         (e/app (e/bvar 1) (e/app (e/bvar 2) (e/bvar 3))))
            goal (e/forall' "a" nat
                            (e/forall' "b" nat
                                       (e/forall' "f" nat-to-nat
                                                  (e/forall' "g" nat-to-nat
                                                             (e/forall' "h" h-type concl :default) :default) :default) :default) :default)
            [ps _] (proof/start-proof env goal)
            ps (basic/intros ps ["a" "b" "f" "g" "h"])
            ps (grind/grind ps)]
        (is (proof/solved? ps))))))
