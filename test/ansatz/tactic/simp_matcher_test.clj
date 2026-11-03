(ns ansatz.tactic.simp-matcher-test
  "Lean pairs: test/lean/simp_matcher.lean."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.simp :as simp]))

(use-fixtures :once
  (fn [t]
    (a/load-init!)
    (binding [a/*verbose* false *ns* (the-ns 'ansatz.tactic.simp-matcher-test)]
      (eval '(a/defn matcher-option [n :- Nat] (Option Nat)
               (match n [zero (Option.none Nat)] [(succ k) (Option.some Nat k)])))
      (eval '(a/defn matcher-clamp [o :- (Option Nat)] Nat
               (match o [none 0] [(some m) (match (Nat.ble m 5) [true m] [false 5])])))
      (eval '(a/inductive MatcherStore [] (mk [a Nat] [b Nat])))
      (eval '(a/defn matcher-store-option [s :- MatcherStore, o :- (Option Nat)] (Option Nat)
               (match o [none (Option.some Nat 0)]
                 [(some m) (match s [(mk a b) (match (Nat.ble m a)
                                              [true (Option.some Nat a)]
                                              [false (Option.some Nat b)])])])))
      (t))))

(deftest rewritten-discriminant-reduces-before-split
  (is (true?
        (do (eval '(a/theorem matcher-rewritten-clamp
                             [n :- Nat, j :- Nat,
                              e :- (= (Option Nat) (matcher-option n) (Option.some Nat j))]
                             (<= (matcher-clamp (matcher-option n)) 5)
                             (simp only [matcher-clamp e]) (split) (omega) (omega)))
            true))))

(deftest structure-match-reduces-before-cases
  (is (true?
        (do (eval '(a/theorem matcher-store-not-none [s :- MatcherStore, o :- (Option Nat)]
                             (Not (= (Option Nat) (matcher-store-option s o) (Option.none Nat)))
                             (intro q) (cases o) (all_goals (simp only [matcher-store-option] at q))
                             (cases q) (cases s) (split at q) (all_goals (cases q))))
            true))))

(defn- c [n] (e/const' (name/from-string n) []))

(deftest structure-eta-respects-type-and-mode
  (let [environment (a/env)
        major (e/fvar 100)
        store (c "MatcherStore")
        st (tc/attach-lctx (tc/mk-tc-state environment)
                          {100 {:tag :local :id 100 :name "s" :type store}})
        rec-ci (env/lookup! environment (name/from-string "MatcherStore.rec"))
        expand (fn [environment opts]
                 (#'red/to-ctor-when-structure
                   environment rec-ci major
                   (fn [environment x] (red/whnf environment x (:lctx st)))
                   #(tc/infer-type st %) opts))
        expected (e/app* (c "MatcherStore.mk")
                         (e/proj (name/from-string "MatcherStore") 0 major)
                         (e/proj (name/from-string "MatcherStore") 1 major))]
    (is (= expected (expand environment {})))
    (is (= major (expand environment {:eta-struct :none})))
    (is (= expected (expand environment {:eta-struct :not-classes})))
    (is (= major (expand (env/with-extension environment :classes #{"MatcherStore"})
                         {:eta-struct :not-classes})))
    (is (= expected (expand (env/with-extension environment :classes #{"MatcherStore"})
                            {:eta-struct :all}))))
  (let [environment (a/env)
        nat (c "Nat")
        major (e/fvar 100)
        and-type (e/app* (c "And") (c "True") (c "True"))
        st (tc/attach-lctx (tc/mk-tc-state environment)
                          {100 {:tag :local :id 100 :name "h" :type and-type}})]
    ;; Proof structures must stay opaque to eta (K reduction is a separate rule).
    (is (= major (#'red/to-ctor-when-structure
                   environment (env/lookup! environment (name/from-string "And.rec")) major
                   (fn [environment x] (red/whnf environment x (:lctx st)))
                   #(tc/infer-type st %) {})))
    ;; Nat is recursive and has multiple constructors; its major stays stuck.
    (is (= major (#'red/to-ctor-when-structure
                   environment (env/lookup! environment (name/from-string "Nat.rec")) major
                   (fn [_ _] (throw (ex-info "unexpected inference" {})))
                   (fn [_] nat) {})))))

(deftest dsimp-opens-structure-match-binders
  (let [store (c "MatcherStore")
        matcher (e/const' (name/from-string "matcher-store-option.match_2") [(lvl/succ lvl/zero)])
        body (e/app* matcher (e/lam "_" store (c "Nat") :default) (e/bvar 0)
                     (e/lam "a" (c "Nat")
                            (e/lam "b" (c "Nat") (e/bvar 1) :default) :default))
        expr (e/lam "s" store body :default)
        expected (e/lam "s" store (e/proj (name/from-string "MatcherStore") 0 (e/bvar 0)) :default)]
    (is (= expected (#'simp/dsimp-expr (a/env) {} expr 20)))
    (is (tc/is-def-eq (tc/mk-tc-state (a/env)) expr expected))))
