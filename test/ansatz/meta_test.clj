(ns ansatz.meta-test
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.meta :as meta]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.proof :as proof]))

(deftest zonk-instantiates-expression-and-level-mvars
  (testing "direct expression and level assignments are chased together"
    (let [u (lvl/mvar 10)
          ty (e/sort' u)
          value (e/const' (name/from-string "Nat") [u])
          mctx (-> meta/empty-context
                   (meta/add-level-mvar-decl 10)
                   (meta/add-expr-mvar-decl 1 ty {})
                   (meta/assign-level 10 lvl/zero)
                   (meta/assign-expr 1 value))
          zonked (meta/zonk-expr mctx (e/mvar 1))]
      (is (= (e/const' (name/from-string "Nat") [lvl/zero])
             zonked))
      (is (meta/closed-expr? mctx zonked)))))

(deftest delayed-assignment-expands-when-pending-is-ground
  (testing "a delayed assignment rebinds its fvars once the pending mvar is solved"
    (let [mctx (-> meta/empty-context
                   (meta/add-expr-mvar-decl 1 (e/sort' lvl/zero) {})
                   (meta/add-expr-mvar-decl 2 (e/sort' lvl/zero) {})
                   (meta/assign-delayed 1 [(e/fvar 42)] 2)
                   (meta/assign-expr 2 (e/fvar 42)))
          expr (e/app (e/mvar 1) (e/lit-nat 7))]
      (is (= (e/lit-nat 7) (meta/zonk-expr mctx expr))))))

(deftest proof-state-mirrors-legacy-assignments-into-meta-mctx
  (testing "a solved tactic proof can be read as a zonked root mvar"
    (let [prop (e/sort' lvl/zero)
          ;; ∀ (p : Prop), p -> p
          goal-type (e/forall' "p" prop
                               (e/forall' "h" (e/bvar 0) (e/bvar 1) :default)
                               :default)
          [ps root] (proof/start-proof (env/empty-env) goal-type)
          ps (-> ps
                 (basic/intro "p")
                 (basic/intro "h")
                 (basic/assumption))
          legacy-term (extract/extract ps)
          meta-term (extract/extract-meta ps)]
      (is (proof/solved? ps))
      (is (= legacy-term meta-term))
      (is (= meta-term (meta/zonk-expr (:meta-mctx ps) (e/mvar root))))
      (is (meta/closed-expr? (:meta-mctx ps) meta-term)))))
