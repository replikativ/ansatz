(ns ansatz.meta.match.basic-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.meta :as meta]
            [ansatz.meta.match.basic :as b]))

(def nat (e/const' (name/from-string "Nat") []))
(def succ (name/from-string "Nat.succ"))

(deftest variable-substitution-marks-patterns-inaccessible
  (let [p (b/ctor succ [] [(e/fvar 1)] [(b/var-pattern 2)])
        out (b/pattern-apply-fvar-subst {1 nat 2 (e/lit-nat 3)} p)]
    (is (= [nat] (:params out)))
    (is (= [(b/inaccessible (e/lit-nat 3))] (:fields out)))
    (is (= p (b/pattern-apply-fvar-subst {} p)))
    (is (= (b/inaccessible (e/fvar 3))
           (b/pattern-replace-fvar-id 2 (e/fvar 3) (b/var-pattern 2))))))

(deftest substitution-is-simultaneous-and-preserves-bound-variables
  (let [rhs (e/lam "n" nat (e/app (e/fvar 1) (e/bvar 0)) :default)
        alt (assoc (b/alt nil 0 rhs [] []) :cnstrs [[(e/fvar 1) (e/fvar 2)]])
        out (b/alt-apply-fvar-subst {1 (e/fvar 2) 2 (e/lit-nat 7)} alt)]
    (is (= (e/lam "n" nat (e/app (e/fvar 2) (e/bvar 0)) :default) (:rhs out)))
    (is (= [[(e/fvar 2) (e/lit-nat 7)]] (:cnstrs out)))))

(deftest named-pattern-substitution-drops-only-replaced-aliases
  (let [p (b/as-pattern 1 (b/var-pattern 2) 3)]
    (is (= (b/var-pattern 2) (b/pattern-apply-fvar-subst {1 nat} p)))
    (is (= (b/as-pattern 1 (b/inaccessible nat) 3)
           (b/pattern-apply-fvar-subst {2 nat} p)))
    (is (= #{1 2 3} (b/pattern-collect-fvars p)))))

(deftest replacement-updates-dependent-locals-and-pending-constraints
  (let [alt (assoc (b/alt :source 4 (e/fvar 1)
                               [{:id 1 :type nat} {:id 2 :type (e/fvar 1) :value (e/fvar 1)}]
                               [(b/inaccessible (e/fvar 1))])
                   :cnstrs [[(e/fvar 1) (e/fvar 2)]] :not-alt-idxs [0])
        out (b/alt-replace-fvar-id 1 (e/lit-nat 5) alt)]
    (is (= [{:id 2 :type (e/lit-nat 5) :value (e/lit-nat 5)}] (:fvar-decls out)))
    (is (= (e/lit-nat 5) (:rhs out)))
    (is (= [(b/inaccessible (e/lit-nat 5))] (:patterns out)))
    (is (= [[(e/lit-nat 5) (e/fvar 2)]] (:cnstrs out)))
    (is (= [0] (:not-alt-idxs out)))
    (is (= 4 (:idx out)))
    (is (= :source (:ref out)))
    (is (b/alt-is-local-decl 2 out))
    (is (not (b/alt-is-local-decl 1 out)))
    ;; Unlike replaceFVarId, applyFVarSubst keeps the declaration being substituted.
    (is (= [1 2] (mapv :id (:fvar-decls (b/alt-apply-fvar-subst {1 nat} alt)))))))

(deftest instantiation-visits-all-pattern-expression-positions
  (let [mctx (-> meta/empty-context
                 (meta/add-expr-mvar-decl 10 nat {})
                 (meta/assign-expr 10 (e/lit-nat 8)))
        p (b/array-lit (e/mvar 10)
                       [(b/ctor succ [] [(e/mvar 10)] [(b/val-pattern (e/mvar 10))])
                        (b/as-pattern 1 (b/inaccessible (e/mvar 10)) 2)])
        lhs (b/alt-lhs :source [{:id 1 :type (e/mvar 10) :value (e/mvar 10)}] [p])
        out (b/instantiate-alt-lhs-mvars mctx lhs)]
    (is (b/pattern-has-expr-mvar p))
    (is (not (b/pattern-has-expr-mvar (first (:patterns out)))))
    (is (= (e/lit-nat 8) (:type (first (:fvar-decls out)))))
    (is (= (e/lit-nat 8) (:value (first (:fvar-decls out)))))
    (is (= (e/lit-nat 8) (:type (first (:patterns out)))))
    (is (= [(e/lit-nat 8)] (get-in out [:patterns 0 :xs 0 :params])))
    (is (= (e/lit-nat 8) (get-in out [:patterns 0 :xs 0 :fields 0 :e])))
    (is (= (e/lit-nat 8) (get-in out [:patterns 0 :xs 1 :p :e])))
    (is (= :source (:ref out)))
    ;; hasExprMVar does not count universe metavariables.
    (is (not (b/pattern-has-expr-mvar (b/val-pattern (e/sort' (lvl/mvar 42))))))))

(deftest dependency-collection-includes-local-types-and-let-values
  (let [lhs (b/alt-lhs nil [{:id 1 :type (e/fvar 7) :value (e/fvar 8)}]
                       [(b/ctor succ [] [(e/fvar 9)]
                                [(b/array-lit (e/fvar 10) [(b/var-pattern 11)])])])]
    (is (= #{7 8 9 10 11} (b/alt-lhs-collect-fvars lhs)))))

(deftest counterexamples-follow-variable-renaming-and-forget-nonvariables
  (let [ex {:tag :ctor :ctor-name succ
            :xs [{:tag :var :fvar-id 1}
                 {:tag :array-lit :xs [{:tag :var :fvar-id 2} {:tag :val :e (e/lit-nat 4)}]}]}
        out (b/example-apply-fvar-subst {1 (e/fvar 3) 2 (e/lit-nat 0)} ex)]
    (is (= {:tag :var :fvar-id 3} (get-in out [:xs 0])))
    (is (= {:tag :underscore} (get-in out [:xs 1 :xs 0])))
    (is (= {:tag :val :e (e/lit-nat 4)} (get-in out [:xs 1 :xs 1])))
    (is (= ex (b/example-apply-fvar-subst {} ex)))
    (is (= {:tag :underscore} (get-in (b/example-vars-to-underscore ex) [:xs 0])))
    (is (= {:tag :val :e (e/lit-nat 9)}
           (get-in (b/example-replace-fvar-id 2 {:tag :val :e (e/lit-nat 9)} ex)
                   [:xs 1 :xs 0])))))
