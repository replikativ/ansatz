(ns ansatz.meta.kabstract
  "Lean Meta/KAbstract.lean kabstract and HeadIndex.lean, v4.33.1.
   Abstract all occurrences of a closed, metavariable-free pattern.
   The kernel defeq backend has no transparency setting; head/arity filtering
   restricts comparisons as in Lean's keyed matching."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.tc :as tc]))

(defn- head-num-args [expr]
  (case (e/tag expr)
    :app (inc (head-num-args (e/app-fn expr)))
    :let (head-num-args (e/let-body expr))
    :mdata (head-num-args (e/mdata-expr expr))
    0))

(defn- to-head-index [expr]
  (case (e/tag expr)
    :app (to-head-index (e/app-fn expr))
    :let (to-head-index (e/instantiate1 (e/let-body expr) (e/let-value expr)))
    :mdata (to-head-index (e/mdata-expr expr))
    :const [:const (e/const-name expr)]
    :fvar [:fvar (e/fvar-id expr)]
    :proj [:proj (e/proj-type-name expr) (e/proj-idx expr)]
    :lit-nat [:lit-nat (e/lit-nat-val expr)]
    :lit-str [:lit-str (e/lit-str-val expr)]
    [(e/tag expr)]))

(defn kabstract
  "Replace keyed, definitionally equal occurrences of pattern with a bound variable."
  [st expr pattern]
  (if (e/fvar? pattern)
    (e/abstract1 expr (e/fvar-id pattern))
    (let [head (to-head-index pattern)
          nargs (head-num-args pattern)]
      (letfn [(visit [expr offset]
                (if (and (not (e/has-loose-bvars? expr))
                         (= head (to-head-index expr))
                         (= nargs (head-num-args expr))
                         (tc/is-def-eq st expr pattern))
                  (e/bvar offset)
                  (case (e/tag expr)
                    :app (e/app (visit (e/app-fn expr) offset) (visit (e/app-arg expr) offset))
                    :proj (e/proj (e/proj-type-name expr) (e/proj-idx expr)
                                  (visit (e/proj-struct expr) offset))
                    :mdata (e/mdata (e/mdata-data expr) (visit (e/mdata-expr expr) offset))
                    :let (e/let' (e/let-name expr) (visit (e/let-type expr) offset)
                                 (visit (e/let-value expr) offset) (visit (e/let-body expr) (inc offset)))
                    :lam (e/lam (e/lam-name expr) (visit (e/lam-type expr) offset)
                                (visit (e/lam-body expr) (inc offset)) (e/lam-info expr))
                    :forall (e/forall' (e/forall-name expr) (visit (e/forall-type expr) offset)
                                      (visit (e/forall-body expr) (inc offset)) (e/forall-info expr))
                    expr)))]
        (visit expr 0)))))
