(ns ansatz.meta.kabstract
  "Lean Meta/KAbstract.lean kabstract and HeadIndex.lean, v4.33.1.
   Abstract keyed occurrences, sharing the caller’s metavariable context.
   The kernel defeq backend has no transparency setting; head/arity filtering
   restricts comparisons as in Lean's keyed matching."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.meta :as meta]))

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
    :mvar [:mvar (e/mvar-id expr)]
    :proj [:proj (e/proj-type-name expr) (e/proj-idx expr)]
    :lit-nat [:lit-nat (e/lit-nat-val expr)]
    :lit-str [:lit-str (e/lit-str-val expr)]
    [(e/tag expr)]))

(defn- contains-occurrence? [occs i]
  (cond
    (= occs :all) true
    (contains? occs :pos) (boolean (some #{i} (:pos occs)))
    (contains? occs :neg) (not (some #{i} (:neg occs)))
    :else (throw (ex-info "Invalid occurrences configuration" {:occs occs}))))

(defn kabstract
  "Lean Meta/KAbstract.lean kabstract. Occurrences are :all, {:pos [1 …]},
   or {:neg [1 …]}. An optional :mctx atom shares assignments with the caller;
   excluded matches roll them back. :transparency follows Meta's configuration."
  ([st expr pattern] (kabstract st expr pattern {}))
  ([st expr pattern {:keys [mctx occs transparency]
                     :or {occs :all transparency meta/*transparency*}}]
   (let [mctx (or mctx (atom meta/empty-context))
         expr (meta/zonk-expr @mctx expr)]
     (if (and (e/fvar? pattern) (= occs :all))
       (e/abstract1 expr (e/fvar-id pattern))
       (let [head (to-head-index pattern)
             nargs (head-num-args pattern)
             occurrence (atom 0)]
         (letfn [(visit-children [expr offset]
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
                     expr))
                 (visit [expr offset]
                   (if (and (not (e/has-loose-bvars? expr))
                            (= head (to-head-index expr))
                            (= nargs (head-num-args expr)))
                     (if-let [matched (meta/is-def-eq @mctx st expr pattern)]
                       (if (contains-occurrence? occs (swap! occurrence inc))
                         (do (reset! mctx matched) (e/bvar offset))
                         (visit-children expr offset))
                       (visit-children expr offset))
                     (visit-children expr offset)))]
           (binding [meta/*transparency* transparency
                     meta/*instance-name?* (or meta/*instance-name?*
                                               (when (= transparency :instances)
                                                 (into #{} (map :name)
                                                       (mapcat val (env/get-extension (:env st) :instances {})))))]
             (visit expr 0))))))))
