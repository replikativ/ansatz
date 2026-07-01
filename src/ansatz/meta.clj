;; Lean-shaped metavariable context for elaboration and tactics.

(ns ansatz.meta
  "Persistent metavariable context.

   This mirrors the useful shape of Lean's `MetavarContext`: expression
   declarations, expression assignments, universe-level assignments, and
   delayed assignments live in one forkable value.  The trusted kernel should
   still only see terms after this context has been zonked."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]))

(def empty-context
  {:depth 0
   :level-assign-depth 0
   :mvar-counter 0
   :level-depth {}
   :decls {}
   :user-names {}
   :level-assignment {}
   :expr-assignment {}
   :delayed-assignment {}})

(defn add-expr-mvar-decl
  "Declare expression metavariable `id` in local context `lctx` with type `type`.
   `opts` may include `:user-name`, `:local-instances`, `:kind`, and
   `:num-scope-args`."
  ([mctx id type lctx]
   (add-expr-mvar-decl mctx id type lctx {}))
  ([mctx id type lctx {:keys [user-name local-instances kind num-scope-args]
                       :or {user-name nil
                            local-instances {}
                            kind :natural
                            num-scope-args 0}}]
   (let [idx (:mvar-counter mctx 0)
         decl {:user-name user-name
               :lctx lctx
               :type type
               :depth (:depth mctx 0)
               :local-instances local-instances
               :kind kind
               :num-scope-args num-scope-args
               :index idx}]
     (cond-> (-> mctx
                 (update :mvar-counter (fnil inc 0))
                 (assoc-in [:decls id] decl))
       user-name (assoc-in [:user-names user-name] id)))))

(defn add-level-mvar-decl
  "Declare universe-level metavariable `id`."
  [mctx id]
  (assoc-in mctx [:level-depth id] (:depth mctx 0)))

(defn expr-decl [mctx id]
  (get-in mctx [:decls id]))

(defn expr-decl! [mctx id]
  (or (expr-decl mctx id)
      (throw (ex-info "Unknown expression metavariable" {:mvar-id id}))))

(defn set-expr-mvar-type [mctx id type]
  (assoc-in mctx [:decls id :type] type))

(defn expr-assignment [mctx id]
  (get-in mctx [:expr-assignment id]))

(defn level-assignment [mctx id]
  (get-in mctx [:level-assignment id]))

(defn delayed-assignment [mctx id]
  (get-in mctx [:delayed-assignment id]))

(defn expr-assigned? [mctx id]
  (contains? (:expr-assignment mctx) id))

(defn expr-delayed-assigned? [mctx id]
  (contains? (:delayed-assignment mctx) id))

(defn expr-assigned-or-delayed? [mctx id]
  (or (expr-assigned? mctx id)
      (expr-delayed-assigned? mctx id)))

(defn assign-expr
  "Low-level expression mvar assignment. Like Lean's low-level API, this does
   not type-check or occurs-check; callers that need safety should perform
   those checks before calling."
  [mctx id value]
  (assoc-in mctx [:expr-assignment id] value))

(defn assign-level [mctx id value]
  (assoc-in mctx [:level-assignment id] value))

(defn assign-delayed
  "Record delayed assignment `?id fvars := ?pending-id`."
  [mctx id fvars pending-id]
  (assoc-in mctx [:delayed-assignment id]
            {:fvars (vec fvars)
             :mvar-id-pending pending-id}))

(defn abstract-fvars
  "Delay abstraction over `fvar-ids` until after metavariables inside `expr`
   have been zonked. This is the local analogue of Lean's delayed abstraction
   machinery for mvars that are solved under binders."
  [expr fvar-ids]
  (e/mdata {::abstract-fvars (vec fvar-ids)} expr))

(declare zonk-level)

(defn- collect-level-mvars* [l acc]
  (if-not (lvl/has-mvar? l)
    acc
    (case (lvl/tag l)
      :mvar (conj acc (lvl/mvar-id l))
      :succ (collect-level-mvars* (lvl/succ-pred l) acc)
      :max (collect-level-mvars* (lvl/max-rhs l)
                                 (collect-level-mvars* (lvl/max-lhs l) acc))
      :imax (collect-level-mvars* (lvl/imax-rhs l)
                                  (collect-level-mvars* (lvl/imax-lhs l) acc))
      acc)))

(defn collect-level-mvars [l]
  (collect-level-mvars* l #{}))

(defn zonk-level
  "Instantiate assigned universe metavariables, chasing assignment chains."
  ([mctx l] (zonk-level mctx l #{}))
  ([mctx l visiting]
   (if-not (lvl/has-mvar? l)
     l
     (case (lvl/tag l)
       :mvar (let [id (lvl/mvar-id l)]
               (if-let [s (level-assignment mctx id)]
                 (do
                   (when (contains? visiting id)
                     (throw (ex-info "Cyclic level metavariable assignment"
                                     {:mvar-id id})))
                   (zonk-level mctx s (conj visiting id)))
                 l))
       :succ (let [p (zonk-level mctx (lvl/succ-pred l) visiting)]
               (if (identical? p (lvl/succ-pred l)) l (lvl/succ p)))
       :max (let [a (zonk-level mctx (lvl/max-lhs l) visiting)
                  b (zonk-level mctx (lvl/max-rhs l) visiting)]
              (if (and (identical? a (lvl/max-lhs l))
                       (identical? b (lvl/max-rhs l)))
                l
                (lvl/level-max a b)))
       :imax (let [a (zonk-level mctx (lvl/imax-lhs l) visiting)
                   b (zonk-level mctx (lvl/imax-rhs l) visiting)]
               (if (and (identical? a (lvl/imax-lhs l))
                        (identical? b (lvl/imax-rhs l)))
                 l
                 (lvl/imax a b)))
       l))))

(defn- contains-unsolved-level-mvar? [mctx l]
  (boolean (seq (remove #(level-assignment mctx %) (collect-level-mvars l)))))

(declare contains-unsolved-expr-mvar?)

(defn- fvar-id-from-expr [x]
  (when (e/fvar? x) (e/fvar-id x)))

(defn- try-expand-delayed [mctx go expr]
  (let [[head args] (e/get-app-fn-args expr)]
    (if-not (e/mvar? head)
      expr
      (let [id (e/mvar-id head)]
        (if-let [{:keys [fvars mvar-id-pending]} (delayed-assignment mctx id)]
          (if (> (count fvars) (count args))
            expr
            (let [pending (go (e/mvar mvar-id-pending))]
              (if (contains-unsolved-expr-mvar? mctx pending)
                expr
                (let [fvar-ids (mapv fvar-id-from-expr fvars)]
                  (if (every? some? fvar-ids)
                    (let [body (e/abstract-many pending fvar-ids)
                          n (count fvar-ids)
                          applied (e/instantiate body (subvec (vec args) 0 n))]
                      (reduce e/app applied (subvec (vec args) n)))
                    expr)))))
          expr)))))

(defn zonk-expr
  "Instantiate assigned expression and level metavariables in `expr`.

   Delayed assignments are only expanded when the pending metavariable is
   already ground after zonking, matching Lean's kernel-boundary discipline."
  [mctx expr]
  (let [cache (java.util.IdentityHashMap.)
        visiting (atom #{})]
    (letfn [(go [expr]
              (or (.get cache expr)
                  (let [result
                        (case (e/tag expr)
                          :mvar (let [id (e/mvar-id expr)]
                                  (if-let [s (expr-assignment mctx id)]
                                    (do
                                      (when (contains? @visiting id)
                                        (throw (ex-info "Cyclic expression metavariable assignment"
                                                        {:mvar-id id})))
                                      (swap! visiting conj id)
                                      (try
                                        (go s)
                                        (finally
                                          (swap! visiting disj id))))
                                    expr))
                          :sort (let [u (zonk-level mctx (e/sort-level expr))]
                                  (if (identical? u (e/sort-level expr))
                                    expr
                                    (e/sort' u)))
                          :const (let [levels (e/const-levels expr)
                                       levels' (mapv #(zonk-level mctx %) levels)]
                                   (if (= levels levels')
                                     expr
                                     (e/const' (e/const-name expr) levels')))
                          :app (let [f (go (e/app-fn expr))
                                     a (go (e/app-arg expr))
                                     rebuilt (if (and (identical? f (e/app-fn expr))
                                                      (identical? a (e/app-arg expr)))
                                               expr
                                               (e/app f a))]
                                 (try-expand-delayed mctx go rebuilt))
                          :lam (let [t (go (e/lam-type expr))
                                     b (go (e/lam-body expr))]
                                 (if (and (identical? t (e/lam-type expr))
                                          (identical? b (e/lam-body expr)))
                                   expr
                                   (e/lam (e/lam-name expr) t b (e/lam-info expr))))
                          :forall (let [t (go (e/forall-type expr))
                                        b (go (e/forall-body expr))]
                                    (if (and (identical? t (e/forall-type expr))
                                             (identical? b (e/forall-body expr)))
                                      expr
                                      (e/forall' (e/forall-name expr) t b (e/forall-info expr))))
                          :let (let [t (go (e/let-type expr))
                                     v (go (e/let-value expr))
                                     b (go (e/let-body expr))]
                                 (if (and (identical? t (e/let-type expr))
                                          (identical? v (e/let-value expr))
                                          (identical? b (e/let-body expr)))
                                   expr
                                   (e/let' (e/let-name expr) t v b)))
                          :mdata (let [x (go (e/mdata-expr expr))]
                                   (if-let [fvar-ids (::abstract-fvars (e/mdata-data expr))]
                                     (e/abstract-many x fvar-ids)
                                     (if (identical? x (e/mdata-expr expr))
                                       expr
                                       (e/mdata (e/mdata-data expr) x))))
                          :proj (let [s (go (e/proj-struct expr))]
                                  (if (identical? s (e/proj-struct expr))
                                    expr
                                    (e/proj (e/proj-type-name expr)
                                            (e/proj-idx expr)
                                            s)))
                          expr)]
                    (.put cache expr result)
                    result)))]
      (go expr))))

(defn collect-expr-mvars
  "Collect expression metavariable ids occurring syntactically in `expr`."
  [expr]
  (letfn [(go [expr acc]
            (case (e/tag expr)
              :mvar (conj acc (e/mvar-id expr))
              :app (go (e/app-arg expr) (go (e/app-fn expr) acc))
              :lam (go (e/lam-body expr) (go (e/lam-type expr) acc))
              :forall (go (e/forall-body expr) (go (e/forall-type expr) acc))
              :let (go (e/let-body expr)
                       (go (e/let-value expr)
                           (go (e/let-type expr) acc)))
              :mdata (go (e/mdata-expr expr) acc)
              :proj (go (e/proj-struct expr) acc)
              acc))]
    (go expr #{})))

(defn contains-unsolved-expr-mvar?
  "True when `expr`, after chasing direct assignments, still contains an
   expression mvar without a direct assignment. Delayed assignments count as
   unsolved until they expand to a ground value."
  [mctx expr]
  (boolean
   (seq
    (filter (fn [id]
              (not (expr-assignment mctx id)))
            (collect-expr-mvars (zonk-expr mctx expr))))))

(defn unassigned-expr-mvars
  "Unassigned expression mvars among the declared mvars, optionally restricted
   to those syntactically occurring in `expr`."
  ([mctx]
   (vec (remove #(expr-assigned-or-delayed? mctx %) (keys (:decls mctx)))))
  ([mctx expr]
   (vec (remove #(expr-assigned-or-delayed? mctx %)
                (collect-expr-mvars (zonk-expr mctx expr))))))

(defn unassigned-level-mvars
  "Unassigned level mvars among declared level mvars, optionally restricted to
   those occurring in `level-or-expr`."
  ([mctx]
   (vec (remove #(level-assignment mctx %) (keys (:level-depth mctx)))))
  ([mctx expr]
   (letfn [(go [expr acc]
             (case (e/tag expr)
               :sort (collect-level-mvars* (e/sort-level expr) acc)
               :const (reduce (fn [acc u] (collect-level-mvars* u acc))
                              acc (e/const-levels expr))
               :app (go (e/app-arg expr) (go (e/app-fn expr) acc))
               :lam (go (e/lam-body expr) (go (e/lam-type expr) acc))
               :forall (go (e/forall-body expr) (go (e/forall-type expr) acc))
               :let (go (e/let-body expr)
                        (go (e/let-value expr)
                            (go (e/let-type expr) acc)))
               :mdata (go (e/mdata-expr expr) acc)
               :proj (go (e/proj-struct expr) acc)
               acc))]
     (vec (remove #(level-assignment mctx %)
                  (go (zonk-expr mctx expr) #{}))))))

(defn closed-expr?
  "True when zonking `expr` leaves no expression or level metavariables."
  [mctx expr]
  (and (empty? (unassigned-expr-mvars mctx expr))
       (empty? (unassigned-level-mvars mctx expr))))
