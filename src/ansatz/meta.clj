;; Lean-shaped metavariable context for elaboration and tactics.

(ns ansatz.meta
  "Persistent metavariable context.

   This mirrors the useful shape of Lean's `MetavarContext`: expression
   declarations, expression assignments, universe-level assignments, and
   delayed assignments live in one forkable value.  The trusted kernel should
   still only see terms after this context has been zonked."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.tc :as tc]
            [clojure.string :as str]))

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

(defn with-synthetic-opaque-assignment
  "Return `mctx` with synthetic-opaque mvars assignable by unification when
   `enabled?` is true. This mirrors Lean's scoped `withAssignableSyntheticOpaque`
   used by `refine'`; callers should strip the flag before exposing the context
   to ordinary tactic search."
  [mctx enabled?]
  (if enabled?
    (assoc mctx :assign-synthetic-opaque? true)
    (dissoc mctx :assign-synthetic-opaque?)))

(defn- canonical-kind
  "Normalize metavariable kind spellings to Lean's names. Accepts the legacy
   `:synthetic-opaque` alias so kind checks can compare a single spelling."
  [kind]
  (case kind
    :synthetic-opaque :syntheticOpaque
    nil :natural
    kind))

(defn add-expr-mvar-decl
  "Declare expression metavariable `id` in local context `lctx` with type `type`.
   `opts` may include `:user-name`, `:local-instances`, `:kind`, and
   `:num-scope-args`, and `:inst-implicit?`."
  ([mctx id type lctx]
   (add-expr-mvar-decl mctx id type lctx {}))
  ([mctx id type lctx {:keys [user-name local-instances kind num-scope-args inst-implicit?]
                       :or {user-name nil
                            local-instances {}
                            kind :natural
                            num-scope-args 0}}]
   (let [kind (canonical-kind kind)
         idx (:mvar-counter mctx 0)
         decl (cond-> {:user-name user-name
                       :lctx lctx
                       :type type
                       :depth (:depth mctx 0)
                       :local-instances local-instances
                       :kind kind
                       :num-scope-args num-scope-args
                       :index idx}
                inst-implicit? (assoc :inst-implicit? true))]
     (cond-> (-> mctx
                 (update :mvar-counter (fnil inc 0))
                 (assoc-in [:decls id] decl))
       user-name (assoc-in [:user-names user-name] id)))))

(defn add-level-mvar-decl
  "Declare universe-level metavariable `id`."
  [mctx id]
  (assoc-in mctx [:level-depth id] (:depth mctx 0)))

(defn with-depth
  "Return `mctx` with its expression metavariable assignment depth set to
   `depth`. Lean uses this depth to prevent nested unification problems from
   assigning parent metavariables."
  [mctx depth]
  (assoc mctx :depth depth))

(defn inc-depth
  "Enter a nested expression-metavariable assignment depth.

   Like Lean's `incDepth`, the new depth also becomes the universe assignment
   depth by default, so nested unification problems cannot assign level mvars
   of outer problems. Pass `allow-level-assignments?` to keep the current
   level-assignment depth (Lean's `withNewMCtxDepth (allowLevelAssignments := true)`)."
  ([mctx]
   (inc-depth mctx false))
  ([mctx allow-level-assignments?]
   (let [d (inc (:depth mctx 0))]
     (cond-> (assoc mctx :depth d)
       (not allow-level-assignments?) (assoc :level-assign-depth d)))))

(defn with-level-assign-depth
  "Return `mctx` with its universe metavariable assignment depth set."
  [mctx depth]
  (assoc mctx :level-assign-depth depth))

(defn expr-decl [mctx id]
  (get-in mctx [:decls id]))

(defn expr-decl! [mctx id]
  (or (expr-decl mctx id)
      (throw (ex-info "Unknown expression metavariable" {:mvar-id id}))))

(defn set-expr-mvar-type [mctx id type]
  (assoc-in mctx [:decls id :type] type))

(defn set-expr-mvar-lctx [mctx id lctx]
  (assoc-in mctx [:decls id :lctx] lctx))

(defn set-expr-mvar-kind [mctx id kind]
  (assoc-in mctx [:decls id :kind] (canonical-kind kind)))

(defn set-expr-mvar-inst-implicit [mctx id inst-implicit?]
  (if inst-implicit?
    (assoc-in mctx [:decls id :inst-implicit?] true)
    (update-in mctx [:decls id] dissoc :inst-implicit?)))

(defn set-expr-mvar-user-name [mctx id user-name]
  (let [old (get-in mctx [:decls id :user-name])]
    (cond-> (assoc-in mctx [:decls id :user-name] user-name)
      old (update :user-names dissoc old)
      user-name (assoc-in [:user-names user-name] id))))

(defn expr-assignment [mctx id]
  (get-in mctx [:expr-assignment id]))

(defn level-assignment [mctx id]
  (get-in mctx [:level-assignment id]))

(defn delayed-assignment [mctx id]
  (get-in mctx [:delayed-assignment id]))

(defn level-assignable?
  "Lean parity for `isLevelMVarAssignable`: a level mvar is assignable when
   its declaration depth is at least the context's level assignment depth."
  [mctx id]
  (if-let [d (get-in mctx [:level-depth id])]
    (>= d (:level-assign-depth mctx 0))
    (throw (ex-info "Unknown universe metavariable" {:mvar-id id}))))

(defn expr-assignable?
  "Lean parity for `MVarId.isAssignable`: expression mvars are assignable only
   at the current metacontext depth."
  [mctx id]
  (= (:depth (expr-decl! mctx id))
     (:depth mctx 0)))

(defn expr-unification-assignable?
  "Return true when `id` may be assigned by unification.

   Lean's `isDefEq` assigns natural and synthetic mvars at the current depth,
   but not synthetic-opaque tactic goals. Explicit tactic assignment may still
   assign synthetic-opaque goals via the low-level/checked assignment path."
  [mctx id]
  (let [decl (expr-decl! mctx id)]
    (and (expr-assignable? mctx id)
         (or (:assign-synthetic-opaque? mctx)
             (not= :syntheticOpaque (canonical-kind (:kind decl)))))))

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

(defn assign-level
  "Low-level universe mvar assignment. Like Lean's low-level API, this does not
   occurs-check or enforce assignment depth."
  [mctx id value]
  (assoc-in mctx [:level-assignment id] value))

(defn- checked-assignment-error! [msg data]
  (throw (ex-info (str "Invalid metavariable assignment: " msg)
                  (merge {:kind :metavar-assignment-error} data))))

(declare zonk-level zonk-expr collect-expr-mvars closed-expr? unassigned-expr-mvars
         unassigned-level-mvars instantiate-lctx-mvars expr-occurs?)

(defn- check-assignment-scope!
  "Scope check for an assignment value, the local analogue of Lean's
   `CheckAssignment.check` (ExprDefEq.lean checkMVar/checkFVar).

   Walks the zonked `value` and requires that
   - every free variable is in the assignee's local context, and
   - every remaining (unassigned or delayed) metavariable has a local context
     contained in the assignee's, so no later legal assignment to a nested
     mvar can leak variables out of the assignee's scope.

   A delayed-abstraction wrapper (`::abstract-fvars`) acts as a binder: the
   fvars it will abstract are in scope for its subtree. Lean instead restricts
   the nested mvar's context or creates an auxiliary mvar (`ctxApprox`); we
   reject conservatively, which is sound but may fail where Lean succeeds."
  [mctx id value allowed]
  (let [seen (java.util.IdentityHashMap.)]
    (letfn [(check! [expr allowed]
              ;; Proof terms share subexpressions extensively. A previous check
              ;; under a subset of the current allowed fvars is sufficient here.
              (let [prior (.get seen expr)]
                (when-not (some #(every? allowed %) prior)
                  (.put seen expr (conj (or prior []) allowed))
                  (case (e/tag expr)
                    :fvar (when-not (contains? allowed (e/fvar-id expr))
                            (checked-assignment-error!
                             "assignment contains free variables outside the metavariable context"
                             {:mvar-id id
                              :escaped-fvars [(e/fvar-id expr)]
                              :allowed-fvars (vec (sort allowed))}))
                    :mvar (let [mid (e/mvar-id expr)]
                      ;; value is zonked, so a remaining mvar is unassigned or
                      ;; delayed; its future value may mention anything in its
                      ;; own local context.
                            (when-let [d (expr-decl mctx mid)]
                              (let [extra (vec (sort (remove allowed (keys (:lctx d)))))]
                                (when (seq extra)
                                  (checked-assignment-error!
                                   "nested metavariable context is not contained in the assignee's context"
                                   {:mvar-id id
                                    :nested-mvar-id mid
                                    :escaping-fvars extra
                                    :allowed-fvars (vec (sort allowed))})))))
                    :app (do (check! (e/app-fn expr) allowed)
                             (check! (e/app-arg expr) allowed))
                    :lam (do (check! (e/lam-type expr) allowed)
                             (check! (e/lam-body expr) allowed))
                    :forall (do (check! (e/forall-type expr) allowed)
                                (check! (e/forall-body expr) allowed))
                    :let (do (check! (e/let-type expr) allowed)
                             (check! (e/let-value expr) allowed)
                             (check! (e/let-body expr) allowed))
                    :mdata (check! (e/mdata-expr expr)
                                   (if-let [fvar-ids (::abstract-fvars (e/mdata-data expr))]
                                     (into allowed fvar-ids)
                                     allowed))
                    :proj (check! (e/proj-struct expr) allowed)
                    nil))))]
      (check! value allowed))))

(defn- validate-expr-assignment
  [mctx id value {:keys [env check-type? allow-depth-mismatch? unification?]
                  :or {allow-depth-mismatch? false
                       unification? false}}]
  (let [decl (expr-decl! mctx id)
        raw-value value
        value (zonk-expr mctx value)
        type (zonk-expr mctx (:type decl))
        check-type? (if (some? check-type?) check-type? (some? env))]
    (when (expr-assigned-or-delayed? mctx id)
      (checked-assignment-error! "metavariable is already assigned"
                                 {:mvar-id id}))
    (when-not (or allow-depth-mismatch? (expr-assignable? mctx id))
      (checked-assignment-error! "metavariable is not assignable at the current depth"
                                 {:mvar-id id
                                  :mvar-depth (:depth decl)
                                  :context-depth (:depth mctx 0)}))
    (when (and unification? (not (expr-unification-assignable? mctx id)))
      (checked-assignment-error! "metavariable is not assignable by unification"
                                 {:mvar-id id
                                  :kind (:kind decl)}))
    (when (expr-occurs? mctx id value)
      (checked-assignment-error! "cyclic expression assignment"
                                 {:mvar-id id
                                  :value value}))
    (check-assignment-scope! mctx id value (set (keys (:lctx decl))))
    (when check-type?
      (when-not env
        (checked-assignment-error! "type checking requested without an environment"
                                   {:mvar-id id}))
      (when-not (closed-expr? mctx value)
        (checked-assignment-error! "cannot type-check assignment with unresolved metavariables"
                                   {:mvar-id id
                                    :unassigned-expr-mvars (unassigned-expr-mvars mctx value)
                                    :unassigned-level-mvars (unassigned-level-mvars mctx value)}))
      (when-not (closed-expr? mctx type)
        (checked-assignment-error! "cannot type-check metavariable type with unresolved metavariables"
                                   {:mvar-id id
                                    :unassigned-expr-mvars (unassigned-expr-mvars mctx type)
                                    :unassigned-level-mvars (unassigned-level-mvars mctx type)}))
      ;; value+type are closed here (guarded above) — gate via the Java kernel
      ;; TC (lazyDeltaReduction defeq). The Clojure tc's whnf-both-sides defeq
      ;; made EVERY unification assignment a potential exponential cliff on
      ;; mathlib-deep types (multi-minute confirms observed in E0).
      (let [lctx (instantiate-lctx-mvars mctx (:lctx decl))
            jtc (ansatz.kernel.TypeChecker. env)
            _ (doseq [[fid d] lctx]
                (when (:type d)
                  (.addLocal jtc (long fid) (str (or (:name d) "x")) (:type d))))
            [inferred ok?] (try
                             (let [inferred (.inferType jtc value)]
                               [inferred (.isDefEq jtc inferred type)])
                             (catch Exception e [(.getMessage e) false]))]
        (when-not ok?
          (checked-assignment-error! "assignment type mismatch"
                                     {:mvar-id id
                                      :expected type
                                      :inferred inferred
                                      :value value}))))
    raw-value))

(defn checked-assign-expr
  "Validate and assign expression metavariable `id := value`.

   This is the checked counterpart to `assign-expr`, analogous to Lean's
   `MVarId.checkedAssign`/`isDefEq` assignment boundary. It always enforces
   assignment freshness, depth, occurs check, and local-context safety. When
   `:env` is supplied, it also verifies `infer(value) ≡ mvar.type` after
   zonking, provided the value and type contain no unresolved mvars.

   Options:
   - `:env` enables type compatibility checking.
   - `:check-type?` overrides whether type compatibility is checked.
   - `:unification?` additionally rejects synthetic-opaque goals.
   - `:allow-depth-mismatch?` bypasses the depth guard for explicit recovery
     paths."
  ([mctx id value]
   (checked-assign-expr mctx id value {}))
  ([mctx id value opts]
   (assign-expr mctx id (validate-expr-assignment mctx id value opts))))

(defn checked-assign-level
  "Validate and assign universe metavariable `id := value` with Lean-style
   depth and occurs checks."
  [mctx id value]
  (when (level-assignment mctx id)
    (checked-assignment-error! "universe metavariable is already assigned"
                               {:mvar-id id}))
  (when-not (level-assignable? mctx id)
    (checked-assignment-error! "universe metavariable is not assignable at the current depth"
                               {:mvar-id id
                                :level-depth (get-in mctx [:level-depth id])
                                :level-assign-depth (:level-assign-depth mctx 0)}))
  (let [value (zonk-level mctx value)]
    (when (lvl/occurs? id value)
      (checked-assignment-error! "cyclic universe assignment"
                                 {:mvar-id id
                                  :value value}))
    (assign-level mctx id value)))

(defn assign-delayed
  "Record delayed assignment `?id fvars := ?pending-id`."
  [mctx id fvars pending-id]
  (assoc-in mctx [:delayed-assignment id]
            {:fvars (vec fvars)
             :mvar-id-pending pending-id}))

(defn abstract-fvars
  "Delay abstraction over `fvar-ids` until after metavariables inside `expr`
   have been zonked. This is the local analogue of Lean's delayed abstraction
   machinery for mvars that are solved under binders.

   The delay marker is ONLY needed when `expr` contains a metavariable (whose
   later solution may reintroduce one of `fvar-ids` under the binder). When
   `expr` is metavariable-free there is nothing to wait for, so we return it
   unwrapped — the caller's own `abstract1` performs the abstraction, and no
   `::abstract-fvars` mdata survives for zonk to strip. This keeps the marker
   off mvar-free terms, which is what lets `zonk-expr` short-circuit on them."
  [^ansatz.kernel.Expr expr fvar-ids]
  (if (.hasMVar expr)
    (e/mdata {::abstract-fvars (vec fvar-ids)} expr)
    expr))

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

(defn has-assigned-level-mvar?
  "Return true iff `l` contains a universe mvar with an assignment."
  [mctx l]
  (boolean (some #(level-assignment mctx %) (collect-level-mvars l))))

(defn has-assignable-level-mvar?
  "Return true iff `l` contains a universe mvar assignable at the current
   level-assignment depth."
  [mctx l]
  (boolean
   (some (fn [id]
           (and (contains? (:level-depth mctx) id)
                (level-assignable? mctx id)))
         (collect-level-mvars l))))

(declare ^:dynamic *is-def-eq-stuck-ex*)

(defn- level-mvar-assignable?
  "A level mvar this metacontext declares at an assignable depth (an undeclared one belongs to an
   outer metacontext)."
  [mctx id]
  (and (contains? (:level-depth mctx) id) (level-assignable? mctx id)))

(defn is-level-def-eq
  "Lean-shaped universe-level unification.

   Return an updated metacontext on success and nil on failure. Successful
   mvar assignments are recorded in `:level-assignment` using the checked
   assignment boundary, so depth and occurs checks still apply."
  [mctx a b]
  (let [a (zonk-level mctx a)
        b (zonk-level mctx b)]
    (cond
      (lvl/level= a b) mctx

      (and (lvl/succ? a) (lvl/succ? b))
      (is-level-def-eq mctx (lvl/succ-pred a) (lvl/succ-pred b))

      (and (lvl/mvar? a) (level-mvar-assignable? mctx (lvl/mvar-id a)))
      (when-not (lvl/occurs? (lvl/mvar-id a) b)
        (try
          (checked-assign-level mctx (lvl/mvar-id a) b)
          (catch clojure.lang.ExceptionInfo _ nil)))

      (and (lvl/mvar? b) (level-mvar-assignable? mctx (lvl/mvar-id b)))
      (when-not (lvl/occurs? (lvl/mvar-id b) a)
        (try
          (checked-assign-level mctx (lvl/mvar-id b) a)
          (catch clojure.lang.ExceptionInfo _ nil)))

      ;; Lean LevelDefEq: `?u =?= v` with no assignable level mvar is stuck under isDefEqStuckEx
      (or (lvl/mvar? a) (lvl/mvar? b))
      (if *is-def-eq-stuck-ex*
        (throw (ex-info "isDefEq stuck" {:kind :ansatz.meta/is-def-eq-stuck :lhs a :rhs b}))
        nil)

      (and (lvl/level-zero? a) (lvl/max? b))
      (when-let [mctx (is-level-def-eq mctx a (lvl/max-lhs b))]
        (is-level-def-eq mctx a (lvl/max-rhs b)))

      (and (lvl/max? a) (lvl/level-zero? b))
      (when-let [mctx (is-level-def-eq mctx (lvl/max-lhs a) b)]
        (is-level-def-eq mctx (lvl/max-rhs a) b))

      (and (lvl/level-zero? a) (lvl/imax? b))
      (is-level-def-eq mctx a (lvl/imax-rhs b))

      (and (lvl/imax? a) (lvl/level-zero? b))
      (is-level-def-eq mctx (lvl/imax-rhs a) b)

      :else nil)))

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

(declare zonk-expr*)

(defn zonk-expr
  "Instantiate assigned expression and level metavariables in `expr`.

   Delayed assignments are only expanded when the pending metavariable is
   already ground after zonking, matching Lean's kernel-boundary discipline.

   Fast path: an expression with NO metavariable (the O(1) `Expr.hasMVar` bit)
   has nothing to instantiate, so it is returned unchanged without traversal.
   This is what keeps `is-def-eq` from re-zonking mvar-free subterms at every
   recursion level (the per-level quadratic)."
  [mctx ^ansatz.kernel.Expr expr]
  (if-not (.hasMVar expr)
    expr
    (zonk-expr* mctx expr)))

(defn- zonk-expr*
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
                            :app (let [h (e/get-app-fn expr)]
                                   (if (and (e/mvar? h) (expr-assignment mctx (e/mvar-id h)))
                                     ;; Lean's instantiateMVars: an assigned mvar head is
                                     ;; instantiated and beta-reduced with its arguments
                                     (let [f (go h)
                                           args (mapv go (e/get-app-args expr))]
                                       (loop [f f args (seq args)]
                                         (if (and args (e/lam? f))
                                           (recur (e/instantiate1 (e/lam-body f) (first args)) (next args))
                                           (reduce e/app f args))))
                                     (let [f (go (e/app-fn expr))
                                           a (go (e/app-arg expr))
                                           rebuilt (if (and (identical? f (e/app-fn expr))
                                                            (identical? a (e/app-arg expr)))
                                                     expr
                                                     (e/app f a))]
                                       (try-expand-delayed mctx go rebuilt))))
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
                                     ;; Abstract only once every mvar inside is
                                     ;; solved. Abstracting while an mvar is
                                     ;; still unassigned would silently drop the
                                     ;; wrapper (an mvar leaf has no fvar
                                     ;; occurrences), so a later solution
                                     ;; mentioning these fvars would leak them
                                     ;; outside their binder.
                                       (if (contains-unsolved-expr-mvar? mctx x)
                                         (if (identical? x (e/mdata-expr expr))
                                           expr
                                           (e/mdata (e/mdata-data expr) x))
                                         (e/abstract-many x fvar-ids))
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

(defn has-expr-mvar?
  "Cheap syntactic check with early exit: does `expr` contain any expression
   metavariable node? (Expr flags do not track mvars, so this is a walk.)"
  [expr]
  (case (e/tag expr)
    :mvar true
    :app (or (has-expr-mvar? (e/app-fn expr)) (has-expr-mvar? (e/app-arg expr)))
    :lam (or (has-expr-mvar? (e/lam-type expr)) (has-expr-mvar? (e/lam-body expr)))
    :forall (or (has-expr-mvar? (e/forall-type expr)) (has-expr-mvar? (e/forall-body expr)))
    :let (or (has-expr-mvar? (e/let-type expr))
             (has-expr-mvar? (e/let-value expr))
             (has-expr-mvar? (e/let-body expr)))
    :mdata (has-expr-mvar? (e/mdata-expr expr))
    :proj (has-expr-mvar? (e/proj-struct expr))
    false))

(defn collect-expr-mvars
  "Collect expression metavariable ids occurring syntactically in `expr`.
   Traverse each expression node once: proof terms from case splitting share
   large subtrees, as Lean's expression DAGs do."
  [expr]
  (let [seen (java.util.IdentityHashMap.)
        ids (java.util.HashSet.)]
    (letfn [(go [expr]
                (when (and (.hasMVar ^ansatz.kernel.Expr expr)
                           (not (.containsKey seen expr)))
                  (.put seen expr true)
                  (case (e/tag expr)
                    :mvar (.add ids (e/mvar-id expr))
                    :app (do (go (e/app-fn expr)) (go (e/app-arg expr)))
                    :lam (do (go (e/lam-type expr)) (go (e/lam-body expr)))
                    :forall (do (go (e/forall-type expr)) (go (e/forall-body expr)))
                    :let (do (go (e/let-type expr))
                             (go (e/let-value expr))
                             (go (e/let-body expr)))
                    :mdata (go (e/mdata-expr expr))
                    :proj (go (e/proj-struct expr))
                    nil)))]
      (go expr)
      (set ids))))

(defn expr-occurs?
  "Occurs check for expression mvar `id` in `expr`.

   Follows direct assignments (via zonking) and, like Lean's `occursCheck`,
   chases delayed assignments to their pending metavariables, so a cycle
   through a delayed assignment is rejected at assignment time instead of
   surfacing later as a zonk error."
  [mctx id expr]
  (letfn [(check [seen expr]
            (let [ids (collect-expr-mvars (zonk-expr mctx expr))]
              (boolean
               (or (contains? ids id)
                   (some (fn [mid]
                           (when-not (contains? seen mid)
                             (when-let [{:keys [mvar-id-pending]} (delayed-assignment mctx mid)]
                               (check (conj seen mid) (e/mvar mvar-id-pending)))))
                         ids)))))]
    (check #{} expr)))

(declare expr-mvars)

(defn expr-mvars
  "Lean-style `getMVars`: instantiate assigned mvars, collect remaining mvars,
   and follow delayed assignments to their pending metavariables."
  ([mctx expr]
   (expr-mvars mctx expr #{}))
  ([mctx expr visiting]
   (let [ids (collect-expr-mvars (zonk-expr mctx expr))]
     (vec
      (sort
       (reduce
        (fn [acc id]
          (let [acc (conj acc id)]
            (if (contains? visiting id)
              acc
              (if-let [{:keys [mvar-id-pending]} (delayed-assignment mctx id)]
                (into acc (expr-mvars mctx (e/mvar mvar-id-pending) (conj visiting id)))
                acc))))
        #{}
        ids))))))

(defn expr-mvars-no-delayed
  "Like `expr-mvars`, but remove mvars that are themselves delayed-assigned."
  [mctx expr]
  (vec (remove #(expr-delayed-assigned? mctx %)
               (expr-mvars mctx expr))))

(declare mvar-dependencies)

(defn- add-expr-mvar-deps [mctx acc expr]
  (into acc (expr-mvars mctx expr)))

(defn- add-local-decl-mvar-deps [mctx acc local-decl]
  (let [acc (if-let [t (:type local-decl)]
              (add-expr-mvar-deps mctx acc t)
              acc)]
    (if-let [v (:value local-decl)]
      (add-expr-mvar-deps mctx acc v)
      acc)))

(defn mvar-dependencies
  "Return mvars that occur in the type/local context of mvar `id`, recursively
   following delayed assignments. This is the local analogue of Lean's
   `MVarId.getMVarDependencies`."
  ([mctx id]
   (mvar-dependencies mctx id false))
  ([mctx id include-delayed?]
   (letfn [(go [seen acc id]
               (if (contains? seen id)
                 acc
                 (let [seen (conj seen id)
                       decl (expr-decl mctx id)
                       acc (if decl
                             (let [acc (add-expr-mvar-deps mctx acc (:type decl))]
                               (reduce (fn [acc [_ local-decl]]
                                         (add-local-decl-mvar-deps mctx acc local-decl))
                                       acc (:lctx decl)))
                             acc)
                       acc (if-let [{:keys [mvar-id-pending]} (delayed-assignment mctx id)]
                             (cond-> acc
                               (or include-delayed?
                                   (not (expr-assigned-or-delayed? mctx mvar-id-pending)))
                               (conj mvar-id-pending))
                             acc)]
                   (if-let [{:keys [mvar-id-pending]} (delayed-assignment mctx id)]
                     (go seen acc mvar-id-pending)
                     acc))))]
     (vec (sort (disj (go #{} #{} id) id))))))

(defn expr-mvar-dependencies
  "Return dependencies of all mvars occurring in `expr`."
  ([mctx expr]
   (expr-mvar-dependencies mctx expr false))
  ([mctx expr include-delayed?]
   (let [ids (if include-delayed?
               (expr-mvars mctx expr)
               (expr-mvars-no-delayed mctx expr))]
     (vec
      (sort
       (reduce (fn [acc id]
                 (into acc (mvar-dependencies mctx id include-delayed?)))
               (set ids)
               ids))))))

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
   (let [seen (java.util.IdentityHashMap.)
         ids (java.util.HashSet.)]
     (letfn [(add-level! [level]
               (doseq [id (collect-level-mvars* level #{})]
                 (.add ids id)))
             (go [expr]
                 (when (and (.hasMVar ^ansatz.kernel.Expr expr)
                            (not (.containsKey seen expr)))
                   (.put seen expr true)
                   (case (e/tag expr)
                     :sort (add-level! (e/sort-level expr))
                     :const (doseq [u (e/const-levels expr)] (add-level! u))
                     :app (do (go (e/app-fn expr)) (go (e/app-arg expr)))
                     :lam (do (go (e/lam-type expr)) (go (e/lam-body expr)))
                     :forall (do (go (e/forall-type expr)) (go (e/forall-body expr)))
                     :let (do (go (e/let-type expr))
                              (go (e/let-value expr))
                              (go (e/let-body expr)))
                     :mdata (go (e/mdata-expr expr))
                     :proj (go (e/proj-struct expr))
                     nil)))]
       (go (zonk-expr mctx expr))
       (vec (remove #(level-assignment mctx %) ids))))))

(defn closed-expr?
  "True when zonking `expr` leaves no expression or level metavariables."
  [mctx expr]
  (and (empty? (unassigned-expr-mvars mctx expr))
       (empty? (unassigned-level-mvars mctx expr))))

(defn fresh-result-mvar-ids
  "Lean-style hole-collection boundary (`collectMVars` over the zonked
   result): unassigned expression mvars occurring in `expr` whose declaration
   index is at least `start-index`, in creation order."
  [mctx expr start-index]
  (->> (expr-mvars-no-delayed mctx expr)
       distinct
       (filter (fn [id]
                 (let [decl (expr-decl mctx id)]
                   (and decl
                        (>= (:index decl 0) start-index)
                        (not (expr-assigned-or-delayed? mctx id))))))
       (sort-by #(get-in mctx [:decls % :index] 0))
       vec))

(defn fresh-result-level-ids
  "Unassigned universe mvars occurring in `expr` that are not in
   `old-level-ids`."
  [mctx expr old-level-ids]
  (->> (unassigned-level-mvars mctx expr)
       distinct
       (remove old-level-ids)
       sort
       vec))

(defn instantiate-level-mvars
  "Lean-named alias for `zonk-level`."
  [mctx l]
  (zonk-level mctx l))

(defn instantiate-expr-mvars
  "Lean-named alias for `zonk-expr`."
  [mctx expr]
  (zonk-expr mctx expr))

(defn instantiate-lctx-mvars
  "Instantiate assigned expression and level metavariables in every declaration
   in an Ansatz local context."
  [mctx lctx]
  (reduce-kv
   (fn [lctx id decl]
     (let [decl' (cond-> decl
                   (:type decl) (update :type #(zonk-expr mctx %))
                   (:value decl) (update :value #(zonk-expr mctx %)))]
       (assoc lctx id decl')))
   {}
   lctx))

(defn instantiate-mvar-decl-mvars
  "Instantiate assigned mvars in a metavariable declaration's local context and
   type, then store the updated declaration."
  [mctx id]
  (let [decl (expr-decl! mctx id)]
    (assoc-in mctx [:decls id]
              (-> decl
                  (update :lctx #(instantiate-lctx-mvars mctx %))
                  (update :type #(zonk-expr mctx %))))))

(declare infer-type is-def-eq)

(defn- open-binder-type
  [st lctx name type body]
  (let [fid (swap! (:next-id st) inc)
        fv (e/fvar fid)
        lctx' (red/lctx-add-local lctx fid name type)
        st' (assoc st :lctx lctx')]
    [st' fv lctx' (e/instantiate1 body fv)]))

(defn- kernel-defeq-when-closed?
  [mctx st a b]
  (let [a (zonk-expr mctx a)
        b (zonk-expr mctx b)]
    (and (closed-expr? mctx a)
         (closed-expr? mctx b)
         (try (tc/is-def-eq st a b)
              (catch Exception _ false)))))

(defn- mvar-head-stuck?
  [mctx expr]
  (let [[head _] (e/get-app-fn-args expr)
        head (zonk-expr mctx head)]
    (e/mvar? head)))

(defn whnf
  "Meta-layer weak-head reduction.

   This is the analogue of Lean `Meta.whnf` for the subset Ansatz currently
   needs: it instantiates assigned mvars first and reduces with a metacontext
   aware `infer-type` callback. If the head is an unassigned expression mvar,
   the expression is stuck and returned unchanged."
  [mctx st expr]
  (let [expr (zonk-expr mctx expr)]
    (if (mvar-head-stuck? mctx expr)
      expr
      (red/whnf (:env st) expr (:lctx st)
                {:infer-fn (fn [e] (infer-type mctx st e))
                 :is-def-eq-fn (fn [a b] (kernel-defeq-when-closed? mctx st a b))}))))

(defn ensure-sort
  "Meta-layer sort check used by `infer-type`."
  [mctx st expr]
  (let [expr (whnf mctx st expr)]
    (if (e/sort? expr)
      expr
      (throw (ex-info "Meta inferType expected a sort"
                      {:kind :meta-type-error :got expr})))))

(defn ensure-pi
  "Meta-layer function-type check used by `infer-type`."
  [mctx st expr]
  (let [expr (whnf mctx st expr)]
    (if (e/forall? expr)
      [(e/forall-name expr) (e/forall-type expr) (e/forall-body expr) (e/forall-info expr)]
      (throw (ex-info "Meta inferType expected a function type"
                      {:kind :meta-type-error :got expr})))))

(defn- infer-proj-type
  "Lean's `inferProjType`: the type of field `idx` of `struct : S params`, from the constructor's
   type with the parameters instantiated and earlier fields replaced by their projections."
  [mctx st sname idx struct struct-type]
  (let [env (:env st)
        t (whnf mctx st struct-type)
        [h params] (e/get-app-fn-args t)
        ^ansatz.kernel.ConstantInfo ici (env/lookup env sname)]
    (when-not (and (e/const? h) (= sname (e/const-name h)) ici (env/induct? ici))
      (throw (ex-info "Meta inferType: projection of a non-structure"
                      {:kind :meta-type-error :struct-type t})))
    (let [ctor (first (.ctors ici))
          ^ansatz.kernel.ConstantInfo cci (env/lookup! env ctor)
          lps (vec (.levelParams cci))
          cty (e/instantiate-level-params (.type cci) (zipmap lps (e/const-levels h)))
          cty (reduce (fn [ty p] (let [ty (if (e/forall? ty) ty (whnf mctx st ty))]
                                   (e/instantiate1 (e/forall-body ty) p)))
                      cty params)]
      (loop [ty cty i 0]
        (let [ty (if (e/forall? ty) ty (whnf mctx st ty))]
          (when-not (e/forall? ty)
            (throw (ex-info "Meta inferType: projection index out of range"
                            {:kind :meta-type-error :idx idx})))
          (if (= i idx)
            (zonk-expr mctx (e/forall-type ty))
            (recur (e/instantiate1 (e/forall-body ty) (e/proj sname i struct)) (inc i))))))))

(defn infer-type
  "Infer the type of `expr` while consulting a Lean-shaped metacontext.

   Unlike the kernel checker, this function accepts real `Expr.mvar` nodes:
   unassigned mvars infer to their declaration type, and assigned mvars are
   instantiated before inference. This follows Lean's Meta `inferType`: it is
   type-shape inference, not full term validation, so application arguments are
   not checked for definitional equality with the domain."
  ([mctx st expr]
   (letfn [(go [st expr]
               (let [expr (zonk-expr mctx expr)]
                 (case (e/tag expr)
                   :mvar (zonk-expr mctx (:type (expr-decl! mctx (e/mvar-id expr))))

                   :bvar (throw (ex-info "Meta inferType found loose bound variable"
                                         {:kind :meta-type-error :expr expr}))

                   :sort (e/sort' (lvl/succ (e/sort-level expr)))

                   :const (tc/infer-type st expr)

                   :fvar (if-let [decl (red/lctx-lookup (:lctx st) (e/fvar-id expr))]
                           (zonk-expr mctx (:type decl))
                           (tc/infer-type st expr))

                   :app (let [fn-type (whnf mctx st (go st (e/app-fn expr)))
                              [_ _ body _] (ensure-pi mctx st fn-type)]
                          (zonk-expr mctx (e/instantiate1 body (e/app-arg expr))))

                   :lam (let [dom-type (zonk-expr mctx (e/lam-type expr))
                              _ (ensure-sort mctx st (go st dom-type))
                              [st' fv _ body] (open-binder-type st (:lctx st)
                                                                (e/lam-name expr)
                                                                dom-type
                                                                (e/lam-body expr))
                              body-type (go st' body)]
                          (e/forall' (e/lam-name expr) dom-type
                                     (e/abstract1 body-type (e/fvar-id fv))
                                     (e/lam-info expr)))

                   :forall (let [dom-type (zonk-expr mctx (e/forall-type expr))
                                 dom-sort (ensure-sort mctx st (go st dom-type))
                                 [st' _ _ body] (open-binder-type st (:lctx st)
                                                                  (e/forall-name expr)
                                                                  dom-type
                                                                  (e/forall-body expr))
                                 cod-sort (ensure-sort mctx st' (go st' body))]
                             (e/sort' (lvl/imax (e/sort-level dom-sort)
                                                (e/sort-level cod-sort))))

                   :let (let [value (zonk-expr mctx (e/let-value expr))
                              type (zonk-expr mctx (e/let-type expr))
                              fid (swap! (:next-id st) inc)
                              fv (e/fvar fid)
                              lctx' (red/lctx-add-let (:lctx st) fid (e/let-name expr) type value)
                              st' (assoc st :lctx lctx')
                              body-type (go st' (e/instantiate1 (e/let-body expr) fv))]
                          (zonk-expr mctx (e/instantiate1 (e/abstract1 body-type fid) value)))

                   :lit-nat (tc/infer-type st expr)
                   :lit-str (tc/infer-type st expr)
                   :mdata (go st (e/mdata-expr expr))
                   :proj (if (.hasMVar ^ansatz.kernel.Expr expr)
                           (infer-proj-type mctx st (e/proj-type-name expr) (e/proj-idx expr)
                                            (e/proj-struct expr) (go st (e/proj-struct expr)))
                           (tc/infer-type st expr)))))]
     (go st expr)))
  ([mctx env lctx expr]
   (infer-type mctx (tc/mk-tc-state-with-locals env lctx) expr)))

(defn- try-assign-expr-defeq
  [mctx st id value]
  (when-not (expr-occurs? mctx id value)
    (try
      (let [decl (expr-decl! mctx id)
            value-type (infer-type mctx st value)
            mctx (is-def-eq mctx st value-type (:type decl))]
        (when mctx
          (checked-assign-expr mctx id value
                               {:check-type? false
                                :unification? true})))
      (catch clojure.lang.ExceptionInfo _ nil))))

(defn- expr-mvar-assignment-candidate
  [mctx a b]
  (letfn [(unassigned? [x]
            (and (e/mvar? x)
                 (not (expr-assigned-or-delayed? mctx (e/mvar-id x)))))
          (synthetic? [x]
            (when (e/mvar? x)
              (= :synthetic (:kind (expr-decl! mctx (e/mvar-id x))))))]
    (cond
      (and (unassigned? a) (unassigned? b) (synthetic? a) (not (synthetic? b)))
      [(e/mvar-id b) a]

      (and (unassigned? a) (unassigned? b))
      [(e/mvar-id a) b]

      (unassigned? a)
      [(e/mvar-id a) b]

      (unassigned? b)
      [(e/mvar-id b) a])))

(defn- mvar-app-spine
  [mctx expr]
  (let [[head args] (e/get-app-fn-args expr)]
    (when (and (e/mvar? head)
               (seq args)
               (not (expr-assigned-or-delayed? mctx (e/mvar-id head))))
      [(e/mvar-id head) args])))

(defn- try-assign-miller-pattern
  [mctx st bound id args value]
  (when (and (every? (fn [arg]
                       (and (e/fvar? arg)
                            (contains? bound (e/fvar-id arg))))
                     args)
             (let [ids (map e/fvar-id args)]
               (apply distinct? ids))
             (not (expr-occurs? mctx id value)))
    (let [ids (mapv e/fvar-id args)
          types (mapv (fn [fid]
                        (:type (red/lctx-lookup (:lctx st) fid)))
                      ids)]
      (when (every? some? types)
        (let [body (e/abstract-many value ids)
              lam (reduce (fn [acc i]
                            (let [type (e/abstract-many
                                        (zonk-expr mctx (nth types i))
                                        (subvec ids 0 i))]
                              (e/lam "x" type acc :default)))
                          body
                          (reverse (range (count ids))))]
          (try-assign-expr-defeq mctx st id lam))))))

(defn zonked-has-mvar?
  "Does `expr` contain any expression- or universe-level metavariable? Uses the
   O(1) `Expr.hasMVar` bit (computed compositionally at construction), so on
   already-zonked terms `(not (zonked-has-mvar? e))` decides closedness in
   constant time — without the full re-zonk that `closed-expr?` performs."
  [^ansatz.kernel.Expr expr]
  (.hasMVar expr))

(defn- closed-kernel-defeq
  [mctx st a b]
  (when (and (closed-expr? mctx a)
             (closed-expr? mctx b))
    (try
      (when (tc/is-def-eq st a b) mctx)
      (catch Exception _ nil))))

(defn- closed-kernel-defeq-zonked
  "Like `closed-kernel-defeq` but assumes `a`/`b` are already zonked, so it uses
   the cheap `zonked-has-mvar?` closedness check instead of re-zonking."
  [mctx st a b]
  (when (and (not (zonked-has-mvar? a))
             (not (zonked-has-mvar? b)))
    (try
      (when (tc/is-def-eq st a b) mctx)
      (catch Exception _ nil))))

(defn- is-def-eq-core
  [mctx st bound a b]
  ;; NOTE: closed terms are handled by the both-closed fast path in `is-def-eq`
  ;; before reaching here, so this runs only when at least one side has an
  ;; unresolved metavariable. We must NOT re-run a full kernel defeq at every
  ;; structural node — that made a single closed comparison do O(term-size)
  ;; kernel reductions (a severe blowup on speculative simp/apply matching).
  (or
   (when (= a b) mctx)
   (when-let [[id value] (expr-mvar-assignment-candidate mctx a b)]
     (or (try-assign-expr-defeq mctx st id value)
         ;; Lean's isDefEqQuickMVarMVar: when both sides are mvars and the
         ;; preferred direction is not assignable (e.g. a synthetic-opaque
         ;; goal on the chosen side), retry assigning the other mvar.
         (when (and (e/mvar? value)
                    (not= (e/mvar-id value) id)
                    (not (expr-assigned-or-delayed? mctx (e/mvar-id value))))
           (try-assign-expr-defeq mctx st (e/mvar-id value) (e/mvar id)))))
   (when-let [[id args] (mvar-app-spine mctx a)]
     (try-assign-miller-pattern mctx st bound id args b))
   (when-let [[id args] (mvar-app-spine mctx b)]
     (try-assign-miller-pattern mctx st bound id args a))
   (when (= (e/tag a) (e/tag b))
     (case (e/tag a)
       :sort (is-level-def-eq mctx (e/sort-level a) (e/sort-level b))

       :const (when (and (= (e/const-name a) (e/const-name b))
                         (= (count (e/const-levels a))
                            (count (e/const-levels b))))
                (reduce (fn [mctx [u v]]
                          (when mctx (is-level-def-eq mctx u v)))
                        mctx
                        (map vector (e/const-levels a) (e/const-levels b))))

       ;; Faithful to Lean's `isDefEqApp`: when the spine heads are CONCRETE,
       ;; decompose the application spine ONCE (head + args) and compare heads
       ;; then arguments pairwise. The old code recursed on the CURRIED `app-fn`
       ;; prefixes, re-running the outer whnf-retry once per prefix level —
       ;; quadratic reduction on deep spines. Lean only reaches `isDefEqApp`
       ;; after the metavariable cases, so we keep the curried peel when either
       ;; ultimate head is an mvar (that the mvar cases above did not resolve):
       ;; there the mvar head must be free to absorb a partial-application
       ;; prefix, which strict arity-matched spine comparison would reject.
       :app (if (or (e/mvar? (e/get-app-fn a)) (e/mvar? (e/get-app-fn b)))
              (when-let [mctx (is-def-eq mctx st bound (e/app-fn a) (e/app-fn b))]
                (is-def-eq mctx st bound (e/app-arg a) (e/app-arg b)))
              (let [[head-a args-a] (e/get-app-fn-args a)
                    [head-b args-b] (e/get-app-fn-args b)]
                (when (= (count args-a) (count args-b))
                  (when-let [mctx (is-def-eq mctx st bound head-a head-b)]
                    (reduce (fn [mctx [x y]]
                              (when mctx (is-def-eq mctx st bound x y)))
                            mctx
                            (map vector args-a args-b))))))

       :lam (when-let [mctx (is-def-eq mctx st bound (e/lam-type a) (e/lam-type b))]
              (let [[st' fv _ body-a] (open-binder-type st (:lctx st)
                                                        (e/lam-name a)
                                                        (e/lam-type a)
                                                        (e/lam-body a))
                    body-b (e/instantiate1 (e/lam-body b) fv)]
                (is-def-eq mctx st' (conj bound (e/fvar-id fv)) body-a body-b)))

       :forall (when-let [mctx (is-def-eq mctx st bound (e/forall-type a) (e/forall-type b))]
                 (let [[st' fv _ body-a] (open-binder-type st (:lctx st)
                                                           (e/forall-name a)
                                                           (e/forall-type a)
                                                           (e/forall-body a))
                       body-b (e/instantiate1 (e/forall-body b) fv)]
                   (is-def-eq mctx st' (conj bound (e/fvar-id fv)) body-a body-b)))

       :let (when-let [mctx (is-def-eq mctx st bound (e/let-type a) (e/let-type b))]
              (when-let [mctx (is-def-eq mctx st bound (e/let-value a) (e/let-value b))]
                (is-def-eq mctx st
                           bound
                           (e/instantiate1 (e/let-body a) (e/let-value a))
                           (e/instantiate1 (e/let-body b) (e/let-value b)))))

       :mdata (is-def-eq mctx st bound (e/mdata-expr a) (e/mdata-expr b))

       :proj (when (and (= (e/proj-type-name a) (e/proj-type-name b))
                        (= (e/proj-idx a) (e/proj-idx b)))
               (is-def-eq mctx st bound (e/proj-struct a) (e/proj-struct b)))

       :fvar (when (= (e/fvar-id a) (e/fvar-id b)) mctx)
       (:lit-nat :lit-str :bvar) (when (= a b) mctx)
       nil))))

(defn- whnf-opts
  [mctx st]
  {:infer-fn (fn [e] (infer-type mctx st e))
   :is-def-eq-fn (fn [a b] (kernel-defeq-when-closed? mctx st a b))})

(defn- same-const-head?
  [a b]
  (let [ha (e/get-app-fn a) hb (e/get-app-fn b)]
    (and (e/const? ha) (e/const? hb) (= (e/const-name ha) (e/const-name hb)))))

(defn- delta-align
  "Unfold `x`'s head (one `lazyDeltaReduction` step at a time, `fuel` steps at most) until it
   shares a head constant with `y`. Returns the aligned `x`, or nil."
  [step x y fuel]
  (loop [x x fuel fuel]
    (cond
      (same-const-head? x y) x
      (not (pos? fuel)) nil
      :else (when-let [x' (step x)] (recur x' (dec fuel))))))

(def ^:dynamic *transparency*
  "Lean's `TransparencyMode` for meta-layer unification: `:default` unfolds every definition;
   `:instances` (instance synthesis) only reducible ones and instances (`*instance-name?*`).
   Metavariable-free comparisons still go to the kernel, which unfolds everything."
  :default)

(def ^:dynamic *instance-name?*
  "Under `:instances` transparency: which constants are instances (set by instance synthesis)."
  nil)

(declare whnf-at reducible-const?)

(defn- unfoldable-head?
  "May the head constant of `x` (or of the structure a projection head is stuck on) be unfolded
   at the current transparency?"
  [env x]
  (or (= *transparency* :default)
      (let [h (e/get-app-fn x)
            h (if (e/proj? h) (e/get-app-fn (e/proj-struct h)) h)]
        (and (e/const? h)
             (let [n (e/const-name h)]
               (or (reducible-const? env n) (and *instance-name?* (*instance-name?* n))))))))

(defn- whnf-t
  "`whnf` at the current transparency."
  [mctx st x]
  (if (= *transparency* :default)
    (whnf mctx st x)
    (whnf-at mctx st x :instances *instance-name?*)))

(defn- lazy-delta-def-eq
  "Lean's `lazyDeltaReduction` (Meta/ExprDefEq.lean): the two sides are applications of
   DIFFERENT constants, so unfold one head at a time until the heads agree and then compare
   arguments (`isDefEqArgs`). Reducing both sides to whnf instead — which is all the retry above
   can do — is not a substitute: whnf takes `@HAdd.hAdd ℕ ℕ ℕ inst ?m ?n` to a `brecOn` stuck on
   `?n` and the goal's `Nat.add 7 1` to the literal `8`, so a Mathlib lemma stated with `+` never
   matches a goal carrying the concrete kernel op. Lean picks the side to unfold by definition
   height; lacking heights we try each side alone before stepping both, which reaches the same
   meeting point for the class-operator-vs-kernel-op case that motivates this.
   (Closed terms never come here: they go to the kernel, which does its own lazy delta.)"
  [mctx st bound a b]
  (let [env (:env st)
        lctx (:lctx st)
        opts (whnf-opts mctx st)
        step (fn [x] (when (unfoldable-head? env x)
                       (try (red/unfold-head-once env x lctx opts) (catch Exception _ nil))))
        fuel 8]
    (or (when-let [a' (delta-align step a b fuel)] (is-def-eq-core mctx st bound a' b))
        (when-let [b' (delta-align step b a fuel)] (is-def-eq-core mctx st bound a b'))
        ;; Neither head is reachable from the other: step both together.
        (loop [a a b b fuel fuel]
          (when (pos? fuel)
            (let [a' (step a) b' (step b)]
              (when (and a' b')
                (if (same-const-head? a' b')
                  (is-def-eq-core mctx st bound a' b')
                  (recur a' b' (dec fuel))))))))))

;; ── Transparency, projections, and stuck metavariables ─────────────────────────────────────

(defn class-name?
  "Lean's `isClass` on a constant name: the env's class extension (`:classes`, Lean's
   classExtension) or a class key of the env's instance registry."
  [env n]
  (and n
       (or (contains? (env/get-extension env :classes #{}) (name/->string n))
           (contains? (env/get-extension env :instances {}) n))))

(def ^:private projection-info-cache
  "env → {Name → projection info | ::none}. Weak in the env, so a dropped env frees its entries."
  (java.util.WeakHashMap.))

(defn projection-fn-info
  "Lean's `getProjectionFnInfo?` (ProjFns.lean), recovered from the declaration itself: Lean
   generates a structure's projection functions as `fun params (self : S params) => self.i`, and
   nothing else has that value. Returns {:struct S :idx i :num-params n :from-class? bool} or nil."
  [env n]
  (let [cache (locking projection-info-cache
                (or (.get ^java.util.WeakHashMap projection-info-cache env)
                    (let [c (java.util.concurrent.ConcurrentHashMap.)]
                      (.put ^java.util.WeakHashMap projection-info-cache env c)
                      c)))
        hit (.get ^java.util.concurrent.ConcurrentHashMap cache n)]
    (if hit
      (when-not (= hit ::none) hit)
      (let [info (when-let [ci (env/lookup env n)]
                   (when (env/def? ci)
                     (when-let [v (env/get-value ci)]
                       (loop [v v k 0]
                         (if (e/lam? v)
                           (recur (e/lam-body v) (inc k))
                           (when (and (e/proj? v) (pos? k)
                                      (let [s (e/proj-struct v)] (and (e/bvar? s) (zero? (e/bvar-idx s)))))
                             (let [sname (e/proj-type-name v)
                                   sci (env/lookup env sname)]
                               (when (and sci (env/induct? sci) (= (dec k) (.numParams ^ansatz.kernel.ConstantInfo sci)))
                                 {:struct sname :idx (e/proj-idx v) :num-params (dec k)
                                  :from-class? (boolean (class-name? env sname))}))))))))]
        (.put ^java.util.concurrent.ConcurrentHashMap cache n (or info ::none))
        info))))

(defn reducible-const?
  "Lean's `@[reducible]` status, as far as the exported environment records it: `abbrev`
   reducibility hints, except class projection functions (Lean generates projections with abbrev
   hints but marks only non-class ones `@[reducible]`; class projections stay folded — the
   DiscrTree's \"reducible canonical form\"). A `@[reducible] def` with regular hints is not
   recognised: the exported store carries no reducibility attribute."
  [env n]
  (when-let [ci (env/lookup env n)]
    (and (= :abbrev (env/get-reducibility-hints ci))
         (not (:from-class? (projection-fn-info env n))))))

(declare whnf-at)

(defn unfold-const-app
  "Delta-beta: `c us args` with `c`'s value instantiated, then beta-reduced at the head."
  [env x]
  (let [[h args] (e/get-app-fn-args x)]
    (when-let [body (#'red/try-unfold-def env h)]
      (loop [f body args (seq args)]
        (if (and args (e/lam? f))
          (recur (e/instantiate1 (e/lam-body f) (first args)) (next args))
          (reduce e/app f args))))))

(defn- unfold-proj-inst
  "Lean's `unfoldProjInst?` (WHNF.lean): at `.instances` transparency a class projection applied
   to an instance unfolds when the instance projection reduces (`instLENat.1` → `Nat.le`)."
  [mctx st x instance-name?]
  (let [env (:env st)
        [h args] (e/get-app-fn-args x)]
    (when-let [{:keys [num-params idx]} (and (e/const? h) (projection-fn-info env (e/const-name h)))]
      (when (> (count args) num-params)
        (let [struct (whnf-at mctx st (nth args num-params) :instances instance-name?)
              [sh sargs] (e/get-app-fn-args struct)
              sci (when (e/const? sh) (env/lookup env (e/const-name sh)))]
          (when (and sci (env/ctor? sci))
            (let [nparams (.numParams ^ansatz.kernel.ConstantInfo sci)]
              (when (> (count sargs) (+ nparams idx))
                (reduce e/app (nth sargs (+ nparams idx)) (drop (inc num-params) args))))))))))

(defn whnf-at
  "Lean's `whnf` at a restricted transparency: `whnfCore`, then unfold the head constant when the
   mode allows it, until nothing applies. `:none` is `whnfCore` alone; `:reducible` unfolds
   `reducible-const?` constants;
   `:instances` additionally unfolds the instances accepted by `instance-name?` and class
   projections of instances (`unfoldProjInst?`)."
  ([mctx st expr mode] (whnf-at mctx st expr mode nil))
  ([mctx st expr mode instance-name?]
   (let [env (:env st)
         opts {:infer-fn (fn [x] (infer-type mctx st x))
               :is-def-eq-fn (fn [a b] (kernel-defeq-when-closed? mctx st a b))
               ;; whnfCore reduces a projection's structure by whnf at the current transparency
               ;; (`:none` is the DiscrTree's whnfCore, which runs under withReducible)
               :proj-whnf-fn (fn [_ x] (whnf-at mctx st x (if (= mode :none) :reducible mode) instance-name?))}]
     (loop [x (zonk-expr mctx expr) fuel 256]
       (let [x (zonk-expr mctx (red/whnf-no-delta env x (:lctx st) opts))
             h (e/get-app-fn x)]
         (if (and (pos? fuel) (e/const? h))
           (let [n (e/const-name h)
                 x' (cond
                      (= mode :none) nil
                      (or (reducible-const? env n)
                          (and (= mode :instances) instance-name? (instance-name? n)))
                      (unfold-const-app env x)
                      (= mode :instances) (unfold-proj-inst mctx st x instance-name?))]
             (if x' (recur x' (dec fuel)) x))
           x))))))

(defn- explicit-binder-infos
  "Binder infos of the first `n` parameters of `f`'s type (Lean's getFunInfo paramInfo)."
  [mctx st f n]
  (loop [t (try (infer-type mctx st f) (catch clojure.lang.ExceptionInfo _ nil)) i 0 acc []]
    (cond
      (or (nil? t) (>= i n)) acc
      (e/forall? t) (recur (e/forall-body t) (inc i) (conj acc (e/forall-info t)))
      :else (let [t' (try (whnf mctx st t) (catch clojure.lang.ExceptionInfo _ nil))]
              (if (and t' (e/forall? t'))
                (recur t' i acc)
                acc)))))

(defn get-stuck-mvar
  "Lean's `getStuckMVar?` (WHNF.lean): the unassigned metavariable that blocks the reduction of
   `expr` — the head of an mvar application, the major premise of a recursor or quotient
   eliminator, or the instance argument of a CLASS projection function (then its explicit
   arguments), looking through projections after weak-head reduction. Returns an mvar id or nil."
  [mctx st expr]
  (let [env (:env st)]
    (letfn [(whnf* [x] (try (whnf-t mctx st x) (catch clojure.lang.ExceptionInfo _ x)))
            (go [x]
                (let [x (zonk-expr mctx x)]
                  (case (e/tag x)
                    :mdata (go (e/mdata-expr x))
                    :proj (let [s (whnf* (e/proj-struct x))] (when-not (= s x) (go s)))
                    :mvar (e/mvar-id x)
                    :app
                    (let [[f args] (e/get-app-fn-args x)]
                      (cond
                        (e/mvar? f) (e/mvar-id f)
                        (e/const? f)
                        (let [ci (env/lookup env (e/const-name f))]
                          (cond
                            (and ci (env/recursor? ci))
                            (when-not (.isK ^ansatz.kernel.ConstantInfo ci)
                              (let [ci ^ansatz.kernel.ConstantInfo ci
                                    major (+ (.numParams ci) (.numMotives ci) (.numMinors ci) (.numIndices ci))]
                                (when (< major (count args)) (go (whnf* (nth args major))))))

                            (and ci (env/quot? ci))
                            (let [kind (str (e/const-name f))
                                  pos (case kind "Quot.lift" 5 "Quot.ind" 4 nil)]
                              (when (and pos (< pos (count args))) (go (whnf* (nth args pos)))))

                            (not (.hasMVar ^ansatz.kernel.Expr x)) nil

                            :else
                            (when-let [{:keys [num-params from-class?]} (projection-fn-info env (e/const-name f))]
                              (when from-class?
                                (or (when (< num-params (count args)) (go (nth args num-params)))
                                    (some (fn [[bi a]] (when (= :default bi) (go a)))
                                          (map vector (explicit-binder-infos mctx st f (count args)) args)))))))
                        (e/proj? f) (let [s (whnf* (e/proj-struct f))] (go s))
                        :else nil))
                    nil)))]
      (go expr))))

;; ── isDefEqOffset (Meta/Offset.lean) ──────────────────────────────────────────────────────

(defn- const-app?
  "`x` is `name` applied to exactly `n` arguments: those arguments, else nil."
  [x nm n]
  (let [[f args] (e/get-app-fn-args x)]
    (when (and (e/const? f) (= nm (name/->string (e/const-name f))) (= n (count args)))
      (vec args))))

(defn- inst-nat?
  "Lean's NatInstTesters: `inst` is syntactically the Nat instance of a class (`instAddNat`,
   `instHAdd Nat instAddNat`, `instOfNatNat n`, …)."
  [inst base-name h-name]
  (or (and (e/const? inst) (= base-name (name/->string (e/const-name inst))))
      (when h-name
        (when-let [[t i] (const-app? inst h-name 2)]
          (and (e/const? t) (= "Nat" (name/->string (e/const-name t)))
               (e/const? i) (= base-name (name/->string (e/const-name i))))))))

(defn- eval-nat
  "Lean's `evalNat`: the value of a closed Nat arithmetic expression, or nil."
  [mctx x]
  (let [x (zonk-expr mctx x)]
    (letfn [(ev [x]
              (cond
                (e/lit-nat? x) (e/lit-nat-val x)
                (e/mdata? x) (ev (e/mdata-expr x))
                (and (e/const? x) (= "Nat.zero" (name/->string (e/const-name x)))) 0
                (e/app? x)
                (let [bin (fn [op a b] (when-let [va (ev a)] (when-let [vb (ev b)] (op va vb))))
                      [f args] (e/get-app-fn-args x)
                      fname (when (e/const? f) (name/->string (e/const-name f)))
                      n (count args)
                      arith {"add" +' "sub" (fn [a b] (max 0 (-' a b))) "mul" *'
                             "div" (fn [a b] (if (zero? b) 0 (quot a b))) "mod" (fn [a b] (if (zero? b) a (mod a b)))}
                      cls {"add" ["Add" "HAdd" "instAddNat"] "sub" ["Sub" "HSub" "instSubNat"]
                           "mul" ["Mul" "HMul" "instMulNat"] "div" ["Div" "HDiv" "Nat.instDiv"]
                           "mod" ["Mod" "HMod" "Nat.instMod"]}]
                  (cond
                    (nil? fname) nil
                    (and (= fname "OfNat.ofNat") (= n 3))
                    (let [[_ v i] args]
                      (when (when-let [[k] (const-app? i "instOfNatNat" 1)] (= k v)) (ev v)))
                    (and (= fname "Nat.succ") (= n 1)) (some-> (ev (first args)) inc')
                    :else
                    (some (fn [[op f]]
                            (let [[c hc inst] (cls op)]
                              (cond
                                (and (= fname (str "Nat." op)) (= n 2)) (bin f (nth args 0) (nth args 1))
                                (and (= fname (str c "." (str/lower-case c))) (= n 4) (inst-nat? (nth args 1) inst nil))
                                (bin f (nth args 2) (nth args 3))
                                (and (= fname (str hc ".h" c)) (= n 6) (inst-nat? (nth args 3) inst (str "inst" hc)))
                                (bin f (nth args 4) (nth args 5)))))
                          arith)))
                :else nil))]
      (ev x))))

(defn- nat-offset
  "Lean's `isOffset?`: [s k] with `x` ≡ `s + k` (k > 0), or nil."
  [mctx x]
  (let [x (zonk-expr mctx x)
        get-offset (fn [a] (or (nat-offset mctx a) [a 0]))
        add (fn [a b] (when-let [v (eval-nat mctx b)] (let [[s k] (get-offset a)] [s (+' k v)])))]
    (or (when-let [[a] (const-app? x "Nat.succ" 1)] (let [[s k] (get-offset a)] [s (inc' k)]))
        (when-let [[a b] (const-app? x "Nat.add" 2)] (add a b))
        (when-let [[_ i a b] (const-app? x "Add.add" 4)] (when (inst-nat? i "instAddNat" nil) (add a b)))
        (when-let [[_ _ _ i a b] (const-app? x "HAdd.hAdd" 6)] (when (inst-nat? i "instAddNat" "instHAdd") (add a b))))))

(defn- mk-nat-lit [v]
  (e/app* (e/const' (name/from-string "OfNat.ofNat") [lvl/zero]) (e/const' (name/from-string "Nat") [])
          (e/lit-nat v) (e/app (e/const' (name/from-string "instOfNatNat") []) (e/lit-nat v))))

(defn- mk-nat-offset [mctx x k]
  (cond (zero? k) x
        (= 0 (eval-nat mctx x)) (mk-nat-lit k)
        :else (let [nat (e/const' (name/from-string "Nat") [])]
                (e/app* (e/const' (name/from-string "HAdd.hAdd") [lvl/zero lvl/zero lvl/zero]) nat nat nat
                        (e/app* (e/const' (name/from-string "instHAdd") [lvl/zero]) nat
                                (e/const' (name/from-string "instAddNat") []))
                        x (mk-nat-lit k)))))

(declare is-def-eq)

(defn- is-def-eq-offset
  "Lean's `isDefEqOffset`: `s + k₁ =?= t + k₂` and `s + k =?= v` on Nat by offset arithmetic.
   Returns a metacontext, ::false, or nil (not applicable)."
  [mctx st bound s t]
  (let [nat-type? (fn [] (let [ty (try (infer-type mctx st s) (catch clojure.lang.ExceptionInfo _ nil))
                               ty (when ty (try (whnf mctx st ty) (catch clojure.lang.ExceptionInfo _ ty)))]
                           (and ty (e/const? ty) (= "Nat" (name/->string (e/const-name ty))))))
        de (fn [a b] (when (nat-type?) (or (is-def-eq mctx st bound a b) ::false)))
        fail (fn [] (when (nat-type?) ::false))]
    (if-let [[s k1] (nat-offset mctx s)]
      (if-let [[t k2] (nat-offset mctx t)]
        (cond (= k1 k2) (de s t)
              (< k1 k2) (de s (mk-nat-offset mctx t (- k2 k1)))
              :else (de (mk-nat-offset mctx s (- k1 k2)) t))
        (when-let [v2 (eval-nat mctx t)]
          (if (>= v2 k1) (de s (mk-nat-lit (- v2 k1))) (fail))))
      (when-let [v1 (eval-nat mctx s)]
        (if-let [[t k2] (nat-offset mctx t)]
          (if (>= v1 k2) (de (mk-nat-lit (- v1 k2)) t) (fail))
          (when-let [v2 (eval-nat mctx t)]
            (when (nat-type?) (if (= v1 v2) mctx ::false))))))))

;; ── isDefEqStuck ──────────────────────────────────────────────────────────────────────────

(def ^:dynamic *is-def-eq-stuck-ex*
  "Lean's `Meta.Config.isDefEqStuckEx`, set by instance synthesis: unification that would have to
   assign a metavariable it may not assign (one of an outer depth, or synthetic opaque) throws
   `is-def-eq-stuck` instead of failing, so synthesis is postponed rather than refuted."
  false)

(defn is-def-eq-stuck?
  "Is `ex` Lean's isDefEqStuck exception?"
  [ex]
  (and (instance? clojure.lang.ExceptionInfo ex)
       (= ::is-def-eq-stuck (:kind (ex-data ex)))))

(defn- throw-is-def-eq-stuck! [data]
  (throw (ex-info "isDefEq stuck" (assoc data :kind ::is-def-eq-stuck))))

(defn- unassigned-mvar-head
  [mctx x]
  (let [h (e/get-app-fn x)]
    (when (and (e/mvar? h) (not (expr-assigned-or-delayed? mctx (e/mvar-id h))))
      (e/mvar-id h))))

(defn- check-stuck!
  "Lean `isDefEqQuick` (ExprDefEq.lean): `?m … =?= t` where neither side's head is an assignable
   metavariable is stuck under `isDefEqStuckEx` (proof irrelevance aside)."
  [mctx a b]
  (when *is-def-eq-stuck-ex*
    (let [ma (unassigned-mvar-head mctx a)
          mb (unassigned-mvar-head mctx b)
          ;; an mvar this metacontext does not declare belongs to an outer one: read-only
          assignable? (fn [id] (and (expr-decl mctx id) (expr-unification-assignable? mctx id)))]
      (when (and (or ma mb)
                 (not (and ma (assignable? ma)))
                 (not (and mb (assignable? mb))))
        (throw-is-def-eq-stuck! {:lhs a :rhs b})))))

;; ── abstractMVars ─────────────────────────────────────────────────────────────────────────

(defn map-levels
  "Rebuild `x` with `f` applied to every universe level (const levels and sorts)."
  [x f]
  (let [memo (java.util.IdentityHashMap.)]
    (letfn [(go [x]
                (if-not (.hasMVar ^ansatz.kernel.Expr x)
                  x
                  (or (.get memo x)
                      (let [r (case (e/tag x)
                                :sort (e/sort' (f (e/sort-level x)))
                                :const (e/const' (e/const-name x) (mapv f (e/const-levels x)))
                                :app (e/app (go (e/app-fn x)) (go (e/app-arg x)))
                                :lam (e/lam (e/lam-name x) (go (e/lam-type x)) (go (e/lam-body x)) (e/lam-info x))
                                :forall (e/forall' (e/forall-name x) (go (e/forall-type x)) (go (e/forall-body x)) (e/forall-info x))
                                :let (e/let' (e/let-name x) (go (e/let-type x)) (go (e/let-value x)) (go (e/let-body x)))
                                :mdata (e/mdata (e/mdata-data x) (go (e/mdata-expr x)))
                                :proj (e/proj (e/proj-type-name x) (e/proj-idx x) (go (e/proj-struct x)))
                                x)]
                        (.put memo x r)
                        r))))]
      (go x))))

(defn level-mvars->params
  "Replace the level mvars of `l` accepted by `pick?` by level params, recording them in `state`
   (an atom {:lmap {id → param} :params [names]}), named `prefix.i`."
  [l pick? state prefix]
  (letfn [(go [l]
              (if-not (lvl/has-mvar? l)
                l
                (case (lvl/tag l)
                  :succ (lvl/succ (go (lvl/succ-pred l)))
                  :max (lvl/level-max (go (lvl/max-lhs l)) (go (lvl/max-rhs l)))
                  :imax (lvl/imax (go (lvl/imax-lhs l)) (go (lvl/imax-rhs l)))
                  :mvar (let [id (lvl/mvar-id l)]
                          (if-not (pick? id)
                            l
                            (or (get-in @state [:lmap id])
                                (let [pn (name/mk-num (name/from-string prefix) (count (:params @state)))
                                      p (lvl/param pn)]
                                  (swap! state #(-> % (assoc-in [:lmap id] p) (update :params conj pn)))
                                  p))))
                  l)))]
    (go l)))

(defn replace-mvars
  "Rebuild `x` with each unassigned expression mvar `m` for which `(f m)` is non-nil replaced by it."
  [x f]
  (let [memo (java.util.IdentityHashMap.)]
    (letfn [(go [x]
                (if-not (.hasMVar ^ansatz.kernel.Expr x)
                  x
                  (or (.get memo x)
                      (let [r (case (e/tag x)
                                :mvar (or (f x) x)
                                :app (e/app (go (e/app-fn x)) (go (e/app-arg x)))
                                :lam (e/lam (e/lam-name x) (go (e/lam-type x)) (go (e/lam-body x)) (e/lam-info x))
                                :forall (e/forall' (e/forall-name x) (go (e/forall-type x)) (go (e/forall-body x)) (e/forall-info x))
                                :let (e/let' (e/let-name x) (go (e/let-type x)) (go (e/let-value x)) (go (e/let-body x)))
                                :mdata (e/mdata (e/mdata-data x) (go (e/mdata-expr x)))
                                :proj (e/proj (e/proj-type-name x) (e/proj-idx x) (go (e/proj-struct x)))
                                x)]
                        (.put memo x r)
                        r))))]
      (go x))))

(defn abstract-mvars
  "Lean's `abstractMVars` (AbstractMVars.lean): the expression and universe metavariables of the
   CURRENT depth in `expr` become binders and level params. Returns
   {:param-names [Name] :num-mvars k :expr (fun (m₁ : A₁) … (mₖ : Aₖ) => expr')}; metavariables of
   outer depths stay (they are constants for the nested problem)."
  [mctx st expr]
  (let [depth (:depth mctx 0)
        lstate (atom {:lmap {} :params []})
        lpick? (fn [id] (= depth (get-in mctx [:level-depth id])))
        abst-l (fn [x] (map-levels x #(level-mvars->params % lpick? lstate "_abstMVar")))
        emap (atom {})
        fvars (atom [])]
    (letfn [(abst [x]
              (abst-l
               (replace-mvars
                x
                (fn [m]
                  (let [id (e/mvar-id m)
                        decl (expr-decl mctx id)]
                    (when (and decl (= depth (:depth decl)))
                      (or (get @emap id)
                          (let [type (abst (zonk-expr mctx (:type decl)))
                                fid (swap! (:next-id st) inc)
                                fv (e/fvar fid)]
                            (swap! emap assoc id fv)
                            (swap! fvars conj [fid type])
                            fv))))))))]
      (let [body (abst (zonk-expr mctx expr))
            fs @fvars
            ids (mapv first fs)
            lam (reduce (fn [acc i]
                          (let [[_ type] (nth fs i)]
                            (e/lam (str "x_" (inc i)) (e/abstract-many type (subvec ids 0 i)) acc :default)))
                        (e/abstract-many body ids)
                        (reverse (range (count fs))))]
        {:param-names (:params @lstate) :num-mvars (count fs) :expr lam}))))

(defn open-abstract-mvars-result
  "Lean's `openAbstractMVarsResult`: fresh level mvars for the params and fresh expression mvars
   (in the lctx of `st`, at the depth of `mctx`) for the binders. Returns [mctx mvars expr]."
  [mctx st {:keys [param-names num-mvars expr]}]
  (let [lids (vec (repeatedly (count param-names) #(swap! (:next-id st) inc)))
        mctx (reduce add-level-mvar-decl mctx lids)
        x (if (seq param-names)
            (e/instantiate-level-params expr (zipmap param-names (map lvl/mvar lids)))
            expr)]
    (loop [x x mctx mctx mvars [] k 0]
      (if (and (< k num-mvars) (e/lam? x))
        (let [id (swap! (:next-id st) inc)
              mctx (add-expr-mvar-decl mctx id (e/lam-type x) (:lctx st))
              mv (e/mvar id)]
          (recur (e/instantiate1 (e/lam-body x) mv) mctx (conj mvars mv) (inc k)))
        [mctx mvars x]))))

;; ── synthPending ──────────────────────────────────────────────────────────────────────────

(def ^:dynamic *synth-pending-fn*
  "Hook for Lean's `synthPending` (Meta/SynthInstance.lean:synthPendingImp): a fn
   `(fn [mctx st mvar-id] → mctx|nil)` that synthesizes the instance metavariable `mvar-id` (when
   its type is a class) and returns the metacontext with it assigned. Installed by the tactic layer
   (which owns the instance registry); nil here, so the meta layer keeps no dependency on it."
  nil)

;; Lean Meta/Basic.lean `maxSynthPendingDepth` (default 1) and SynthInstance.lean
;; synthPendingImp: synthPending fails once the nesting depth EXCEEDS this bound, and every
;; nested synthesis increments it.
(def max-synth-pending-depth 1)

(def ^:dynamic *synth-pending-depth*
  "The number of synthPending invocations enclosing the current one (Lean's `synthPendingDepth`).
   Instance-synthesis caches key on it: a search under a deeper bound may fail where a shallower
   one succeeds."
  0)

(defn synth-pending
  "Lean's `Meta.synthPending`: ask the installed hook to synthesize `mvar-id`. nil when no hook is
   installed or synthesis fails."
  [mctx st mvar-id]
  (when-let [f *synth-pending-fn*]
    (f mctx st mvar-id)))

(defn- unstuck-mvar
  "Lean's `unstuckMVar` (ExprDefEq.lean): when `x` is stuck on an mvar, synthPending it. Returns
   the new metacontext, or nil. Under `isDefEqStuckEx` an mvar of an outer depth that cannot be
   synthesized makes the problem stuck."
  [mctx st x]
  (when-let [id (get-stuck-mvar mctx st x)]
    (or (synth-pending mctx st id)
        (when (and *is-def-eq-stuck-ex*
                   (when-let [d (expr-decl mctx id)] (< (:depth d 0) (:depth mctx 0))))
          (throw-is-def-eq-stuck! {:mvar-id id})))))

(defn is-def-eq
  "Lean-shaped expression definitional equality with metavariable assignment.

   Return an updated metacontext on success and nil on failure. This is a Meta
   service, not a kernel check: it may assign expression and level
   metavariables in the returned metacontext, but accepted proofs still have to
   be zonked and checked by the kernel."
  ([mctx st a b]
   (is-def-eq mctx st #{} a b))
  ([mctx st bound a b]
   (let [a (zonk-expr mctx a)
         b (zonk-expr mctx b)]
     (if (and (not (zonked-has-mvar? a)) (not (zonked-has-mvar? b)))
       ;; Both sides are metavariable-free: the trusted kernel's reduction-based
       ;; `is-def-eq` is complete and authoritative, so decide it in ONE call and
       ;; do not descend into the meta structural recursion (which would redo a
       ;; full kernel defeq AND a full re-zonk per subterm). This is the common
       ;; case for the speculative match checks that simp/apply/rewrite perform.
       ;; The closedness check is syntactic (no re-zonk) since a/b are zonked.
       (closed-kernel-defeq-zonked mctx st a b)
       (or (when (= a b) mctx)
           (do (check-stuck! mctx a b) nil)
           (is-def-eq-core mctx st bound a b)
           ;; Lean's isDefEqOffset (Nat offset constraints, `?n + 2 =?= 5`); ::false is a
           ;; definite failure
           (let [off (is-def-eq-offset mctx st bound a b)]
             (cond
               (= off ::false) nil
               off off
               :else
               (let [a' (whnf-t mctx st a)
                     b' (whnf-t mctx st b)]
                 (or (when (or (not= a a') (not= b b'))
                       (is-def-eq-core mctx st bound (zonk-expr mctx a') (zonk-expr mctx b')))
                     ;; Different constant heads: step them together (Lean's lazyDeltaReduction).
                     (when (and (e/const? (e/get-app-fn a)) (e/const? (e/get-app-fn b))
                                (not (same-const-head? a b)))
                       (lazy-delta-def-eq mctx st bound a b))
                     ;; isDefEqOnFailure: stuck on a metavariable — synthesize it (Lean's
                     ;; synthPending, through unstuckMVar on either side) and retry.
                     (when-let [mctx' (or (unstuck-mvar mctx st a')
                                          (unstuck-mvar mctx st b'))]
                       (is-def-eq mctx' st bound a b)))))))))))

(declare local-decl-depends-on?)

(defn expr-depends-on?
  "Lean-style may-dependency check.

   Returns true iff `expr` depends on a free variable accepted by `fvar-pred`
   or on an unassigned metavariable accepted by `mvar-pred`. For an unassigned
   metavariable that is not itself accepted, this checks the metavariable's
   local context, matching Lean's conservative dependency rule."
  ([mctx expr fvar-id]
   (expr-depends-on? mctx expr #{fvar-id} #{}))
  ([mctx expr fvar-pred mvar-pred]
   (let [fvar-pred (if (set? fvar-pred) fvar-pred (or fvar-pred (constantly false)))
         mvar-pred (if (set? mvar-pred) mvar-pred (or mvar-pred (constantly false)))
         visited (atom #{})]
     (letfn [(go [expr]
                 (let [expr (zonk-expr mctx expr)]
                   (if (contains? @visited expr)
                     false
                     (do
                       (swap! visited conj expr)
                       (case (e/tag expr)
                         :fvar (boolean (fvar-pred (e/fvar-id expr)))
                         :mvar (let [id (e/mvar-id expr)]
                                 (or (boolean (mvar-pred id))
                                     (when-let [decl (expr-decl mctx id)]
                                       (some (fn [[fid local-decl]]
                                               (or (fvar-pred fid)
                                                   (local-decl-depends-on? mctx local-decl fvar-pred mvar-pred)))
                                             (:lctx decl)))))
                         :sort false
                         :const false
                         :app (or (go (e/app-fn expr))
                                  (go (e/app-arg expr)))
                         :lam (or (go (e/lam-type expr))
                                  (go (e/lam-body expr)))
                         :forall (or (go (e/forall-type expr))
                                     (go (e/forall-body expr)))
                         :let (or (go (e/let-type expr))
                                  (go (e/let-value expr))
                                  (go (e/let-body expr)))
                         :mdata (go (e/mdata-expr expr))
                         :proj (go (e/proj-struct expr))
                         false)))))]
       (boolean (go expr))))))

(defn local-decl-depends-on?
  "Dependency check for a local declaration."
  [mctx local-decl fvar-pred mvar-pred]
  (or (when-let [t (:type local-decl)]
        (expr-depends-on? mctx t fvar-pred mvar-pred))
      (when-let [v (:value local-decl)]
        (expr-depends-on? mctx v fvar-pred mvar-pred))))

(defn has-assigned-mvar?
  "Return true iff `expr` contains an assigned expression/level mvar or a
   delayed-assigned expression mvar."
  [mctx expr]
  ;; Lean Expr.hasMVar short-circuits closed subterms. Use an explicit worklist
  ;; and identity memo here: this predicate runs before guarded Meta traversals,
  ;; and must handle deep terms and shared Expr DAGs without consuming the stack.
  (let [seen (java.util.IdentityHashMap.)]
    (loop [pending [expr]]
      (if-let [expr (peek pending)]
        (let [pending (pop pending)]
          (if (or (not (.hasMVar ^ansatz.kernel.Expr expr)) (.containsKey seen expr))
            (recur pending)
            (do
              (.put seen expr true)
              (case (e/tag expr)
                :mvar (if (or (expr-assigned? mctx (e/mvar-id expr))
                              (expr-delayed-assigned? mctx (e/mvar-id expr)))
                        true (recur pending))
                :sort (if (has-assigned-level-mvar? mctx (e/sort-level expr)) true (recur pending))
                :const (if (some #(has-assigned-level-mvar? mctx %) (e/const-levels expr))
                         true (recur pending))
                :app (recur (conj pending (e/app-arg expr) (e/app-fn expr)))
                :lam (recur (conj pending (e/lam-body expr) (e/lam-type expr)))
                :forall (recur (conj pending (e/forall-body expr) (e/forall-type expr)))
                :let (recur (conj pending (e/let-body expr) (e/let-value expr) (e/let-type expr)))
                :mdata (recur (conj pending (e/mdata-expr expr)))
                :proj (recur (conj pending (e/proj-struct expr)))
                (recur pending)))))
        false))))

(defn has-assignable-mvar?
  "Return true iff `expr` contains an expression/level mvar assignable at the
   current metacontext depth."
  [mctx expr]
  (letfn [(go [expr]
              (case (e/tag expr)
                :mvar (and (expr-decl mctx (e/mvar-id expr))
                           (expr-assignable? mctx (e/mvar-id expr)))
                :sort (has-assignable-level-mvar? mctx (e/sort-level expr))
                :const (boolean (some #(has-assignable-level-mvar? mctx %)
                                      (e/const-levels expr)))
                :app (or (go (e/app-fn expr)) (go (e/app-arg expr)))
                :lam (or (go (e/lam-type expr)) (go (e/lam-body expr)))
                :forall (or (go (e/forall-type expr)) (go (e/forall-body expr)))
                :let (or (go (e/let-type expr))
                         (go (e/let-value expr))
                         (go (e/let-body expr)))
                :mdata (go (e/mdata-expr expr))
                :proj (go (e/proj-struct expr))
                false))]
    (boolean (go expr))))
