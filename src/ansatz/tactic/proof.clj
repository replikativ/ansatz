;; Tactic layer — proof state and metavariable infrastructure.

(ns ansatz.tactic.proof
  "Proof state management for interactive tactic proofs.
   Proof states are persistent Clojure maps; forking is free.

   Trace support: each tactic application is recorded in :trace,
   enabling search strategies to learn from proof histories."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.reduce :as red]
            [ansatz.meta :as meta]
            [clojure.string]))

(defn alloc-id
  "Allocate a fresh unique id, returning [ps' new-id]."
  [ps]
  (let [id (:next-id ps)]
    [(update ps :next-id inc) id]))

(defn fresh-mvar
  "Create a fresh metavariable with the given type and local context.
   Returns [ps' mvar-id]."
  [ps type lctx]
  (let [[ps' id] (alloc-id ps)]
    [(-> ps'
         (update :meta-mctx #(meta/add-expr-mvar-decl (or % meta/empty-context) id type lctx))
         (update :goals conj id))
     id]))

(defn fresh-mvar-replacing
  "Create a fresh mvar that replaces an existing goal in the goals list.
   The new mvar takes the position of replaced-id (after assign-mvar removes it).
   Returns [ps' mvar-id]."
  [ps type lctx replaced-id]
  (let [[ps' id] (alloc-id ps)
        ;; Find position of replaced-id before it gets removed
        pos (.indexOf ^java.util.List (vec (:goals ps')) replaced-id)
        pos (if (neg? pos) -1 pos)]
    [(-> ps'
         (update :meta-mctx #(meta/add-expr-mvar-decl (or % meta/empty-context) id type lctx))
         (update :goals (fn [gs]
                          (if (neg? pos)
                            (conj gs id)  ;; fallback: append
                            (into (conj (subvec (vec gs) 0 pos) id)
                                  (subvec (vec gs) pos))))))
     id]))

(defn- legacy-mvar-decl [ps id]
  (get-in ps [:mctx id]))

(defn mvar-decl
  "Get mvar declaration data, preferring the Lean-shaped `:meta-mctx` and
   falling back to the legacy `:mctx` representation."
  [ps id]
  (or (when-let [mctx (:meta-mctx ps)]
        (meta/expr-decl mctx id))
      (legacy-mvar-decl ps id)))

(defn mvar-type [ps id]
  (:type (mvar-decl ps id)))

(defn mvar-lctx [ps id]
  (:lctx (mvar-decl ps id)))

(defn mvar-ids
  "All known metavariable ids, preferring the Lean-shaped metacontext."
  [ps]
  (if-let [mctx (:meta-mctx ps)]
    (keys (:decls mctx))
    (keys (:mctx ps))))

(defn mvar-assignment
  "Return the legacy assignment recipe for `id`, if any.

   During migration this is still the source of extraction recipes; callers
   that only need assigned/open status should use `mvar-assigned?` or
   `mvar-open?` instead."
  [ps id]
  (get-in ps [:mctx id :assignment]))

(defn mvar-exact-term
  "Return the exact term assigned to `id` when the legacy recipe is `:exact`."
  [ps id]
  (let [assignment (mvar-assignment ps id)]
    (when (= :exact (:kind assignment))
      (:term assignment))))

(defn set-mvar-type
  "Update an mvar type, preferring the Lean-shaped metacontext.
   Legacy proof states without `:meta-mctx` still store the type in `:mctx`."
  [ps id type]
  (if (:meta-mctx ps)
    (update ps :meta-mctx meta/set-expr-mvar-type id type)
    (assoc-in ps [:mctx id :type] type)))

(defn- assignment-concrete-value
  "Extract the concrete value from an assignment, if available.
   Returns nil when the value cannot be determined (e.g., apply with unsolved args)."
  [ps assignment]
  (case (:kind assignment)
    :exact (:term assignment)
    ;; For apply: value is (app* head solved-arg-values...) when all args are solved
    :apply (let [{:keys [head arg-mvars]} assignment]
             (when (every? #(some? (mvar-assignment ps %)) arg-mvars)
               (reduce (fn [t mid]
                         (let [a (mvar-assignment ps mid)]
                           (e/app t
                                  (or (assignment-concrete-value ps a) (e/fvar mid)))))
                       head arg-mvars)))
    nil))

(defn- replace-mvar
  "Replace all occurrences of `(mvar mvar-id)` with `replacement`."
  [expr mvar-id replacement]
  (letfn [(go [expr]
            (cond
              (and (e/mvar? expr) (= (e/mvar-id expr) mvar-id)) replacement
              (e/app? expr) (let [f (go (e/app-fn expr))
                                  a (go (e/app-arg expr))]
                              (if (and (identical? f (e/app-fn expr))
                                       (identical? a (e/app-arg expr)))
                                expr
                                (e/app f a)))
              (e/lam? expr) (let [t (go (e/lam-type expr))
                                  b (go (e/lam-body expr))]
                              (if (and (identical? t (e/lam-type expr))
                                       (identical? b (e/lam-body expr)))
                                expr
                                (e/lam (e/lam-name expr) t b (e/lam-info expr))))
              (e/forall? expr) (let [t (go (e/forall-type expr))
                                     b (go (e/forall-body expr))]
                                 (if (and (identical? t (e/forall-type expr))
                                          (identical? b (e/forall-body expr)))
                                   expr
                                   (e/forall' (e/forall-name expr) t b (e/forall-info expr))))
              (e/let? expr) (let [t (go (e/let-type expr))
                                  v (go (e/let-value expr))
                                  b (go (e/let-body expr))]
                              (if (and (identical? t (e/let-type expr))
                                       (identical? v (e/let-value expr))
                                       (identical? b (e/let-body expr)))
                                expr
                                (e/let' (e/let-name expr) t v b)))
              (e/mdata? expr) (let [x (go (e/mdata-expr expr))]
                                (if (identical? x (e/mdata-expr expr))
                                  expr
                                  (e/mdata (e/mdata-data expr) x)))
              (e/proj? expr) (let [s (go (e/proj-struct expr))]
                               (if (identical? s (e/proj-struct expr))
                                 expr
                                 (e/proj (e/proj-type-name expr) (e/proj-idx expr) s)))
              :else expr))]
    (go expr)))

(defn- assignment-expr
  "Translate a legacy tactic assignment recipe into a Lean-style expression
   assignment, using real child mvars as placeholders. Returns nil for recipes
   that are intentionally unsupported."
  [ps assignment]
  (case (:kind assignment)
    :intro (let [{:keys [fvar-id name type info child]} assignment]
             (e/lam name type (meta/abstract-fvars (e/mvar child) [fvar-id]) info))

    :apply (reduce e/app (:head assignment) (map e/mvar (:arg-mvars assignment)))

    :exact (:term assignment)

    :generalize (let [{:keys [child e rfl]} assignment]
                  (e/app* (e/mvar child) e rfl))

    :rfl (let [eq-refl-name (name/from-string "Eq.refl")
               levels (:levels assignment)]
           (e/app* (e/const' eq-refl-name levels)
                   (:eq-type assignment)
                   (:val assignment)))

    :assumption (e/fvar (:fvar-id assignment))

    :rewrite (let [{:keys [eq-term eq-type lhs rhs motive reverse? levels motive-level child]} assignment
                   child-term (e/mvar child)
                   eq-symm-name (name/from-string "Eq.symm")
                   eq-ndrec-name (name/from-string "Eq.ndrec")
                   u-level (first levels)
                   v-level (or motive-level lvl/zero)]
               (if reverse?
                 (e/app* (e/const' eq-ndrec-name [v-level u-level])
                         eq-type lhs motive child-term rhs eq-term)
                 (let [symm-eq (e/app* (e/const' eq-symm-name [u-level])
                                       eq-type lhs rhs eq-term)]
                   (e/app* (e/const' eq-ndrec-name [v-level u-level])
                           eq-type rhs motive child-term lhs symm-eq))))

    :cases (let [{:keys [rec-name motive params indices levels ctor-goals dep-fids]} assignment
                 minor-terms (mapv (fn [{:keys [field-fvars goal-id]}]
                                     (reduce (fn [body fid]
                                               (let [decl (get (mvar-lctx ps goal-id) fid)
                                                     ft (or (:type decl) (e/sort' lvl/zero))]
                                                 (e/lam (or (:name decl) "x") ft
                                                        (meta/abstract-fvars body [fid]) :default)))
                                             (e/mvar goal-id)
                                             (reverse field-fvars)))
                                   ctor-goals)
                 hyp-fvar (e/fvar (:hyp-fvar-id assignment))
                 rec-term (reduce e/app
                                  (e/const' rec-name levels)
                                  (concat params [motive] minor-terms indices [hyp-fvar]))]
             (reduce (fn [t fid] (e/app t (e/fvar fid)))
                     rec-term (or dep-fids [])))

    :have (let [{:keys [fvar-id name type proof-goal body-goal]} assignment]
            (e/app (e/lam name type (meta/abstract-fvars (e/mvar body-goal) [fvar-id]) :default)
                   (e/mvar proof-goal)))

    :simp-reduce (let [{:keys [eq-proof child mpr-level goal-type simplified]} assignment
                       child-term (e/mvar child)]
                   (if eq-proof
                     (e/app* (e/const' (name/from-string "Eq.mpr") [mpr-level])
                             goal-type simplified eq-proof child-term)
                     child-term))

    :revert (let [{:keys [fvar-id child]} assignment]
              (e/app (e/mvar child) (e/fvar fvar-id)))

    :exfalso (let [{:keys [child goal-type motive-level]} assignment
                   false-elim-name (name/from-string "False.elim")]
               (e/app* (e/const' false-elim-name [(or motive-level lvl/zero)])
                       goal-type (e/mvar child)))

    :subst (let [{:keys [full-term child-mvar-id child]} assignment]
             (if full-term
               (replace-mvar full-term child-mvar-id (e/mvar (or child-mvar-id child)))
               (e/mvar child)))

    :by-cases (let [{:keys [cond motive motive-level rfl-proof
                            h-false-id h-true-id false-goal true-goal]} assignment
                    bool-type (e/const' (name/from-string "Bool") [])
                    eq-1 (lvl/succ lvl/zero)
                    eq-type-false (e/app* (e/const' (name/from-string "Eq") [eq-1])
                                          bool-type cond (e/const' (name/from-string "Bool.false") []))
                    eq-type-true (e/app* (e/const' (name/from-string "Eq") [eq-1])
                                         bool-type cond (e/const' (name/from-string "Bool.true") []))
                    false-lam (e/lam "h" eq-type-false
                                     (meta/abstract-fvars (e/mvar false-goal) [h-false-id]) :default)
                    true-lam (e/lam "h" eq-type-true
                                    (meta/abstract-fvars (e/mvar true-goal) [h-true-id]) :default)]
                (e/app* (e/const' (name/from-string "Bool.rec") [motive-level])
                        motive false-lam true-lam cond rfl-proof))

    :by-cases-dec (let [{:keys [cond inst motive motive-level not-c
                                h-false-id h-true-id false-goal true-goal]} assignment
                        false-lam (e/lam "h" not-c
                                         (meta/abstract-fvars (e/mvar false-goal) [h-false-id]) :default)
                        true-lam (e/lam "h" cond
                                        (meta/abstract-fvars (e/mvar true-goal) [h-true-id]) :default)]
                    (e/app* (e/const' (name/from-string "Decidable.casesOn") [motive-level])
                            cond motive inst false-lam true-lam))

    :split-matcher
    (let [{:keys [match-name us params discr discr-type eq-lvl motive alts]} assignment
          alt-lams (mapv (fn [{:keys [ys-ids ys-types h-id h-type goal]}]
                           (let [h-lam (e/lam "h" h-type
                                              (meta/abstract-fvars (e/mvar goal) [h-id]) :default)]
                             (reduce (fn [b [yid yty]]
                                       (e/lam "y" yty (meta/abstract-fvars b [yid]) :default))
                                     h-lam (reverse (map vector ys-ids ys-types)))))
                         alts)
          matcher-app (apply e/app* (e/const' (name/from-string match-name) us)
                             (concat params [motive discr] alt-lams))
          refl (e/app* (e/const' (name/from-string "Eq.refl") [eq-lvl]) discr-type discr)]
      (e/app matcher-app refl))

    :simp-all-hyps
    (let [{:keys [replacements child]} assignment
          eq-mp-nm (name/from-string "Eq.mp")]
      (reduce (fn [body {:keys [old-fvar-id new-fvar-id old-type new-type
                                proof-old-type proof-new-type eq-proof]}]
                (let [actual-old (or proof-old-type old-type)
                      actual-new (or proof-new-type new-type)
                      transport-proof (if eq-proof
                                        (e/app* (e/const' eq-mp-nm [lvl/zero])
                                                actual-old actual-new eq-proof (e/fvar old-fvar-id))
                                        (e/fvar old-fvar-id))]
                  (e/app (e/lam "h" actual-new (meta/abstract-fvars body [new-fvar-id]) :default)
                         transport-proof)))
              (e/mvar child)
              (reverse replacements)))

    :clear (e/mvar (:child assignment))

    :generalize-indices
    (let [{:keys [child orig-indices orig-hyp-fvar-id rfl-proofs]} assignment]
      (reduce e/app (e/mvar child)
              (concat orig-indices
                      [(e/fvar orig-hyp-fvar-id)]
                      rfl-proofs)))

    nil))

(defn- assign-meta-if-possible [ps mvar-id assignment]
  (if-let [expr (assignment-expr ps assignment)]
    (update ps :meta-mctx #(meta/checked-assign-expr (or % meta/empty-context) mvar-id expr
                                                     {:check-type? false}))
    ps))

(defn assign-mvar
  "Assign a metavariable, removing it from open goals.
   When the assignment has a concrete value, substitute the fvar→value
   mapping into remaining goal types. This propagates solutions from
   earlier subgoals to later ones (e.g., after providing a witness for
   ∃, the proof goal gets the witness substituted)."
  [ps mvar-id assignment]
  (let [ps (-> ps
               (assoc-in [:mctx mvar-id :assignment] assignment)
               (update :goals (fn [gs] (into [] (remove #{mvar-id}) gs)))
               (assign-meta-if-possible mvar-id assignment))]
    ;; Propagate: if this mvar was used as an fvar in sibling goal types,
    ;; substitute the solution value
    (if-let [val (assignment-concrete-value ps assignment)]
      (reduce (fn [ps goal-id]
                (if-let [m (mvar-decl ps goal-id)]
                  (let [old-type (:type m)]
                    (if (ansatz.kernel.expr/has-fvar-flag old-type)
                      (let [new-type (ansatz.kernel.expr/instantiate1
                                      (ansatz.kernel.expr/abstract1 old-type mvar-id)
                                      val)]
                        (if (identical? new-type old-type)
                          ps
                          (set-mvar-type ps goal-id new-type)))
                      ps))
                  ps))
              ps (:goals ps))
      ps)))

(defn start-proof
  "Create a proof state with one open goal of the given type.
   Returns [ps mvar-id]."
  [env goal-type]
  (let [ps {:env env
            :goals []
            :mctx {}
            :meta-mctx meta/empty-context
            :next-id 1
            :root-mvar nil
            :trace []
            :weight 1.0}
        [ps' root-id] (fresh-mvar ps goal-type (red/empty-lctx))]
    [(assoc ps' :root-mvar root-id) root-id]))

(defn current-goal
  "Get the first open goal as {:id :type :lctx}, or nil."
  [ps]
  (when-let [id (first (:goals ps))]
    (let [m (mvar-decl ps id)]
      {:id id :type (:type m) :lctx (:lctx m)})))

(defn goals
  "Get all open goals as seq of {:id :type :lctx}."
  [ps]
  (map (fn [id]
         (let [m (mvar-decl ps id)]
           {:id id :type (:type m) :lctx (:lctx m)}))
       (:goals ps)))

(defn solved?
  "True if all goals are solved."
  [ps]
  (empty? (:goals ps)))

(defn format-goal
  "Format a goal for display, Lean 4 style:
   h1 : T1
   h2 : T2
   ⊢ goal-type"
  [goal]
  (let [hyps (keep (fn [[id decl]]
                     (when (= :local (:tag decl))
                       (str "  " (or (:name decl) (str "?fv" id))
                            " : " (ansatz.kernel.expr/->string (:type decl)))))
                   (:lctx goal))
        goal-str (ansatz.kernel.expr/->string (:type goal))]
    (str (when (seq hyps) (str (clojure.string/join "\n" hyps) "\n"))
         "  ⊢ " goal-str)))

(defn format-goals
  "Format all open goals for display."
  [ps]
  (let [gs (goals ps)]
    (if (empty? gs)
      "No goals"
      (str (count gs) " goal(s):\n"
           (clojure.string/join "\n\n"
                                (map-indexed (fn [i g]
                                               (str "Goal " (inc i) ":\n" (format-goal g)))
                                             gs))))))

;; ============================================================
;; Trace and search infrastructure
;; ============================================================

(defn record-tactic
  "Record a tactic application in the trace."
  [ps tactic-name args goal-id]
  (update ps :trace conj
          {:tactic tactic-name
           :args args
           :goal-id goal-id
           :timestamp (System/nanoTime)}))

(defn set-weight
  "Set the weight (log-likelihood) of this proof branch."
  [ps w]
  (assoc ps :weight w))

(defn adjust-weight
  "Multiply the weight by a factor."
  [ps factor]
  (update ps :weight * factor))

(defn mvar-assigned?
  "Check if a metavariable has been assigned."
  [ps mvar-id]
  (or (true? (when-let [mctx (:meta-mctx ps)]
               (meta/expr-assigned-or-delayed? mctx mvar-id)))
      (some? (get-in ps [:mctx mvar-id :assignment]))))

(defn mvar-open?
  "True when `mvar-id` is declared and not assigned or delayed-assigned."
  [ps mvar-id]
  (and (some? (mvar-decl ps mvar-id))
       (not (mvar-assigned? ps mvar-id))))
