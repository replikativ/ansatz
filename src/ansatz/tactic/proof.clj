;; Tactic layer — proof state and metavariable infrastructure.

(ns ansatz.tactic.proof
  "Proof state management for interactive tactic proofs.
   Proof states are persistent Clojure maps; forking is free.

   Trace support: each tactic application is recorded in :trace,
   enabling search strategies to learn from proof histories."
  (:require [ansatz.kernel.expr]
            [ansatz.kernel.reduce :as red]
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
         (assoc-in [:mctx id] {:type type :lctx lctx :assignment nil})
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
         (assoc-in [:mctx id] {:type type :lctx lctx :assignment nil})
         (update :goals (fn [gs]
                          (if (neg? pos)
                            (conj gs id)  ;; fallback: append
                            (into (conj (subvec (vec gs) 0 pos) id)
                                  (subvec (vec gs) pos))))))
     id]))

(defn- assignment-concrete-value
  "Extract the concrete value from an assignment, if available.
   Returns nil when the value cannot be determined (e.g., apply with unsolved args)."
  [ps assignment]
  (case (:kind assignment)
    :exact (:term assignment)
    ;; For apply: value is (app* head solved-arg-values...) when all args are solved
    :apply (let [{:keys [head arg-mvars]} assignment]
             (when (every? #(some? (get-in ps [:mctx % :assignment])) arg-mvars)
               (reduce (fn [t mid]
                         (let [a (get-in ps [:mctx mid :assignment])]
                           (ansatz.kernel.expr/app t
                                                   (or (assignment-concrete-value ps a) (ansatz.kernel.expr/fvar mid)))))
                       head arg-mvars)))
    nil))

(defn assign-mvar
  "Assign a metavariable, removing it from open goals.
   When the assignment has a concrete value, substitute the fvar→value
   mapping into remaining goal types. This propagates solutions from
   earlier subgoals to later ones (e.g., after providing a witness for
   ∃, the proof goal gets the witness substituted)."
  [ps mvar-id assignment]
  (let [ps (-> ps
               (assoc-in [:mctx mvar-id :assignment] assignment)
               (update :goals (fn [gs] (into [] (remove #{mvar-id}) gs))))]
    ;; Propagate: if this mvar was used as an fvar in sibling goal types,
    ;; substitute the solution value
    (if-let [val (assignment-concrete-value ps assignment)]
      (reduce (fn [ps goal-id]
                (if-let [m (get-in ps [:mctx goal-id])]
                  (let [old-type (:type m)]
                    (if (ansatz.kernel.expr/has-fvar-flag old-type)
                      (let [new-type (ansatz.kernel.expr/instantiate1
                                      (ansatz.kernel.expr/abstract1 old-type mvar-id)
                                      val)]
                        (if (identical? new-type old-type)
                          ps
                          (assoc-in ps [:mctx goal-id :type] new-type)))
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
    (let [m (get-in ps [:mctx id])]
      {:id id :type (:type m) :lctx (:lctx m)})))

(defn goals
  "Get all open goals as seq of {:id :type :lctx}."
  [ps]
  (map (fn [id]
         (let [m (get-in ps [:mctx id])]
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
  (some? (get-in ps [:mctx mvar-id :assignment])))
