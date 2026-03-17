;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; Tactic layer — core tactics.

(ns ansatz.tactic.basic
  "Core tactics: intro, intros, exact, assumption, apply, rfl, constructor,
   cases, induction, rewrite, have-tac, revert, exfalso, subst, clear.
   Tactic combinators: try-tac, or-else, repeat-tac, all-goals.
   Each tactic is a pure function: (tactic ps ...args) → ps'."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.proof :as proof]
            [ansatz.config :as config])
  (:import [ansatz.kernel ConstantInfo]))

(defn- tactic-error! [msg data]
  (throw (ex-info (str "Tactic error: " msg) (merge {:kind :tactic-error} data))))

(defn- mk-tc
  "Create a TC state from the proof state and a goal's local context."
  [ps lctx]
  (let [st (tc/mk-tc-state (:env ps))]
    (assoc st :lctx lctx)))

(defn- whnf-in-goal
  "WHNF reduce an expression in the context of a goal."
  [ps goal-lctx expr]
  (let [st (mk-tc ps goal-lctx)]
    (#'tc/cached-whnf st expr)))

;; ============================================================
;; First-order pattern matching (for apply unification)
;; ============================================================

(defn- match-expr
  "First-order pattern match: try to find a substitution mapping mvar-ids (fvars)
   to subterms of target, such that pattern[subst] = target.
   Returns substitution map {mvar-id → Expr} or nil on failure.
   mvar-ids is a set of fvar ids that are treated as unification variables."
  [pattern target mvar-ids]
  (let [subst (atom {})
        ok (atom true)]
    (letfn [(go [p t]
                (when @ok
                  (cond
                  ;; Pattern is an mvar (fvar in mvar-ids) — bind or check
                    (and (e/fvar? p) (contains? mvar-ids (e/fvar-id p)))
                    (let [id (e/fvar-id p)]
                      (if-let [existing (get @subst id)]
                        (when-not (= existing t)
                          (reset! ok false))
                        (swap! subst assoc id t)))

                  ;; Both are the same tag — recurse
                    (= (e/tag p) (e/tag t))
                    (case (e/tag p)
                      :bvar (when-not (= (e/bvar-idx p) (e/bvar-idx t))
                              (reset! ok false))
                      :sort (when-not (lvl/level= (e/sort-level p) (e/sort-level t))
                              (reset! ok false))
                      :const (do (when-not (= (e/const-name p) (e/const-name t))
                                   (reset! ok false))
                                 (when @ok
                                   (let [pl (e/const-levels p)
                                         tl (e/const-levels t)]
                                     (when-not (and (= (count pl) (count tl))
                                                    (every? true? (map lvl/level= pl tl)))
                                       (reset! ok false)))))
                      :app (do (go (e/app-fn p) (e/app-fn t))
                               (go (e/app-arg p) (e/app-arg t)))
                      :lam (do (go (e/lam-type p) (e/lam-type t))
                               (go (e/lam-body p) (e/lam-body t)))
                      :forall (do (go (e/forall-type p) (e/forall-type t))
                                  (go (e/forall-body p) (e/forall-body t)))
                      :let (do (go (e/let-type p) (e/let-type t))
                               (go (e/let-value p) (e/let-value t))
                               (go (e/let-body p) (e/let-body t)))
                      :fvar (when-not (= (e/fvar-id p) (e/fvar-id t))
                              (reset! ok false))
                      :proj (do (when-not (and (= (e/proj-type-name p) (e/proj-type-name t))
                                               (= (e/proj-idx p) (e/proj-idx t)))
                                  (reset! ok false))
                                (go (e/proj-struct p) (e/proj-struct t)))
                      (:lit-nat :lit-str) (when-not (= p t) (reset! ok false))
                      :mdata (go (e/mdata-expr p) (e/mdata-expr t))
                      (reset! ok false))

                    :else (reset! ok false))))]
      (go pattern target))
    (when @ok @subst)))

;; ============================================================
;; intro
;; ============================================================

(defn intro
  "Introduce a universally quantified variable. Goal must be a forall/Pi type.
   Optional binding-name overrides the binder name."
  ([ps] (intro ps nil))
  ([ps binding-name]
   (let [goal (proof/current-goal ps)
         _ (when-not goal (tactic-error! "No goals" {}))
         goal-type (whnf-in-goal ps (:lctx goal) (:type goal))]
     (when-not (e/forall? goal-type)
       (tactic-error! "Goal is not a forall/Pi type" {:type (:type goal)}))
     (let [binder-name (or binding-name (e/forall-name goal-type))
           binder-type (e/forall-type goal-type)
           binder-info (e/forall-info goal-type)
           [ps' fvar-id] (proof/alloc-id ps)
           new-lctx (red/lctx-add-local (:lctx goal) fvar-id binder-name binder-type)
           new-goal-type (e/instantiate1 (e/forall-body goal-type) (e/fvar fvar-id))
           [ps'' child-id] (proof/fresh-mvar ps' new-goal-type new-lctx)]
       (-> (proof/assign-mvar ps'' (:id goal)
                              {:kind :intro
                               :fvar-id fvar-id
                               :name binder-name
                               :type binder-type
                               :info binder-info
                               :child child-id})
           ;; Move child to front of goals (it replaces the current goal)
           (update :goals (fn [gs]
                            (into [child-id] (remove #{child-id} gs))))
           (proof/record-tactic :intro [binder-name] (:id goal)))))))

;; ============================================================
;; intros
;; ============================================================

(defn intros
  "Introduce forall binders. With names: introduce exactly that many.
   Without names: introduce ALL foralls until goal is no longer forall."
  ([ps] (intros ps nil))
  ([ps names]
   (if (seq names)
     ;; Named intros: introduce exactly (count names) binders
     (reduce (fn [ps n] (intro ps (str n))) ps names)
     ;; No names: introduce all foralls
     (loop [ps ps]
       (let [goal (proof/current-goal ps)]
         (when-not goal (tactic-error! "No goals" {}))
         (let [goal-type (whnf-in-goal ps (:lctx goal) (:type goal))]
           (if (e/forall? goal-type)
             (recur (intro ps nil))
             ps)))))))

;; ============================================================
;; exact
;; ============================================================

(defn exact
  "Close the current goal with the given term."
  [ps term]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        st (mk-tc ps (:lctx goal))
        inferred (tc/infer-type st term)]
    (when-not (tc/is-def-eq st inferred (:type goal))
      (tactic-error! "Type mismatch in exact"
                     {:expected (:type goal) :inferred inferred}))
    (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term term})
        (proof/record-tactic :exact [:term] (:id goal)))))

;; ============================================================
;; assumption
;; ============================================================

(defn assumption
  "Search the local context for a hypothesis matching the goal type.
   Prefers structural equality over def-eq to avoid proof-irrelevance
   false positives (e.g., two different Prop-typed fvars)."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        st (mk-tc ps (:lctx goal))
        lctx (:lctx goal)
        goal-type (:type goal)
        ;; Structural equality only — is-def-eq is too permissive
        ;; due to proof irrelevance (all Props are def-eq to each other).
        ;; Lean 4's assumption also uses isDefEq but their proof irrelevance
        ;; is more controlled (only for proof terms, not propositions).
        ;; Our kernel's is-def-eq treats ALL Props as equal, so we must
        ;; use structural matching to avoid picking wrong hypotheses.
        ;; First: structural equality (safe, avoids proof-irrelevance)
        match (or (some (fn [[id decl]]
                          (when (and (= :local (:tag decl))
                                     (= (:type decl) goal-type))
                            id))
                        lctx)
                  ;; Fallback: Java TC isDefEq (handles instance chain differences).
                  ;; Safe: only matches hypotheses at the same structural nesting level
                  ;; (same number of app args) to avoid proof-irrelevance issues.
                  (let [jtc (ansatz.kernel.TypeChecker. (:env ps))
                        _ (.setFuel jtc config/*default-fuel*)
                        [_ goal-args] (e/get-app-fn-args goal-type)
                        n-goal (count goal-args)]
                    (some (fn [[id decl]]
                            (when (= :local (:tag decl))
                              (let [[_ hyp-args] (e/get-app-fn-args (:type decl))]
                                ;; Same arg count → likely same structure
                                (when (and (= (count hyp-args) n-goal)
                                           (try (.isDefEq jtc (:type decl) goal-type)
                                                (catch Exception _ false)))
                                  id))))
                          lctx)))]
    (when-not match
      (tactic-error! "No matching hypothesis found" {:goal-type (:type goal)}))
    (-> (proof/assign-mvar ps (:id goal) {:kind :assumption :fvar-id match})
        (proof/record-tactic :assumption [] (:id goal)))))

;; ============================================================
;; apply (following Lean 4's MVarId.apply algorithm)
;; ============================================================
;; Key differences from Lean 4:
;; - We use fvars as "metavariables" + pattern matching instead of real mvars
;; - Pattern matching replaces isDefEq for unification
;; - Instance synthesis delegated to post-processing

(defn apply-tac
  "Apply a term to the current goal, generating subgoals for its arguments.
   Following Lean 4's Meta/Tactic/Apply.lean:
   1. Peel forall binders, creating fvars as metavariable placeholders
   2. Match result type against goal via first-order pattern matching
   3. Assign matched fvars, create subgoals for unmatched ones
   4. Substitute solved values into remaining subgoal types"
  [ps term]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        st (mk-tc ps (:lctx goal))
        term-type (tc/infer-type st term)]
    ;; Peel forall binders, creating fresh fvars for each argument.
    ;; For inst-implicit params, try to synthesize immediately — this resolves
    ;; projections like LE.0(Preorder.toLE) before they reach matching.
    (loop [ps ps
           ty (whnf-in-goal ps (:lctx goal) term-type)
           arg-mvars []
           mvar-id-set #{}]
      (if (e/forall? ty)
        (let [param-type (e/forall-type ty)
              binfo (e/forall-info ty)
              ;; Substitute already-resolved fvars into the param type
              inst-type (reduce (fn [t fid]
                                  (let [m (get-in ps [:mctx fid])]
                                    (if (and m (:assignment m) (= :exact (:kind (:assignment m))))
                                      (e/instantiate1 (e/abstract1 t fid)
                                                      (:term (:assignment m)))
                                      t)))
                                param-type arg-mvars)
              ;; Goal-directed inference following Lean 4:
              ;; 1. Implicit type params (Sort): infer from goal's type args
              ;; 2. Inst-implicit: synthesize instance
              ;; 3. Implicit value params: try to infer from goal structure
              inferred-val
              (cond
                ;; Implicit type param: infer from goal's corresponding arg
                (and (#{:implicit :strict-implicit} binfo)
                     (let [stw (try (#'tc/cached-whnf st inst-type) (catch Exception _ nil))]
                       (and stw (e/sort? stw))))
                (let [[gh ga] (e/get-app-fn-args (:type goal))]
                  (when (seq ga) (first ga)))

                ;; Inst-implicit: synthesize
                (= binfo :inst-implicit)
                (try
                  (let [synth-fn (requiring-resolve 'ansatz.core/try-synthesize-instance)]
                    (synth-fn (:env ps) inst-type))
                  (catch Exception _ nil))

                ;; Implicit value param: try to extract from goal args
                (#{:implicit :strict-implicit} binfo)
                nil)  ;; leave as mvar
              synthesized inferred-val]
          (if synthesized
            ;; Value inferred/synthesized — create a pre-assigned mvar
            (let [[ps' mvar-id] (proof/fresh-mvar ps inst-type (:lctx goal))
                  ps' (proof/assign-mvar ps' mvar-id {:kind :exact :term synthesized})
                  new-ty (e/instantiate1 (e/forall-body ty) synthesized)]
              (recur ps' (whnf-in-goal ps' (:lctx goal) new-ty)
                     (conj arg-mvars mvar-id) mvar-id-set))
            ;; Not synthesized — create mvar (for implicit, inst-implicit, AND explicit params)
            ;; Following Lean 4: peel ALL foralls, explicit mvars become subgoals
            (let [[ps' mvar-id] (proof/fresh-mvar ps inst-type (:lctx goal))
                  new-ty (e/instantiate1 (e/forall-body ty) (e/fvar mvar-id))]
              (recur ps' (whnf-in-goal ps' (:lctx goal) new-ty)
                     (conj arg-mvars mvar-id)
                     (conj mvar-id-set mvar-id)))))
        ;; Phase 2: Match result type against goal.
        ;; Following Lean 4's apply (Apply.lean): use isDefEq as the PRIMARY
        ;; matching mechanism. isDefEq handles WHNF reduction, delta unfolding,
        ;; and def-eq matching in one pass. No structural matching needed.
        ;;
        ;; Strategy A: structural matching (fast path for simple cases)
        ;; Strategy B: Java TC isDefEq (handles def-eq like sorted vs List.rec)
        (let [goal-whnf (whnf-in-goal ps (:lctx goal) (:type goal))
              ty-whnf (whnf-in-goal ps (:lctx goal) ty)
              ;; Substitute ALL resolved mvars into the result type
              resolved-ty (reduce (fn [t mid]
                                    (let [m (get-in ps [:mctx mid])]
                                      (if (and m (:assignment m)
                                               (= :exact (:kind (:assignment m))))
                                        (e/instantiate1 (e/abstract1 t mid)
                                                        (:term (:assignment m)))
                                        t)))
                                  ty arg-mvars)
              resolved-whnf (whnf-in-goal ps (:lctx goal) resolved-ty)
              ;; Strategy A: structural matching
              subst (or (match-expr ty (:type goal) mvar-id-set)
                        (match-expr ty goal-whnf mvar-id-set)
                        (match-expr ty-whnf (:type goal) mvar-id-set)
                        (match-expr ty-whnf goal-whnf mvar-id-set)
                        ;; Strategy B: Java TC isDefEq (Lean 4's primary mechanism).
                        ;; isDefEq on resolved-ty (with assigned mvars substituted)
                        ;; handles cases where heads differ structurally but are def-eq
                        ;; (e.g., sorted(insertSorted ...) vs List.rec ...).
                        (try
                          (let [jtc (ansatz.kernel.TypeChecker. (:env ps))
                                _ (.setFuel jtc config/*default-fuel*)
                                ;; Register goal's lctx with TC
                                _ (doseq [[id decl] (:lctx goal)]
                                    (when (= :local (:tag decl))
                                      (.addLocal jtc (long id) (str (:name decl)) (:type decl))))
                                ;; Register unresolved mvars as locals so TC can handle them
                                _ (doseq [mid arg-mvars]
                                    (let [m (get-in ps [:mctx mid])]
                                      (when (and m (not (:assignment m)))
                                        (.addLocal jtc (long mid) "?mvar" (:type m)))))]
                            ;; Try isDefEq on resolved type (with substituted mvars)
                            ;; For non-dependent arrows, resolved-ty has NO unresolved
                            ;; fvars in the conclusion — isDefEq can verify directly.
                            ;; Lean 4: isDefEq is the primary matching mechanism.
                            (when (.isDefEq jtc resolved-ty (:type goal))
                              ;; Deep extraction: walk to collect any fvar bindings
                              (let [deep-subst (atom {})]
                                (letfn [(extract [r g]
                                          (cond
                                            (and (e/fvar? r) (contains? mvar-id-set (e/fvar-id r)))
                                            (swap! deep-subst assoc (e/fvar-id r) g)
                                            (and (e/app? r) (e/app? g))
                                            (do (extract (e/app-fn r) (e/app-fn g))
                                                (extract (e/app-arg r) (e/app-arg g)))
                                            :else nil))]
                                  (extract resolved-ty (:type goal)))
                                @deep-subst)))
                          (catch Exception _ nil))
                        ;; Direct equality
                        (when (or (= ty (:type goal)) (= ty goal-whnf)) {}))]
          (when-not subst
            (tactic-error! (str "apply: result type does not match goal\n"
                                "  result: " (e/->string ty) "\n"
                                "  goal:   " (e/->string (:type goal)))
                           {:expected (:type goal) :actual ty :term term}))

          ;; Assign solved mvars from the substitution
          (let [ps (reduce (fn [ps mvar-id]
                             (if-let [val (get subst mvar-id)]
                               (proof/assign-mvar ps mvar-id
                                                  {:kind :exact :term val})
                               ps))
                           ps arg-mvars)
                ;; Substitute solved values into remaining unsolved goal types
                ps (if (seq subst)
                     (reduce (fn [ps mvar-id]
                               (if (proof/mvar-assigned? ps mvar-id)
                                 ps
                                 (let [old-type (get-in ps [:mctx mvar-id :type])
                                       new-type (reduce (fn [ty [fid val]]
                                                          (e/instantiate1
                                                           (e/abstract1 ty fid) val))
                                                        old-type subst)]
                                   (assoc-in ps [:mctx mvar-id :type] new-type))))
                             ps arg-mvars)
                     ps)]
            (let [ps (-> (proof/assign-mvar ps (:id goal)
                                            {:kind :apply :head term :arg-mvars arg-mvars})
                         (proof/record-tactic :apply [term] (:id goal)))
                  ;; Post-processing: auto-close typeclass instance subgoals.
                  ;; Lean 4's apply does this via synthAppInstances (Apply.lean).
                  ;; If a subgoal's type is a class application (not a relation/prop),
                  ;; try to synthesize the instance automatically.
                  ps (reduce
                      (fn [ps mid]
                        (if (proof/mvar-assigned? ps mid)
                          ps
                          (let [mtype (get-in ps [:mctx mid :type])
                                [mhead _] (when mtype (e/get-app-fn-args mtype))]
                            (if (and mtype (e/const? mhead)
                                      ;; Heuristic: class-like types (capitalized,
                                      ;; not relation/logic constructors)
                                     (let [s (name/->string (e/const-name mhead))]
                                       (and (pos? (count s))
                                            (Character/isUpperCase ^char (first s))
                                            (not (#{"Eq" "LE" "LT" "GE" "GT"
                                                    "Not" "And" "Or" "Iff"
                                                    "HAdd" "HMul" "HSub" "HDiv"
                                                    "HPow" "Exists" "Sigma"} s)))))
                              (if-let [inst (or
                                               ;; Fast path: Clojure synthesis
                                             (try (let [f (requiring-resolve
                                                           'ansatz.core/try-synthesize-instance)]
                                                    (f (:env ps) mtype))
                                                  (catch Exception _ nil))
                                               ;; Deep path: tabled synthesis
                                             (try (let [f (requiring-resolve
                                                           'ansatz.tactic.instance/tabled-synthesize)
                                                        st' (tc/mk-tc-state (:env ps))
                                                        idx ((requiring-resolve 'ansatz.core/instance-index))]
                                                    (f st' (:env ps) idx mtype))
                                                  (catch Exception _ nil)))]
                                (proof/assign-mvar ps mid {:kind :exact :term inst})
                                ps)
                              ps))))
                      ps arg-mvars)
                  ;; Move unsolved arg-mvars to front of goals (Lean 4: new goals first)
                  unsolved-args (filterv #(not (proof/mvar-assigned? ps %)) arg-mvars)]
              (update ps :goals (fn [gs]
                                  (into (vec unsolved-args)
                                        (remove (set unsolved-args) gs)))))))))))

;; ============================================================
;; rfl
;; ============================================================

(defn rfl
  "Close the current goal if it is @Eq T a a (reflexivity)."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        goal-type (whnf-in-goal ps (:lctx goal) (:type goal))
        [head args] (e/get-app-fn-args goal-type)
        eq-name (name/from-string "Eq")]
    (when-not (and (e/const? head)
                   (= (e/const-name head) eq-name)
                   (= 3 (count args)))
      (tactic-error! "rfl: goal is not an Eq application" {:type (:type goal)}))
    (let [eq-type (nth args 0)
          lhs (nth args 1)
          rhs (nth args 2)
          st (mk-tc ps (:lctx goal))]
      (when-not (tc/is-def-eq st lhs rhs)
        (tactic-error! "rfl: sides are not definitionally equal"
                       {:lhs lhs :rhs rhs}))
      (-> (proof/assign-mvar ps (:id goal)
                             {:kind :rfl :eq-type eq-type :val lhs
                              :levels (e/const-levels head)})
          (proof/record-tactic :rfl [] (:id goal))))))

;; ============================================================
;; constructor
;; ============================================================

(defn constructor
  "Apply the constructor of the inductive type at the head of the goal."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        goal-type (whnf-in-goal ps (:lctx goal) (:type goal))
        [head args] (e/get-app-fn-args goal-type)]
    (when-not (e/const? head)
      (tactic-error! "constructor: goal head is not a constant" {:type goal-type}))
    (let [^ConstantInfo ci (env/lookup! (:env ps) (e/const-name head))]
      (when-not (.isInduct ci)
        (tactic-error! "constructor: goal type is not an inductive" {:type goal-type}))
      (let [ctors (.ctors ci)]
        (when (zero? (alength ctors))
          (tactic-error! "constructor: no constructors" {:type goal-type}))
        (let [ctor-name (aget ctors 0)
              ctor-levels (e/const-levels head)
              ctor-term (e/const' ctor-name ctor-levels)]
          (apply-tac ps ctor-term))))))

;; ============================================================
;; rewrite
;; ============================================================

(defn rewrite
  "Rewrite the goal using an equality hypothesis.
   eq-term should have type @Eq T lhs rhs.
   Replaces occurrences of lhs with rhs in the goal type (left-to-right).
   If reverse? is true, rewrites right-to-left (rhs → lhs)."
  ([ps eq-term] (rewrite ps eq-term false))
  ([ps eq-term reverse?]
   (let [goal (proof/current-goal ps)
         _ (when-not goal (tactic-error! "No goals" {}))
         st (mk-tc ps (:lctx goal))
         eq-type (tc/infer-type st eq-term)
         eq-type-whnf (whnf-in-goal ps (:lctx goal) eq-type)
         [head args] (e/get-app-fn-args eq-type-whnf)
         eq-name (name/from-string "Eq")]
     (when-not (and (e/const? head)
                    (= (e/const-name head) eq-name)
                    (= 3 (count args)))
       (tactic-error! "rewrite: term is not an Eq proof"
                      {:type eq-type}))
     (let [ty (nth args 0)
           lhs (if reverse? (nth args 2) (nth args 1))
           rhs (if reverse? (nth args 1) (nth args 2))
           eq-levels (e/const-levels head)
           ;; Build the motive: λ x, goal-type[lhs := x]
           ;; We need to abstract lhs from the goal type
           [ps' motive-fvar-id] (proof/alloc-id ps)
           motive-fvar (e/fvar motive-fvar-id)
           ;; Replace occurrences of lhs in goal type with a bvar
           ;; We do this by: replace lhs with motive-fvar, then abstract1
           goal-type-replaced (let [replace-in
                                    (fn replace-in [expr]
                                      (if (tc/is-def-eq st expr lhs)
                                        motive-fvar
                                        (case (e/tag expr)
                                          :app (let [f (replace-in (e/app-fn expr))
                                                     a (replace-in (e/app-arg expr))]
                                                 (if (and (identical? f (e/app-fn expr))
                                                          (identical? a (e/app-arg expr)))
                                                   expr
                                                   (e/app f a)))
                                          :lam expr ;; don't go under binders for now
                                          :forall expr
                                          :let expr
                                          expr)))]
                                (replace-in (:type goal)))
           motive-body (e/abstract1 goal-type-replaced motive-fvar-id)
           motive (e/lam "x" ty motive-body :default)
           ;; Compute the motive output sort level
           goal-sort (tc/infer-type st (:type goal))
           goal-sort-whnf (whnf-in-goal ps (:lctx goal) goal-sort)
           motive-level (if (e/sort? goal-sort-whnf)
                          (e/sort-level goal-sort-whnf)
                          lvl/zero)
           ;; New goal type: goal-type[lhs := rhs]
           new-goal-type (e/instantiate1 motive-body rhs)
           ;; Create subgoal for the rewritten goal
           [ps'' new-goal-id] (proof/fresh-mvar ps' new-goal-type (:lctx goal))]
       (-> (proof/assign-mvar ps'' (:id goal)
                              {:kind :rewrite
                               :eq-term eq-term
                               :eq-type ty
                               :lhs lhs
                               :rhs rhs
                               :motive motive
                               :reverse? reverse?
                               :levels eq-levels
                               :motive-level motive-level
                               :child new-goal-id})
           (proof/record-tactic :rewrite [eq-term reverse?] (:id goal)))))))

;; ============================================================
;; cases (case analysis on an inductive hypothesis)
;; ============================================================

(defn cases
  "Perform case analysis on a hypothesis (fvar) of inductive type.
   Creates one subgoal per constructor."
  [ps hyp-fvar-id]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        st (mk-tc ps (:lctx goal))
        hyp-decl (red/lctx-lookup (:lctx goal) hyp-fvar-id)
        _ (when-not hyp-decl
            (tactic-error! "cases: hypothesis not in context" {:id hyp-fvar-id}))
        hyp-type (whnf-in-goal ps (:lctx goal) (:type hyp-decl))
        [type-head type-args] (e/get-app-fn-args hyp-type)
        _ (when-not (e/const? type-head)
            (tactic-error! "cases: hypothesis type head is not a constant"
                           {:type hyp-type}))
        ind-name (e/const-name type-head)
        ^ConstantInfo ind-ci (env/lookup! (:env ps) ind-name)
        _ (when-not (.isInduct ind-ci)
            (tactic-error! "cases: hypothesis type is not an inductive"
                           {:type hyp-type}))
        ind-levels (e/const-levels type-head)
        num-params (.numParams ind-ci)
        params (subvec (vec type-args) 0 (min num-params (count type-args)))
        indices (subvec (vec type-args) (min num-params (count type-args)))
        ;; Compute the motive output sort level
        goal-sort (tc/infer-type st (:type goal))
        goal-sort-whnf (whnf-in-goal ps (:lctx goal) goal-sort)
        motive-level (if (e/sort? goal-sort-whnf)
                       (e/sort-level goal-sort-whnf)
                       lvl/zero)
        ;; Look up the recursor — prefer casesOn if it's a recursor, else fall back to rec
        cases-on-name (name/mk-str ind-name "casesOn")
        cases-on-ci (env/lookup (:env ps) cases-on-name)
        [rec-name ^ConstantInfo rec-ci]
        (if (and cases-on-ci (.isRecursor ^ConstantInfo cases-on-ci))
          [cases-on-name cases-on-ci]
          (let [rn (name/mk-str ind-name "rec")
                rc (env/lookup! (:env ps) rn)]
            [rn rc]))
        _ (when-not (.isRecursor rec-ci)
            (tactic-error! "cases: recursor not found" {:name rec-name}))
        ;; Build the motive: λ indices x, goal-type
        ;; For casesOn, the motive takes indices + major premise
        ;; We abstract the hypothesis from the goal type
        motive-body (e/abstract1 (:type goal) hyp-fvar-id)
        ;; Abstract indices too if present (from back to front)
        motive-body (reduce (fn [body idx-expr]
                              (if (e/fvar? idx-expr)
                                (e/abstract1 body (e/fvar-id idx-expr))
                                body))
                            motive-body
                            (reverse indices))
        ;; Wrap in lambdas for indices + major premise
        ;; The major premise has type = the inductive applied to params + indices
        major-type hyp-type
        ;; Build motive types: index types (if any) + major type
        ;; For simplicity in the no-index case, just wrap with the major premise type
        idx-types (mapv (fn [idx-expr]
                          (if (e/fvar? idx-expr)
                            (let [d (red/lctx-lookup (:lctx goal) (e/fvar-id idx-expr))]
                              (or (:type d) (e/sort' lvl/zero)))
                            (e/sort' lvl/zero)))
                        indices)
        motive-binder-types (conj idx-types major-type)
        motive (reduce (fn [body ty] (e/lam "x" ty body :default))
                       motive-body
                       (reverse motive-binder-types))
        ;; Create subgoals for each constructor
        ctors (.ctors ind-ci)]
    (loop [ps ps
           i 0
           ctor-goals []]
      (if (< i (alength ctors))
        (let [ctor-name (aget ctors i)
              ^ConstantInfo ctor-ci (env/lookup! (:env ps) ctor-name)
              ctor-type (.type ctor-ci)
              ;; Instantiate level params
              subst (into {} (map vector (vec (.levelParams ctor-ci)) ind-levels))
              ctor-type (e/instantiate-level-params ctor-type subst)
              ;; Skip params (already known)
              ctor-type (loop [t ctor-type n num-params ps-args params]
                          (if (and (pos? n) (e/forall? t))
                            (recur (e/instantiate1 (e/forall-body t) (first ps-args))
                                   (dec n) (rest ps-args))
                            t))
              ;; Peel fields, creating fvars for each
              [ps' field-fvars new-lctx ctor-type]
              (loop [ps ps field-fvars [] lctx (:lctx goal) t ctor-type]
                (if (e/forall? t)
                  (let [[ps' fid] (proof/alloc-id ps)
                        fv (e/fvar fid)
                        ft (e/forall-type t)
                        fname-raw (e/forall-name t)
                        fname (if fname-raw
                                (name/->string fname-raw)
                                (str "h" fid))
                        lctx' (red/lctx-add-local lctx fid fname ft)]
                    (recur ps' (conj field-fvars fid)
                           lctx' (e/instantiate1 (e/forall-body t) fv)))
                  [ps field-fvars lctx t]))
              ;; Build ctor applied to params and field fvars
              ctor-term (reduce e/app
                                (e/const' ctor-name ind-levels)
                                (concat params (map e/fvar field-fvars)))
              branch-goal-type (e/instantiate1 motive-body ctor-term)
              ;; Also instantiate any remaining index abstractions
              [ps' branch-id] (proof/fresh-mvar ps' branch-goal-type new-lctx)]
          (recur ps' (inc i)
                 (conj ctor-goals {:ctor-name ctor-name
                                   :field-fvars field-fvars
                                   :goal-id branch-id})))
        ;; Assign the original goal
        ;; Recursor levels: motive level + inductive levels
        (let [;; Build recursor levels: only include motive level if rec has level params
              rec-lparams (vec (.levelParams rec-ci))
              rec-levels (if (seq rec-lparams)
                           (into [motive-level] ind-levels)
                           [])]
          (let [branch-ids (mapv :goal-id ctor-goals)
                ps' (-> (proof/assign-mvar ps (:id goal)
                                           {:kind :cases
                                            :hyp-fvar-id hyp-fvar-id
                                            :ind-name ind-name
                                            :rec-name rec-name
                                            :motive motive
                                            :params params
                                            :indices indices
                                            :levels rec-levels
                                            :ctor-goals ctor-goals})
                        (proof/record-tactic :cases [hyp-fvar-id] (:id goal)))]
            ;; Move branch goals to front to maintain focus
            (update ps' :goals (fn [gs]
              (let [branch-set (set branch-ids)
                    others (filterv #(not (branch-set %)) gs)]
                (into (vec branch-ids) others))))))))))

;; ============================================================
;; induction (structural induction on a hypothesis)
;; ============================================================
;; Lean 4: induction produces subgoals with induction hypotheses.
;; Like cases but each recursive field gets an IH hypothesis.

(defn induction
  "Perform structural induction on a hypothesis of inductive type.
   Like cases but adds induction hypotheses for recursive fields.
   Following Lean 4's Induction tactic.

   Creates one subgoal per constructor. For each constructor field
   that has the same type as the inductive being eliminated,
   adds an induction hypothesis to the local context."
  [ps hyp-fvar-id]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        st (mk-tc ps (:lctx goal))
        hyp-decl (red/lctx-lookup (:lctx goal) hyp-fvar-id)
        _ (when-not hyp-decl
            (tactic-error! "induction: hypothesis not in context" {:id hyp-fvar-id}))
        hyp-type (whnf-in-goal ps (:lctx goal) (:type hyp-decl))
        [type-head type-args] (e/get-app-fn-args hyp-type)
        _ (when-not (e/const? type-head)
            (tactic-error! "induction: hypothesis type head is not a constant"
                           {:type hyp-type}))
        ind-name (e/const-name type-head)
        ^ConstantInfo ind-ci (env/lookup! (:env ps) ind-name)
        _ (when-not (.isInduct ind-ci)
            (tactic-error! "induction: hypothesis type is not an inductive"
                           {:type hyp-type}))
        ind-levels (e/const-levels type-head)
        num-params (.numParams ind-ci)
        params (subvec (vec type-args) 0 (min num-params (count type-args)))
        indices (subvec (vec type-args) (min num-params (count type-args)))
        ;; Compute the motive output sort level
        goal-sort (tc/infer-type st (:type goal))
        goal-sort-whnf (whnf-in-goal ps (:lctx goal) goal-sort)
        motive-level (if (e/sort? goal-sort-whnf)
                       (e/sort-level goal-sort-whnf)
                       lvl/zero)
        ;; Use .rec (not .casesOn) — rec provides proper IH
        rec-name (name/mk-str ind-name "rec")
        ^ConstantInfo rec-ci (env/lookup! (:env ps) rec-name)
        _ (when-not (.isRecursor rec-ci)
            (tactic-error! "induction: recursor not found" {:name rec-name}))
        ;; Build the motive: λ indices x, goal-type
        motive-body (e/abstract1 (:type goal) hyp-fvar-id)
        motive-body (reduce (fn [body idx-expr]
                              (if (e/fvar? idx-expr)
                                (e/abstract1 body (e/fvar-id idx-expr))
                                body))
                            motive-body
                            (reverse indices))
        major-type hyp-type
        idx-types (mapv (fn [idx-expr]
                          (if (e/fvar? idx-expr)
                            (let [d (red/lctx-lookup (:lctx goal) (e/fvar-id idx-expr))]
                              (or (:type d) (e/sort' lvl/zero)))
                            (e/sort' lvl/zero)))
                        indices)
        motive-binder-types (conj idx-types major-type)
        motive (reduce (fn [body ty] (e/lam "x" ty body :default))
                       motive-body
                       (reverse motive-binder-types))
        ctors (.ctors ind-ci)]
    (loop [ps ps i 0 ctor-goals []]
      (if (< i (alength ctors))
        (let [ctor-name (aget ctors i)
              ^ConstantInfo ctor-ci (env/lookup! (:env ps) ctor-name)
              ctor-type (.type ctor-ci)
              ;; Instantiate level params
              subst (into {} (map vector (vec (.levelParams ctor-ci)) ind-levels))
              ctor-type (e/instantiate-level-params ctor-type subst)
              ;; Skip params
              ctor-type (loop [t ctor-type n num-params ps-args params]
                          (if (and (pos? n) (e/forall? t))
                            (recur (e/instantiate1 (e/forall-body t) (first ps-args))
                                   (dec n) (rest ps-args))
                            t))
              ;; Peel fields AND add IH for recursive fields
              ;; Track ctor-fvars (for building constructor term) separately
              ;; from all-fvars (for extraction lambda abstraction)
              [ps' ctor-fvars all-fvars new-lctx _]
              (loop [ps ps ctor-fvars [] all-fvars [] lctx (:lctx goal) t ctor-type]
                (if (e/forall? t)
                  (let [[ps' fid] (proof/alloc-id ps)
                        fv (e/fvar fid)
                        ft (e/forall-type t)
                        fname-raw (e/forall-name t)
                        fname (if fname-raw
                                (name/->string fname-raw)
                                (str "h" fid))
                        lctx' (red/lctx-add-local lctx fid fname ft)
                        ft-whnf (whnf-in-goal ps lctx ft)
                        [ft-head _] (e/get-app-fn-args ft-whnf)
                        is-recursive (and (e/const? ft-head)
                                          (= (e/const-name ft-head) ind-name))
                        [ps'' lctx'' ih-fvars]
                        (if is-recursive
                          (let [[ps'' ih-id] (proof/alloc-id ps')
                                ih-type (e/instantiate1 motive-body fv)
                                ih-name (str "ih_" fname)
                                lctx'' (red/lctx-add-local lctx' ih-id ih-name ih-type)]
                            [ps'' lctx'' [ih-id]])
                          [ps' lctx' []])]
                    (recur ps''
                           (conj ctor-fvars fid)  ;; ctor-fvars: only real fields
                           (into (conj all-fvars fid) ih-fvars)  ;; all-fvars: fields + IHs
                           lctx'' (e/instantiate1 (e/forall-body t) fv)))
                  [ps ctor-fvars all-fvars lctx t]))
              ;; Build ctor applied to params and ONLY field fvars (not IH)
              ctor-term (reduce e/app
                                (e/const' ctor-name ind-levels)
                                (concat params (map e/fvar ctor-fvars)))
              branch-goal-type (e/instantiate1 motive-body ctor-term)
              [ps' branch-id] (proof/fresh-mvar ps' branch-goal-type new-lctx)]
          (recur ps' (inc i)
                 (conj ctor-goals {:ctor-name ctor-name
                                   :field-fvars all-fvars  ;; includes IH fvars for extraction
                                   :goal-id branch-id})))
        ;; Assign the original goal
        (let [;; Build recursor levels: only include motive level if rec has level params
              rec-lparams (vec (.levelParams rec-ci))
              rec-levels (if (seq rec-lparams)
                           (into [motive-level] ind-levels)
                           [])]
          (let [branch-ids (mapv :goal-id ctor-goals)
                ps' (-> (proof/assign-mvar ps (:id goal)
                                           {:kind :cases  ;; reuse cases extraction
                                            :hyp-fvar-id hyp-fvar-id
                                            :ind-name ind-name
                                            :rec-name rec-name
                                            :motive motive
                                            :params params
                                            :indices indices
                                            :levels rec-levels
                                            :ctor-goals ctor-goals})
                        (proof/record-tactic :induction [hyp-fvar-id] (:id goal)))]
            ;; Move branch goals to front to maintain focus
            (update ps' :goals (fn [gs]
              (let [branch-set (set branch-ids)
                    others (filterv #(not (branch-set %)) gs)]
                (into (vec branch-ids) others))))))))))

;; ============================================================
;; have (introduce intermediate lemma)
;; ============================================================

(defn have-tac
  "Introduce an intermediate lemma.
   Lean 4: have h : T := proof; ...
   Creates two subgoals: (1) prove T, (2) prove original goal with h : T in context."
  [ps hyp-name hyp-type]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        ;; Subgoal 1: prove hyp-type
        [ps' sub1-id] (proof/fresh-mvar ps hyp-type (:lctx goal))
        ;; Subgoal 2: prove goal with h : hyp-type added
        [ps'' fvar-id] (proof/alloc-id ps')
        new-lctx (red/lctx-add-local (:lctx goal) fvar-id hyp-name hyp-type)
        [ps''' sub2-id] (proof/fresh-mvar ps'' (:type goal) new-lctx)]
    (let [ps' (-> (proof/assign-mvar ps''' (:id goal)
                                         {:kind :have
                                          :name hyp-name
                                          :type hyp-type
                                          :fvar-id fvar-id
                                          :proof-goal sub1-id
                                          :body-goal sub2-id})
                  (proof/record-tactic :have [hyp-name] (:id goal)))]
      ;; Move proof-goal and body-goal to front (proof first, then body)
      (update ps' :goals (fn [gs]
        (let [new-ids #{sub1-id sub2-id}
              others (filterv #(not (new-ids %)) gs)]
          (into [sub1-id sub2-id] others)))))))

;; ============================================================
;; revert (move hypothesis back into goal)
;; ============================================================

(defn revert
  "Move a hypothesis back into the goal as a forall binder.
   Lean 4: revert h changes goal from G to ∀ h : T, G.
   Essential before induction to generalize."
  [ps hyp-fvar-id]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        hyp-decl (red/lctx-lookup (:lctx goal) hyp-fvar-id)
        _ (when-not hyp-decl (tactic-error! "revert: hypothesis not in context" {:id hyp-fvar-id}))
        hyp-name (or (:name hyp-decl) "x")
        hyp-type (:type hyp-decl)
        ;; New goal: ∀ h : T, goal-type (with fvar abstracted)
        new-goal-type (e/forall' hyp-name hyp-type
                                 (e/abstract1 (:type goal) hyp-fvar-id)
                                 :default)
        ;; Remove hypothesis from lctx
        new-lctx (dissoc (:lctx goal) hyp-fvar-id)
        [ps' new-goal-id] (proof/fresh-mvar ps new-goal-type new-lctx)
        ;; Move new goal to front to maintain focus on current branch
        ps' (update ps' :goals (fn [gs]
              (let [others (filterv #(not= % new-goal-id) gs)]
                (into [new-goal-id] others))))]
    (-> (proof/assign-mvar ps' (:id goal)
                           {:kind :revert
                            :fvar-id hyp-fvar-id
                            :child new-goal-id})
        (proof/record-tactic :revert [hyp-fvar-id] (:id goal)))))

;; ============================================================
;; exfalso (change goal to False)
;; ============================================================

(defn exfalso
  "Change the goal to False.
   Lean 4: exfalso changes any goal to False.
   Useful when hypotheses are contradictory."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        false-type (e/const' (name/from-string "False") [])
        ;; Compute the universe level of the goal type
        ;; False.elim : {C : Sort u} → False → C
        ;; u = sort level of the goal type
        st (mk-tc ps (:lctx goal))
        goal-sort (try (tc/infer-type st (:type goal)) (catch Exception _ nil))
        goal-sort-whnf (when goal-sort (whnf-in-goal ps (:lctx goal) goal-sort))
        motive-level (if (and goal-sort-whnf (e/sort? goal-sort-whnf))
                       (e/sort-level goal-sort-whnf)
                       lvl/zero)
        [ps' false-goal-id] (proof/fresh-mvar ps false-type (:lctx goal))]
    (-> (proof/assign-mvar ps' (:id goal)
                           {:kind :exfalso
                            :child false-goal-id
                            :goal-type (:type goal)
                            :motive-level motive-level})
        (proof/record-tactic :exfalso [] (:id goal)))))

;; ============================================================
;; subst (substitute equality into context)
;; ============================================================

(defn subst
  "Given h : x = t (where x is an fvar), substitute t for x everywhere.
   Lean 4: subst h eliminates h and replaces x with t.
   The hypothesis h must be of the form (fvar = expr) or (expr = fvar)."
  [ps hyp-fvar-id]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        st (mk-tc ps (:lctx goal))
        hyp-decl (red/lctx-lookup (:lctx goal) hyp-fvar-id)
        _ (when-not hyp-decl (tactic-error! "subst: hypothesis not in context" {:id hyp-fvar-id}))
        hyp-type (whnf-in-goal ps (:lctx goal) (:type hyp-decl))
        [head args] (e/get-app-fn-args hyp-type)
        _ (when-not (and (e/const? head)
                         (= (e/const-name head) (name/from-string "Eq"))
                         (= 3 (count args)))
            (tactic-error! "subst: hypothesis is not an Eq" {:type hyp-type}))
        lhs (nth args 1)
        rhs (nth args 2)
        ;; Determine which side is an fvar (the variable to substitute)
        [var-id replacement reverse?]
        (cond
          (e/fvar? lhs) [(e/fvar-id lhs) rhs false]
          (e/fvar? rhs) [(e/fvar-id rhs) lhs true]
          :else (tactic-error! "subst: neither side of Eq is a free variable"
                               {:lhs lhs :rhs rhs}))
        ;; Replace var-id with replacement in the goal type
        new-goal-type (e/instantiate1 (e/abstract1 (:type goal) var-id) replacement)
        ;; Build new lctx without the variable and the hypothesis
        new-lctx (-> (:lctx goal) (dissoc var-id) (dissoc hyp-fvar-id))
        [ps' new-goal-id] (proof/fresh-mvar ps new-goal-type new-lctx)]
    (-> (proof/assign-mvar ps' (:id goal)
                           {:kind :subst
                            :hyp-fvar-id hyp-fvar-id
                            :var-id var-id
                            :replacement replacement
                            :reverse? reverse?
                            :child new-goal-id})
        (proof/record-tactic :subst [hyp-fvar-id] (:id goal)))))

;; ============================================================
;; clear (remove hypothesis from context)
;; ============================================================

(defn clear
  "Remove a hypothesis from the local context.
   Lean 4: clear h removes h from context."
  [ps hyp-fvar-id]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        _ (when-not (red/lctx-lookup (:lctx goal) hyp-fvar-id)
            (tactic-error! "clear: hypothesis not in context" {:id hyp-fvar-id}))
        new-lctx (dissoc (:lctx goal) hyp-fvar-id)
        [ps' new-goal-id] (proof/fresh-mvar ps (:type goal) new-lctx)]
    (-> (proof/assign-mvar ps' (:id goal)
                           {:kind :clear
                            :fvar-id hyp-fvar-id
                            :child new-goal-id})
        (proof/record-tactic :clear [hyp-fvar-id] (:id goal)))))

;; ============================================================
;; Tactic combinators — Lean 4: try, <|>, repeat, all_goals
;; ============================================================

(defn try-tac
  "Try a tactic; if it fails, return the proof state unchanged.
   Lean 4: try tac.
   tac-fn is a function of one argument (proof state)."
  [ps tac-fn]
  (try
    (tac-fn ps)
    (catch Exception _ ps)))

(defn or-else
  "Try first tactic; if it fails, try second.
   Lean 4: tac1 <|> tac2."
  [ps tac1 tac2]
  (try
    (tac1 ps)
    (catch Exception _
      (tac2 ps))))

(defn first-tac
  "Try each tactic in order; return result of first that succeeds.
   Lean 4: first [tac1, tac2, ...]."
  [ps & tacs]
  (loop [remaining tacs]
    (if (empty? remaining)
      (tactic-error! "first: all tactics failed" {})
      (let [tac (first remaining)]
        (if-let [result (try (tac ps) (catch Exception _ nil))]
          result
          (recur (rest remaining)))))))

(defn repeat-tac
  "Apply a tactic repeatedly until it fails or makes no progress.
   Lean 4: repeat tac."
  ([ps tac-fn] (repeat-tac ps tac-fn 100))
  ([ps tac-fn max-iters]
   (loop [ps ps n 0]
     (if (>= n max-iters) ps
         (let [result (try (tac-fn ps) (catch Exception _ nil))]
           (if (and result (not= (:goals result) (:goals ps)))
             (recur result (inc n))
             ps))))))

(defn all-goals
  "Apply a tactic to all open goals.
   Lean 4: all_goals tac or tac1 <;> tac2."
  [ps tac-fn]
  (loop [ps ps goals (:goals ps)]
    (if (empty? goals) ps
        (let [gid (first goals)]
          (if (proof/mvar-assigned? ps gid)
            (recur ps (rest goals))
          ;; Focus on this goal by reordering
            (let [ps' (assoc ps :goals (into [gid] (remove #{gid} (:goals ps))))
                  ps' (try (tac-fn ps') (catch Exception _ ps'))]
              (recur ps' (rest goals))))))))

;; ============================================================
;; solve_by_elim — apply + assumption chain
;; ============================================================

(defn solve-by-elim
  "Close goals by repeatedly trying assumption on all open goals.
   Lean 4 Mathlib: solve_by_elim uses a backtracking search
   applying lemmas from the context. Our version tries assumption
   on all goals up to max-depth times.
   Optional extra-lemmas: vector of Ansatz terms to also try via apply."
  ([ps] (solve-by-elim ps 5 []))
  ([ps max-depth] (solve-by-elim ps max-depth []))
  ([ps max-depth extra-lemmas]
   (loop [ps ps depth 0]
     (if (or (>= depth max-depth) (proof/solved? ps))
       (if (proof/solved? ps) ps
           (tactic-error! "solve_by_elim: could not close all goals"
                          {:remaining (count (:goals ps))}))
       (let [ps' (all-goals ps
                            (fn [ps'']
                     ;; Try assumption first
                              (or (try (assumption ps'') (catch Exception _ nil))
                         ;; Try each extra lemma
                                  (some (fn [lemma]
                                          (try (apply-tac ps'' lemma)
                                               (catch Exception _ nil)))
                                        extra-lemmas)
                                  ps'')))]
         (if (= (:goals ps') (:goals ps))
           ;; No progress
           (if (proof/solved? ps') ps'
               (tactic-error! "solve_by_elim: no progress"
                              {:remaining (count (:goals ps'))}))
           (recur ps' (inc depth))))))))

;; ============================================================
;; Convenience tactics — Lean 4 sugar
;; ============================================================

(defn left
  "Choose the left branch of an Or goal. Lean 4: left."
  [ps]
  (apply-tac ps (e/const' (name/from-string "Or.inl") [])))

(defn right
  "Choose the right branch of an Or goal. Lean 4: right."
  [ps]
  (apply-tac ps (e/const' (name/from-string "Or.inr") [])))

(defn use-witness
  "Provide a witness for an existential goal.
   Lean 4: use w. Applies Exists.intro with the witness,
   then beta-reduces the predicate goal."
  [ps witness]
  (let [ps (constructor ps)]
    ;; First subgoal: the type (witness type). Provide the witness.
    (exact ps witness)))

(defn whnf-goal
  "WHNF-reduce the goal type. Useful after unfold/rewrite to let the
   kernel simplify beta-redexes, iota-reductions, etc."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        st (mk-tc ps (:lctx goal))
        reduced (#'tc/cached-whnf st (:type goal))]
    (if (= reduced (:type goal))
      ps ;; no change
      (let [[ps' new-id] (proof/fresh-mvar ps reduced (:lctx goal))]
        (-> (proof/assign-mvar ps' (:id goal) {:kind :exact :term (e/fvar new-id)})
            (proof/record-tactic :whnf [] (:id goal)))))))

(defn unfold-in-goal
  "Unfold (delta-reduce) a definition in the goal type.
   Replaces the outermost application of `def-name` with its definition value.
   This makes opaque function bodies visible for further reduction.

   Usage: (unfold sorted)
   Effect: sorted(args...) → body[args...] in the goal"
  [ps def-name-str]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        st (mk-tc ps (:lctx goal))
        def-name (name/from-string def-name-str)
        ^ConstantInfo ci (env/lookup! (:env ps) def-name)
        _ (when-not (.value ci)
            (tactic-error! (str "unfold: " def-name-str " has no definition value") {}))
        def-val (.value ci)
        def-levels (e/const-levels (e/get-app-fn (:type goal)))
        ;; Replace the constant application in the goal with its unfolded form
        ;; Walk the goal and find applications of def-name, replace with def-val applied to args
        replace-fn (fn replace-fn [expr]
                     (let [[head args] (e/get-app-fn-args expr)]
                       (if (and (e/const? head) (= (e/const-name head) def-name))
                         ;; Unfold: apply the definition value to the args
                         (let [subst (into {} (map vector
                                                   (vec (.levelParams ci))
                                                   (e/const-levels head)))
                               val (if (seq subst)
                                     (e/instantiate-level-params def-val subst)
                                     def-val)]
                           (reduce e/app val args))
                         ;; Recurse into applications
                         (case (e/tag expr)
                           :app (let [f (replace-fn (e/app-fn expr))
                                      a (replace-fn (e/app-arg expr))]
                                  (if (and (identical? f (e/app-fn expr))
                                           (identical? a (e/app-arg expr)))
                                    expr (e/app f a)))
                           expr))))
        new-goal-type (replace-fn (:type goal))
        ;; WHNF the unfolded goal to reduce the beta-redex
        new-goal-type-reduced (#'tc/cached-whnf st new-goal-type)
        [ps' new-id] (proof/fresh-mvar ps new-goal-type-reduced (:lctx goal))]
    ;; The new goal should be def-eq to the old goal (just unfolded)
    (-> (proof/assign-mvar ps' (:id goal) {:kind :exact :term (e/fvar new-id)})
        (proof/record-tactic :unfold [def-name-str] (:id goal)))))

(defn exact?
  "Search the environment + local context for a term that closes the goal.
   Returns the proof state if found, nil if not.
   Lean 4: exact? suggests candidates."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        st (mk-tc ps (:lctx goal))
        goal-type (:type goal)
        env (:env ps)]
    ;; Strategy 1: search local context (like assumption but with apply)
    (or
     ;; Direct match (assumption)
     (try (assumption ps) (catch Exception _ nil))
     ;; Strategy 2: search environment for constants whose type matches
     ;; Try common lemma names that might close the goal
     (let [goal-whnf (whnf-in-goal ps (:lctx goal) goal-type)
           [head args] (e/get-app-fn-args goal-whnf)]
       (when (e/const? head)
         (let [head-name (name/->string (e/const-name head))]
           ;; Try well-known lemmas based on goal head
           (some (fn [lemma-name]
                   (try
                     (when-let [ci (env/lookup env (name/from-string lemma-name))]
                       (apply-tac ps (e/const' (name/from-string lemma-name)
                                               (vec (repeat (count (.levelParams ci))
                                                            lvl/zero)))))
                     (catch Exception _ nil)))
                 (case head-name
                   "True" ["True.intro"]
                   "And" ["And.intro"]
                   "Eq" ["Eq.refl"]
                   "Iff" ["Iff.refl"]
                   "LE.le" ["Nat.le_refl" "le_refl"]
                   "LT.lt" []
                   "Nat.le" ["Nat.le.refl"]
                   [])))))
     ;; Strategy 3: try rfl
     (try (rfl ps) (catch Exception _ nil))
     ;; Strategy 4: try constructor
     (try (constructor ps) (catch Exception _ nil))
     ;; Nothing found
     (tactic-error! "exact?: no matching term found" {:goal goal-type}))))

;; ============================================================
;; by_cases — case split on a Bool expression
;; ============================================================

(defn by-cases
  "Case-split on a Bool expression. Creates two subgoals:
   1. The goal with `cond = true` as a hypothesis (h)
   2. The goal with `cond = false` as a hypothesis (h)

   Implemented via `have h_val : Bool := cond` then `cases h_val`,
   which substitutes cond with true/false in each branch.

   Usage: (by_cases (<= x y))
   Produces:
     Goal 1: h : Eq Bool cond true  ⊢ goal
     Goal 2: h : Eq Bool cond false ⊢ goal"
  [ps cond-expr]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        st (mk-tc ps (:lctx goal))
        ;; Verify cond-expr is Bool-typed
        cond-type (tc/infer-type st cond-expr)
        cond-type-whnf (whnf-in-goal ps (:lctx goal) cond-type)
        _ (when-not (and (e/const? cond-type-whnf)
                         (= (name/->string (e/const-name cond-type-whnf)) "Bool"))
            (tactic-error! "by_cases: expression is not Bool"
                           {:type cond-type :expr cond-expr}))
        bool-type (e/const' (name/from-string "Bool") [])
        bool-true (e/const' (name/from-string "Bool.true") [])
        bool-false (e/const' (name/from-string "Bool.false") [])
        ;; Strategy: introduce `h : cond = true` and `h : cond = false` as two subgoals.
        ;; Build proof: Bool.rec (motive := λ b, cond = b → Goal)
        ;;                       (λ h, false-branch) (λ h, true-branch) cond rfl
        ;; The motive says: "for each Bool value b, if cond = b then Goal"
        ;; Applied to cond with rfl (cond = cond), this gives Goal.
        eq-type (fn [val] (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                                  bool-type cond-expr val))
        ;; Create goals with hypothesis
        [ps' h-false-id] (proof/alloc-id ps)
        lctx-false (red/lctx-add-local (:lctx goal) h-false-id "hc" (eq-type bool-false))
        [ps' false-goal-id] (proof/fresh-mvar ps' (:type goal) lctx-false)
        [ps' h-true-id] (proof/alloc-id ps')
        lctx-true (red/lctx-add-local (:lctx goal) h-true-id "hc" (eq-type bool-true))
        [ps' true-goal-id] (proof/fresh-mvar ps' (:type goal) lctx-true)
        ;; Build the proof term directly:
        ;; @Bool.rec (λ b, Eq Bool cond b → Goal) (λ h, false_proof) (λ h, true_proof) cond (Eq.refl Bool cond)
        goal-sort (tc/infer-type st (:type goal))
        goal-sort-whnf (whnf-in-goal ps (:lctx goal) goal-sort)
        motive-level (if (e/sort? goal-sort-whnf) (e/sort-level goal-sort-whnf) lvl/zero)
        ;; motive: λ (b : Bool), Eq Bool cond b → Goal
        motive (e/lam "b" bool-type
                      (e/arrow (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                                       bool-type cond-expr (e/bvar 0))
                               (:type goal))
                      :default)
        ;; rfl : Eq Bool cond cond
        rfl-proof (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                          bool-type cond-expr)]
    (-> (proof/assign-mvar ps' (:id goal)
                           {:kind :by-cases
                            :cond cond-expr
                            :motive motive
                            :motive-level motive-level
                            :rfl-proof rfl-proof
                            :h-false-id h-false-id
                            :h-true-id h-true-id
                            :false-goal false-goal-id
                            :true-goal true-goal-id})
        (proof/record-tactic :by-cases [cond-expr] (:id goal)))))

;; ============================================================
;; split_ifs — automatic case split on stuck Bool.rec
;; ============================================================

(defn- find-stuck-bool-rec
  "Walk expression to find first stuck Bool.rec discriminant.
   A Bool.rec is stuck if its discriminant doesn't WHNF to Bool.true/Bool.false.
   Returns the Bool discriminant expression, or nil."
  [ps goal-lctx expr]
  (let [result (volatile! nil)]
    (letfn [(walk [e]
              (when-not @result
                ;; Check for Bool.rec
                (let [[head args] (e/get-app-fn-args e)]
                  (when (and (e/const? head)
                             (= (name/->string (e/const-name head)) "Bool.rec")
                             (= 4 (count args)))
                    (let [discr (nth args 3)
                          dw (try (whnf-in-goal ps goal-lctx discr) (catch Exception _ discr))]
                      (when-not (and (e/const? dw)
                                     (let [n (name/->string (e/const-name dw))]
                                       (or (= n "Bool.true") (= n "Bool.false"))))
                        (vreset! result discr)))))
                ;; Recurse into subterms
                (when-not @result
                  (case (e/tag e)
                    :app (do (walk (e/app-fn e)) (walk (e/app-arg e)))
                    :lam (walk (e/lam-body e))
                    :forall (walk (e/forall-body e))
                    :let (do (walk (e/let-value e)) (walk (e/let-body e)))
                    :mdata (walk (e/mdata-expr e))
                    :proj (walk (e/proj-struct e))
                    nil))))]
      (walk expr))
    @result))

(defn split-ifs
  "Case-split on the first stuck Bool.rec in the goal type.
   Finds a Bool.rec whose discriminant doesn't reduce to true/false,
   then applies by_cases on that discriminant.
   Lean 4: splitIfTarget? from Tactic/SplitIf.lean."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        ;; Search raw goal type first
        discr (find-stuck-bool-rec ps (:lctx goal) (:type goal))]
    (if discr
      (by-cases ps discr)
      ;; Try after WHNF reduction
      (let [goal-whnf (whnf-in-goal ps (:lctx goal) (:type goal))
            discr (find-stuck-bool-rec ps (:lctx goal) goal-whnf)]
        (if discr
          (by-cases ps discr)
          (tactic-error! "split_ifs: no stuck if-then-else found" {:goal (:type goal)}))))))
