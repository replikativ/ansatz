;; Tactic layer — core tactics.

(ns ansatz.tactic.basic
  "Core tactics: intro, intros, exact, assumption, apply, rfl, constructor,
   cases, induction, rewrite, have-tac, revert, exfalso, subst, clear.
   Tactic combinators: try-tac, or-else, repeat-tac, all-goals.
   Each tactic is a pure function: (tactic ps ...args) → ps'."
  (:require [clojure.set]
            [ansatz.kernel.expr :as e]
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

;; Forward declarations for mutually-dependent tactics
(declare generalize-indices unify-cases-eqs unify-eq revert)

(defn- mk-impossible-branch-proof
  "Build a proof term for an impossible branch in cases on indexed families.
   The branch goal type is a Prop that should never be reached.
   Uses a temporary axiom for soundness — the recursor never evaluates
   this branch because the index head doesn't match.
   TODO: replace with proper noConfusion derivation."
  [ps goal-type]
  ;; Register a temporary axiom and return [updated-ps proof-term].
  ;; The axiom is needed for the kernel to type-check the impossible minor.
  (let [axiom-name (name/from-string "Ansatz.impossible")
        env (:env ps)
        ps (if (env/lookup env axiom-name)
             ps
             ;; Axiom: ∀ {P : Prop}, P
             (let [ax-type (e/forall' "P" (e/sort' lvl/zero) (e/bvar 0) :implicit)
                   ax-ci (env/mk-axiom axiom-name [] ax-type)
                   new-env (env/add-constant env ax-ci)]
               (assoc ps :env new-env)))]
    ;; Apply: Ansatz.impossible {goal-type}
    [ps (e/app (e/const' axiom-name []) goal-type)]))

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
   Following Lean 4: uses isDefEq as primary matching (Assumption.lean:20).
   When the goal has unresolved fvar-mvars, isDefEq matching extracts
   the bindings and propagates them to sibling goals."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        lctx (:lctx goal)
        goal-type (:type goal)
        ;; Collect ALL unresolved fvar-mvars (including implicit/hidden ones)
        unresolved-mvars (set (keep (fn [[mid m]]
                                      (when (not (:assignment m)) mid))
                                    (:mctx ps)))
        ;; Strategy 1: structural equality (fast, no mvar issues)
        struct-match (some (fn [[id decl]]
                             (when (and (= :local (:tag decl))
                                        (= (:type decl) goal-type))
                               {:fvar-id id :bindings {}}))
                           lctx)
        ;; Strategy 2: isDefEq with WHNF extraction (Lean 4's primary mechanism).
        ;; Try each hypothesis; extract fvar-mvar bindings on match.
        deq-match (when-not struct-match
                    (let [jtc (ansatz.kernel.TypeChecker. (:env ps))
                          _ (.setFuel jtc config/*default-fuel*)
                          _ (doseq [[id decl] lctx]
                              (when (= :local (:tag decl))
                                (.addLocal jtc (long id) (str (:name decl)) (:type decl))))
                          ;; Also register unresolved mvars as locals
                          _ (doseq [mid unresolved-mvars]
                              (let [m (get-in ps [:mctx mid])]
                                (when m (.addLocal jtc (long mid) "?m" (:type m)))))
                          st (mk-tc ps lctx)
                          goal-whnf (try (#'tc/cached-whnf st goal-type)
                                         (catch Exception _ goal-type))]
                      (some (fn [[id decl]]
                              (when (= :local (:tag decl))
                                (let [hyp-type (:type decl)
                                      hyp-whnf (try (#'tc/cached-whnf st hyp-type)
                                                     (catch Exception _ hyp-type))
                                      ;; Extract fvar-mvar bindings from WHNF forms
                                      bindings (atom {})
                                      _ (letfn [(extract [g h]
                                                  (cond
                                                    (and (e/fvar? g) (contains? unresolved-mvars (e/fvar-id g)))
                                                    (swap! bindings assoc (e/fvar-id g) h)
                                                    (and (e/app? g) (e/app? h))
                                                    (do (extract (e/app-fn g) (e/app-fn h))
                                                        (extract (e/app-arg g) (e/app-arg h)))
                                                    :else nil))]
                                          (try (extract goal-whnf hyp-whnf) (catch Exception _ nil)))
                                      ;; Substitute bindings and verify with isDefEq
                                      resolved-goal (reduce (fn [t [mid val]]
                                                              (e/instantiate1 (e/abstract1 t mid) val))
                                                            goal-type @bindings)]
                                  (when (try (.isDefEq jtc hyp-type resolved-goal)
                                             (catch Exception _ false))
                                    {:fvar-id id :bindings @bindings}))))
                            lctx)))
        result (or struct-match deq-match)]
    (when-not result
      (tactic-error! "No matching hypothesis found" {:goal-type (:type goal)}))
    ;; Propagate fvar-mvar bindings to sibling goals
    (let [ps (reduce (fn [ps [mid val]]
                       (proof/assign-mvar ps mid {:kind :exact :term val}))
                     ps (:bindings result))]
      (-> (proof/assign-mvar ps (:id goal) {:kind :assumption :fvar-id (:fvar-id result)})
          (proof/record-tactic :assumption [] (:id goal))))))

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
           mvar-id-set #{}
           type-param-idx 0
           implicit-mvars #{}]
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
              is-type-param (and (#{:implicit :strict-implicit} binfo)
                                 (let [stw (try (#'tc/cached-whnf st inst-type) (catch Exception _ nil))]
                                   (and stw (e/sort? stw))))
              inferred-val
              (cond
                ;; Implicit type param: infer from goal's corresponding arg
                ;; Use type-param-idx to pick the right arg (not always first)
                is-type-param
                (let [[gh ga] (e/get-app-fn-args (:type goal))]
                  (when (and (seq ga) (< type-param-idx (count ga)))
                    (nth ga type-param-idx)))

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
                     (conj arg-mvars mvar-id) mvar-id-set
                     (if is-type-param (inc type-param-idx) type-param-idx)
                     implicit-mvars))
            ;; Not synthesized — create mvar (for implicit, inst-implicit, AND explicit params)
            ;; Following Lean 4: peel ALL foralls, explicit mvars become subgoals.
            ;; Track implicit mvars separately — they won't become visible subgoals.
            (let [[ps' mvar-id] (proof/fresh-mvar ps inst-type (:lctx goal))
                  new-ty (e/instantiate1 (e/forall-body ty) (e/fvar mvar-id))
                  is-implicit (#{:implicit :strict-implicit :inst-implicit} binfo)]
              (recur ps' (whnf-in-goal ps' (:lctx goal) new-ty)
                     (conj arg-mvars mvar-id)
                     (conj mvar-id-set mvar-id)
                     (if is-type-param (inc type-param-idx) type-param-idx)
                     (if is-implicit (conj implicit-mvars mvar-id) implicit-mvars)))))
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
                            ;; Following Lean 4: isDefEq is the primary matching mechanism.
                            ;; First, try to resolve remaining mvars by WHNF-matching
                            ;; the resolved type against the goal type. This handles cases
                            ;; like Nat.le vs LE.le where heads differ but are def-eq.
                            (let [;; Collect unresolved mvar fvar-ids
                                  unresolved (set (filter (fn [mid]
                                                           (let [m (get-in ps [:mctx mid])]
                                                             (and m (not (:assignment m)))))
                                                         arg-mvars))
                                  ;; Try structural extraction on WHNF'd forms first
                                  deep-subst (atom {})
                                  _ (letfn [(extract [r g]
                                              (cond
                                                (and (e/fvar? r) (contains? unresolved (e/fvar-id r)))
                                                (swap! deep-subst assoc (e/fvar-id r) g)
                                                (and (e/app? r) (e/app? g))
                                                (do (extract (e/app-fn r) (e/app-fn g))
                                                    (extract (e/app-arg r) (e/app-arg g)))
                                                :else nil))]
                                      (try (extract resolved-whnf goal-whnf) (catch Exception _ nil)))
                                  ;; Substitute extracted bindings into resolved-ty
                                  resolved-ty' (reduce (fn [t [mid val]]
                                                         (e/instantiate1 (e/abstract1 t mid) val))
                                                       resolved-ty @deep-subst)
                                  ;; Now try isDefEq with all mvars resolved
                                  deq (or (.isDefEq jtc resolved-ty' (:type goal))
                                          ;; Also try with original (in case extraction was wrong)
                                          (.isDefEq jtc resolved-ty (:type goal)))]
                                (when deq @deep-subst)))
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
                  ;; Move unsolved EXPLICIT arg-mvars to front of goals (Lean 4: new goals first)
                  ;; Implicit mvars stay in mctx as shared mvars but aren't visible subgoals.
                  ;; They get resolved when explicit subgoals are solved (via assign-mvar propagation).
                  unsolved-args (filterv #(and (not (proof/mvar-assigned? ps %))
                                               (not (contains? implicit-mvars %)))
                                         arg-mvars)]
              (update ps :goals (fn [gs]
                                  (into (vec unsolved-args)
                                        (remove (set (filterv #(not (proof/mvar-assigned? ps %)) arg-mvars)) gs)))))))))))

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
        ;; Build motive for the recursor.
        ;; Three paths:
        ;; A) Simple indices (all fvars): abstract-many from goal directly.
        ;; B-old) Complex indices (single ctor application): casesOn-based motive (legacy).
        ;; C) Complex indices with noConfusion available: generalizeIndices pipeline.
        ;;    This is the Lean 4 approach: generalize → cases (Path A) → unifyCasesEqs.
        st (mk-tc ps (:lctx goal))
        has-complex-indices (some #(not (e/fvar? %)) indices)
        ;; Check if noConfusion is available for the index type (needed for Path C)
        has-no-confusion
        (when (and has-complex-indices (seq indices))
          (let [idx-expr (first indices)
                idx-type (try (tc/infer-type st idx-expr) (catch Exception _ nil))
                [idx-type-head _] (when idx-type (e/get-app-fn-args idx-type))]
            (when (and idx-type-head (e/const? idx-type-head))
              (let [nc-name (name/mk-str (e/const-name idx-type-head) "noConfusion")]
                (some? (env/lookup (:env ps) nc-name))))))
        ;; Build the motive (and possibly update ps with fresh fvar allocations)
        [ps motive motive-body use-whnf-branch-goals nextra]
        (if (and has-complex-indices (seq indices) has-no-confusion)
          ;; Path C: Full Lean 4 pipeline — generalizeIndices → cases → unifyCasesEqs
          ;; Step 1: generalize indices (transforms goal, adds equality hypotheses)
          (let [gen-result (generalize-indices ps hyp-fvar-id)
                ps (:ps gen-result)
                num-eqs (count (:orig-indices gen-result))
                _ (let [g (proof/current-goal ps)]
                    (when-not (and g (e/forall? (or (:type g) (e/sort' lvl/zero))))
                      (throw (ex-info "Path C: generalized goal is not forall"
                                      {:has-goal (some? g)
                                       :goal-type (when g (e/->string (:type g)))}))))
                ;; Step 2: Intro the generalized binders
                ;; Intro index fvars
                ps (reduce (fn [ps _] (intro ps)) ps (range (count (:index-fvar-ids gen-result))))
                ;; Intro the major premise
                ps (intro ps)
                ;; Now the current goal has simple fvar indices — run cases (Path A) recursively
                new-goal (proof/current-goal ps)
                ;; Find the new hypothesis (last introduced)
                new-hyp-fvar-id (last (sort (keys (:lctx new-goal))))
                ;; Track goals before cases to identify new branch goals
                goals-before (set (:goals ps))
                ;; Run cases on the new hypothesis (Path A - simple indices)
                ps (cases ps new-hyp-fvar-id)
                ;; Step 3: For each open goal from THIS cases, solve the equalities
                ;; Only process goals that were created by the inner cases (not outer goals)
                branch-goals (filterv #(not (goals-before %)) (:goals ps))
                ps (reduce (fn [ps goal-id]
                             (if (proof/mvar-assigned? ps goal-id)
                               ps ;; Already closed (e.g., by subst propagation)
                               (let [ps (update ps :goals
                                                (fn [gs] (into [goal-id] (remove #{goal-id}) gs)))]
                                 (unify-cases-eqs ps num-eqs))))
                           ps branch-goals)]
            ;; Return a sentinel — the work is already done, skip the rest of cases
            [ps :pipeline-done :pipeline-done :pipeline-done 0])

          (if (and has-complex-indices (= 1 (count indices))
                   (not has-no-confusion))
          ;; Path B: CasesOn-based motive for single complex index
          (let [idx-expr (first indices)
                [orig-head orig-args] (e/get-app-fn-args idx-expr)
                _ (when-not (e/const? orig-head)
                    (tactic-error! "cases: complex index must be a constructor application"
                                   {:index idx-expr}))
                ;; Infer the index type
                idx-type (tc/infer-type st idx-expr)
                [idx-type-head idx-type-args] (e/get-app-fn-args idx-type)
                idx-type-name (e/const-name idx-type-head)
                idx-type-levels (e/const-levels idx-type-head)
                ^ConstantInfo idx-ind-ci (env/lookup! (:env ps) idx-type-name)
                idx-num-params (.numParams idx-ind-ci)
                idx-params (vec (take idx-num-params idx-type-args))
                ;; Original index components (constructor args after params)
                orig-components (subvec (vec orig-args) idx-num-params)
                orig-ctor-name (e/const-name orig-head)
                ;; Create fresh fvars for motive binders (idx and h)
                [ps idx-fid] (proof/alloc-id ps)
                idx-fvar (e/fvar idx-fid)
                [ps h-fid] (proof/alloc-id ps)
                ;; CasesOn for the index type.
                ;; The inner casesOn produces goal TYPES (e.g. ValidRB l : Prop).
                ;; Goal types live in Sort(motive-level), so the casesOn motive
                ;; returns Sort(motive-level) which itself lives in Sort(motive-level+1).
                ;; Therefore the casesOn universe level = succ(motive-level).
                idx-co-name (name/mk-str idx-type-name "casesOn")
                idx-co-motive-level (lvl/succ motive-level)
                idx-co-levels (into [idx-co-motive-level] idx-type-levels)
                ;; CasesOn motive: λ _ => Sort(motive-level)
                idx-co-motive (e/lam "_" idx-type (e/sort' motive-level) :default)
                ;; Build a minor for each constructor of the index type
                idx-ctors (vec (.ctors idx-ind-ci))
                idx-minors
                (mapv
                  (fn [idx-ctor-nm]
                    (let [^ConstantInfo ctor-ci (env/lookup! (:env ps) idx-ctor-nm)
                          ctor-ty (.type ctor-ci)
                          subst-m (into {} (map vector (vec (.levelParams ctor-ci)) idx-type-levels))
                          ctor-ty (e/instantiate-level-params ctor-ty subst-m)
                          ;; Skip params
                          ctor-ty (loop [t ctor-ty ps-args idx-params]
                                    (if (and (seq ps-args) (e/forall? t))
                                      (recur (e/instantiate1 (e/forall-body t) (first ps-args))
                                             (rest ps-args))
                                      t))
                          ;; Collect field types (instantiate with originals for matching ctor)
                          field-types
                          (loop [t ctor-ty types [] ci 0]
                            (if (e/forall? t)
                              (let [ft (e/forall-type t)
                                    ;; For matching ctor, instantiate body with original component
                                    inst-val (if (= idx-ctor-nm orig-ctor-name)
                                               (get orig-components ci (e/fvar 999999))
                                               (e/fvar (+ 2000000 ci)))]
                                (recur (e/instantiate1 (e/forall-body t) inst-val)
                                       (conj types ft) (inc ci)))
                              types))]
                      (if (= idx-ctor-nm orig-ctor-name)
                        ;; Matching constructor: abstract original components from goal.
                        ;; Process from innermost field to outermost (reverse order).
                        ;; For fvar components: abstract1 (replaces fvar with bvar(0) at depth).
                        ;; For non-fvar components: body unchanged (lambda param is unused).
                        (reduce (fn [body [comp ft]]
                                  (e/lam "_" ft
                                         (if (e/fvar? comp)
                                           (e/abstract1 body (e/fvar-id comp))
                                           body)
                                         :default))
                                (:type goal)
                                (reverse (map vector orig-components field-types)))
                        ;; Non-matching constructor: return the original goal for all fields.
                        ;; (Impossible branches will be closed by Ansatz.impossible.)
                        (reduce (fn [body ft]
                                  (e/lam "_" ft body :default))
                                (:type goal)
                                (reverse field-types)))))
                  idx-ctors)
                ;; Build the casesOn expression: @IdxType.casesOn params motive idx minors
                co-expr (reduce e/app
                                (e/const' idx-co-name idx-co-levels)
                                (concat idx-params [idx-co-motive idx-fvar] idx-minors))
                ;; Abstract idx-fvar and h-fvar from the casesOn expression
                motive-body (e/abstract-many co-expr [idx-fid h-fid])
                ;; Build the full motive: λ (idx : IdxType) (h : IndType params idx). body
                fresh-h-type (reduce e/app (e/const' ind-name ind-levels)
                                     (concat params [idx-fvar]))
                h-type-abs (e/abstract1 fresh-h-type idx-fid)
                motive (e/lam "x" idx-type
                              (e/lam "x" h-type-abs motive-body :default)
                              :default)]
            [ps motive motive-body true 0])
          ;; Path A: Following Lean 4 MVarId.induction (lines 203-240):
          ;; Revert indices + major + dependents, re-intro indices + major,
          ;; build motive from the enlarged goal, then re-intro dependents in branches.
          (let [;; Step 1: Find dependents of the major premise (Lean 4 line 221)
                idx-fvar-ids (vec (keep (fn [idx] (when (e/fvar? idx) (e/fvar-id idx))) indices))
                revert-fids (conj idx-fvar-ids hyp-fvar-id)
                ;; Revert indices + major + dependents (preserveOrder=true)
                ;; We revert in reverse order (highest-ID first), then the explicitly listed ones
                all-fids-to-revert
                (let [revert-set (set revert-fids)
                      ;; Dependents: simple const-headed hypotheses that depend on reverted fids.
                      ;; Excludes IH types (lambda apps) and Eq types (equality leftovers).
                      ;; Matches Lean 4's approach: only revert hypotheses with simple inductive types.
                      eq-name (name/from-string "Eq")
                      deps (vec (sort (for [[fid d] (:lctx goal)
                                           :when (and (not (revert-set fid))
                                                      (= :local (:tag d))
                                                      (e/has-fvar-flag (:type d))
                                                      (some (fn [rfid]
                                                              (not= (e/abstract1 (:type d) rfid) (:type d)))
                                                            revert-fids)
                                                      ;; Filter: only simple inductive types
                                                      (let [[h _] (e/get-app-fn-args (:type d))]
                                                        (and (e/const? h)
                                                             (not= (e/const-name h) eq-name))))]
                                       fid)))]
                  ;; Revert order: dependents (highest first), then hyp, then indices (highest first)
                  (vec (concat (reverse deps) [hyp-fvar-id] (reverse idx-fvar-ids))))
                nextra (- (count all-fids-to-revert) (count idx-fvar-ids) 1)
                ;; Perform reverts
                ps (reduce (fn [ps fid]
                             (if (red/lctx-lookup (:lctx (proof/current-goal ps)) fid)
                               (revert ps fid)
                               ps))
                           ps all-fids-to-revert)
                ;; Step 2: Re-intro indices + major (Lean 4 lines 223-224)
                ps (reduce (fn [ps _] (intro ps)) ps (range (count idx-fvar-ids)))
                ps (intro ps)  ;; re-intro major
                ;; Get the current goal (with enlarged type including dependent foralls)
                goal-after (proof/current-goal ps)
                ;; Find the re-introduced fvar IDs
                new-hyp-fvar-id (last (sort (keys (:lctx goal-after))))
                new-hyp-type (whnf-in-goal ps (:lctx goal-after)
                                           (:type (red/lctx-lookup (:lctx goal-after) new-hyp-fvar-id)))
                ;; Re-extract indices from the re-introduced major's type
                [_ new-type-args] (e/get-app-fn-args new-hyp-type)
                new-indices (subvec (vec new-type-args) (min num-params (count new-type-args)))
                new-idx-fvar-ids (vec (keep (fn [idx] (when (e/fvar? idx) (e/fvar-id idx))) new-indices))
                ;; Step 3: Build motive from the enlarged goal (Lean 4 lines 193-198)
                motive-fv-ids (conj new-idx-fvar-ids new-hyp-fvar-id)
                motive-body (e/abstract-many (:type goal-after) motive-fv-ids)
                new-idx-types (mapv (fn [idx-expr]
                                      (if (e/fvar? idx-expr)
                                        (or (:type (red/lctx-lookup (:lctx goal-after) (e/fvar-id idx-expr)))
                                            (e/sort' lvl/zero))
                                        (e/sort' lvl/zero)))
                                    new-indices)
                new-major-type-abs (reduce (fn [ty fid] (e/abstract1 ty fid))
                                           new-hyp-type
                                           (reverse new-idx-fvar-ids))
                motive-binder-types (conj new-idx-types new-major-type-abs)
                motive (reduce (fn [body ty] (e/lam "x" ty body :default))
                               motive-body
                               (reverse motive-binder-types))
                ;; Update goal/hyp refs for the rest of the cases function
                goal goal-after
                hyp-fvar-id new-hyp-fvar-id
                hyp-type new-hyp-type
                indices new-indices]
            [ps motive motive-body false nextra])))]
    (if (= motive :pipeline-done)
      ;; Path C completed — return ps directly
      ps
      ;; Path A/B: continue with subgoal creation
      ;; After revert+re-intro in Path A, re-read goal from ps (it may have changed)
      (let [goal (proof/current-goal ps)
            ;; Re-find hyp-fvar-id: pick highest-ID fvar of the inductive type
            hyp-fvar-id (or (reduce (fn [best [fid d]]
                                      (if (and (= :local (:tag d))
                                               (let [[h _] (e/get-app-fn-args
                                                            (whnf-in-goal ps (:lctx goal)
                                                                          (or (:type d) (e/sort' lvl/zero))))]
                                                 (and (e/const? h) (= (e/const-name h) ind-name)))
                                               (or (nil? best) (> (long fid) (long best))))
                                        fid best))
                                    nil (:lctx goal))
                            hyp-fvar-id)
            hyp-type (whnf-in-goal ps (:lctx goal) (:type (red/lctx-lookup (:lctx goal) hyp-fvar-id)))
            [_ type-args-new] (e/get-app-fn-args hyp-type)
            params (subvec (vec type-args-new) 0 (min num-params (count type-args-new)))
            indices (subvec (vec type-args-new) (min num-params (count type-args-new)))
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
              ;; Lean 4: remove major premise (and index fvars) from branch lctx
              base-lctx (let [remove-ids (into #{hyp-fvar-id}
                                               (keep (fn [idx] (when (e/fvar? idx) (e/fvar-id idx))))
                                               indices)]
                          (reduce dissoc (:lctx goal) remove-ids))
              ;; Peel fields, creating fvars for each
              [ps' field-fvars new-lctx ctor-type]
              (loop [ps ps field-fvars [] lctx base-lctx t ctor-type]
                (if (e/forall? t)
                  (let [[ps' fid] (proof/alloc-id ps)
                        fv (e/fvar fid)
                        ft (e/forall-type t)
                        fname-raw (e/forall-name t)
                        fname (cond
                                (nil? fname-raw) (str "h" fid)
                                (string? fname-raw) fname-raw
                                :else (name/->string fname-raw))
                        lctx' (red/lctx-add-local lctx fid fname ft)]
                    (recur ps' (conj field-fvars fid)
                           lctx' (e/instantiate1 (e/forall-body t) fv)))
                  [ps field-fvars lctx t]))
              ;; For the recursor (not casesOn), add IH fvars for recursive fields.
              ;; The rec minor expects: ∀ fields, ∀ ih_fields, motive(ctor ...).
              ;; IH fvars are included in the minor lambdas during extraction
              ;; but are NOT shown to the user (they don't affect the branch goal).
              [ps' all-field-fvars new-lctx]
              (let [rec-field-ids (filterv
                                   (fn [fid]
                                     (let [ft (:type (red/lctx-lookup new-lctx fid))
                                           ft-whnf (whnf-in-goal ps new-lctx ft)
                                           [fh _] (e/get-app-fn-args ft-whnf)]
                                       (and (e/const? fh) (= (e/const-name fh) ind-name))))
                                   field-fvars)]
                (if (empty? rec-field-ids)
                  [ps' field-fvars new-lctx]
                  (loop [ps-acc ps' ih-fvars [] lctx-acc new-lctx rfs (seq rec-field-ids)]
                    (if-not rfs
                      [ps-acc (into (vec field-fvars) ih-fvars) lctx-acc]
                      (let [rec-fid (first rfs)
                            [ps-acc' ih-fid] (proof/alloc-id ps-acc)
                            rec-decl (red/lctx-lookup lctx-acc rec-fid)
                            rec-type-whnf (whnf-in-goal ps lctx-acc (:type rec-decl))
                            [_ rec-args] (e/get-app-fn-args rec-type-whnf)
                            rec-indices (subvec (vec rec-args) (min num-params (count rec-args)))
                            ;; IH type: motive(indices..., field-fvar)
                            ih-type (reduce e/app motive (concat rec-indices [(e/fvar rec-fid)]))
                            lctx' (red/lctx-add-local lctx-acc ih-fid
                                    (str "ih_" (or (:name rec-decl) rec-fid)) ih-type)]
                        (recur ps-acc' (conj ih-fvars ih-fid) lctx' (next rfs)))))))
              ;; Build ctor applied to params and field fvars
              ctor-term (reduce e/app
                                (e/const' ctor-name ind-levels)
                                (concat params (map e/fvar field-fvars)))
              ;; Substitute the eliminated hypothesis in the branch lctx.
              ;; Lean 4: cases removes the hyp and substitutes everywhere.
              ;; For `cases l` where `hl : ValidRB l`, this gives `hl : ValidRB(ctor-app)`.
              new-lctx (reduce-kv
                         (fn [lctx fid decl]
                           (if (= fid hyp-fvar-id)
                             lctx ;; Remove eliminated hypothesis
                             (assoc lctx fid
                                    (if (e/has-fvar-flag (:type decl))
                                      (update decl :type
                                              (fn [t] (e/instantiate1 (e/abstract1 t hyp-fvar-id) ctor-term)))
                                      decl))))
                         {} new-lctx)
              ;; For indexed families, extract return indices from ctor return type
              ;; ctor-type here is the constructor's return type after field peeling
              ctor-ret-indices (when (seq indices)
                                 (let [[_ ret-args] (e/get-app-fn-args ctor-type)]
                                   (when (>= (count ret-args) num-params)
                                     (subvec (vec ret-args) num-params))))
              ;; Check if this branch is impossible (index heads don't match).
              ;; Lean 4: unifyCasesEqs + noConfusion eliminates these.
              ;; We do a simpler head-check: if ANY index head differs, skip.
              impossible? (and (seq ctor-ret-indices) (seq indices)
                               (some (fn [[ci mi]]
                                       (let [[ch _] (e/get-app-fn-args ci)
                                             [mh _] (e/get-app-fn-args mi)]
                                         (and (e/const? ch) (e/const? mh)
                                              (not= (e/const-name ch) (e/const-name mh)))))
                                     ;; Use original indices for impossible check
                                     ;; (heads must match the concrete major premise)
                                     (map vector ctor-ret-indices indices)))
              ;; Compute branch goal type by instantiating the motive body.
              ;; bvar(0)=h, bvar(1..k)=indices. instantiate maps bvar(i)→vals[n-1-i],
              ;; so vals = [idx_first, ..., idx_last, ctor-term].
              branch-goal-type-raw (if (seq ctor-ret-indices)
                                    (e/instantiate motive-body
                                                   (conj (vec ctor-ret-indices) ctor-term))
                                    (e/instantiate1 motive-body ctor-term))
              ;; For casesOn-based motives: WHNF to reduce the inner casesOn
              branch-goal-type (if use-whnf-branch-goals
                                 (whnf-in-goal ps new-lctx branch-goal-type-raw)
                                 branch-goal-type-raw)
              [ps' branch-id] (if impossible?
                                 ;; Impossible branch: create and immediately close.
                                 (let [[ps-with-axiom dummy-term] (mk-impossible-branch-proof ps branch-goal-type)
                                       [ps' id] (proof/alloc-id ps-with-axiom)]
                                   [(-> ps'
                                        (assoc-in [:mctx id] {:type branch-goal-type :lctx new-lctx
                                                               :assignment {:kind :exact :term dummy-term}}))
                                    id])
                                 ;; Possible branch: create open goal
                                 (proof/fresh-mvar ps' branch-goal-type new-lctx))]
          ;; Re-intro reverted dependents in each open branch (Lean 4 line 111)
          ;; The re-intro'd fvar IDs must be added to field-fvars so the cases
          ;; extraction abstracts them in the minor lambda.
          (let [[ps' branch-id extra-fids]
                (if (and (not impossible?) (pos? nextra))
                  (let [ps-front (update ps' :goals
                                         (fn [gs] (into [branch-id] (remove #{branch-id}) gs)))
                        ;; Collect the re-intro'd fvar IDs
                        [ps-introed intro-fids]
                        (loop [ps ps-front n nextra fids []]
                          (if (zero? n)
                            [ps fids]
                            (let [ps (intro ps)
                                  g (proof/current-goal ps)
                                  ;; The most recently introduced fvar
                                  newest (last (sort (keys (:lctx g))))]
                              (recur ps (dec n) (conj fids newest)))))
                        new-id (first (:goals ps-introed))]
                    [ps-introed new-id intro-fids])
                  [ps' branch-id []])]
            (recur ps' (inc i)
                   (conj ctor-goals {:ctor-name ctor-name
                                     :field-fvars (into (vec all-field-fvars) extra-fids)
                                     :goal-id branch-id}))))
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
                                            :ctor-goals ctor-goals
                                            ;; dep-fids empty: the revert extraction handles dep application
                                            :dep-fids []})
                        (proof/record-tactic :cases [hyp-fvar-id] (:id goal)))]
            ;; Move open branch goals to front (skip impossible branches)
            (let [open-ids (filterv #(not (proof/mvar-assigned? ps' %)) branch-ids)]
              (update ps' :goals (fn [gs]
                (let [branch-set (set open-ids)
                      others (filterv #(not (branch-set %)) gs)]
                  (into (vec open-ids) others)))))))))))))

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
        ;; Build the motive body using abstract-many for correct bvar indexing.
        ;; fv-ids outermost→innermost: [idx1, ..., idxk, h]
        motive-fv-ids (conj (vec (keep (fn [idx] (when (e/fvar? idx) (e/fvar-id idx)))
                                       indices))
                            hyp-fvar-id)
        motive-body (e/abstract-many (:type goal) motive-fv-ids)
        major-type hyp-type
        idx-types (mapv (fn [idx-expr]
                          (if (e/fvar? idx-expr)
                            (let [d (red/lctx-lookup (:lctx goal) (e/fvar-id idx-expr))]
                              (or (:type d) (e/sort' lvl/zero)))
                            (e/sort' lvl/zero)))
                        indices)
        ;; For indexed families, abstract index fvars from major-type
        major-type-abs (if (seq indices)
                         (reduce (fn [ty idx-expr]
                                   (if (e/fvar? idx-expr)
                                     (e/abstract1 ty (e/fvar-id idx-expr))
                                     ty))
                                 major-type (reverse indices))
                         major-type)
        motive-binder-types (conj idx-types major-type-abs)
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
              ;; Peel fields AND add IH for recursive fields.
              ;; Recursor expects: all fields first, then all IHs.
              ;; Track ctor-fvars (for constructor term) separately.
              ;; Lean 4: remove major premise (and index fvars for indexed families)
              ;; from each branch's lctx — they're consumed by the recursor
              base-lctx (let [remove-ids (into #{hyp-fvar-id}
                                               (keep (fn [idx] (when (e/fvar? idx) (e/fvar-id idx))))
                                               indices)]
                          (reduce dissoc (:lctx goal) remove-ids))
              [ps' ctor-fvars ih-fvar-ids new-lctx ctor-ret-type]
              (loop [ps ps ctor-fvars [] ih-fvars [] lctx base-lctx t ctor-type]
                (if (e/forall? t)
                  (let [[ps' fid] (proof/alloc-id ps)
                        fv (e/fvar fid)
                        ft (e/forall-type t)
                        fname-raw (e/forall-name t)
                        fname (cond
                                (nil? fname-raw) (str "h" fid)
                                (string? fname-raw) fname-raw
                                :else (name/->string fname-raw))
                        lctx' (red/lctx-add-local lctx fid fname ft)
                        ft-whnf (whnf-in-goal ps lctx ft)
                        [ft-head _] (e/get-app-fn-args ft-whnf)
                        is-recursive (and (e/const? ft-head)
                                          (= (e/const-name ft-head) ind-name))
                        [ps'' lctx'' new-ih-fvars]
                        (if is-recursive
                          (let [[ps'' ih-id] (proof/alloc-id ps')
                                ;; For indexed families, extract indices from the
                                ;; recursive field's type and instantiate motive with them
                                [_ ft-args] (e/get-app-fn-args ft-whnf)
                                field-ret-indices (when (and (seq indices)
                                                            (>= (count ft-args) num-params))
                                                   (subvec (vec ft-args) num-params))
                                ih-type (if (seq field-ret-indices)
                                          (e/instantiate motive-body
                                                         (conj (vec field-ret-indices) fv))
                                          (e/instantiate1 motive-body fv))
                                ih-name (str "ih_" fname)
                                lctx'' (red/lctx-add-local lctx' ih-id ih-name ih-type)]
                            [ps'' lctx'' [ih-id]])
                          [ps' lctx' []])]
                    (recur ps''
                           (conj ctor-fvars fid)
                           (into ih-fvars new-ih-fvars)
                           lctx'' (e/instantiate1 (e/forall-body t) fv)))
                  [ps ctor-fvars ih-fvars lctx t]))
              ;; all-fvars: fields first, then IHs (matching recursor order)
              all-fvars (into (vec ctor-fvars) ih-fvar-ids)
              ;; Build ctor applied to params and ONLY field fvars (not IH)
              ctor-term (reduce e/app
                                (e/const' ctor-name ind-levels)
                                (concat params (map e/fvar ctor-fvars)))
              ;; For indexed families, extract return indices from ctor return type
              ctor-ret-indices (when (seq indices)
                                 (let [[_ ret-args] (e/get-app-fn-args ctor-ret-type)]
                                   (when (>= (count ret-args) num-params)
                                     (subvec (vec ret-args) num-params))))
              branch-goal-type (if (seq ctor-ret-indices)
                                 (e/instantiate motive-body
                                                (conj (vec ctor-ret-indices) ctor-term))
                                 (e/instantiate1 motive-body ctor-term))
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
   Lean 4 substCore builds the motive from the GOAL TYPE, which after revert
   includes all dependent hypothesis types. We achieve the same by directly
   building the motive from the goal type (which contains the foralls from
   unresolved equalities), without revert+intro (which creates fvar mismatches)."
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
        ;; new-goal-type and new-lctx computed AFTER dependent-fids (see below)
        placeholder-for-goal-type nil
        placeholder-for-new-lctx nil
        ;; Build the Eq.ndrec term at tactic time (Lean 4 substCore pattern).
        eq-type (nth args 0)
        eq-level (first (e/const-levels head))
        goal-sort (try (tc/infer-type st (:type goal)) (catch Exception _ nil))
        goal-sort-whnf (when goal-sort (whnf-in-goal ps (:lctx goal) goal-sort))
        motive-level (if (and goal-sort-whnf (e/sort? goal-sort-whnf))
                       (e/sort-level goal-sort-whnf)
                       lvl/zero)
        var-decl (red/lctx-lookup (:lctx goal) var-id)
        var-type (or (:type var-decl) eq-type)
        ;; Find SIMPLE dependent hypotheses (following Lean 4 substCore revert pattern).
        ;; Only include hypotheses whose type directly references var-id AND whose head
        ;; is a constant (like ValidRB), not a lambda application (like IH motive apps).
        ;; This avoids picking up complex IH types from the recursor minor.
        dependent-fids
        (vec (sort (for [[fid d] (:lctx goal)
                         :when (and (not= fid var-id) (not= fid hyp-fvar-id)
                                    (= :local (:tag d))
                                    (e/has-fvar-flag (:type d))
                                    (not= (e/abstract1 (:type d) var-id) (:type d))
                                    ;; Include hypotheses that depend on the variable
                                    ;; (Lean 4 substCore reverts ALL dependents)
                                    true)]
                     fid)))
        ;; Build enlarged goal type that includes dependent hypotheses
        enlarged-type
        (if (empty? dependent-fids)
          (:type goal)
          (reduce (fn [body fid]
                    (let [d (red/lctx-lookup (:lctx goal) fid)]
                      (e/forall' (or (:name d) "x") (:type d) (e/abstract1 body fid) :default)))
                  (:type goal)
                  (reverse dependent-fids)))
        ;; Compute goal type and lctx, incorporating dependents
        simple-goal-type (e/instantiate1 (e/abstract1 (:type goal) var-id) replacement)
        remove-set (into #{var-id hyp-fvar-id} dependent-fids)
        new-lctx (reduce (fn [lctx [fid decl]]
                           (if (remove-set fid)
                             lctx
                             (assoc lctx fid
                                    (update decl :type
                                            (fn [t] (e/instantiate1 (e/abstract1 t var-id) replacement))))))
                         {} (:lctx goal))
        ;; Child goal type: includes dependents as foralls (with substituted types)
        new-goal-type
        (if (empty? dependent-fids)
          simple-goal-type
          (reduce (fn [body fid]
                    (let [d (red/lctx-lookup (:lctx goal) fid)
                          dep-type (e/instantiate1 (e/abstract1 (:type d) var-id) replacement)]
                      (e/forall' (or (:name d) "x") dep-type (e/abstract1 body fid) :default)))
                  simple-goal-type
                  (reverse dependent-fids)))
        [ps' new-goal-id] (proof/fresh-mvar-replacing ps new-goal-type new-lctx (:id goal))
        ;; Motive: λ z => enlarged-type[z/var-id]
        ;; When there are dependents, the motive captures var-id in hypothesis types too.
        motive (e/lam "z" var-type (e/abstract1 enlarged-type var-id) :default)
        eq-ndrec-name (name/from-string "Eq.ndrec")
        eq-symm-name (name/from-string "Eq.symm")
        v-level (or motive-level lvl/zero)
        u-level (or eq-level (lvl/succ lvl/zero))
        minor (e/mvar new-goal-id)  ;; mvar placeholder — NOT affected by abstract1!
        ;; When there are dependents, the child goal includes ∀ deps, so minor
        ;; already has the right type. No wrapping needed.
        major (if reverse?
                (e/fvar hyp-fvar-id)
                (e/app* (e/const' eq-symm-name [u-level])
                        eq-type (e/fvar var-id) replacement (e/fvar hyp-fvar-id)))
        ndrec-term (e/app* (e/const' eq-ndrec-name [v-level u-level])
                           eq-type replacement motive minor (e/fvar var-id) major)
        ;; Apply the Eq.ndrec result to the actual dependent fvars
        full-term (reduce (fn [t fid] (e/app t (e/fvar fid))) ndrec-term dependent-fids)]
    (let [ps (-> (proof/assign-mvar ps' (:id goal)
                                      {:kind :subst
                                       :full-term full-term
                                       :child-mvar-id new-goal-id
                                       :child new-goal-id})
                  (proof/record-tactic :subst [hyp-fvar-id] (:id goal)))
          ;; Re-intro dependent hypotheses (like Lean 4 substCore line 80)
          ;; The child goal has ∀ deps, Goal; intro each dep to restore them to the lctx
          ps (reduce (fn [ps _] (intro ps)) ps (range (count dependent-fids)))]
      ps)))

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
;; generalizeIndices (for indexed family cases pipeline)
;; ============================================================
;; Following Lean 4 Cases.lean: transforms complex-index cases to
;; simple-index cases + equality hypotheses.
;; Given h : I params j1..jk, builds:
;;   ∀ (j1'..jk') (h' : I params j1'..jk'), j1 = j1' → ... → jk = jk' → Goal
;; Assigns original goal: newGoal j1..jk h rfl..rfl

(defn- generalize-indices
  "Transform goal to add equality hypotheses for indexed family indices.
   Returns {:ps ps' :goal-id new-goal-id :num-eqs k
            :index-fvar-ids [fresh-idx-fvar-ids] :hyp-fvar-id fresh-h-fvar-id
            :orig-indices [original-index-exprs] :orig-hyp-fvar-id hyp-fvar-id
            :eq-fvar-ids [eq-hypothesis-fvar-ids]}."
  [ps hyp-fvar-id]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        st (mk-tc ps (:lctx goal))
        hyp-decl (red/lctx-lookup (:lctx goal) hyp-fvar-id)
        hyp-type (whnf-in-goal ps (:lctx goal) (:type hyp-decl))
        [type-head type-args] (e/get-app-fn-args hyp-type)
        ind-name (e/const-name type-head)
        ^ConstantInfo ind-ci (env/lookup! (:env ps) ind-name)
        ind-levels (e/const-levels type-head)
        num-params (.numParams ind-ci)
        params (subvec (vec type-args) 0 (min num-params (count type-args)))
        orig-indices (subvec (vec type-args) (min num-params (count type-args)))
        num-indices (count orig-indices)
        _ (when (zero? num-indices)
            (tactic-error! "generalize-indices: type has no indices" {:type hyp-type}))

        ;; Infer index types from the inductive type's forall telescope
        ind-type-ci (.type ind-ci)
        index-types
        (loop [t ind-type-ci i 0 ps-rem params idx-types []]
          (if (and (< i num-params) (e/forall? t))
            (recur (e/instantiate1 (e/forall-body t) (nth ps-rem i)) (inc i) ps-rem idx-types)
            ;; Now at the index binders
            (loop [t t idx-types idx-types]
              (if (e/forall? t)
                (let [it (e/forall-type t)]
                  (recur (e/instantiate1 (e/forall-body t) (e/sort' lvl/zero)) ;; placeholder
                         (conj idx-types it)))
                idx-types))))

        ;; Compute Eq level from index type sorts
        eq-levels
        (mapv (fn [idx-type]
                (let [idx-sort (try (tc/infer-type st idx-type) (catch Exception _ nil))]
                  (if (and idx-sort (e/sort? (whnf-in-goal ps (:lctx goal) idx-sort)))
                    (e/sort-level (whnf-in-goal ps (:lctx goal) idx-sort))
                    (lvl/succ lvl/zero))))
              index-types)

        ;; Allocate fresh fvars for indices, major, and equalities
        ;; 1. Fresh index fvars j1'..jk'
        [ps index-fvar-ids index-types-inst]
        (loop [ps ps i 0 fids [] types []]
          (if (>= i num-indices)
            [ps fids types]
            (let [[ps' fid] (proof/alloc-id ps)
                  ;; Index type may depend on previous indices — instantiate with fresh fvars
                  it (nth index-types i)
                  it (reduce (fn [t [j fid2]]
                               (e/instantiate1 (e/abstract1 t (+ j 999999)) (e/fvar fid2)))
                             it (map vector (range i) fids))]
              (recur ps' (inc i) (conj fids fid) (conj types it)))))

        ;; 2. Fresh major fvar h' : I params j1'..jk'
        [ps h-fid] (proof/alloc-id ps)
        h-type (reduce e/app (e/const' ind-name ind-levels)
                       (concat params (mapv e/fvar index-fvar-ids)))

        ;; 3. Equality fvars: ji = ji' for each index
        [ps eq-fvar-ids eq-types]
        (loop [ps ps i 0 eqfids [] eqtypes []]
          (if (>= i num-indices)
            [ps eqfids eqtypes]
            (let [[ps' eqfid] (proof/alloc-id ps)
                  idx-type (nth index-types-inst i)
                  eq-level (nth eq-levels i)
                  ;; Equality direction: original = fresh
                  ;; After cases + injection, field eqs are orig=fresh.
                  ;; Subst eliminates orig (lhs), replacing with fresh.
                  ;; This makes the motive non-constant when the goal references
                  ;; the original var, allowing Eq.ndrec to properly transport.
                  eq-type (e/app* (e/const' (name/from-string "Eq") [eq-level])
                                  idx-type
                                  (nth orig-indices i)
                                  (e/fvar (nth index-fvar-ids i)))]
              (recur ps' (inc i) (conj eqfids eqfid) (conj eqtypes eq-type)))))

        ;; Build new goal type:
        ;; ∀ (j1':I1) ... (jk':Ik) (h':IndType j1'..jk'), eq1 → ... → eqk → Goal
        ;; Build from inside out, abstracting the fresh fvars
        all-fvar-ids (into (vec index-fvar-ids) [h-fid])
        new-goal-type
        (let [;; Start with Goal, abstract eq fvars as foralls
              body (reduce (fn [body i]
                             (let [eqt (nth eq-types (- num-indices i 1))
                                   eqfid (nth eq-fvar-ids (- num-indices i 1))]
                               (e/forall' "heq" eqt (e/abstract1 body eqfid) :default)))
                           (:type goal) (range num-indices))
              ;; Abstract h'
              body (e/forall' "h" h-type (e/abstract1 body h-fid) :default)
              ;; Abstract index fvars (from innermost to outermost)
              body (loop [i (dec num-indices) body body]
                     (if (< i 0) body
                         (let [fid (nth index-fvar-ids i)
                               it (nth index-types-inst i)]
                           (recur (dec i) (e/forall' "idx" it (e/abstract1 body fid) :default)))))]
          body)

        ;; Build new lctx: remove the original hypothesis
        new-lctx (dissoc (:lctx goal) hyp-fvar-id)

        [ps new-goal-id] (proof/fresh-mvar-replacing ps new-goal-type new-lctx (:id goal))

        ;; Build assignment term: newGoal j1..jk h rfl..rfl
        eq-refl-name (name/from-string "Eq.refl")
        rfl-proofs (mapv (fn [i]
                           (e/app* (e/const' eq-refl-name [(nth eq-levels i)])
                                   (nth index-types-inst i)
                                   (nth orig-indices i)))
                         (range num-indices))]

    (let [ps (-> (proof/assign-mvar ps (:id goal)
                                      {:kind :generalize-indices
                                       :child new-goal-id
                                       :orig-indices orig-indices
                                       :orig-hyp-fvar-id hyp-fvar-id
                                       :index-fvar-ids index-fvar-ids
                                       :hyp-fvar-id h-fid
                                       :eq-fvar-ids eq-fvar-ids
                                       :eq-levels eq-levels
                                       :index-types index-types-inst
                                       :rfl-proofs rfl-proofs})
                  (proof/record-tactic :generalize-indices [hyp-fvar-id] (:id goal)))]
      {:ps ps
       :goal-id new-goal-id
       :num-eqs num-indices
       :index-fvar-ids index-fvar-ids
       :hyp-fvar-id h-fid
       :orig-indices orig-indices
       :orig-hyp-fvar-id hyp-fvar-id
       :eq-fvar-ids eq-fvar-ids})))

;; ============================================================
;; unifyCasesEqs (solve equality hypotheses after cases)
;; ============================================================
;; After generalizeIndices + cases, each branch has equalities like:
;; node c l k r = leaf (impossible) or node c l k r = node c' l' k' r' (decompose)

(defn- unify-eq
  "Process one equality hypothesis in a cases branch.
   Returns {:ps ps' :status :solved/:continue :num-new-eqs n}.
   :solved means the branch is impossible (goal closed).
   :continue means the equality was resolved (via subst, injection, or clear)."
  [ps eq-fvar-id]
  (let [goal (proof/current-goal ps)
        st (mk-tc ps (:lctx goal))
        eq-decl (red/lctx-lookup (:lctx goal) eq-fvar-id)
        eq-type (whnf-in-goal ps (:lctx goal) (:type eq-decl))
        [head args] (e/get-app-fn-args eq-type)
        _ (when-not (and (e/const? head)
                         (= (e/const-name head) (name/from-string "Eq"))
                         (= 3 (count args)))
            (tactic-error! "unify-eq: not an equality" {:type eq-type}))
        alpha (nth args 0)
        lhs (nth args 1)
        rhs (nth args 2)
        lhs-whnf (whnf-in-goal ps (:lctx goal) lhs)
        rhs-whnf (whnf-in-goal ps (:lctx goal) rhs)]

    (cond
      ;; Case 1: fvar = expr or expr = fvar → subst
      (e/fvar? lhs-whnf)
      {:ps (subst ps eq-fvar-id) :status :continue :num-new-eqs 0}

      (e/fvar? rhs-whnf)
      {:ps (subst ps eq-fvar-id) :status :continue :num-new-eqs 0}

      ;; Case 2: defEq a b → clear the equality
      (tc/is-def-eq st lhs-whnf rhs-whnf)
      {:ps (clear ps eq-fvar-id) :status :continue :num-new-eqs 0}

      ;; Case 3: ctor_i args = ctor_j args' → use noConfusion
      :else
      (let [[lhs-head lhs-args] (e/get-app-fn-args lhs-whnf)
            [rhs-head rhs-args] (e/get-app-fn-args rhs-whnf)]
        (if (and (e/const? lhs-head) (e/const? rhs-head))
          (let [lhs-name (e/const-name lhs-head)
                rhs-name (e/const-name rhs-head)
                ;; Look up noConfusion for the type
                [alpha-head alpha-args] (e/get-app-fn-args alpha)
                _ (when-not (e/const? alpha-head)
                    (tactic-error! "unify-eq: cannot determine inductive type" {:alpha alpha}))
                ind-name (e/const-name alpha-head)
                nc-name (name/mk-str ind-name "noConfusion")
                nc-ci (env/lookup (:env ps) nc-name)
                _ (when-not nc-ci
                    (tactic-error! (str "unify-eq: " (name/->string nc-name) " not found") {}))
                ;; Compute goal sort level
                goal-sort (try (tc/infer-type st (:type goal)) (catch Exception _ nil))
                goal-sort-whnf (when goal-sort (whnf-in-goal ps (:lctx goal) goal-sort))
                motive-level (if (and goal-sort-whnf (e/sort? goal-sort-whnf))
                               (e/sort-level goal-sort-whnf)
                               lvl/zero)
                ;; noConfusion levels: [v, ...ind-levels]
                ind-levels (e/const-levels alpha-head)
                nc-levels (into [motive-level] ind-levels)
                ;; Different constructors → noConfusion closes the goal
                ;; noConfusion.{v,...} {params} {P} {a} {b} h : noConfusionType P a b
                ;; For diff ctors: noConfusionType P a b = P (= goal type)
                ;; So noConfusion h : P directly!
                nc-term (e/app* (e/const' nc-name nc-levels)
                                ;; {params} (implicit, inferred)
                                ;; {P} (implicit = goal type)
                                ;; {a} {b} (implicit = lhs, rhs)
                                ;; h = eq-fvar
                                (e/fvar eq-fvar-id))]
            (if (not= lhs-name rhs-name)
              ;; Different constructors: noConfusion closes the goal
              (let [;; Apply noConfusion: need to supply implicit args
                    ;; noConfusion {params} {P} {a} {b} h
                    ^ConstantInfo ind-ci (env/lookup! (:env ps) ind-name)
                    num-params (.numParams ind-ci)
                    ind-params (subvec (vec alpha-args) 0 (min num-params (count alpha-args)))
                    nc-full (reduce e/app
                                    (e/const' nc-name nc-levels)
                                    (concat ind-params
                                            [(:type goal) lhs rhs (e/fvar eq-fvar-id)]))]
                ;; Assign goal directly with the noConfusion proof
                {:ps (-> (proof/assign-mvar ps (:id goal)
                                            {:kind :exact :term nc-full})
                         (proof/record-tactic :injection-solved [eq-fvar-id] (:id goal)))
                 :status :solved :num-new-eqs 0})

              ;; Same constructor: noConfusion gives continuation type
              ;; noConfusionType P (ctor args) (ctor args') = (a1=a1' → ... → P) → P
              ;; noConfusion h : (a1=a1' → ... → P) → P
              ;; We derive the continuation type from noConfusion's actual type (principled).
              (let [^ConstantInfo ind-ci (env/lookup! (:env ps) ind-name)
                    ^ConstantInfo lhs-ctor-ci (env/lookup! (:env ps) lhs-name)
                    num-params (.numParams ind-ci)
                    n-ctor-fields (.numFields lhs-ctor-ci)
                    ind-params (subvec (vec alpha-args) 0 (min num-params (count alpha-args)))
                    nc-full (reduce e/app
                                    (e/const' nc-name nc-levels)
                                    (concat ind-params
                                            [(:type goal) lhs rhs (e/fvar eq-fvar-id)]))
                    ;; Infer nc-full's type and WHNF to get (cont-type → P) → P
                    ;; Then extract cont-type from the forall domain
                    nc-full-type (tc/infer-type st nc-full)
                    nc-full-type-whnf (whnf-in-goal ps (:lctx goal) nc-full-type)
                    ;; nc-full-type-whnf should be: ∀ (_ : cont-type → P), P
                    ;; i.e., a forall whose domain is (cont-type → P) and body is P
                    ;; Extract the domain (which is the continuation type including → P)
                    cont-with-p (when (e/forall? nc-full-type-whnf)
                                  (e/forall-type nc-full-type-whnf))
                    ;; cont-with-p = f1=g1 → ... → fn=gn → P
                    ;; This is exactly the continuation type we need
                    cont-type (or cont-with-p (:type goal))
                    [ps' cont-goal-id] (proof/fresh-mvar-replacing ps cont-type (:lctx goal) (:id goal))]
                ;; Assign original goal: noConfusion h cont-proof
                ;; nc-full : (a1=a1' → ... → P) → P
                ;; cont-proof : a1=a1' → ... → P
                {:ps (-> (proof/assign-mvar ps' (:id goal)
                                            {:kind :apply
                                             :head nc-full
                                             :arg-mvars [cont-goal-id]})
                         (proof/record-tactic :injection-decompose [eq-fvar-id] (:id goal)))
                 :status :continue :num-new-eqs n-ctor-fields})))
          ;; Not constructor-headed: can't solve
          (tactic-error! "unify-eq: cannot solve equality" {:lhs lhs-whnf :rhs rhs-whnf}))))))

(defn- unify-cases-eqs
  "Solve all equality hypotheses in a cases branch.
   Repeatedly intros and solves equalities.
   Returns updated ps (goals may be closed for impossible branches)."
  [ps num-eqs]
  (loop [ps ps remaining num-eqs]
    (if (<= remaining 0)
      ps
      ;; Intro the next equality hypothesis
      (let [ps (intro ps)
            goal (proof/current-goal ps)]
        (if-not goal
          ps  ;; All goals closed
          (let [;; Find the most recently introduced fvar (last in lctx)
                eq-fvar-id (last (sort (keys (:lctx goal))))
                result (unify-eq ps eq-fvar-id)]
            (case (:status result)
              :solved (:ps result)  ;; Impossible branch closed
              :continue (recur (:ps result)
                               (+ (dec remaining) (:num-new-eqs result))))))))))

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
      (let [[ps' new-id] (proof/fresh-mvar-replacing ps reduced (:lctx goal) (:id goal))]
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
                           ;; WHNF the unfolded result immediately (beta + iota)
                           (#'tc/cached-whnf st (reduce e/app val args)))
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
        [ps' new-id] (proof/fresh-mvar-replacing ps new-goal-type-reduced (:lctx goal) (:id goal))]
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
        [ps' false-goal-id] (proof/fresh-mvar-replacing ps' (:type goal) lctx-false (:id goal))
        [ps' h-true-id] (proof/alloc-id ps')
        lctx-true (red/lctx-add-local (:lctx goal) h-true-id "hc" (eq-type bool-true))
        [ps' true-goal-id] (proof/fresh-mvar-replacing ps' (:type goal) lctx-true (:id goal))
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
                    (let [discr (nth args 3)]
                      ;; Only consider discriminants without loose bvars —
                      ;; discriminants inside lambda bodies reference bound
                      ;; variables that can't be case-split on.
                      (when-not (e/has-loose-bvars? discr)
                        (let [dw (try (whnf-in-goal ps goal-lctx discr) (catch Exception _ discr))]
                          (when-not (and (e/const? dw)
                                         (let [n (name/->string (e/const-name dw))]
                                           (or (= n "Bool.true") (= n "Bool.false"))))
                            (vreset! result discr)))))))
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
