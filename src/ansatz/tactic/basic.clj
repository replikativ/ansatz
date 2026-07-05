;; Tactic layer — core tactics.

(ns ansatz.tactic.basic
  "Core tactics: intro, intros, exact, refine, specialize, change, show, assumption, apply, rfl, constructor,
   cases, induction, rewrite, have-tac, replace-tac, revert, exfalso, subst, clear.
   Tactic combinators: try-tac, or-else, repeat-tac, all-goals.
   Each tactic is a pure function: (tactic ps ...args) → ps'."
  (:require [clojure.set]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta :as meta]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.elab-term :as telab]
            [ansatz.tactic.instance :as inst]
            [ansatz.config :as config])
  (:import [ansatz.kernel ConstantInfo]))

(defn- tactic-error! [msg data]
  (throw (ex-info (str "Tactic error: " msg) (merge {:kind :tactic-error} data))))

;; Forward declarations for mutually-dependent tactics/helpers
(declare generalize-indices unify-cases-eqs unify-eq revert match-expr try-clear)

(defn- mk-tc
  "Create a TC state from the proof state and a goal's local context."
  [ps lctx]
  (tc/attach-lctx (tc/mk-tc-state (:env ps)) lctx))

(defn- meta-whnf-in-goal
  "WHNF reduce an expression while consulting the proof state's metacontext."
  [ps goal-lctx expr]
  (let [st (mk-tc ps goal-lctx)]
    (meta/whnf (:meta-mctx ps) st expr)))

(defn- whnf-in-goal
  "WHNF reduce an expression in the context of a goal. Expressions mentioning
   metavariables route through the metacontext-aware reducer; the mvar-free
   common case stays on the kernel path."
  [ps goal-lctx expr]
  (if (and (:meta-mctx ps) (meta/has-expr-mvar? expr))
    (meta-whnf-in-goal ps goal-lctx expr)
    (let [st (mk-tc ps goal-lctx)]
      (#'tc/cached-whnf st expr))))

(defn- infer-in-goal
  "Infer a type in a goal context, consulting the metacontext when the
   expression mentions metavariables (kernel `tc/infer-type` throws on mvars)."
  [ps goal-lctx expr]
  (let [st (mk-tc ps goal-lctx)]
    (if (and (:meta-mctx ps) (meta/has-expr-mvar? expr))
      (meta/infer-type (:meta-mctx ps) st expr)
      (tc/infer-type st expr))))

(defn- declare-level-mvars
  "Declare any undeclared universe metavariables occurring in `exprs` so a
   following `meta/is-def-eq` can assign them (the deleted legacy bridge did
   this scan when building its context)."
  [mctx exprs]
  (reduce (fn [m expr]
            (reduce (fn [m lid]
                      (if (contains? (:level-depth m) lid)
                        m
                        (meta/add-level-mvar-decl m lid)))
                    m
                    (meta/unassigned-level-mvars m expr)))
          mctx
          exprs))

(defn- defeq-in-goal
  "Definitional equality in a goal context. Returns an updated proof state on
   success (metavariable assignments installed, solved goals pruned) and nil
   on failure. Mvar-free inputs stay on the kernel path (kernel `tc/is-def-eq`
   is silently false on distinct mvars)."
  [ps goal-lctx a b]
  (let [st (mk-tc ps goal-lctx)]
    (if (and (:meta-mctx ps)
             (or (meta/has-expr-mvar? a) (meta/has-expr-mvar? b)))
      (when-let [mctx' (meta/is-def-eq (:meta-mctx ps) st a b)]
        (-> ps
            (assoc :meta-mctx mctx')
            (proof/prune-solved-goals)))
      (when (tc/is-def-eq st a b) ps))))

(defn- instantiate-solved-mvars
  "Instantiate solved proof-state holes in `expr` through the metacontext."
  [ps expr]
  (if (meta/has-expr-mvar? expr)
    (meta/zonk-expr (:meta-mctx ps) expr)
    expr))

(defn- collect-fvar-ids
  "Every fvar id occurring in `e`. Used to find the proof mvars (fvar-encoded) that a goal type
   mentions — Lean's `getMVars`."
  [e]
  (let [acc (java.util.HashSet.)]
    (letfn [(go [e]
                (when (e/has-fvar-flag e)
                  (case (e/tag e)
                    :fvar   (.add acc (e/fvar-id e))
                    :app    (do (go (e/app-fn e)) (go (e/app-arg e)))
                    :lam    (do (go (e/lam-type e)) (go (e/lam-body e)))
                    :forall (do (go (e/forall-type e)) (go (e/forall-body e)))
                    :let    (do (go (e/let-type e)) (go (e/let-value e)) (go (e/let-body e)))
                    :proj   (go (e/proj-struct e))
                    :mdata  (go (e/mdata-expr e))
                    nil)))]
      (go e))
    (set acc)))

(defn- expr-depends-on-fvar?
  [expr fvar-id]
  (contains? (collect-fvar-ids expr) fvar-id))

(defn- lctx-dependency-on-fvar
  [lctx fvar-id]
  (some (fn [[id decl]]
          (when (and (not= id fvar-id)
                     (or (expr-depends-on-fvar? (:type decl) fvar-id)
                         (when-let [value (:value decl)]
                           (expr-depends-on-fvar? value fvar-id))))
            [id decl]))
        lctx))

(defn- generated-goal-depends-on-others?
  [ps generated-ids id]
  (let [others (disj (set generated-ids) id)
        type (proof/mvar-type ps id)]
    (boolean (or (some others (collect-fvar-ids type))
                 (some others (meta/collect-expr-mvars type))))))

(defn- reorder-generated-goals-nondependent-first
  "Lean's ApplyNewGoals.nonDependentFirst ordering: generated goals whose types
   do not mention another generated goal come before generated goals that do."
  [ps generated-ids]
  (let [[nondeps deps] (reduce (fn [[nondeps deps] id]
                                 (if (generated-goal-depends-on-others? ps generated-ids id)
                                   [nondeps (conj deps id)]
                                   [(conj nondeps id) deps]))
                               [[] []]
                               generated-ids)]
    (into nondeps deps)))

(defn- head-beta
  "Iterated head beta-reduction, matching Lean's `Expr.headBeta` shape without
   delta/iota/proj/zeta reduction."
  [expr]
  (loop [expr expr
         fuel 128]
    (let [[head args] (e/get-app-fn-args expr)]
      (if (and (pos? fuel) (e/lam? head) (seq args))
        (recur (apply e/app*
                      (e/instantiate1 (e/lam-body head) (first args))
                      (rest args))
               (dec fuel))
        expr))))

(defn- zonk-mvar-decl-types
  "Instantiate assigned metavariables inside the declaration types of open
   mvars. Lean calls `headBetaType` on returned apply goals; this is the local
   analogue needed after apply assigns type holes in the metacontext."
  [ps ids]
  (reduce (fn [ps id]
            (if-let [decl (proof/mvar-decl ps id)]
              (let [ty (head-beta (meta/zonk-expr (:meta-mctx ps) (:type decl)))]
                (proof/set-mvar-type ps id ty))
              ps))
          ps
          ids))

(defn- zonk-proof-expr
  "Instantiate assigned metavariables inside `expr`."
  [ps expr]
  (when expr
    (meta/zonk-expr (:meta-mctx ps) expr)))

(defn- assigned-mvar-term
  [ps mvar-id]
  (meta/expr-assignment (:meta-mctx ps) mvar-id))

(defn- try-synthesize-instance-in-context
  "Try instance synthesis using the metavariable's local context first. This is
   the local analogue of Lean's `mvarId.withContext` around `synthInstance`."
  [ps lctx goal-type]
  (let [goal-type (zonk-proof-expr ps goal-type)
        st (mk-tc ps lctx)
        idx (try ((requiring-resolve 'ansatz.core/instance-index))
                 (catch Throwable _ {}))]
    (or (try (inst/synthesize* st (:env ps) idx goal-type 0)
             (catch Throwable _ nil))
        (try (inst/tabled-synthesize st (:env ps) idx goal-type)
             (catch Throwable _ nil))
        (try (let [f (requiring-resolve 'ansatz.core/try-synthesize-instance)]
               (f (:env ps) goal-type idx))
             (catch Throwable _ nil)))))

(defn- assigned-instance-compatible
  "Return an updated proof state when the already-assigned instance mvar is
   definitionally equal to the synthesized instance, otherwise nil."
  [ps lctx mvar-id inst-term]
  (when-let [assigned (assigned-mvar-term ps mvar-id)]
    (let [st (mk-tc ps lctx)
          assigned (zonk-proof-expr ps assigned)
          inst-term (zonk-proof-expr ps inst-term)]
      (try
        (when-let [mctx (meta/is-def-eq (:meta-mctx ps) st assigned inst-term)]
          (assoc ps :meta-mctx mctx))
        (catch Throwable _ nil)))))

(defn- synthesize-apply-instances
  "Lean-shaped `synthAppInstances` for `apply`: synthesize inst-implicit
   telescope metavariables after result-type unification, including assigned
   instance arguments, and retry postponed failures when later synthesis made
   progress."
  ([ps arg-mvars arg-binfos]
   (synthesize-apply-instances ps arg-mvars arg-binfos
                               {:synth-assigned-instances? true
                                :allow-synth-failures? false}))
  ([ps arg-mvars arg-binfos {:keys [synth-assigned-instances?
                                    allow-synth-failures?]}]
   (let [todo (->> (map vector arg-mvars arg-binfos)
                   (filterv (fn [[mvar-id binfo]]
                              (and (= binfo :inst-implicit)
                                   (or synth-assigned-instances?
                                       (not (proof/mvar-assigned? ps mvar-id)))))))]
     (loop [ps ps
            todo todo]
       (if (empty? todo)
         ps
         (let [{:keys [ps postponed first-error progress-after-error?]}
               (reduce
                (fn [{:keys [ps saw-error?] :as acc} [mvar-id _binfo]]
                  (let [decl (proof/mvar-decl ps mvar-id)
                        lctx (:lctx decl)
                        mtype (zonk-proof-expr ps (:type decl))
                        ps (proof/set-mvar-type ps mvar-id mtype)
                        inst-term (try-synthesize-instance-in-context ps lctx mtype)]
                    (if inst-term
                      (let [ps' (if (proof/mvar-assigned? ps mvar-id)
                                  (assigned-instance-compatible ps lctx mvar-id inst-term)
                                  (proof/assign-mvar ps mvar-id
                                                     {:kind :exact :term inst-term}))]
                        (if ps'
                          (-> acc
                              (assoc :ps ps')
                              (cond-> saw-error? (assoc :progress-after-error? true)))
                          (assoc acc
                                 :saw-error? true
                                 :first-error (or (:first-error acc)
                                                  (ex-info "apply: failed to assign synthesized instance"
                                                           {:mvar-id mvar-id
                                                            :type mtype
                                                            :instance inst-term}))
                                 :postponed (conj (:postponed acc) [mvar-id :inst-implicit]))))
                      (assoc acc
                             :saw-error? true
                             :first-error (or (:first-error acc)
                                              (ex-info "apply: failed to synthesize instance implicit argument"
                                                       {:mvar-id mvar-id
                                                        :type mtype}))
                             :postponed (conj (:postponed acc) [mvar-id :inst-implicit])))))
                {:ps ps
                 :postponed []
                 :first-error nil
                 :saw-error? false
                 :progress-after-error? false}
                todo)]
           (cond
             (nil? first-error) ps
             progress-after-error? (recur ps postponed)
             allow-synth-failures? ps
             :else (throw first-error))))))))

(defn- normalize-for-match
  "Recursively normalize an expression enough for tactic-side matching.
   Unlike plain WHNF, this also reduces inside the application spine so
   projection-heavy theorem conclusions can be compared to elaborated goals."
  [ps goal-lctx expr]
  (letfn [(go [expr]
              (let [expr (whnf-in-goal ps goal-lctx expr)]
                (case (e/tag expr)
                  :app (let [nf (go (e/app-fn expr))
                             na (go (e/app-arg expr))
                             rebuilt (if (and (identical? nf (e/app-fn expr))
                                              (identical? na (e/app-arg expr)))
                                       expr
                                       (e/app nf na))]
                         (whnf-in-goal ps goal-lctx rebuilt))
                  :lam (let [nt (go (e/lam-type expr))
                             nb (go (e/lam-body expr))]
                         (if (and (identical? nt (e/lam-type expr))
                                  (identical? nb (e/lam-body expr)))
                           expr
                           (e/lam (e/lam-name expr) nt nb (e/lam-info expr))))
                  :forall (let [nt (go (e/forall-type expr))
                                nb (go (e/forall-body expr))]
                            (if (and (identical? nt (e/forall-type expr))
                                     (identical? nb (e/forall-body expr)))
                              expr
                              (e/forall' (e/forall-name expr) nt nb (e/forall-info expr))))
                  :let (let [nt (go (e/let-type expr))
                             nv (go (e/let-value expr))
                             nb (go (e/let-body expr))
                             rebuilt (if (and (identical? nt (e/let-type expr))
                                              (identical? nv (e/let-value expr))
                                              (identical? nb (e/let-body expr)))
                                       expr
                                       (e/let' (e/let-name expr) nt nv nb))]
                         (whnf-in-goal ps goal-lctx rebuilt))
                  :proj (let [ns (go (e/proj-struct expr))
                              rebuilt (if (identical? ns (e/proj-struct expr))
                                        expr
                                        (e/proj (e/proj-type-name expr) (e/proj-idx expr) ns))]
                          (whnf-in-goal ps goal-lctx rebuilt))
                  :mdata (let [ne (go (e/mdata-expr expr))]
                           (if (identical? ne (e/mdata-expr expr))
                             expr
                             (e/mdata (e/mdata-data expr) ne)))
                  expr)))]
    (go expr)))

(defn- apply-target-compatible?
  "Cheap Lean-style `apply` stopping check: can the current partially-applied
   result type close the target if we stop adding arguments here?"
  [ps goal ty arg-mvars mvar-id-set]
  (let [st (mk-tc ps (:lctx goal))
        resolved-ty (instantiate-solved-mvars ps ty)
        goal-type (:type goal)
        goal-whnf (whnf-in-goal ps (:lctx goal) goal-type)
        resolved-whnf (whnf-in-goal ps (:lctx goal) resolved-ty)]
    (boolean
     (or (match-expr resolved-ty goal-type mvar-id-set)
         (match-expr resolved-ty goal-whnf mvar-id-set)
         (match-expr resolved-whnf goal-type mvar-id-set)
         (match-expr resolved-whnf goal-whnf mvar-id-set)
         ;; Speculative one-mctx isDefEq probe (result discarded — the main
         ;; cascade re-runs matching and commits). Goal mvars stay protected
         ;; by their syntheticOpaque kind.
         (try
           (some? (meta/is-def-eq (declare-level-mvars (:meta-mctx ps)
                                                       [resolved-ty goal-type])
                                  st resolved-ty goal-type))
           (catch Exception _ false))
         (try
           (and (not (meta/has-expr-mvar? resolved-ty))
                (tc/is-def-eq st resolved-ty goal-type))
           (catch Exception _ false))))))

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
                  ;; Pattern is a hole (real mvar, or legacy fvar-encoded) — bind or check
                    (and (e/mvar? p) (contains? mvar-ids (e/mvar-id p)))
                    (let [id (e/mvar-id p)]
                      (if-let [existing (get @subst id)]
                        (when-not (= existing t)
                          (reset! ok false))
                        (swap! subst assoc id t)))

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
                      :mvar (when-not (= (e/mvar-id p) (e/mvar-id t))
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

(declare apply-tac)

(defn- funext-sort-lvl
  "The universe level `u` such that `e : Sort u`, or lvl/zero if not a sort."
  [st e]
  (let [t (try (#'tc/cached-whnf st (tc/infer-type st e)) (catch Throwable _ nil))]
    (if (and t (e/sort? t)) (e/sort-level t) lvl/zero)))

(defn apply-funext
  "One `apply funext` step (Lean's `funext` tactic is `repeat (apply funext; intro)`). Reduces a
   function-equality goal `f = g` (where `f g : ∀x:α, β x`) to `∀x:α, f x = g x` via the `funext`
   axiom. ansatz's generic `apply` can't higher-order-unify funext's dependent `β`, so we build the
   concrete `funext.{u,v} α β f g` from the goal (the same proof term Lean's `apply funext` yields,
   with α/β solved explicitly) and delegate to `apply-tac`."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        gt (whnf-in-goal ps (:lctx goal) (:type goal))
        [hd args] (e/get-app-fn-args gt)]
    (when-not (and (e/const? hd) (= "Eq" (name/->string (e/const-name hd))) (= 3 (count args)))
      (tactic-error! "funext: goal is not an equality `f = g`" {:type gt}))
    (let [T (nth args 0) f (nth args 1) g (nth args 2)
          st (tc/attach-lctx (tc/mk-tc-state (:env ps)) (:lctx goal))
          Tw (#'tc/cached-whnf st T)]
      (when-not (e/forall? Tw)
        (tactic-error! "funext: the equated values are not functions" {:type Tw}))
      (let [alpha (e/forall-type Tw)
            B (e/forall-body Tw)
            nm (e/forall-name Tw)
            beta (e/lam nm alpha B :default)
            u (funext-sort-lvl st alpha)
            ;; β's codomain level: open the binder so a DEPENDENT B infers correctly
            [_ xid] (proof/alloc-id ps)
            st' (tc/attach-lctx (tc/mk-tc-state (:env ps)) (red/lctx-add-local (:lctx goal) xid nm alpha))
            v (funext-sort-lvl st' (e/instantiate1 B (e/fvar xid)))
            partial (e/app* (e/const' (name/from-string "funext") [u v]) alpha beta f g)]
        (apply-tac ps partial)))))

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
        inferred (infer-in-goal ps (:lctx goal) term)
        ps' (defeq-in-goal ps (:lctx goal) inferred (:type goal))]
    (when-not ps'
      (tactic-error! "Type mismatch in exact"
                     {:expected (:type goal) :inferred inferred}))
    (-> (proof/assign-mvar ps' (:id goal) {:kind :exact :term term})
        (proof/record-tactic :exact [:term] (:id goal)))))

(defn exact-form
  "Close the current goal with a surface term elaborated against the target.

   Lean's `exact` rejects fresh unassigned holes instead of turning them into
   subgoals. Use `refine`/`refine'` when holes should remain open."
  [ps form]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        {:keys [ps checked-expr visible-holes]}
        (telab/elab-term-with-holes ps goal form
                                    {:allow-natural-holes? false
                                     :tag-suffix (name/from-string "exact")
                                     :tactic-name "exact"})
        visible-holes (vec visible-holes)]
    (when (seq visible-holes)
      (let [diagnostics (mapv telab/hole-diagnostic visible-holes)]
        (tactic-error! (str "exact: unresolved holes\n"
                            (telab/format-hole-diagnostics diagnostics))
                       {:holes visible-holes
                        :hole-diagnostics diagnostics
                        :hole-count (count diagnostics)})))
    (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term checked-expr})
        (proof/record-tactic :exact [form] (:id goal)))))

(defn refine
  "Refine the current goal using a surface term.

   This mirrors Lean's tactic-side `refine`: elaborate the term against the
   current goal type, assign the goal to the elaborated value, and replace it
   with the new non-natural holes. Natural holes are rejected by default, as in
   Lean's `refine`; pass `{:allow-natural-holes? true}` or use
   `refine-prime` for Lean's `refine'` behavior."
  ([ps form]
   (refine ps form {}))
  ([ps form {:keys [allow-natural-holes?]
             :or {allow-natural-holes? false}}]
   (let [goal (proof/current-goal ps)
         _ (when-not goal (tactic-error! "No goals" {}))
         tag-suffix (name/from-string (if allow-natural-holes? "refine'" "refine"))
         {:keys [ps expr checked-expr visible-ids]}
         (telab/elab-term-with-holes ps goal form
                                     {:allow-natural-holes? allow-natural-holes?
                                      :tag-suffix tag-suffix
                                      :tactic-name "refine"
                                      :natural-hole-hint "use refine' if these holes should become goals"})]
     (cond
       (= checked-expr (e/mvar (:id goal)))
       (-> ps
           (update :goals (fn [gs]
                            (into [(:id goal)]
                                  (concat visible-ids
                                          (remove #{(:id goal)} gs)))))
           (proof/record-tactic :refine [form] (:id goal)))

       (contains? (meta/collect-expr-mvars checked-expr) (:id goal))
       (tactic-error! "refine: value depends on the main goal metavariable"
                      {:mvar-id (:id goal) :value checked-expr})

       :else
         ;; If child goals remain, keep the raw expression because it may carry
         ;; delayed-abstraction metadata needed when those children are solved.
       (let [assignment-expr (if (seq visible-ids) expr checked-expr)
             ps (proof/assign-mvar ps (:id goal) {:kind :exact :term assignment-expr})]
         (-> ps
             (update :goals (fn [gs] (into visible-ids gs)))
             (proof/record-tactic :refine [form] (:id goal))))))))

(defn refine-prime
  "Lean `refine'`: like `refine`, but natural holes become subgoals."
  [ps form]
  (refine ps form {:allow-natural-holes? true}))

;; ============================================================
;; assumption
;; ============================================================

(defn assumption
  "Search the local context for a hypothesis matching the goal type —
   Lean's `findLocalDeclWithType?` (Assumption.lean): isDefEq per hypothesis.
   Goals whose types mention metavariable holes match through the shared
   metacontext, so a hypothesis can determine open holes (e.g. le_trans's
   middle term)."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        lctx (:lctx goal)
        goal-type (:type goal)
        ;; Strategy 1: structural equality (fast, no mvar issues)
        struct-match (some (fn [[id decl]]
                             (when (and (= :local (:tag decl))
                                        (= (:type decl) goal-type))
                               {:fvar-id id}))
                           lctx)
        ;; Strategy 2: one isDefEq per hypothesis in the shared metacontext;
        ;; assignments commit into the returned proof state.
        meta-match (when-not struct-match
                     (some (fn [[id decl]]
                             (when (and (= :local (:tag decl))
                                        (or (meta/has-expr-mvar? goal-type)
                                            (meta/has-expr-mvar? (:type decl))))
                               (when-let [ps' (try (defeq-in-goal ps lctx (:type decl) goal-type)
                                                   (catch Exception _ nil))]
                                 {:fvar-id id :ps ps'})))
                           lctx))
        ;; Strategy 3: Java-TC isDefEq for mvar-free goals — full lazy-delta
        ;; reduction (e.g. a hypothesis spelled through definitions).
        deq-match (when-not (or struct-match meta-match
                                (meta/has-expr-mvar? goal-type))
                    (let [jtc (ansatz.kernel.TypeChecker. (:env ps))
                          _ (.setFuel jtc config/*default-fuel*)
                          _ (doseq [[id decl] lctx]
                              (when (= :local (:tag decl))
                                (.addLocal jtc (long id) (str (:name decl)) (:type decl))))]
                      (some (fn [[id decl]]
                              (when (and (= :local (:tag decl))
                                         (try (.isDefEq jtc (:type decl) goal-type)
                                              (catch Exception _ false)))
                                {:fvar-id id}))
                            lctx)))
        result (or struct-match meta-match deq-match)]
    (when-not result
      (tactic-error! "No matching hypothesis found" {:goal-type (:type goal)}))
    (-> (proof/assign-mvar (or (:ps result) ps) (:id goal)
                           {:kind :assumption :fvar-id (:fvar-id result)})
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
   1. Peel forall binders until the partial conclusion matches the target,
      creating fvars as metavariable placeholders
   2. Match result type against goal via first-order pattern matching
   3. Assign matched fvars, create subgoals for unmatched ones
   4. Substitute solved values into remaining subgoal types"
  [ps term]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        st (mk-tc ps (:lctx goal))
        term-type (meta/infer-type (:meta-mctx ps) st term)]
    ;; Peel forall binders, creating fresh fvars for each argument. As in
    ;; Lean's MVarId.apply, stop early when the partial result type already
    ;; matches the target.
    ;; For inst-implicit params, try to synthesize immediately — this resolves
    ;; projections like LE.0(Preorder.toLE) before they reach matching.
    (loop [ps ps
           ty (meta-whnf-in-goal ps (:lctx goal) term-type)
           arg-mvars []
           arg-binfos []
           mvar-id-set #{}
           implicit-mvars #{}]
      (if (and (e/forall? ty)
               (not (apply-target-compatible? ps goal ty arg-mvars mvar-id-set)))
        (let [param-type (e/forall-type ty)
              binfo (e/forall-info ty)
              ;; Substitute already-resolved holes into the param type
              inst-type (instantiate-solved-mvars ps param-type)
              ;; Lean's apply creates metavariables for ordinary implicit
              ;; parameters and lets result-type unification solve them. Do not
              ;; guess type parameters from goal arguments here: for equality
              ;; goals, the first goal argument is the equality domain, not
              ;; necessarily the theorem's first implicit type parameter.
              inferred-val
              (cond
                ;; Inst-implicit: synthesize
                (= binfo :inst-implicit)
                (try
                  (try-synthesize-instance-in-context ps (:lctx goal) inst-type)
                  (catch Exception _ nil))

                ;; Ordinary implicit value/type params remain apply mvars.
                (#{:implicit :strict-implicit} binfo)
                nil)  ;; leave as mvar
              synthesized inferred-val]
          (if synthesized
            ;; Value inferred/synthesized — create a pre-assigned mvar
            (let [mvar-kind (if (= binfo :inst-implicit) :synthetic :natural)
                  [ps' mvar-id] (proof/fresh-mvar ps inst-type (:lctx goal) {:kind mvar-kind})
                  ps' (proof/assign-mvar ps' mvar-id {:kind :exact :term synthesized})
                  new-ty (e/instantiate1 (e/forall-body ty) synthesized)]
              (recur ps' (meta-whnf-in-goal ps' (:lctx goal) new-ty)
                     (conj arg-mvars mvar-id)
                     (conj arg-binfos binfo)
                     mvar-id-set
                     implicit-mvars))
            ;; Not synthesized — create mvar (for implicit, inst-implicit, AND explicit params).
            ;; Following Lean 4, explicit mvars become subgoals when they remain unsolved.
            ;; Track implicit mvars separately — they won't become visible subgoals.
            (let [mvar-kind (if (= binfo :inst-implicit) :synthetic :natural)
                  [ps' mvar-id] (proof/fresh-mvar ps inst-type (:lctx goal) {:kind mvar-kind})
                  ;; Lean's forallMetaTelescope: the hole is a REAL Expr.mvar in
                  ;; the goal type, so any later isDefEq (exact/assumption/apply)
                  ;; can assign it through the one shared metacontext.
                  new-ty (e/instantiate1 (e/forall-body ty) (e/mvar mvar-id))
                  is-implicit (#{:implicit :strict-implicit :inst-implicit} binfo)]
              (recur ps' (meta-whnf-in-goal ps' (:lctx goal) new-ty)
                     (conj arg-mvars mvar-id)
                     (conj arg-binfos binfo)
                     (conj mvar-id-set mvar-id)
                     (if is-implicit (conj implicit-mvars mvar-id) implicit-mvars)))))
        ;; Phase 2: Match result type against goal.
        ;; Following Lean 4's apply (Apply.lean): use isDefEq as the PRIMARY
        ;; matching mechanism. isDefEq handles WHNF reduction, delta unfolding,
        ;; and def-eq matching in one pass. No structural matching needed.
        ;;
        ;; Strategy A: structural matching (fast path for simple cases)
        ;; Strategy B: Java TC isDefEq (handles def-eq like sorted vs List.rec)
        (let [resolved-ty (instantiate-solved-mvars ps ty)
              goal-whnf (whnf-in-goal ps (:lctx goal) (:type goal))
              resolved-whnf (meta-whnf-in-goal ps (:lctx goal) resolved-ty)
              ;; LAZY: `normalize-for-match` deeply WHNF-normalizes every subnode, which DIVERGES on a
              ;; goal carrying a stuck recursor over a symbolic arg (e.g. `Map.join`'s `group_by` foldl
              ;; over an abstract list — the filter→join pushdown C). Lean never pre-normalizes the goal
              ;; for `apply`; it matches via lazy `isDefEq`. So defer these: they are
              ;; only forced by the normalize-based fallbacks, which run AFTER the isDefEq strategy.
              goal-norm (delay (normalize-for-match ps (:lctx goal) (:type goal)))
              resolved-norm (delay (normalize-for-match ps (:lctx goal) resolved-ty))
              ;; Lean's PRIMARY apply mechanism (Apply.lean:207): ONE
              ;; isDefEq(conclusion, goal) assigning expr- AND level-mvars in
              ;; the proof state's shared metacontext. It whnf's lazily ON
              ;; MISMATCH, so it solves cases the structural cascade can't
              ;; (univ-poly lemmas whose level isn't pinned; subterms needing
              ;; one whnf step) WITHOUT the divergent deep normalize.
              real-mctx (atom (:meta-mctx ps))
              try-real-mctx-isdefeq
              (fn []
                (try
                  (let [mctx0 (declare-level-mvars @real-mctx
                                                   [resolved-ty (:type goal)])]
                    (when-let [mctx (meta/is-def-eq mctx0 st resolved-ty (:type goal))]
                      (reset! real-mctx mctx)
                      {}))
                  (catch Exception _ nil)))
              ;; Strategy A: structural matching (cheap — no normalization)
              subst (or (match-expr resolved-ty (:type goal) mvar-id-set)
                        (match-expr resolved-ty goal-whnf mvar-id-set)
                        (match-expr resolved-whnf (:type goal) mvar-id-set)
                        (match-expr resolved-whnf goal-whnf mvar-id-set)
                        ;; Lean's PRIMARY apply mechanism (Apply.lean:207): ONE
                        ;; isDefEq(conclusion, goal) in the shared metacontext,
                        ;; assigning generated holes, sibling-shared holes, and
                        ;; level mvars together. It whnf's lazily on mismatch,
                        ;; so it never triggers the divergent deep normalize.
                        (try-real-mctx-isdefeq)
                        (match-expr @resolved-norm @goal-norm mvar-id-set)
                        (match-expr @resolved-norm goal-whnf mvar-id-set)
                        (match-expr resolved-whnf @goal-norm mvar-id-set)
                        ;; Strategy B: Java TC isDefEq (Lean 4's primary mechanism).
                        ;; isDefEq on resolved-ty (with assigned mvars substituted)
                        ;; handles cases where heads differ structurally but are def-eq
                        ;; (e.g., sorted(insertSorted ...) vs List.rec ...).
                        ;; The Java TC cannot infer through real Expr.mvar nodes
                        ;; (inferType throws on tag 12) — skip when holes remain.
                        (when-not (or (meta/has-expr-mvar? resolved-ty)
                                      (meta/has-expr-mvar? (:type goal)))
                          (try
                            (let [jtc (ansatz.kernel.TypeChecker. (:env ps))
                                  _ (.setFuel jtc config/*default-fuel*)
                                ;; Register goal's lctx with TC
                                  _ (doseq [[id decl] (:lctx goal)]
                                      (when (= :local (:tag decl))
                                        (.addLocal jtc (long id) (str (:name decl)) (:type decl))))
                                ;; Register unresolved mvars as locals so TC can handle them
                                  _ (doseq [mid arg-mvars]
                                      (when (proof/mvar-open? ps mid)
                                        (.addLocal jtc (long mid) "?mvar" (proof/mvar-type ps mid))))]
                            ;; Following Lean 4: isDefEq is the primary matching mechanism.
                            ;; First, try to resolve remaining mvars by WHNF-matching
                            ;; the resolved type against the goal type. This handles cases
                            ;; like Nat.le vs LE.le where heads differ but are def-eq.
                              (let [;; Collect unresolved mvar fvar-ids
                                    unresolved (set (filter (fn [mid]
                                                              (proof/mvar-open? ps mid))
                                                            arg-mvars))
                                  ;; Try structural extraction on recursively-normalized forms first
                                    deep-subst (atom {})
                                    _ (letfn [(extract [r g]
                                                (cond
                                                  (and (e/fvar? r) (contains? unresolved (e/fvar-id r)))
                                                  (swap! deep-subst assoc (e/fvar-id r) g)
                                                  (and (e/app? r) (e/app? g))
                                                  (do (extract (e/app-fn r) (e/app-fn g))
                                                      (extract (e/app-arg r) (e/app-arg g)))
                                                  :else nil))]
                                        (try (extract @resolved-norm @goal-norm) (catch Exception _ nil))
                                        (try (extract resolved-whnf goal-whnf) (catch Exception _ nil)))
                                  ;; Substitute extracted bindings into resolved-ty
                                    resolved-ty' (reduce (fn [t [mid val]]
                                                           (e/instantiate1 (e/abstract1 t mid) val))
                                                         resolved-ty @deep-subst)
                                    resolved-ty'' (normalize-for-match ps (:lctx goal) resolved-ty')
                                  ;; Now try isDefEq with all mvars resolved
                                    deq (or (.isDefEq jtc resolved-ty'' @goal-norm)
                                            (.isDefEq jtc resolved-ty' (:type goal))
                                          ;; Also try with original (in case extraction was wrong)
                                            (.isDefEq jtc resolved-ty (:type goal)))]
                                (when deq @deep-subst)))
                            (catch Exception _ nil)))
                        ;; Direct equality
                        (when (or (= resolved-ty (:type goal))
                                  (= resolved-ty goal-whnf)
                                  (= @resolved-norm @goal-norm)) {}))]
          (when-not subst
            (tactic-error! (str "apply: result type does not match goal\n"
                                "  result: " (e/->string resolved-ty) "\n"
                                "  goal:   " (e/->string (:type goal)))
                           {:expected (:type goal) :actual resolved-ty :term term}))

          ;; Assign solved mvars from the substitution
          (let [ps (assoc ps :meta-mctx @real-mctx)
                real-term-mvars (meta/expr-mvars-no-delayed (:meta-mctx ps) term)
                ps (zonk-mvar-decl-types ps real-term-mvars)
                ps (reduce (fn [ps mvar-id]
                             (if-let [val (get subst mvar-id)]
                               (proof/assign-mvar ps mvar-id
                                                  {:kind :exact :term val})
                               ps))
                           ps arg-mvars)
                ;; Solved values (subst + isDefEq assignments) live in the ONE
                ;; metacontext: remaining goal types pick them up through
                ;; zonk-on-access and the decl-type zonk below; sibling-shared
                ;; holes (the `trans` middle term etc.) are assigned there
                ;; directly, matching Lean's single-MetavarContext apply.
                ]
            (let [;; The kernel check must see a concrete head: zonk assigned
                  ;; expr- and level-mvars (e.g. `List.Perm.{?lm}`) into it.
                  head-term (meta/zonk-expr (:meta-mctx ps) term)
                  ps (-> (proof/assign-mvar ps (:id goal)
                                            {:kind :apply :head head-term :arg-mvars arg-mvars})
                         (proof/record-tactic :apply [head-term] (:id goal)))
                  ;; Lean 4's apply postprocesses exactly the inst-implicit
                  ;; telescope metavariables with synthAppInstances. It retries
                  ;; postponed synthesis when later instance synthesis made
                  ;; progress, and it checks already-assigned instance mvars too.
                  ps (synthesize-apply-instances ps arg-mvars arg-binfos)
                  ;; Move unsolved EXPLICIT arg-mvars to front of goals (Lean 4: new goals first).
                  ;; Implicit mvars stay in mctx as shared mvars but aren't visible subgoals.
                  ;; They get resolved when explicit subgoals are solved (via assign-mvar propagation).
                  unsolved-args (filterv #(and (not (proof/mvar-assigned? ps %))
                                               (not (contains? implicit-mvars %)))
                                         arg-mvars)
                  unsolved-args (reorder-generated-goals-nondependent-first ps unsolved-args)
                  other-mvar-ids (->> (meta/expr-mvars-no-delayed (:meta-mctx ps)
                                                                  (meta/zonk-expr (:meta-mctx ps) head-term))
                                      (remove (set unsolved-args))
                                      (filterv #(and (proof/mvar-open? ps %)
                                                     (not (contains? implicit-mvars %)))))
                  front (into (vec unsolved-args) other-mvar-ids)
                  front-set (set front)
                  generated-set (set (filterv #(not (proof/mvar-assigned? ps %)) arg-mvars))
                  ps (zonk-mvar-decl-types ps front)
                  ps (proof/tag-untagged-goals ps (:user-name goal)
                                               (name/from-string "apply")
                                               unsolved-args)]
              (-> ps
                  (update :goals (fn [gs]
                                   (into front
                                         (remove #(or (front-set %) (generated-set %)) gs))))
                  ;; holes solved by isDefEq live only in the metacontext;
                  ;; fresh-mvar listed them as goals, so prune (Lean's
                  ;; pruneSolvedGoals after apply).
                  (proof/prune-solved-goals)))))))))

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
          ps' (defeq-in-goal ps (:lctx goal) lhs rhs)]
      (when-not ps'
        (tactic-error! "rfl: sides are not definitionally equal"
                       {:lhs lhs :rhs rhs}))
      (-> (proof/assign-mvar ps' (:id goal)
                             {:kind :rfl :eq-type eq-type :val lhs
                              :levels (e/const-levels head)})
          (proof/record-tactic :rfl [] (:id goal))))))

;; ============================================================
;; constructor
;; ============================================================

(defn constructor
  "Apply the first applicable constructor of the inductive type at the head of
   the goal, matching Lean's `MVarId.constructor`."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        goal-type (whnf-in-goal ps (:lctx goal) (:type goal))
        [head _args] (e/get-app-fn-args goal-type)]
    (when-not (e/const? head)
      (tactic-error! "constructor: goal head is not a constant" {:type goal-type}))
    (let [^ConstantInfo ci (env/lookup! (:env ps) (e/const-name head))]
      (when-not (.isInduct ci)
        (tactic-error! "constructor: goal type is not an inductive" {:type goal-type}))
      (let [ctors (.ctors ci)]
        (when (zero? (alength ctors))
          (tactic-error! "constructor: no constructors" {:type goal-type}))
        (let [ctor-levels (e/const-levels head)]
          (loop [i 0
                 first-error nil]
            (if (< i (alength ctors))
              (let [ctor-term (e/const' (aget ctors i) ctor-levels)]
                (let [attempt (try
                                {:ok? true :ps (apply-tac ps ctor-term)}
                                (catch Exception ex
                                  {:ok? false :error ex}))]
                  (if (:ok? attempt)
                    (:ps attempt)
                    (recur (inc i) (or first-error (:error attempt))))))
              (tactic-error! "constructor: no applicable constructor found"
                             (cond-> {:type goal-type}
                               first-error (assoc :first-error (ex-data first-error)))))))))))

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
           ;; Replace occurrences of lhs in the goal type with motive-fvar (later
           ;; abstract1'd to the motive's bound var). Faithful to Lean's kabstract:
           ;; descend UNDER binders — open each with a fresh fvar (so is-def-eq has the
           ;; binder in context), replace in the opened body, then re-abstract. Without
           ;; this, occurrences under a λ/∀ (e.g. the foldl accumulator, or a Subtype
           ;; predicate) are missed and the resulting Eq.ndrec motive is ill-typed.
           ;; Fresh ids come from st's :next-id, already bumped above the lctx + motive id.
           goal-type-replaced (let [_ (swap! (:next-id st) (fn [v] (max v (inc motive-fvar-id))))
                                    open-binder
                                    (fn [replace-in st nm dom body mk]
                                      (let [d (replace-in st dom)
                                            fid (swap! (:next-id st) inc)
                                            st' (update st :lctx red/lctx-add-local fid nm dom)
                                            b (replace-in st' (e/instantiate1 body (e/fvar fid)))]
                                        (mk d (e/abstract1 b fid))))
                                    replace-in
                                    (fn replace-in [st expr]
                                      (if (try (tc/is-def-eq st expr lhs) (catch Exception _ false))
                                        motive-fvar
                                        (case (e/tag expr)
                                          :app (let [f (replace-in st (e/app-fn expr))
                                                     a (replace-in st (e/app-arg expr))]
                                                 (if (and (identical? f (e/app-fn expr))
                                                          (identical? a (e/app-arg expr)))
                                                   expr
                                                   (e/app f a)))
                                          :lam (open-binder replace-in st (e/lam-name expr)
                                                            (e/lam-type expr) (e/lam-body expr)
                                                            (fn [d b] (e/lam (e/lam-name expr) d b (e/lam-info expr))))
                                          :forall (open-binder replace-in st (e/forall-name expr)
                                                               (e/forall-type expr) (e/forall-body expr)
                                                               (fn [d b] (e/forall' (e/forall-name expr) d b (e/forall-info expr))))
                                          expr)))]
                                (replace-in st (:type goal)))
           motive-body (e/abstract1 goal-type-replaced motive-fvar-id)
           motive (e/lam "x" ty motive-body :default)
           ;; Compute the motive output sort level
           goal-sort (infer-in-goal ps (:lctx goal) (:type goal))
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

(defn rewrite-lemma
  "Rewrite the goal with a possibly ∀-QUANTIFIED Eq proof `term` — an env lemma (`rw [add_assoc]`)
   or a quantified hypothesis (a generalized IH `∀ acc, lhs = rhs`). The ∀-bound parameters are
   instantiated by matching the lemma's LHS (RHS if reverse?) against the first goal subterm via the
   reduction-aware unifier (Lean's `rw`: forallMetaTelescope + kabstract). A concrete Eq proof falls
   straight through to `rewrite`."
  ([ps term] (rewrite-lemma ps term false))
  ([ps term reverse?]
   (let [goal (proof/current-goal ps)
         _ (when-not goal (tactic-error! "No goals" {}))
         st (mk-tc ps (:lctx goal))
         ty (infer-in-goal ps (:lctx goal) term)
         ;; Lean's withNewMCtxDepth: lemma-parameter mvars live at depth+1 in
         ;; the ONE metacontext, so matching cannot assign goal-level holes;
         ;; the bumped context is discarded once the proof is zonked out.
         base-mctx (or (:meta-mctx ps) meta/empty-context)
         mctx (atom (reduce (fn [m lid]
                              (if (contains? (:level-depth m) lid)
                                m
                                (meta/add-level-mvar-decl m lid)))
                            (meta/inc-depth base-mctx)
                            (meta/unassigned-level-mvars base-mctx ty)))
         base (long (+ 50000000 (or (some-> (:next-id st) deref long) 0)))
         ;; forallMetaTelescopeReducing: peel ∀ to fresh metavars (none if already concrete).
         [mvars body] (loop [t ty xs [] i 0]
                        (if (e/forall? t)
                          (let [id (+ base i)
                                _ (swap! mctx meta/add-expr-mvar-decl id
                                         (e/forall-type t) (:lctx goal))]
                            (recur (e/instantiate1 (e/forall-body t) (e/mvar id))
                                   (conj xs (e/mvar id)) (inc i)))
                          [xs t]))
         heq (reduce e/app term mvars)
         [head args] (e/get-app-fn-args body)
         hname (when (e/const? head) (name/->string (e/const-name head)))
         ;; matchEq?: accept Eq or Iff (Lean rewrites Iff via propext → Eq Prop). → [eqT lhs rhs eqProof eqLevels]
         [eqT lhs0 rhs0 eq-proof eq-lvls]
         (cond
           (and (= hname "Eq") (= 3 (count args)))
           [(nth args 0) (nth args 1) (nth args 2) heq (e/const-levels head)]
           (and (= hname "Iff") (= 2 (count args)))
           (let [a (nth args 0) b (nth args 1) L1 (lvl/succ lvl/zero)]
             [(e/sort' lvl/zero) a b
              (e/app* (e/const' (name/from-string "propext") []) a b heq) [L1]])
           :else (tactic-error! "rewrite: lemma is not (∀ …, _ = _ / _ ↔ _)" {:type ty}))]
     (let [pat (if reverse? rhs0 lhs0)   ; match the side we'll FIND in the goal
           found (atom false)
           try-match (fn [e]
                       (try
                         (when-let [m (meta/is-def-eq @mctx st pat e)]
                           (reset! mctx m)
                           true)
                         (catch Exception _ false)))
           scan (fn scan [e]
                  (when-not @found
                    (if (try-match e)
                      (reset! found true)
                      (case (e/tag e)
                        :app (do (scan (e/app-fn e)) (scan (e/app-arg e)))
                        :lam (do (scan (e/lam-type e)) (scan (e/lam-body e)))
                        :forall (do (scan (e/forall-type e)) (scan (e/forall-body e)))
                        :let (do (scan (e/let-value e)) (scan (e/let-body e)))
                        :proj (scan (e/proj-struct e))
                        nil))))]
       (scan (:type goal))
       (when-not @found
         (tactic-error! "rewrite: no subterm of the goal matches the lemma's LHS" {:lemma-type ty}))
       ;; postprocessAppMVars: a param mvar not pinned by the match (e.g. the TYPE S in
       ;; `m : WAddMonoid S`, erased when an accessor reduces to a projection) is recovered by
       ;; unifying each ASSIGNED mvar's solution type against its declared type. Iterate for chains.
       (loop [i 0]
         (when (< i 8)
           (let [before @mctx]
             (doseq [mv mvars]
               (let [id (e/mvar-id mv)
                     sol (meta/expr-assignment @mctx id)]
                 (when sol
                   (let [dty (meta/zonk-expr @mctx (:type (meta/expr-decl @mctx id)))
                         sty (try (meta/infer-type @mctx st (meta/zonk-expr @mctx sol))
                                  (catch Exception _ nil))]
                     (when sty
                       (when-let [m (try (meta/is-def-eq @mctx st dty sty)
                                         (catch Exception _ nil))]
                         (reset! mctx m)))))))
             (when (not= before @mctx) (recur (inc i))))))
       (let [zonk* #(meta/zonk-expr @mctx %)
             eq-proof (zonk* eq-proof)]
         (when (or (meta/has-expr-mvar? eq-proof)
                   (seq (meta/unassigned-level-mvars @mctx eq-proof)))
           (tactic-error! "rewrite: lemma parameters unresolved after matching" {:type ty}))
         ;; Always FORWARD-rewrite: for `<-`, flip with Eq.symm (sidesteps basic/rewrite's
         ;; reverse-motive Eq.ndrec path).
         (if reverse?
           (rewrite ps (e/app* (e/const' (name/from-string "Eq.symm")
                                         (mapv #(meta/zonk-level @mctx %) eq-lvls))
                               (zonk* eqT) (zonk* lhs0) (zonk* rhs0) eq-proof)
                    false)
           (rewrite ps eq-proof false)))))))

;; ============================================================
;; cases (case analysis on an inductive hypothesis)
;; ============================================================

(defn cases
  "Perform case analysis on a hypothesis (fvar) of inductive type.
   Creates one subgoal per constructor."
  [ps hyp-fvar-id]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        ;; Lean refuses to build a motive over a goal with open holes — a
        ;; shared mvar would otherwise be silently pinned across branches.
        _ (when (seq (meta/collect-expr-mvars (:type goal)))
            (tactic-error! "cases: goal type contains unassigned metavariables"
                           {:type (:type goal)}))
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
        goal-sort (infer-in-goal ps (:lctx goal) (:type goal))
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
        ;; Check if noConfusion is available for every complex index type (needed for Path C)
        complex-index-info
        (when has-complex-indices
          (mapv (fn [idx-expr]
                  (let [idx-type (try (tc/infer-type st idx-expr) (catch Exception _ nil))
                        [idx-type-head _] (when idx-type (e/get-app-fn-args idx-type))]
                    {:expr idx-expr
                     :type idx-type
                     :type-head idx-type-head
                     :no-confusion?
                     (when (and idx-type-head (e/const? idx-type-head))
                       (some? (env/lookup (:env ps)
                                          (name/mk-str (e/const-name idx-type-head) "noConfusion"))))}))
                indices))
        has-no-confusion
        (and (seq complex-index-info)
             (every? :no-confusion? complex-index-info))
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

          (if (and has-complex-indices (seq indices) (not has-no-confusion))
            (tactic-error! "cases: complex indexed families require noConfusion support for index equalities"
                           {:hyp hyp-type
                            :indices indices
                            :index-info complex-index-info})
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
                      ;; Dependents: const-headed hypotheses (incl. Eq) that depend on reverted fids.
                      ;; Lean's `MVarId.revert` reverts the major + ALL forward dependents with no type
                      ;; filter; we only skip lambda-headed recursor IHs (handled by the motive).
                        deps (vec (sort (for [[fid d] (:lctx goal)
                                              :when (and (not (revert-set fid))
                                                         (= :local (:tag d))
                                                         (e/has-fvar-flag (:type d))
                                                         (some (fn [rfid]
                                                                 (not= (e/abstract1 (:type d) rfid) (:type d)))
                                                               revert-fids)
                                                      ;; Lean's `MVarId.revert` reverts the major + ALL
                                                      ;; forward dependents (no type filter), so a
                                                      ;; scrutinee-dependent equation like `generalize`'s
                                                      ;; `h : e = x` IS reverted → substituted in the
                                                      ;; branch (the RAWREC case). We only keep the
                                                      ;; const-head guard, which skips the lambda-headed
                                                      ;; recursor IHs (their motive-app types can't be
                                                      ;; cleanly reverted here).
                                                         (let [[h _] (e/get-app-fn-args (:type d))]
                                                           (e/const? h)))]
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
                  ;; abstract index fvars SIMULTANEOUSLY (sequential abstract1 collapses them — see induction)
                  new-major-type-abs (if (seq new-idx-fvar-ids)
                                       (e/abstract-many new-hyp-type new-idx-fvar-ids)
                                       new-hyp-type)
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
                            fname0 (cond
                                     (nil? fname-raw) (str "h" fid)
                                     (string? fname-raw) fname-raw
                                     :else (name/->string fname-raw))
                            ;; Lean freshens constructor-field names on COLLISION (so `cases c` after
                            ;; `induction l` doesn't shadow l's `head`/`tail` — which would confuse
                            ;; simp_all/by-name lookups). Only freshen when the name is already taken,
                            ;; so the common no-collision case keeps the readable ctor-field names.
                            existing (into #{} (keep :name) (vals lctx))
                            fname (if (contains? existing fname0) (str fname0 "_" fid) fname0)
                            lctx' (red/lctx-add-local lctx fid fname ft)]
                        (recur ps' (conj field-fvars fid)
                               lctx' (e/instantiate1 (e/forall-body t) fv)))
                      [ps field-fvars lctx t]))
              ;; For the recursor (not casesOn), add IH fvars for recursive fields.
              ;; The rec minor expects: ∀ fields, ∀ ih_fields, motive(ctor ...).
              ;; IH fvars are included in the minor lambdas during extraction
              ;; but are NOT shown to the user (they don't affect the branch goal).
                  [ps' all-field-fvars new-lctx]
                  (let [rec-tc (mk-tc ps new-lctx)
                        rec-field-ids (filterv
                                       (fn [fid]
                                         (let [ft (:type (red/lctx-lookup new-lctx fid))
                                               ft-whnf (whnf-in-goal ps new-lctx ft)
                                               [fh fargs] (e/get-app-fn-args ft-whnf)]
                                           ;; A field is RECURSIVE only if its type is the SAME
                                           ;; inductive applied to the SAME parameters — not merely
                                           ;; headed by `ind-name`. Otherwise `head : List A` is
                                           ;; misclassified as recursive when eliminating
                                           ;; `List (List A)` (both are `List`-headed), and the IH
                                           ;; `motive head` applies `motive : List(List A)→…` to a
                                           ;; `List A`, producing an ill-typed (kernel-rejected)
                                           ;; minor. Lean's recursor minors only carry IHs for
                                           ;; genuine recursive occurrences (matching params).
                                           (and (e/const? fh) (= (e/const-name fh) ind-name)
                                                (>= (count fargs) num-params)
                                                (every? identity
                                                        (map (fn [fp p]
                                                               (try (tc/is-def-eq rec-tc fp p)
                                                                    (catch Exception _ false)))
                                                             (subvec (vec fargs) 0 num-params)
                                                             params)))))
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
                                    (tactic-error! "cases: encountered impossible indexed branch without equality elimination support"
                                                   {:ctor ctor-name
                                                    :goal-type branch-goal-type
                                                    :indices indices
                                                    :ctor-ret-indices ctor-ret-indices})
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
            (let [;; Build recursor levels. A recursor's level params are the inductive's
                  ;; universes plus — for inductives that eliminate into an arbitrary Sort —
                  ;; the motive universe at the FRONT. Prop-eliminating recursors (e.g.
                  ;; List.Perm.rec) have a FIXED Sort 0 motive, so NO motive universe: their
                  ;; level-param count equals the inductive's. Prepend motive-level only when
                  ;; the recursor actually has that extra param (count > ind-levels).
                  rec-lparams (vec (.levelParams rec-ci))
                  rec-levels (cond
                               (empty? rec-lparams) []
                               (> (count rec-lparams) (count ind-levels)) (into [motive-level] ind-levels)
                               :else (vec ind-levels))]
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
        ;; Lean refuses to build a motive over a goal with open holes — a
        ;; shared mvar would otherwise be silently pinned across branches.
        _ (when (seq (meta/collect-expr-mvars (:type goal)))
            (tactic-error! "induction: goal type contains unassigned metavariables"
                           {:type (:type goal)}))
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
        goal-sort (infer-in-goal ps (:lctx goal) (:type goal))
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
        ;; For indexed families, abstract the index fvars from major-type SIMULTANEOUSLY.
        ;; (A sequential `abstract1` reduce is WRONG: abstract1 replaces fv→bvar0 without shifting
        ;; existing loose bvars, so two indices both become bvar0 — e.g. Perm l1 l2 → Perm #0 #0,
        ;; a degenerate motive. abstract-many uses the same outermost→innermost convention as the
        ;; motive-body abstraction above, so the major binder's type stays Perm #1 #0 = Perm l1 l2.)
        major-type-abs (let [idx-ids (vec (keep (fn [idx] (when (e/fvar? idx) (e/fvar-id idx))) indices))]
                         (if (seq idx-ids) (e/abstract-many major-type idx-ids) major-type))
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
                        [ft-head ft-args] (e/get-app-fn-args ft-whnf)
                        ;; A field is RECURSIVE only if its type IS the inductive being eliminated —
                        ;; same head const AND the same (uniform) PARAMETERS. Checking the head alone
                        ;; is WRONG for nested types: a field `head : List α` of `List (List α)` has
                        ;; head `List` = ind-name but is NOT recursive (List α ≠ List (List α)), so it
                        ;; must not get an induction hypothesis (which would be ill-typed: motive head).
                        is-recursive (and (e/const? ft-head)
                                          (= (e/const-name ft-head) ind-name)
                                          (>= (count ft-args) num-params)
                                          (let [stf (mk-tc ps lctx)]
                                            (every? (fn [[fa pa]] (tc/is-def-eq stf fa pa))
                                                    (map vector (take num-params ft-args) params))))
                        [ps'' lctx'' new-ih-fvars]
                        (if is-recursive
                          (let [[ps'' ih-id] (proof/alloc-id ps')
                                ;; For indexed families, extract indices from the
                                ;; recursive field's type and instantiate motive with them
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
        (let [;; Build recursor levels (see `cases`): prepend the motive universe only when the
              ;; recursor declares more level params than the inductive has universes. Prop-
              ;; eliminating recursors (List.Perm.rec) fix the motive at Sort 0 — no extra param.
              rec-lparams (vec (.levelParams rec-ci))
              rec-levels (cond
                           (empty? rec-lparams) []
                           (> (count rec-lparams) (count ind-levels)) (into [motive-level] ind-levels)
                           :else (vec ind-levels))]
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

(defn- reject-inline-have-holes! [tactic-name visible-holes]
  (when (seq visible-holes)
    (let [diagnostics (mapv telab/hole-diagnostic visible-holes)]
      (tactic-error! (str tactic-name ": unresolved holes\n"
                          (telab/format-hole-diagnostics diagnostics))
                     {:holes visible-holes
                      :hole-diagnostics diagnostics
                      :hole-count (count diagnostics)}))))

(defn- elab-have-proof-with-inferred-type
  [ps proof-form tactic-name]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        {:keys [ps checked-expr visible-holes meta-mctx]}
        (telab/elab-term-with-holes ps goal proof-form
                                    {:expected-type nil
                                     :allow-natural-holes? false
                                     :tag-suffix (name/from-string tactic-name)
                                     :tactic-name tactic-name})
        visible-holes (vec visible-holes)
        _ (reject-inline-have-holes! tactic-name visible-holes)
        st (mk-tc ps (:lctx goal))
        hyp-type (meta/zonk-expr meta-mctx
                                 (meta/infer-type meta-mctx st checked-expr))]
    {:ps ps
     :proof checked-expr
     :type hyp-type}))

(defn have-infer-tac
  "Lean-style `have h := proof`: elaborate `proof` without an expected type,
   infer the asserted local type, then assert/exact it."
  [ps hyp-name proof-form]
  (let [{:keys [ps proof type]} (elab-have-proof-with-inferred-type ps proof-form "have")]
    (exact (have-tac ps hyp-name type) proof)))

(defn- move-goals-to-front
  [ps front]
  (let [front (vec front)
        front-set (set front)]
    (update ps :goals (fn [gs]
                        (into front (remove front-set gs))))))

(defn- clear-focused-goal-if-possible
  [ps goal-id hyp-fvar-id]
  (if-not hyp-fvar-id
    [ps goal-id]
    (let [focused (move-goals-to-front ps [goal-id])
          cleared (try-clear focused hyp-fvar-id)
          ;; `clear` replaces the focused goal in position (fresh-mvar-replacing);
          ;; on failure try-clear returns the state unchanged, so the front
          ;; goal is the focused goal either way.
          child-id (or (first (:goals cleared)) goal-id)]
      [cleared child-id])))

(defn replace-tac
  "Lean-style `replace`: introduce a new hypothesis and try to clear the old
   hypothesis with the same user-facing name from the body goal.

   With no proof, the proof subgoal keeps the old hypothesis available, while
   the body goal is cleared when possible."
  ([ps old-fvar-id hyp-name hyp-type]
   (let [ps-have (have-tac ps hyp-name hyp-type)
         proof-goal-id (first (:goals ps-have))
         body-goal-id (second (:goals ps-have))
         _ (when-not (and proof-goal-id body-goal-id)
             (tactic-error! "replace: failed to create assertion goals" {:name hyp-name}))
         [ps-cleared body-goal-id] (clear-focused-goal-if-possible ps-have body-goal-id old-fvar-id)]
     (-> (move-goals-to-front ps-cleared [proof-goal-id body-goal-id])
         (proof/record-tactic :replace [hyp-name] (:id (proof/current-goal ps))))))
  ([ps old-fvar-id hyp-name hyp-type proof-form]
   (let [goal-id (:id (proof/current-goal ps))
         ps-have (have-tac ps hyp-name hyp-type)
         ps-proof (exact-form ps-have proof-form)
         body-goal-id (first (:goals ps-proof))
         _ (when-not body-goal-id
             (tactic-error! "replace: proof closed all goals unexpectedly" {:name hyp-name}))
         [ps-cleared body-goal-id] (clear-focused-goal-if-possible ps-proof body-goal-id old-fvar-id)]
     (-> (move-goals-to-front ps-cleared [body-goal-id])
         (proof/record-tactic :replace [hyp-name] goal-id)))))

(defn replace-infer-tac
  "Lean-style `replace h := proof`: infer the replacement type from `proof`,
   assert it under the old user-facing name, then try to clear the old local."
  [ps old-fvar-id hyp-name proof-form]
  (let [goal-id (:id (proof/current-goal ps))
        {:keys [ps proof type]} (elab-have-proof-with-inferred-type ps proof-form "replace")
        ps-have (have-tac ps hyp-name type)
        ps-proof (exact ps-have proof)
        body-goal-id (first (:goals ps-proof))
        _ (when-not body-goal-id
            (tactic-error! "replace: proof closed all goals unexpectedly" {:name hyp-name}))
        [ps-cleared body-goal-id] (clear-focused-goal-if-possible ps-proof body-goal-id old-fvar-id)]
    (-> (move-goals-to-front ps-cleared [body-goal-id])
        (proof/record-tactic :replace [hyp-name] goal-id))))

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
        goal-sort (try (infer-in-goal ps (:lctx goal) (:type goal)) (catch Exception _ nil))
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

(defn- false-const? [t]
  (and (e/const? t) (= "False" (name/->string (e/const-name t)))))

(defn contradiction
  "Close the goal from contradictory hypotheses — a faithful SUBSET of Lean 4's
   `MVarId.contradiction` (Meta/Tactic/Contradiction.lean) covering the no-noConfusion paths:
     (1) a hypothesis `h : False`             → `exfalso; exact h`;
     (2) a `¬p` hypothesis paired with `p`    → `exfalso; exact (hneg hpos)` (Lean's mkFalseElim).
   Each hypothesis type is whnf'd, so `¬p` is recognized through its `p → False` unfolding and `p`
   is matched up to def-eq. The constructor-clash / decide / empty-type paths (which need
   noConfusion or `cases`) are intentionally omitted. Throws if nothing fires (Lean throwTacticEx)."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        lctx (:lctx goal)
        st (mk-tc ps lctx)
        whnf (fn [t] (whnf-in-goal ps lctx t))
        locals (filterv (fn [[_ d]] (= :local (:tag d))) (seq lctx))
        false-hyp (some (fn [[id d]] (when (false-const? (whnf (:type d))) id)) locals)]
    (cond
      false-hyp
      (exact (exfalso ps) (e/fvar false-hyp))

      :else
      (let [neg (some (fn [[id d]]
                        (let [w (whnf (:type d))]
                          ;; `¬p` ≡ `p → False`: a non-dependent Pi whose body whnf's to False.
                          (when (and (e/forall? w)
                                     (false-const? (whnf (e/forall-body w)))
                                     (zero? (e/bvar-range (e/forall-body w))))
                            (let [p (e/forall-type w)
                                  hpos (some (fn [[id2 d2]]
                                               (when (and (not= id2 id)
                                                          (try (tc/is-def-eq st (whnf (:type d2)) p)
                                                               (catch Exception _ false)))
                                                 id2))
                                             locals)]
                              (when hpos [id hpos])))))
                      locals)]
        (if neg
          (exact (exfalso ps) (e/app (e/fvar (first neg)) (e/fvar (second neg))))
          (tactic-error! "contradiction: no contradictory hypotheses found" {}))))))

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
        goal-sort (try (infer-in-goal ps (:lctx goal) (:type goal)) (catch Exception _ nil))
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

(defn subst-vars
  "Lean 4 `subst_vars`: repeatedly substitute every hypothesis that is a *variable*
   equality — `h : x = e` or `h : e = x` where `x` is a local fvar that does NOT
   occur in `e` (occurs-check) — until no such hypothesis remains. Each substitution
   reuses `subst`, which reverts/re-intros all dependents (Lean substCore). Robust:
   a candidate that `subst` rejects is skipped, so the loop always terminates."
  [ps]
  (let [eq-name (name/from-string "Eq")
        var-eq? (fn [d]
                  (and (= :local (:tag d))
                       (e/has-fvar-flag (:type d))
                       (let [[h args] (e/get-app-fn-args (:type d))]
                         (and (e/const? h) (= (e/const-name h) eq-name) (= 3 (count args))
                              (let [lhs (nth args 1) rhs (nth args 2)]
                                (or (and (e/fvar? lhs) (= (e/abstract1 rhs (e/fvar-id lhs)) rhs))
                                    (and (e/fvar? rhs) (= (e/abstract1 lhs (e/fvar-id rhs)) lhs))))))))]
    (loop [ps ps, skip #{}, guard 0]
      (if (> guard 500)
        ps
        (let [goal (proof/current-goal ps)
              cand (when goal
                     (some (fn [[fid d]] (when (and (not (skip fid)) (var-eq? d)) fid))
                           (:lctx goal)))]
          (if (nil? cand)
            ps
            (let [ps' (try (subst ps cand) (catch Throwable _ nil))]
              (if ps'
                (recur ps' #{} (inc guard))
                (recur ps (conj skip cand) (inc guard))))))))))

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
        _ (when-let [[dep-id _] (lctx-dependency-on-fvar (:lctx goal) hyp-fvar-id)]
            (tactic-error! "clear: local declaration depends on hypothesis"
                           {:id hyp-fvar-id :dependent-id dep-id}))
        _ (when (expr-depends-on-fvar? (:type goal) hyp-fvar-id)
            (tactic-error! "clear: target depends on hypothesis" {:id hyp-fvar-id}))
        new-lctx (dissoc (:lctx goal) hyp-fvar-id)
        ;; Replace the goal IN POSITION (Lean's MVarId.clear returns the
        ;; replacement goal where the old one was).
        [ps' new-goal-id] (proof/fresh-mvar-replacing ps (:type goal) new-lctx (:id goal))]
    (-> (proof/assign-mvar ps' (:id goal)
                           {:kind :clear
                            :fvar-id hyp-fvar-id
                            :child new-goal-id})
        (proof/record-tactic :clear [hyp-fvar-id] (:id goal)))))

(defn- try-clear
  [ps hyp-fvar-id]
  (try
    (clear ps hyp-fvar-id)
    (catch Exception _
      ps)))

(defn specialize
  "Specialize a local hypothesis application.

   Mirrors Lean's `specialize h a`: elaborate the application without an
   expected type, allow holes in its arguments to become goals, add the
   specialized result as a hypothesis, and try to clear the original
   hypothesis."
  [ps form]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        {:keys [ps expr checked-expr visible-ids]}
        (telab/elab-term-with-holes ps goal form
                                    {:allow-natural-holes? true
                                     :expected-type nil
                                     :tag-suffix (name/from-string "specialize")
                                     :tactic-name "specialize"})
        head (e/get-app-fn checked-expr)
        _ (when-not (e/fvar? head)
            (tactic-error! "'specialize' requires a term whose head is a local hypothesis"
                           {:term checked-expr}))
        hyp-fvar-id (e/fvar-id head)
        hyp-decl (or (red/lctx-lookup (:lctx goal) hyp-fvar-id)
                     (tactic-error! "'specialize' requires a local hypothesis"
                                    {:term checked-expr :head hyp-fvar-id}))
        st (mk-tc ps (:lctx goal))
        specialized-type (->> (meta/infer-type (:meta-mctx ps) st expr)
                              (meta/zonk-expr (:meta-mctx ps)))
        proof-term (if (seq visible-ids) expr checked-expr)
        ps-have (have-tac ps (:name hyp-decl) specialized-type)
        proof-goal-id (first (:goals ps-have))
        body-goal-id (second (:goals ps-have))
        _ (when-not (and proof-goal-id body-goal-id)
            (tactic-error! "specialize: failed to create assertion goals" {:term checked-expr}))
        ps-proof (proof/assign-mvar ps-have proof-goal-id {:kind :exact :term proof-term})
        ps-body (assoc ps-proof :goals
                       (into [body-goal-id]
                             (remove #{body-goal-id} (:goals ps-proof))))
        ps-cleared (try-clear ps-body hyp-fvar-id)
        body-id (first (:goals ps-cleared))
        front (into (vec visible-ids) [body-id])
        front-set (set front)]
    (-> ps-cleared
        (update :goals (fn [gs]
                         (into (vec front) (remove front-set gs))))
        (proof/record-tactic :specialize [form] (:id goal)))))

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

        ;; Infer index types from the inductive type's forall telescope. The inductive's declared
        ;; type is UNIVERSE-POLYMORPHIC (e.g. `List.Mem.{u} : {α : Type u} → α → List.{u} α → Prop`);
        ;; instantiate its level params with the CONCRETE levels from the actual hypothesis
        ;; (`ind-levels`), or the extracted index types (`List.{u} α`) carry an abstract `u` and the
        ;; fresh index var / equality / new-goal terms fail to type-check (Sort 1 vs Sort (u+1)).
        ind-type-ci (e/instantiate-level-params
                     (.type ind-ci)
                     (into {} (map vector (vec (.levelParams ind-ci)) ind-levels)))
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

(defn- assert-hyp
  "Lean `have h : T := proof` at the proof-state level: discharge the have-subgoal with `proof-term`,
   leaving the body goal (with `hyp-name : hyp-type` in scope) the current goal."
  [ps hyp-name hyp-type proof-term]
  (exact (have-tac ps hyp-name hyp-type) proof-term))

(defn- count-head-foralls [t]
  (loop [t t n 0] (if (e/forall? t) (recur (e/forall-body t) (inc n)) n)))

(defn- sort-level-of
  "Universe level `u` such that `expr : Sort u` (the level of expr's type), or `lvl/zero` on failure."
  [ps st lctx expr]
  (let [s (try (whnf-in-goal ps lctx (tc/infer-type st expr)) (catch Exception _ nil))]
    (if (and s (e/sort? s)) (e/sort-level s) lvl/zero)))

(defn- unify-eq
  "Process one equality hypothesis in a cases branch (Lean 4 UnifyEq.lean + injectionCore).
   Returns {:ps ps' :status :solved/:continue :num-new-eqs n}.
   :solved means the branch is impossible (goal closed via noConfusion/False.elim).
   :continue means the equality was resolved (via subst, clear, or constructor injection)."
  [ps eq-fvar-id]
  (let [goal (proof/current-goal ps)
        st (mk-tc ps (:lctx goal))
        lctx (:lctx goal)
        eq-decl (red/lctx-lookup lctx eq-fvar-id)
        eq-type (whnf-in-goal ps lctx (:type eq-decl))
        [head args] (e/get-app-fn-args eq-type)
        hname (when (e/const? head) (name/->string (e/const-name head)))]
    (cond
      ;; HEq α a β b with α ≡ β → convert to a homogeneous `Eq a b` (Lean injectionCore: mkEqOfHEq)
      ;; and recurse. Per-ctor noConfusion produces HEq field equalities even when the field types
      ;; match, so this is the bridge that lets the Eq machinery (subst/injection) consume them.
      (and (= hname "HEq") (= 4 (count args)))
      (let [a-ty (nth args 0) a (nth args 1) b-ty (nth args 2) b (nth args 3)]
        (if (tc/is-def-eq st a-ty b-ty)
          (let [lvl (sort-level-of ps st lctx a-ty)
                eq-proof (e/app* (e/const' (name/from-string "eq_of_heq") [lvl]) a-ty a b (e/fvar eq-fvar-id))
                eq-T (e/app* (e/const' (name/from-string "Eq") [lvl]) a-ty a b)
                ps (assert-hyp ps "heqEq" eq-T eq-proof)
                g2 (proof/current-goal ps)
                new-eq (last (sort (keys (:lctx g2))))]
            (unify-eq ps new-eq))
          (tactic-error! "unify-eq: heterogeneous HEq (types not defeq)" {:type eq-type})))

      (and (= hname "Eq") (= 3 (count args)))
      (let [alpha (nth args 0) lhs (nth args 1) rhs (nth args 2)
            lhs-whnf (whnf-in-goal ps lctx lhs)
            rhs-whnf (whnf-in-goal ps lctx rhs)]
        (cond
          ;; fvar = e / e = fvar → subst
          (e/fvar? lhs-whnf) {:ps (subst ps eq-fvar-id) :status :continue :num-new-eqs 0}
          (e/fvar? rhs-whnf) {:ps (subst ps eq-fvar-id) :status :continue :num-new-eqs 0}
          ;; defEq → clear
          (tc/is-def-eq st lhs-whnf rhs-whnf) {:ps (clear ps eq-fvar-id) :status :continue :num-new-eqs 0}
          ;; ctor … = ctor … → injection / noConfusion
          :else
          (let [[lhs-head lhs-args] (e/get-app-fn-args lhs-whnf)
                [rhs-head rhs-args] (e/get-app-fn-args rhs-whnf)]
            (if (and (e/const? lhs-head) (e/const? rhs-head))
              (let [lhs-name (e/const-name lhs-head)
                    rhs-name (e/const-name rhs-head)
                    same? (= lhs-name rhs-name)
                    [alpha-head alpha-args] (e/get-app-fn-args alpha)
                    _ (when-not (e/const? alpha-head)
                        (tactic-error! "unify-eq: cannot determine inductive type" {:alpha alpha}))
                    ind-name (e/const-name alpha-head)
                    ind-levels (e/const-levels alpha-head)
                    ^ConstantInfo ind-ci (env/lookup! (:env ps) ind-name)
                    num-params (.numParams ind-ci)
                    ind-params (subvec (vec alpha-args) 0 (min num-params (count alpha-args)))
                    motive-level (sort-level-of ps st lctx (:type goal))]
                ;; Two discharge strategies, picked by which aux declarations the type actually has:
                ;;  • FAITHFUL per-ctor / ctorIdx injection (Lean injectionCore / AppBuilder.mkNoConfusion)
                ;;    when the per-constructor `<ctor>.noConfusion` (same ctor) or `<Ind>.ctorIdx` +
                ;;    `noConfusion_of_Nat` (different ctors) exist — IMPORTED parameterized types like List,
                ;;    whose monolithic `<Ind>.noConfusion` is HETEROGENEOUS and unusable as `(params P a b h)`.
                ;;  • MONOLITHIC `<Ind>.noConfusion` `(params)(P)(a)(b)(h)` otherwise — parameterless types
                ;;    (Nat) and ansatz `a/inductive` types, whose generated noConfusion is HOMOGENEOUS.
                ;; Parameterless types always take the monolithic path (it is tested + Eq-direct).
                (let [nc-mono-name (name/mk-str ind-name "noConfusion")
                      perctor-name (name/mk-str lhs-name "noConfusion")
                      ci-name (name/mk-str ind-name "ctorIdx")
                      nc-levels (into [motive-level] ind-levels)
                      optionC? (and (pos? num-params)
                                    (if same?
                                      (some? (env/lookup (:env ps) perctor-name))
                                      (and (some? (env/lookup (:env ps) ci-name))
                                           (some? (env/lookup (:env ps) (name/from-string "noConfusion_of_Nat"))))))]
                  (cond
                    ;; FAITHFUL — different constructors → False.elim P (noConfusion_of_Nat α (ctorIdx params) a b h)
                    (and optionC? (not same?))
                    (let [alpha-lvl (sort-level-of ps st lctx alpha)
                          f (reduce e/app (e/const' ci-name ind-levels) ind-params)
                          noc (e/app* (e/const' (name/from-string "noConfusion_of_Nat") [alpha-lvl])
                                      alpha f lhs rhs (e/fvar eq-fvar-id))
                          fe (e/app* (e/const' (name/from-string "False.elim") [motive-level]) (:type goal) noc)]
                      {:ps (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term fe})
                               (proof/record-tactic :injection-solved [eq-fvar-id] (:id goal)))
                       :status :solved :num-new-eqs 0})

                    ;; FAITHFUL — same ctor → <ctor>.noConfusion params P fields₁ fields₂ [indexEqRefls…] h
                    (and optionC? same?)
                    (let [^ConstantInfo nc-ci (env/lookup (:env ps) perctor-name)
                          ^ConstantInfo lc (env/lookup! (:env ps) lhs-name)
                          nfields (.numFields lc)
                          fields1 (subvec (vec lhs-args) (min num-params (count lhs-args)))
                          fields2 (subvec (vec rhs-args) (min num-params (count rhs-args)))
                          base (reduce e/app (e/const' perctor-name nc-levels)
                                       (concat ind-params [(:type goal)] fields1 fields2))
                          ;; supply the constructor's fixed-index equalities (refl) before `h`
                          arity (count-head-foralls (.type nc-ci))
                          num-ind-eqs (- arity (count ind-params) (* 2 nfields) 3)
                          base+idx
                          (loop [e base k num-ind-eqs]
                            (if (<= k 0) e
                                (let [et (whnf-in-goal ps lctx (tc/infer-type st e))
                                      dom (when (e/forall? et) (whnf-in-goal ps lctx (e/forall-type et)))
                                      [dh dargs] (when dom (e/get-app-fn-args dom))
                                      dn (when (and dh (e/const? dh)) (name/->string (e/const-name dh)))
                                      refl (cond
                                             (= dn "HEq")
                                             (e/app* (e/const' (name/from-string "HEq.refl")
                                                               [(sort-level-of ps st lctx (nth dargs 0))])
                                                     (nth dargs 0) (nth dargs 1))
                                             (= dn "Eq")
                                             (e/app* (e/const' (name/from-string "Eq.refl")
                                                               [(sort-level-of ps st lctx (nth dargs 0))])
                                                     (nth dargs 0) (nth dargs 1))
                                             :else
                                             (tactic-error! "unify-eq: unexpected index-eq arg in per-ctor noConfusion"
                                                            {:dom dom}))]
                                  (recur (e/app e refl) (dec k)))))
                          nc-full (e/app base+idx (e/fvar eq-fvar-id))
                          nct (whnf-in-goal ps lctx (tc/infer-type st nc-full))
                          cont-type (if (e/forall? nct) (e/forall-type nct) (:type goal))
                          [ps' cg] (proof/fresh-mvar-replacing ps cont-type lctx (:id goal))]
                      {:ps (-> (proof/assign-mvar ps' (:id goal) {:kind :apply :head nc-full :arg-mvars [cg]})
                               (proof/record-tactic :injection-decompose [eq-fvar-id] (:id goal)))
                       :status :continue :num-new-eqs nfields})

                    ;; MONOLITHIC fallback (homogeneous <Ind>.noConfusion) — Nat + ansatz a/inductive types.
                    :else
                    (let [_ (when-not (env/lookup (:env ps) nc-mono-name)
                              (tactic-error! (str "unify-eq: " (name/->string nc-mono-name)
                                                  " not found (and no per-ctor/ctorIdx aux)") {}))
                          nc-full (reduce e/app (e/const' nc-mono-name nc-levels)
                                          (concat ind-params [(:type goal) lhs rhs (e/fvar eq-fvar-id)]))]
                      (if-not same?
                        {:ps (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term nc-full})
                                 (proof/record-tactic :injection-solved [eq-fvar-id] (:id goal)))
                         :status :solved :num-new-eqs 0}
                        (let [^ConstantInfo lc (env/lookup! (:env ps) lhs-name)
                              nfields (.numFields lc)
                              nct (whnf-in-goal ps lctx (tc/infer-type st nc-full))
                              cont-type (if (e/forall? nct) (e/forall-type nct) (:type goal))
                              [ps' cg] (proof/fresh-mvar-replacing ps cont-type lctx (:id goal))]
                          {:ps (-> (proof/assign-mvar ps' (:id goal) {:kind :apply :head nc-full :arg-mvars [cg]})
                                   (proof/record-tactic :injection-decompose [eq-fvar-id] (:id goal)))
                           :status :continue :num-new-eqs nfields}))))))
              (tactic-error! "unify-eq: cannot solve equality" {:lhs lhs-whnf :rhs rhs-whnf})))))

      :else
      (tactic-error! "unify-eq: not an equality" {:type eq-type}))))

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
  "Close ALL open goals by backtracking depth-first search, faithful to Lean 4's `solveByElim`
   (Lean/Meta/Tactic/SolveByElim + the `backtrack` engine in Backtrack.lean): focus the first goal,
   try each candidate (assumption, then each extra-lemma via `apply`), and for each that succeeds,
   recurse on the remaining goals; if the recursion dead-ends, BACKTRACK and try the next candidate.
   Because proof states are immutable, backtracking is just trying the next branch — no undo needed,
   and metavar assignments made down one branch stay confined to that branch's state.

   This subsumes the old greedy fixpoint: it can pick a `List.Perm.trans` whose middle term is only
   determined by a LATER sibling goal (greedy committed to a wrong middle and got stuck). `max-depth`
   bounds the proof-tree path length; an internal node budget caps total exploration so an unbounded
   `trans`-chain can't run away (it just fails, as before). Order the lemma list with closing lemmas
   first and `trans` last for best pruning. Optional extra-lemmas: vector of Ansatz terms tried via
   `apply` (a bare local-hyp term is fine)."
  ([ps] (solve-by-elim ps 6 []))
  ([ps max-depth] (solve-by-elim ps max-depth []))
  ([ps max-depth extra-lemmas]
   (let [budget (atom 6000)
         ;; Candidate next-states from acting on the FIRST open goal: assumption, then each lemma.
         step (fn [ps']
                (let [gid (first (:goals ps'))
                      psf (assoc ps' :goals (into [gid] (remove #{gid} (:goals ps'))))]
                  (concat
                   (when-let [r (try (assumption psf) (catch Exception _ nil))] [r])
                   (keep (fn [lemma] (try (apply-tac psf lemma) (catch Exception _ nil)))
                         extra-lemmas))))
         search (fn search [ps' depth]
                  (cond
                    (proof/solved? ps') ps'
                    (or (>= depth (max max-depth 8)) (neg? @budget)) nil
                    :else
                    (some (fn [nxt] (swap! budget dec) (search nxt (inc depth)))
                          (step ps'))))]
     (or (search ps 0)
         (tactic-error! "solve_by_elim: could not close all goals"
                        {:remaining (count (:goals ps))})))))

;; ============================================================
;; Convenience tactics — Lean 4 sugar
;; ============================================================

(defn- nth-constructor
  "Lean's `MVarId.nthConstructor`: apply constructor `idx` of the target
   inductive, optionally requiring an exact constructor count."
  [ps tactic-name idx expected-count]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        goal-type (whnf-in-goal ps (:lctx goal) (:type goal))
        [head _args] (e/get-app-fn-args goal-type)]
    (when-not (e/const? head)
      (tactic-error! (str tactic-name ": target is not an inductive datatype")
                     {:type goal-type}))
    (let [^ConstantInfo ci (env/lookup! (:env ps) (e/const-name head))]
      (when-not (.isInduct ci)
        (tactic-error! (str tactic-name ": target is not an inductive datatype")
                       {:type goal-type}))
      (let [ctors (.ctors ci)
            num-ctors (alength ctors)]
        (when (and expected-count (not= num-ctors expected-count))
          (tactic-error! (str tactic-name " tactic works for inductive types with exactly "
                              expected-count " constructors")
                         {:type goal-type :expected expected-count :actual num-ctors}))
        (when-not (< idx num-ctors)
          (tactic-error! (str tactic-name ": constructor index out of bounds")
                         {:type goal-type :index idx :num-constructors num-ctors}))
        (apply-tac ps (e/const' (aget ctors idx) (e/const-levels head)))))))

(defn left
  "Apply constructor 0 of a two-constructor inductive. Lean 4: left."
  [ps]
  (nth-constructor ps "left" 0 2))

(defn right
  "Apply constructor 1 of a two-constructor inductive. Lean 4: right."
  [ps]
  (nth-constructor ps "right" 1 2))

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
        ;; The reduced goal is DEF-EQ to the original (whnf preserves def-eq), so the
        ;; subgoal's proof directly proves the original. Delegate via :simp-reduce with a
        ;; nil eq-proof (extract returns the child proof) — NOT `:exact (fvar new-id)`,
        ;; which would leave the subgoal mvar dangling as an unbound free variable.
        (-> (proof/assign-mvar ps' (:id goal) {:kind :simp-reduce :eq-proof nil :child new-id})
            (proof/record-tactic :whnf [] (:id goal)))))))

(defn- elab-change-pattern
  "Lean's `elabChange`: elaborate `new-type-form` with the type of
   `target-expr` as expected type, then require it to be definitionally equal
   to `target-expr`, while allowing synthetic opaque placeholders to be solved
   by the defeq check."
  [ps goal target-expr new-type-form {:keys [tactic-name tag-suffix]
                                      :or {tactic-name "change"}}]
  (let [st (mk-tc ps (:lctx goal))
        expected-type (infer-in-goal ps (:lctx goal) target-expr)
        tag-suffix (or tag-suffix (name/from-string tactic-name))]
    (telab/elab-term-with-holes
     ps goal new-type-form
     {:allow-natural-holes? false
      :tag-suffix tag-suffix
      :tactic-name tactic-name
      :expected-type expected-type
      :after-elab
      (fn [{:keys [expr meta-mctx]}]
        (let [mctx (meta/with-synthetic-opaque-assignment meta-mctx true)
              expr (meta/zonk-expr mctx expr)]
          (if-let [mctx (meta/is-def-eq mctx st expr target-expr)]
            {:expr (meta/zonk-expr mctx expr)
             :meta-mctx (meta/with-synthetic-opaque-assignment mctx false)}
            (tactic-error! (str "'" tactic-name "' tactic failed")
                           {:pattern expr :target target-expr}))))})))

(defn- change-target*
  [ps new-type-form {:keys [tactic-name record-kind tag-suffix]
                     :or {tactic-name "change"
                          record-kind :change}}]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        {:keys [ps checked-expr visible-ids]}
        (elab-change-pattern ps goal (:type goal) new-type-form
                             {:tactic-name tactic-name
                              :tag-suffix tag-suffix})
        [ps' new-id] (proof/fresh-mvar-replacing ps checked-expr (:lctx goal) (:id goal))
        ps' (-> (proof/assign-mvar ps' (:id goal)
                                   {:kind :simp-reduce :eq-proof nil :child new-id})
                (proof/record-tactic record-kind [new-type-form] (:id goal)))]
    {:ps ps'
     :old-id (:id goal)
     :new-id new-id
     :visible-ids visible-ids}))

(defn change
  "Replace the main target with a definitionally equal target type.

   Target-only version of Lean's `change`: placeholders in `new-type-form` are
   solved by unification against the current target when possible; remaining
   synthetic holes become goals."
  [ps new-type-form]
  (let [{:keys [ps new-id visible-ids]} (change-target* ps new-type-form {})
        front (into [new-id] visible-ids)
        front-set (set front)]
    (update ps :goals (fn [gs]
                        (into (vec front) (remove front-set gs))))))

(defn change-local
  "Replace a local hypothesis type with a definitionally equal type.

   Mirrors Lean's `change newType at h`: the local fvar id is preserved, only
   its declaration type changes in the child goal."
  [ps hyp-fvar-id new-type-form]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        hyp-decl (red/lctx-lookup (:lctx goal) hyp-fvar-id)
        _ (when-not hyp-decl
            (tactic-error! "change: hypothesis not in context" {:id hyp-fvar-id}))
        old-type (:type hyp-decl)
        {:keys [ps checked-expr visible-ids]}
        (elab-change-pattern ps goal old-type new-type-form
                             {:tactic-name "change"
                              :tag-suffix (name/from-string "change")})
        new-lctx (assoc (:lctx goal) hyp-fvar-id (assoc hyp-decl :type checked-expr))
        [ps' new-id] (proof/fresh-mvar-replacing ps (:type goal) new-lctx (:id goal))
        ps' (-> (proof/assign-mvar ps' (:id goal)
                                   {:kind :change-local
                                    :fvar-id hyp-fvar-id
                                    :old-type old-type
                                    :new-type checked-expr
                                    :child new-id})
                (proof/record-tactic :change-local [new-type-form hyp-fvar-id] (:id goal)))
        front (into [new-id] visible-ids)
        front-set (set front)]
    (update ps' :goals (fn [gs]
                         (into (vec front) (remove front-set gs))))))

(defn show
  "Find the first open goal whose target is definitionally equal to `new-type-form`,
   replace that target, and bring the matching goal to the front.

   This mirrors Lean's `show`: it is equivalent to trying `change` on each goal
   in order, then focusing the first match."
  [ps new-type-form]
  (let [goal-ids (vec (:goals ps))
        _ (when (empty? goal-ids) (tactic-error! "No goals" {}))]
    (loop [prev []
           remaining goal-ids
           first-error nil]
      (if (empty? remaining)
        (tactic-error! "'show' tactic failed, no goals unify with the given pattern"
                       (cond-> {:pattern new-type-form}
                         first-error (assoc :first-error (ex-data first-error))))
        (let [gid (first remaining)
              tail (subvec (vec remaining) 1)
              focused-goals (into [gid] (concat prev tail))
              focused (assoc ps :goals focused-goals)
              attempt (try
                        {:ok? true
                         :result (change-target* focused new-type-form
                                                 {:tactic-name "show"
                                                  :record-kind :show
                                                  :tag-suffix (name/from-string "show")})}
                        (catch Exception e
                          {:ok? false :error e}))]
          (if (:ok? attempt)
            (let [{:keys [ps new-id visible-ids]} (:result attempt)
                  front (into [new-id] (concat prev visible-ids tail))
                  front-set (set front)]
              (update ps :goals (fn [gs]
                                  (into (vec front) (remove front-set gs)))))
            (recur (conj prev gid) tail (or first-error (:error attempt)))))))))

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
    ;; The unfolded goal is DEF-EQ to the original (delta + whnf preserve def-eq), so the
    ;; subgoal's proof directly proves the original. Delegate via :simp-reduce with a nil
    ;; eq-proof (extract returns the child proof) — NOT `:exact (fvar new-id)`, which would
    ;; leave the subgoal mvar dangling as an unbound free variable in the extracted term.
    (-> (proof/assign-mvar ps' (:id goal) {:kind :simp-reduce :eq-proof nil :child new-id})
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
        goal-sort (infer-in-goal ps (:lctx goal) (:type goal))
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

(defn cases-eq
  "Faithful `cases h : e` for a Bool discriminant — Lean's substituting case split.

   Unlike `by-cases` (which leaves the goal verbatim and only adds `h : e = b`),
   this GENERALIZES the discriminant `e` out of the goal (kabstract, under binders),
   so each branch carries the LITERAL `true`/`false` in `e`'s positions. Stuck
   `ite`/`cond`/`Bool.rec` on `e` then iota-reduce in that branch. Matches Lean's
   `Meta.Tactic.Generalize` + `cases` pipeline (the `cases hp : q y <;> simp [hp]` idiom).

   Produces:
     Goal 1: h : Eq Bool e true  ⊢ Goal[e := true]
     Goal 2: h : Eq Bool e false ⊢ Goal[e := false]"
  [ps cond-expr hname]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        st (mk-tc ps (:lctx goal))
        cond-type (tc/infer-type st cond-expr)
        cond-type-whnf (whnf-in-goal ps (:lctx goal) cond-type)
        _ (when-not (and (e/const? cond-type-whnf)
                         (= (name/->string (e/const-name cond-type-whnf)) "Bool"))
            (tactic-error! "cases-eq: expression is not Bool"
                           {:type cond-type :expr cond-expr}))
        bool-type (e/const' (name/from-string "Bool") [])
        bool-true (e/const' (name/from-string "Bool.true") [])
        bool-false (e/const' (name/from-string "Bool.false") [])
        eq-type (fn [val] (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                                  bool-type cond-expr val))
        ;; --- kabstract: replace occurrences of cond-expr in the goal with a fresh fvar,
        ;; descending under binders (mirrors the rewrite tactic, basic.clj ~719). ---
        [ps' abs-fvar-id] (proof/alloc-id ps)
        abs-fvar (e/fvar abs-fvar-id)
        goal-replaced (let [_ (swap! (:next-id st) (fn [v] (max v (inc abs-fvar-id))))
                            open-binder
                            (fn [replace-in st nm dom body mk]
                              (let [d (replace-in st dom)
                                    fid (swap! (:next-id st) inc)
                                    st' (update st :lctx red/lctx-add-local fid nm dom)
                                    b (replace-in st' (e/instantiate1 body (e/fvar fid)))]
                                (mk d (e/abstract1 b fid))))
                            replace-in
                            (fn replace-in [st expr]
                              (if (try (tc/is-def-eq st expr cond-expr) (catch Exception _ false))
                                abs-fvar
                                (case (e/tag expr)
                                  :app (let [f (replace-in st (e/app-fn expr))
                                             a (replace-in st (e/app-arg expr))]
                                         (if (and (identical? f (e/app-fn expr))
                                                  (identical? a (e/app-arg expr)))
                                           expr
                                           (e/app f a)))
                                  :lam (open-binder replace-in st (e/lam-name expr)
                                                    (e/lam-type expr) (e/lam-body expr)
                                                    (fn [d b] (e/lam (e/lam-name expr) d b (e/lam-info expr))))
                                  :forall (open-binder replace-in st (e/forall-name expr)
                                                       (e/forall-type expr) (e/forall-body expr)
                                                       (fn [d b] (e/forall' (e/forall-name expr) d b (e/forall-info expr))))
                                  expr)))]
                        (replace-in st (:type goal)))
        ;; Goal[e := val] by re-substituting the abstracted fvar
        subst (fn [val] (e/instantiate1 (e/abstract1 goal-replaced abs-fvar-id) val))
        goal-true (subst bool-true)
        goal-false (subst bool-false)
        ;; Substituted branch goals + the named equality hypothesis
        [ps' h-false-id] (proof/alloc-id ps')
        lctx-false (red/lctx-add-local (:lctx goal) h-false-id hname (eq-type bool-false))
        [ps' false-goal-id] (proof/fresh-mvar-replacing ps' goal-false lctx-false (:id goal))
        [ps' h-true-id] (proof/alloc-id ps')
        lctx-true (red/lctx-add-local (:lctx goal) h-true-id hname (eq-type bool-true))
        [ps' true-goal-id] (proof/fresh-mvar-replacing ps' goal-true lctx-true (:id goal))
        goal-sort (infer-in-goal ps (:lctx goal) (:type goal))
        goal-sort-whnf (whnf-in-goal ps (:lctx goal) goal-sort)
        motive-level (if (e/sort? goal-sort-whnf) (e/sort-level goal-sort-whnf) lvl/zero)
        ;; motive: λ (b : Bool), Eq Bool e b → Goal[e := b]  (abstracted over the fvar)
        motive (e/lam "b" bool-type
                      (e/abstract1 (e/arrow (eq-type abs-fvar) goal-replaced) abs-fvar-id)
                      :default)
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
        (proof/record-tactic :cases-eq [cond-expr] (:id goal)))))

(defn generalize
  "Lean `generalize h : e = x`: abstract every occurrence of the term `e` in the goal as a fresh
   variable `x`, leaving ONE new goal `x : T, h : e = x ⊢ G[e := x]`. This lets you `cases`/`induction`
   on `x` (now a plain variable) when the scrutinee is a NESTED term — the RAWREC case the bare `cases`
   can't reach. Reconstructs the original goal as `?n e (Eq.refl e)` where `?n : ∀ x, e = x → G[e:=x]`
   (no new extract kind needed — a plain `:exact` referencing the new goal mvar)."
  [ps e-expr xname hname]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        st (mk-tc ps (:lctx goal))
        T (tc/infer-type st e-expr)
        T-sort (whnf-in-goal ps (:lctx goal) (tc/infer-type st T))
        Tlvl (if (e/sort? T-sort) (e/sort-level T-sort) lvl/zero)
        ;; kabstract: replace occurrences of e-expr in the goal with a fresh fvar, under binders
        ;; (mirrors cases-eq / the rewrite tactic).
        [ps' abs-id] (proof/alloc-id ps)
        abs-fvar (e/fvar abs-id)
        goal-replaced (let [_ (swap! (:next-id st) (fn [v] (max v (inc abs-id))))
                            open-binder
                            (fn [replace-in st nm dom body mk]
                              (let [d (replace-in st dom)
                                    fid (swap! (:next-id st) inc)
                                    st' (update st :lctx red/lctx-add-local fid nm dom)
                                    b (replace-in st' (e/instantiate1 body (e/fvar fid)))]
                                (mk d (e/abstract1 b fid))))
                            replace-in
                            (fn replace-in [st expr]
                              (if (try (tc/is-def-eq st expr e-expr) (catch Exception _ false))
                                abs-fvar
                                (case (e/tag expr)
                                  :app (let [f (replace-in st (e/app-fn expr))
                                             a (replace-in st (e/app-arg expr))]
                                         (if (and (identical? f (e/app-fn expr)) (identical? a (e/app-arg expr)))
                                           expr (e/app f a)))
                                  :lam (open-binder replace-in st (e/lam-name expr) (e/lam-type expr) (e/lam-body expr)
                                                    (fn [d b] (e/lam (e/lam-name expr) d b (e/lam-info expr))))
                                  :forall (open-binder replace-in st (e/forall-name expr) (e/forall-type expr) (e/forall-body expr)
                                                       (fn [d b] (e/forall' (e/forall-name expr) d b (e/forall-info expr))))
                                  expr)))]
                        (replace-in st (:type goal)))
        _ (when (identical? goal-replaced (:type goal))
            (tactic-error! "generalize: term does not occur in the goal" {:expr e-expr}))
        ;; N = ∀ (x : T), Eq T e x → G[e := x]
        [ps' xfv-id] (proof/alloc-id ps')
        xfv (e/fvar xfv-id)
        g-x (e/instantiate1 (e/abstract1 goal-replaced abs-id) xfv)   ;; G[e := xfv]
        eq-e-x (e/app* (e/const' (name/from-string "Eq") [Tlvl]) T e-expr xfv)
        inner (e/forall' hname eq-e-x g-x :default)                   ;; (e = x) → G[e:=x]  (h unused)
        n-type (e/forall' xname T (e/abstract1 inner xfv-id) :default)
        [ps' n-id] (proof/fresh-mvar-replacing ps' n-type (:lctx goal) (:id goal))
        ;; original goal := ?n e (Eq.refl e). Record a dedicated `:generalize` kind so extraction
        ;; splices in the SUBGOAL's proof (`?n`): `(extract n-id) e rfl`. (A plain `:exact` term
        ;; returns verbatim and would leave the `?n` reference dangling — free var / unknown tag.)
        rfl (e/app* (e/const' (name/from-string "Eq.refl") [Tlvl]) T e-expr)]
    (-> (proof/assign-mvar ps' (:id goal) {:kind :generalize :child n-id :e e-expr :rfl rfl})
        (proof/record-tactic :generalize [e-expr] (:id goal)))))

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

;; ============================================================
;; split — faithful port of Lean 4 Tactic/Split.lean (findSplit? + dispatch)
;; ============================================================

(defn- find-split-target
  "Lean 4 findSplit? (Meta/Tactic/SplitIf.lean:39-120): walk the goal for the
   first splittable discriminant. Recognizes (in Lean's priority order, innermost
   condition first):
     - cond α c a b      → {:kind :bool  :discr c}   (Bool eliminator; split via by-cases)
     - Bool.rec _ _ _ c  → {:kind :bool  :discr c}
     - ite/dite α c i …  → {:kind :dec   :cond c :inst i}  (Decidable; split via by-cases-dec)
     - Foo.match_N …     → {:kind :matcher :app e :head h :args as}  (matcher splitter)
   Discriminants with loose bvars (inside a binder) are skipped, matching Lean.
   `badCases` is a set of exprs to skip (the splitMatch retry set)."
  [ps goal-lctx expr badCases]
  (let [result (volatile! nil)]
    (letfn [(splittable-bool? [b]
              (and (not (e/has-loose-bvars? b))
                   (let [bw (try (whnf-in-goal ps goal-lctx b) (catch Exception _ b))]
                     (not (and (e/const? bw)
                               (contains? #{"Bool.true" "Bool.false"}
                                          (name/->string (e/const-name bw))))))))
            (walk [e]
              (when (and (not @result) (not (contains? badCases e)))
                (let [[head args] (e/get-app-fn-args e)]
                  (when (e/const? head)
                    (let [hn (name/->string (e/const-name head))]
                      (cond
                        (and (= hn "cond") (>= (count args) 2))
                        (let [c (nth args 1)]
                          (when (splittable-bool? c) (vreset! result {:kind :bool :discr c})))

                        (and (= hn "Bool.rec") (= 4 (count args)))
                        (let [c (nth args 3)]
                          (when (splittable-bool? c) (vreset! result {:kind :bool :discr c})))

                        (and (contains? #{"ite" "dite"} hn) (>= (count args) 3))
                        (let [c (nth args 1) inst (nth args 2)]
                          (when-not (e/has-loose-bvars? c)
                            (vreset! result {:kind :dec :cond c :inst inst})))

                        (re-find #"\.match_\d+$" hn)
                        (vreset! result {:kind :matcher :app e :head head :args args})

                        :else nil))))
                (when-not @result
                  (case (e/tag e)
                    :app (do (walk (e/app-fn e)) (walk (e/app-arg e)))
                    :lam (do (walk (e/lam-type e)) (walk (e/lam-body e)))
                    :forall (do (walk (e/forall-type e)) (walk (e/forall-body e)))
                    :let (do (walk (e/let-value e)) (walk (e/let-body e)))
                    :mdata (walk (e/mdata-expr e))
                    :proj (walk (e/proj-struct e))
                    nil))))]
      (walk expr))
    @result))

(defn by-cases-dec
  "Decidable case-split (Lean 4 MVarId.byCasesDec, Cases.lean:371). Given a Prop
   `c` and a `Decidable c` instance term, produces two subgoals via Decidable.casesOn
   with a CONSTANT motive (λ _:Decidable c, Goal):
     Goal 1 (isFalse): h : ¬c ⊢ goal
     Goal 2 (isTrue):  h : c  ⊢ goal
   The ite/dite stays unreduced; the following simp_all reduces it via if_pos/if_neg
   discharged by h (faithful to `split <;> simp_all` in combination)."
  [ps c inst]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        st (mk-tc ps (:lctx goal))
        not-c (e/app* (e/const' (name/from-string "Not") []) c)
        goal-sort (infer-in-goal ps (:lctx goal) (:type goal))
        goal-sort-whnf (whnf-in-goal ps (:lctx goal) goal-sort)
        motive-level (if (e/sort? goal-sort-whnf) (e/sort-level goal-sort-whnf) lvl/zero)
        ;; constant motive: λ (_ : Decidable c), Goal
        dec-c (e/app* (e/const' (name/from-string "Decidable") []) c)
        motive (e/lam "d" dec-c (:type goal) :default)
        [ps' h-false-id] (proof/alloc-id ps)
        lctx-false (red/lctx-add-local (:lctx goal) h-false-id "h" not-c)
        [ps' false-goal-id] (proof/fresh-mvar-replacing ps' (:type goal) lctx-false (:id goal))
        [ps' h-true-id] (proof/alloc-id ps')
        lctx-true (red/lctx-add-local (:lctx goal) h-true-id "h" c)
        [ps' true-goal-id] (proof/fresh-mvar-replacing ps' (:type goal) lctx-true (:id goal))]
    (-> (proof/assign-mvar ps' (:id goal)
                           {:kind :by-cases-dec
                            :cond c
                            :inst inst
                            :motive motive
                            :motive-level motive-level
                            :not-c not-c
                            :h-false-id h-false-id
                            :h-true-id h-true-id
                            :false-goal false-goal-id
                            :true-goal true-goal-id})
        (proof/record-tactic :by-cases-dec [c] (:id goal)))))

(declare split-matcher)

(defn split-tac
  "Lean 4 `split` (Tactic/Split.lean:328-346): find a splittable discriminant in
   the goal (ite/dite/cond/Bool.rec/matcher) and case-split on it.
     - cond/Bool.rec  → by-cases on the Bool (hc : c = true / c = false)
     - ite/dite       → by-cases-dec on the Decidable (h : c / h : ¬c)
     - matcher        → matcher splitter (one subgoal per alternative, +discr eqs)
   On a matcher whose splitter application fails, retry skipping it (badCases)."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        find1 (fn [bad]
                (or (find-split-target ps (:lctx goal) (:type goal) bad)
                    (find-split-target ps (:lctx goal)
                                       (whnf-in-goal ps (:lctx goal) (:type goal)) bad)))]
    (loop [bad #{}]
      (let [tgt (find1 bad)]
        (if (nil? tgt)
          (tactic-error! "split: no if/match/cond discriminant found" {:goal (:type goal)})
          (case (:kind tgt)
            :bool (by-cases ps (:discr tgt))
            :dec  (by-cases-dec ps (:cond tgt) (:inst tgt))
            :matcher (let [res (try {:ok (split-matcher ps tgt)}
                                    (catch clojure.lang.ExceptionInfo ex
                                      (if (:split-retry (ex-data ex))
                                        {:retry true}
                                        (throw ex))))]
                       (if (:retry res) (recur (conj bad (:app tgt))) (:ok res)))))))))

(defn split-matcher
  "Split a stuck matcher (Foo.match_N application) via the faithful applyMatchSplitter port
   (ansatz.tactic.match-eqns/split-matcher): the matcher IS the (non-overlapping) splitter, applied
   as an eliminator with motive λd.(discr=d)→Goal, one minor premise per alternative carrying the
   discriminant equality. Signals :split-retry for shapes not yet supported (multi-discriminant /
   overlapping), so split-tac skips this discriminant."
  [ps tgt]
  ((requiring-resolve 'ansatz.tactic.match-eqns/split-matcher) ps tgt))
