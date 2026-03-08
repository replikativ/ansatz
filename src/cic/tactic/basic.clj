;; Copyright (c) 2026 Simmis GmbH. All rights reserved.
;; Tactic layer — core tactics.

(ns cic.tactic.basic
  "Core tactics: intro, intros, exact, assumption, apply, rfl, constructor,
   cases, induction, rewrite.
   Each tactic is a pure function: (tactic ps ...args) → ps'."
  (:require [cic.kernel.expr :as e]
            [cic.kernel.env :as env]
            [cic.kernel.name :as name]
            [cic.kernel.level :as lvl]
            [cic.kernel.reduce :as red]
            [cic.kernel.tc :as tc]
            [cic.tactic.proof :as proof])
  (:import [cic.kernel ConstantInfo ConstantInfo$RecursorRule]))

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
           (proof/record-tactic :intro [binder-name] (:id goal)))))))

;; ============================================================
;; intros
;; ============================================================

(defn intros
  "Repeatedly introduce forall binders until the goal is no longer a forall."
  ([ps] (intros ps []))
  ([ps names]
   (loop [ps ps names (seq names)]
     (let [goal (proof/current-goal ps)]
       (when-not goal (tactic-error! "No goals" {}))
       (let [goal-type (whnf-in-goal ps (:lctx goal) (:type goal))]
         (if (e/forall? goal-type)
           (let [n (first names)]
             (recur (intro ps n) (rest names)))
           ps))))))

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
  "Search the local context for a hypothesis matching the goal type."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        st (mk-tc ps (:lctx goal))
        lctx (:lctx goal)
        match (some (fn [[id decl]]
                      (when (and (= :local (:tag decl))
                                 (tc/is-def-eq st (:type decl) (:type goal)))
                        id))
                    lctx)]
    (when-not match
      (tactic-error! "No matching hypothesis found" {:goal-type (:type goal)}))
    (-> (proof/assign-mvar ps (:id goal) {:kind :assumption :fvar-id match})
        (proof/record-tactic :assumption [] (:id goal)))))

;; ============================================================
;; apply (with first-order unification)
;; ============================================================

(defn apply-tac
  "Apply a term to the current goal, generating subgoals for its arguments.
   Uses first-order pattern matching to resolve implicit arguments."
  [ps term]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        st (mk-tc ps (:lctx goal))
        term-type (tc/infer-type st term)]
    ;; Peel forall binders, creating fresh mvars for each argument
    (loop [ps ps
           ty (whnf-in-goal ps (:lctx goal) term-type)
           arg-mvars []
           mvar-id-set #{}]
      (if (e/forall? ty)
        (let [[ps' mvar-id] (proof/fresh-mvar ps (e/forall-type ty) (:lctx goal))
              new-ty (e/instantiate1 (e/forall-body ty) (e/fvar mvar-id))]
          (recur ps' (whnf-in-goal ps' (:lctx goal) new-ty)
                 (conj arg-mvars mvar-id)
                 (conj mvar-id-set mvar-id)))
        ;; Try to match the result type against the goal type
        (let [;; First try direct def-eq (works if no mvars in result)
              direct-ok (tc/is-def-eq st ty (:type goal))
              ;; If that fails, try first-order pattern matching
              subst (when-not direct-ok
                      (match-expr ty (:type goal) mvar-id-set))]
          (when (and (not direct-ok) (not subst))
            (tactic-error! "apply: result type does not match goal"
                           {:expected (:type goal) :actual ty}))
          ;; Assign solved mvars from the substitution
          (let [ps (reduce (fn [ps mvar-id]
                             (if-let [val (get subst mvar-id)]
                               (proof/assign-mvar ps mvar-id
                                                  {:kind :exact :term val})
                               ps))
                           ps arg-mvars)
                ;; Substitute solved mvar values into remaining unsolved goal types
                ;; so that fvar references to solved mvars are replaced
                ps (if subst
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
            (-> (proof/assign-mvar ps (:id goal)
                                   {:kind :apply :head term :arg-mvars arg-mvars})
                (proof/record-tactic :apply [term] (:id goal)))))))))

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
                        fname (or (e/forall-name t) (str "h" fid))
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
        (let [rec-levels (into [motive-level] ind-levels)]
          (-> (proof/assign-mvar ps (:id goal)
                                 {:kind :cases
                                  :hyp-fvar-id hyp-fvar-id
                                  :ind-name ind-name
                                  :rec-name rec-name
                                  :motive motive
                                  :params params
                                  :indices indices
                                  :levels rec-levels
                                  :ctor-goals ctor-goals})
            (proof/record-tactic :cases [hyp-fvar-id] (:id goal))))))))
