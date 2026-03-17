;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; Tactic layer — proof term extraction and verification.

(ns ansatz.tactic.extract
  "Extract complete proof terms from solved proof states and verify them."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof])
  (:import [ansatz.kernel TypeChecker]))

(defn extract-term
  "Recursively extract a proof term from a metavariable assignment."
  [ps mvar-id]
  (let [m (get-in ps [:mctx mvar-id])
        assignment (:assignment m)]
    (when-not assignment
      (throw (ex-info "Cannot extract: unassigned metavariable"
                      {:mvar-id mvar-id})))
    (case (:kind assignment)
      :intro (let [{:keys [fvar-id name type info child]} assignment
                   child-term (extract-term ps child)]
               (e/lam name type (e/abstract1 child-term fvar-id) info))

      :apply (let [head (:head assignment)]
               (reduce (fn [acc mid]
                         (e/app acc (extract-term ps mid)))
                       head
                       (:arg-mvars assignment)))

      :exact (:term assignment)

      :rfl (let [eq-refl-name (name/from-string "Eq.refl")
                 levels (:levels assignment)]
             (e/app* (e/const' eq-refl-name levels)
                     (:eq-type assignment)
                     (:val assignment)))

      :assumption (e/fvar (:fvar-id assignment))

      :rewrite (let [{:keys [eq-term eq-type lhs rhs motive reverse? levels motive-level child]} assignment
                     child-term (extract-term ps child)
                     ;; Eq.ndrec : {α : Sort u} {a : α} {motive : α → Sort v},
                     ;;              motive a → {b : α} → a = b → motive b
                     eq-symm-name (name/from-string "Eq.symm")
                     eq-ndrec-name (name/from-string "Eq.ndrec")
                     u-level (first levels)
                     v-level (or motive-level lvl/zero)]
                 (if reverse?
                   ;; reverse: rhs→lhs in goal, eq: lhs=rhs
                   ;; child proves motive(lhs), need motive(rhs)
                   ;; Eq.ndrec child eq : motive rhs
                   (e/app* (e/const' eq-ndrec-name [v-level u-level])
                           eq-type lhs motive child-term rhs eq-term)
                   ;; forward: lhs→rhs in goal, eq: lhs=rhs
                   ;; child proves motive(rhs), need motive(lhs)
                   ;; Eq.ndrec child (Eq.symm eq) : motive lhs
                   (let [symm-eq (e/app* (e/const' eq-symm-name [u-level])
                                         eq-type lhs rhs eq-term)]
                     (e/app* (e/const' eq-ndrec-name [v-level u-level])
                             eq-type rhs motive child-term lhs symm-eq))))

      :cases (let [{:keys [rec-name motive params indices levels ctor-goals]} assignment]
               ;; Build: @Ind.casesOn params motive major minor1 ... minorN
               ;; For now, this is complex — create a simple version
               ;; The recursor takes: params, motive, minors, indices, major
               ;; But casesOn reorders to: params, motive, indices, major, minors
               ;; We extract each constructor branch
               (let [minor-terms (mapv (fn [{:keys [field-fvars goal-id]}]
                                         ;; Abstract field fvars to create a lambda
                                         (let [branch-term (extract-term ps goal-id)]
                                           (reduce (fn [body fid]
                                                     (let [decl (get-in ps [:mctx goal-id :lctx fid])
                                                           ft (or (:type decl) (e/sort' lvl/zero))]
                                                       (e/lam (or (:name decl) "x") ft
                                                              (e/abstract1 body fid) :default)))
                                                   branch-term
                                                   (reverse field-fvars))))
                                       ctor-goals)
                     hyp-fvar (e/fvar (:hyp-fvar-id assignment))]
                 ;; Bool.rec order: motive, minors..., major
                ;; General rec order: params, motive, minors..., indices, major
                 (reduce e/app
                         (e/const' rec-name levels)
                         (concat params [motive] minor-terms indices [hyp-fvar]))))

      ;; have h : T := proof; body  →  (λ h : T => body) proof
      :have (let [{:keys [fvar-id name type proof-goal body-goal]} assignment
                  proof-term (extract-term ps proof-goal)
                  body-term (extract-term ps body-goal)]
              (e/app (e/lam name type (e/abstract1 body-term fvar-id) :default)
                     proof-term))

      ;; simp-reduce: simp simplified the goal but couldn't close it.
      ;; If eq-proof is non-nil: Eq.mpr goal-type simplified eq-proof child-proof
      ;; If eq-proof is nil: transition is by def-eq, child-proof directly proves original
      ;; Lean 4: applySimpResultToTarget (Main.lean:780)
      :simp-reduce (let [{:keys [eq-proof child mpr-level goal-type simplified]} assignment
                         child-term (extract-term ps child)]
                     (if eq-proof
                       (let [eq-mpr-name (name/from-string "Eq.mpr")]
                         (e/app* (e/const' eq-mpr-name [mpr-level])
                                 goal-type simplified eq-proof child-term))
                       ;; Nil proof: simplified is def-eq to goal, child proves simplified
                       child-term))

      ;; revert h  →  child applied to h
      ;; If goal was G and we reverted h : T, child proves ∀ h : T, G
      ;; So original goal proof = child h
      :revert (let [{:keys [fvar-id child]} assignment
                    child-term (extract-term ps child)]
                (e/app child-term (e/fvar fvar-id)))

      ;; exfalso  →  False.elim goal-type child
      ;; False.elim : {C : Sort u} → False → C
      ;; u = level of goal-type's sort (0 for Prop goals, 1 for Type goals)
      :exfalso (let [{:keys [child goal-type motive-level]} assignment
                     child-term (extract-term ps child)
                     false-elim-name (name/from-string "False.elim")
                     u (or motive-level lvl/zero)]
                 (e/app* (e/const' false-elim-name [u])
                         goal-type child-term))

      ;; subst h  →  Eq.mpr/ndrec based rewrite
      ;; For now, the child proves the substituted goal; we need to
      ;; transport back via the equality
      :subst (let [{:keys [child]} assignment]
               ;; The child proves the goal with substitution applied
               ;; For simple cases, def-eq handles this
               (extract-term ps child))

      ;; by-cases cond → Bool.rec motive false-branch true-branch cond rfl
      :by-cases (let [{:keys [cond motive motive-level rfl-proof
                              h-false-id h-true-id false-goal true-goal]} assignment
                      false-term (extract-term ps false-goal)
                      true-term (extract-term ps true-goal)
                      ;; Build actual hypothesis types: Eq Bool cond false/true
                      bool-type (e/const' (name/from-string "Bool") [])
                      eq-1 (lvl/succ lvl/zero)
                      eq-type-false (e/app* (e/const' (name/from-string "Eq") [eq-1])
                                            bool-type cond (e/const' (name/from-string "Bool.false") []))
                      eq-type-true (e/app* (e/const' (name/from-string "Eq") [eq-1])
                                           bool-type cond (e/const' (name/from-string "Bool.true") []))
                      ;; Wrap each branch in λ h, body (abstract the eq hypothesis)
                      false-lam (e/lam "h" eq-type-false
                                       (e/abstract1 false-term h-false-id) :default)
                      true-lam (e/lam "h" eq-type-true
                                      (e/abstract1 true-term h-true-id) :default)
                      ;; Bool.rec.{u} (motive : Bool → Sort u) (false : motive false) (true : motive true) (b : Bool) : motive b
                      bool-rec (e/const' (name/from-string "Bool.rec") [motive-level])]
                  ;; @Bool.rec motive false-lam true-lam cond rfl
                  (e/app* bool-rec motive false-lam true-lam cond rfl-proof))

      ;; simp-all-hyps: hypothesis simplification wrapper.
      ;; For each replacement (h : P → h' : P'), wrap child proof:
      ;; (λ h' : P' => child[h'/bvar]) (Eq.mp eq h)
      ;; eq : P = P' (from simp), Eq.mp eq h : P'
      ;; Following Lean 4: SimpAll.lean applySimpResult uses Eq.mp (forward direction)
      :simp-all-hyps
      (let [{:keys [replacements child]} assignment
            child-term (extract-term ps child)
            eq-mp-nm (name/from-string "Eq.mp")]
        (reduce (fn [body {:keys [old-fvar-id new-fvar-id old-type new-type eq-proof]}]
                  (let [transport-proof
                        (if eq-proof
                          ;; eq-proof : old-type = new-type
                          ;; Eq.mp.{0} old-type new-type eq-proof (fvar h) : new-type
                          (e/app* (e/const' eq-mp-nm [lvl/zero])
                                  old-type new-type eq-proof (e/fvar old-fvar-id))
                          ;; No proof — def-eq, old fvar works directly
                          (e/fvar old-fvar-id))]
                    (e/app (e/lam "h" new-type (e/abstract1 body new-fvar-id) :default)
                           transport-proof)))
                child-term
                (reverse replacements)))

      ;; clear h  →  just extract child (same goal, fewer hyps)
      :clear (let [{:keys [child]} assignment]
               (extract-term ps child)))))

(defn extract
  "Extract the complete proof term from the root metavariable.
   Throws if any goals remain open."
  [ps]
  (when-not (proof/solved? ps)
    (throw (ex-info "Cannot extract: proof has open goals"
                    {:open-goals (count (:goals ps))})))
  (extract-term ps (:root-mvar ps)))

(defn verify
  "Extract the proof term and verify it with the Java TypeChecker.
   Returns the extracted term on success, throws on failure."
  [ps]
  (let [term (extract ps)
        env (:env ps)
        root-type (get-in ps [:mctx (:root-mvar ps) :type])]
    (when (e/has-fvar-flag term)
      (throw (ex-info "Extracted term contains free variables" {:term term})))
    (let [tc (TypeChecker. env)]
      ;; Use generous fuel for verification — simp proofs may need deep reduction
      (.setFuel tc 50000000)
      (let [inferred (.inferType tc term)]
        (when-not (.isDefEq tc inferred root-type)
          (throw (ex-info "Extracted term type does not match goal"
                          {:expected root-type :inferred inferred})))))
    term))
