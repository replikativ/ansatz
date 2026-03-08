;; Copyright (c) 2026 Simmis GmbH. All rights reserved.
;; Tactic layer — proof term extraction and verification.

(ns cic.tactic.extract
  "Extract complete proof terms from solved proof states and verify them."
  (:require [cic.kernel.expr :as e]
            [cic.kernel.name :as name]
            [cic.kernel.level :as lvl]
            [cic.tactic.proof :as proof])
  (:import [cic.kernel TypeChecker]))

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
                         (concat params [motive] minor-terms indices [hyp-fvar])))))))

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
    (let [tc (TypeChecker. env)
          inferred (.inferType tc term)]
      (when-not (.isDefEq tc inferred root-type)
        (throw (ex-info "Extracted term type does not match goal"
                        {:expected root-type :inferred inferred}))))
    term))
