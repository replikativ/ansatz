(ns ansatz.meta.tactic.apply
  "Goal policy from Lean 4 v4.33.1, Lean/Meta/Tactic/Apply.lean.
   Telescope search and instance synthesis remain in tactic.basic."
  (:require [ansatz.meta :as meta]
            [ansatz.kernel.name :as name]
            [ansatz.tactic.proof :as proof]))

(defn depends-on-others?
  "Lean dependsOnOthers: another generated hole's type contains this hole."
  [ps id other-mvars]
  (boolean
   (some (fn [other]
           (and (not= id other)
                (contains? (meta/collect-expr-mvars
                            (meta/zonk-expr (:meta-mctx ps)
                                            (proof/mvar-type ps other))) id)))
         other-mvars)))

(defn partition-dependent-mvars
  "Lean partitionDependentMVars, preserving telescope order in both parts."
  [ps mvars]
  (reduce (fn [[non-deps deps] id]
            (if (depends-on-others? ps id mvars)
              [non-deps (conj deps id)]
              [(conj non-deps id) deps]))
          [[] []] mvars))

(defn reorder-goals
  "Lean reorderGoals / ApplyNewGoals. Defaults to nonDependentFirst."
  ([ps mvars] (reorder-goals ps mvars :non-dependent-first))
  ([ps mvars mode]
   (case mode
     :non-dependent-first (let [[non-deps deps] (partition-dependent-mvars ps mvars)]
                            (into non-deps deps))
     :non-dependent-only (first (partition-dependent-mvars ps mvars))
     :all (vec mvars)
     (throw (ex-info "Tactic error: unknown ApplyNewGoals mode"
                     {:kind :tactic-error :new-goals mode})))))

(defn append-parent-tag
  "Lean appendParentTag: one telescope hole inherits the parent tag;
   otherwise append binder tags for open, non-instance holes."
  [ps parent-tag new-mvars binder-infos]
  (cond
    (= 1 (count new-mvars))
    (proof/set-mvar-user-name ps (first new-mvars) parent-tag)

    (name/anonymous? parent-tag) ps

    :else
    (reduce (fn [ps [id info]]
              (if (or (proof/mvar-assigned? ps id) (= info :inst-implicit))
                ps
                (let [tag (proof/mvar-user-name ps id)]
                  (proof/set-mvar-user-name
                   ps id (if (name/anonymous? tag) parent-tag
                             (name/from-string (str (name/->string parent-tag) "."
                                                    (name/->string tag))))))))
            ps (map vector new-mvars binder-infos))))
