;; Port of Init/Omega/Constraint.lean: exact, scale, combine, combo, Lean checkout 55f80e10.
(ns ansatz.tactic.omega.constraint)

(defn mk-constraint
  "Make a constraint with optional lower and upper bounds."
  [lower upper]
  {:lower lower :upper upper})

(defn constraint-exact
  "Constraint for exact value: {v} = [v, v]."
  [v]
  {:lower v :upper v})

(defn constraint-geq
  "Constraint: value >= lower."
  [lower]
  {:lower lower :upper nil})

(defn constraint-leq
  "Constraint: value <= upper."
  [upper]
  {:lower nil :upper upper})

(defn constraint-trivial
  "Unconstrained."
  []
  {:lower nil :upper nil})

(defn constraint-impossible?
  "Is this constraint impossible?"
  [{:keys [lower upper]}]
  (and lower upper (> lower upper)))

(defn constraint-is-exact?
  "Is this an exact constraint (lower = upper)?"
  [{:keys [lower upper]}]
  (and lower upper (= lower upper)))

(defn constraint-combine
  "Intersect two constraints (tighten bounds)."
  [a b]
  {:lower (cond
            (nil? (:lower a)) (:lower b)
            (nil? (:lower b)) (:lower a)
            :else (max (:lower a) (:lower b)))
   :upper (cond
            (nil? (:upper a)) (:upper b)
            (nil? (:upper b)) (:upper a)
            :else (min (:upper a) (:upper b)))})

(defn constraint-negate
  "neg c (Constraint.neg = flip then negate): {lower l, upper u} -> {lower -u, upper -l}."
  [{:keys [lower upper]}]
  {:lower (when upper (-' upper))
   :upper (when lower (-' lower))})

(defn constraint-scale
  "Scale a constraint by integer k (Constraint.scale). k>0 keeps bounds; k<0 flips
   lower<->upper (and negates); k=0 collapses to the point {0,0} (or trivial if no bounds)."
  [k {:keys [lower upper]}]
  (let [sb (fn [b] (when b (*' k b)))]
    (cond
      (pos? k) {:lower (sb lower) :upper (sb upper)}
      (neg? k) {:lower (sb upper) :upper (sb lower)}
      :else    {:lower (when (or lower upper) 0) :upper (when (or lower upper) 0)})))

(defn constraint-combo
  "Linear combination of constraints: a*s + b*t."
  [a s b t]
  (let [scale-constraint constraint-scale]
    (let [sa (scale-constraint a s)
          sb (scale-constraint b t)]
      {:lower (when (and (:lower sa) (:lower sb))
                (+' (:lower sa) (:lower sb)))
       :upper (when (and (:upper sa) (:upper sb))
                (+' (:upper sa) (:upper sb)))})))

;; ============================================================
;; Justification: derivation tree (proof recipe)
