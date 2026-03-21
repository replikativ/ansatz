;; Omega problem: constraint algebra, justification tree, and problem data structures.
;;
;; This module defines the solver-independent representation of an omega problem.
;; Both the FM solver and the SMT solver operate on these structures.
;; The Justification tree is the contract between solver and proof extraction.

(ns ansatz.tactic.omega.problem
  "Solver-independent omega problem representation.

   Data structures:
   - Constraint: interval [lower, upper] with nil = unbounded
   - Justification: tagged derivation tree (the proof recipe)
   - Fact: coefficients + constraint + justification
   - Problem: the full constraint system with assumptions and disjunctions

   The Justification tags form the contract between solver and proof extraction:
   :assumption, :tidy, :combine, :combo, :bmod, :trivial-zero")

;; ============================================================
;; Safe arithmetic (auto-promoting to avoid overflow)
;; ============================================================

(defn safe-abs
  "Absolute value that works with both long and BigInteger."
  [x]
  (if (neg? x) (-' x) x))

;; ============================================================
;; LinearCombo: dense coefficient vector
;; ============================================================

(defn mk-lc
  "Make a linear combination."
  ([const] {:const const :coeffs []})
  ([const coeffs] {:const const :coeffs (vec coeffs)}))

(defn lc-coordinate
  "LinearCombo for the i-th atom: 0 + 0*x0 + ... + 1*xi + ..."
  [n]
  {:const 0 :coeffs (vec (concat (repeat n 0) [1]))})

(defn lc-add [a b]
  (let [ca (:coeffs a) cb (:coeffs b)
        len (max (count ca) (count cb))]
    {:const (+' (:const a) (:const b))
     :coeffs (vec (for [i (range len)]
                    (+' (get ca i 0) (get cb i 0))))}))

(defn lc-sub [a b]
  (let [ca (:coeffs a) cb (:coeffs b)
        len (max (count ca) (count cb))]
    {:const (-' (:const a) (:const b))
     :coeffs (vec (for [i (range len)]
                    (-' (get ca i 0) (get cb i 0))))}))

(defn lc-negate [a]
  {:const (-' (:const a))
   :coeffs (mapv -' (:coeffs a))})

(defn lc-scale [a k]
  {:const (*' (:const a) k)
   :coeffs (mapv #(*' % k) (:coeffs a))})

(defn lc-is-zero? [a]
  (and (zero? (:const a))
       (every? zero? (:coeffs a))))

(defn lc-clean
  "Remove trailing zeros from coeffs."
  [a]
  (let [cs (:coeffs a)]
    (loop [i (dec (count cs))]
      (if (or (neg? i) (not (zero? (nth cs i))))
        (assoc a :coeffs (subvec cs 0 (inc i)))
        (recur (dec i))))))

;; ============================================================
;; Balanced mod (matches Lean's Int.bmod)
;; ============================================================

(defn int-bmod
  "Balanced mod: result in [-(m-1)/2, m/2]. Matches Int.bmod in Lean."
  [x m]
  (if (zero? m)
    x
    (let [r (mod x m)]
      (if (< r (quot (+' m 1) 2))
        r
        (-' r m)))))

(defn coeffs-bmod
  "Apply balanced mod to each coefficient."
  [coeffs m]
  (mapv #(int-bmod % m) coeffs))

(defn min-nat-abs
  "Minimum of |c| for non-zero c in coeffs."
  [coeffs]
  (reduce (fn [best c]
            (let [a (safe-abs c)]
              (if (zero? a) best (if (nil? best) a (min best a)))))
          nil coeffs))

(defn max-nat-abs
  "Maximum of |c| for non-zero c in coeffs."
  [coeffs]
  (reduce (fn [best c]
            (let [a (safe-abs c)]
              (if (zero? a) best (if (nil? best) a (max best a)))))
          nil coeffs))

;; ============================================================
;; Constraint: interval [lower, upper]
;; ============================================================

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

(defn constraint-combo
  "Linear combination of constraints: a*s + b*t."
  [a s b t]
  (let [scale-bound (fn [k bound]
                      (when bound (*' k bound)))
        scale-constraint (fn [k {:keys [lower upper]}]
                           (if (pos? k)
                             {:lower (scale-bound k lower)
                              :upper (scale-bound k upper)}
                             {:lower (scale-bound k upper)
                              :upper (scale-bound k lower)}))]
    (let [sa (scale-constraint a s)
          sb (scale-constraint b t)]
      {:lower (when (and (:lower sa) (:lower sb))
                (+' (:lower sa) (:lower sb)))
       :upper (when (and (:upper sa) (:upper sb))
                (+' (:upper sa) (:upper sb)))})))

;; ============================================================
;; Justification: derivation tree (proof recipe)
;; ============================================================
;;
;; Tags:
;;   :assumption — from hypothesis i
;;   :tidy      — GCD normalization
;;   :combine   — intersection of two same-coeffs constraints
;;   :combo     — linear combination of two different-coeffs constraints
;;   :bmod      — balanced mod for hard equality solving
;;   :trivial-zero — zero-coefficients with impossible constraint

(defn justification-assumption
  "Derived from assumption i with constraint s and coeffs x."
  [i s x]
  {:tag :assumption :idx i :constraint s :coeffs x})

(defn justification-tidy
  "Result of tidying another justification.
   Stores the original constraint/coeffs for the tidy_sat lemma."
  [j new-s new-x]
  {:tag :tidy :inner j
   :orig-constraint (:constraint j) :orig-coeffs (:coeffs j)
   :constraint new-s :coeffs new-x})

(defn justification-combine
  "Combination of two justifications with same coefficients.
   j proves s.sat' x v, k proves t.sat' x v."
  [j k combined-s]
  {:tag :combine :left j :right k
   :left-constraint (:constraint j) :right-constraint (:constraint k)
   :constraint combined-s :coeffs (:coeffs j)})

(defn justification-combo
  "Linear combination: a*j + b*k.
   j proves s.sat' x v, k proves t.sat' y v."
  [a j b k combined-s combined-x]
  {:tag :combo :a a :left j :b b :right k
   :left-constraint (:constraint j) :left-coeffs (:coeffs j)
   :right-constraint (:constraint k) :right-coeffs (:coeffs k)
   :constraint combined-s :coeffs combined-x})

(defn justification-bmod
  "Bmod of a justification for hard equality solving.
   j proves (exact r).sat' x v.
   Result proves (exact (bmod r m)).sat' (bmod_coeffs m i x) v."
  [j m r i]
  (let [orig-coeffs (:coeffs j)
        new-coeffs (assoc (vec (coeffs-bmod orig-coeffs m)) i m)
        new-r (int-bmod r m)]
    {:tag :bmod :inner j :m m :r r :i i
     :orig-coeffs orig-coeffs
     :constraint (constraint-exact (-' new-r))
     :coeffs new-coeffs}))

;; ============================================================
;; Fact: coefficients + constraint + justification
;; ============================================================

(defn mk-fact [coeffs constraint justification]
  {:coeffs coeffs :constraint constraint :justification justification})

;; ============================================================
;; GCD utilities
;; ============================================================

(defn gcd-list
  "GCD of absolute values of a list of integers."
  [xs]
  (let [gcd2 (fn [a b]
               (loop [a (safe-abs a) b (safe-abs b)]
                 (if (zero? b) a (recur b (mod a b)))))]
    (reduce gcd2 0 xs)))

;; ============================================================
;; Tidy: normalize constraint/coefficients by GCD
;; ============================================================

(defn tidy-fact
  "Tidy a fact: divide constraint and coefficients by GCD of coefficients.
   Returns the fact unchanged if GCD <= 1.
   Records a :tidy justification node for proof term construction via tidy_sat.
   Uses floor division (matching Lean's Int.div) for constraint bounds."
  [{:keys [coeffs constraint justification] :as fact}]
  (let [g (gcd-list coeffs)]
    (if (<= g 1)
      fact
      (let [new-coeffs (mapv #(quot % g) coeffs)
            floor-div (fn [a b]
                        (let [q (quot a b)
                              r (rem a b)]
                          (if (and (not (zero? r)) (not= (neg? a) (neg? b)))
                            (dec q) q)))
            new-constraint {:lower (when-let [l (:lower constraint)]
                                     (- (floor-div (- (long l)) (long g))))
                            :upper (when-let [u (:upper constraint)]
                                     (floor-div (long u) (long g)))}
            new-j (justification-tidy justification new-constraint new-coeffs)]
        (mk-fact new-coeffs new-constraint new-j)))))

;; ============================================================
;; Coefficients utilities
;; ============================================================

(defn coeffs-key
  "Canonical key for a coefficient vector."
  [coeffs]
  (vec coeffs))

(defn all-zero-coeffs?
  "True if all coefficients are zero."
  [coeffs]
  (every? zero? coeffs))

(defn constraint-unsat-at-zero?
  "True if the constraint is unsatisfiable when the value is 0."
  [{:keys [lower upper]}]
  (or (and lower (pos? lower))
      (and upper (neg? upper))))

(defn is-impossible?
  "Check if a fact represents an impossible constraint."
  [{:keys [coeffs constraint]}]
  (or (constraint-impossible? constraint)
      (and (all-zero-coeffs? coeffs)
           (constraint-unsat-at-zero? constraint))))

;; ============================================================
;; Problem: the constraint system
;; ============================================================

(defn mk-problem []
  {:assumptions []     ;; Vector of delayed proofs (fns returning Expr)
   :num-vars 0
   :constraints {}     ;; coeffs-key -> Fact
   :equalities #{}     ;; set of coeffs-keys that are equalities
   :eliminations []    ;; list of [fact var-idx sign]
   :possible true
   :proof-false nil    ;; {:justification :constraint :coeffs}
   :disjunctions []})  ;; queue of {:or-proof Expr, :left-type Expr, :right-type Expr}

(defn queue-disjunction
  "Add a disjunction to the problem's disjunction queue."
  [problem disj]
  (update problem :disjunctions conj disj))

;; ============================================================
;; Constraint insertion and combination
;; ============================================================

(defn insert-constraint
  "Insert a constraint, checking for impossibility."
  [problem {:keys [coeffs constraint justification] :as fact}]
  (cond
    ;; Standard impossibility: lower > upper (both present)
    (constraint-impossible? constraint)
    (assoc problem
           :possible false
           :proof-false {:justification justification
                         :constraint constraint
                         :coeffs coeffs})

    ;; Zero coefficients with one-sided constraint unsatisfied at 0
    (and (all-zero-coeffs? coeffs)
         (constraint-unsat-at-zero? constraint))
    (let [trivial-s (constraint-exact 0)
          trivial-j {:tag :trivial-zero :constraint trivial-s :coeffs coeffs}
          combined-s (constraint-combine constraint trivial-s)
          combined-j (justification-combine justification trivial-j combined-s)]
      (assoc problem
             :possible false
             :proof-false {:justification combined-j
                           :constraint combined-s
                           :coeffs coeffs}))

    :else
    (let [key (coeffs-key coeffs)]
      (-> problem
          (update :num-vars max (count coeffs))
          (assoc-in [:constraints key] fact)
          (cond->
           (constraint-is-exact? constraint)
            (update :equalities conj key))))))

(defn add-constraint
  "Add a constraint, combining with existing constraint for same coefficients."
  [problem {:keys [coeffs constraint justification] :as fact}]
  (if-not (:possible problem)
    problem
    (let [key (coeffs-key coeffs)]
      (if-let [existing (get-in problem [:constraints key])]
        (let [combined (constraint-combine constraint (:constraint existing))]
          (if (= combined (:constraint existing))
            problem
            (if (= combined constraint)
              (insert-constraint problem fact)
              (insert-constraint problem
                                 (mk-fact coeffs combined
                                          (justification-combine justification (:justification existing) combined))))))
        (if (and (nil? (:lower constraint)) (nil? (:upper constraint)))
          problem
          (insert-constraint problem fact))))))

;; ============================================================
;; Add inequality/equality (with assumption tracking)
;; ============================================================

(defn add-inequality
  "Add: const + dot(coeffs, atoms) >= 0.
   Stored as: coeffs in [-const, infinity).
   proof-fn: delayed fn producing a proof of `const + dot(coeffs, atoms) >= 0`.
   assumption-wrap-fn: wraps raw proof in addInequality_sat (provided by caller)."
  [problem const coeffs proof-fn assumption-wrap-fn]
  (let [i (count (:assumptions problem))
        s (constraint-geq (- const))
        x (vec coeffs)
        j (justification-assumption i s x)
        assumption-proof (assumption-wrap-fn const x proof-fn)
        problem (update problem :assumptions conj assumption-proof)
        fact (mk-fact x s j)]
    (add-constraint problem (tidy-fact fact))))

(defn add-equality
  "Add: const + dot(coeffs, atoms) = 0.
   Stored as: coeffs in {-const}.
   proof-fn: delayed fn producing a proof of `const + dot(coeffs, atoms) = 0`.
   assumption-wrap-fn: wraps raw proof in addEquality_sat (provided by caller)."
  [problem const coeffs proof-fn assumption-wrap-fn]
  (let [i (count (:assumptions problem))
        s (constraint-exact (- const))
        x (vec coeffs)
        j (justification-assumption i s x)
        assumption-proof (assumption-wrap-fn const x proof-fn)
        problem (update problem :assumptions conj assumption-proof)
        fact (mk-fact x s j)]
    (add-constraint problem (tidy-fact fact))))

;; ============================================================
;; Atom table
;; ============================================================

(defn mk-atom-table []
  {:expr->idx {} :idx->expr {} :idx->int-expr {} :next-idx 0})
