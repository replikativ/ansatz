;; Port of Lean/Elab/Tactic/Omega/Core.lean: Problem, Fact, Justification,
;; solveEqualities, fourierMotzkinSelect, runOmega (checkout 55f80e10).
;; Omega problem: constraint algebra, justification tree, and problem data structures.
;;
;; This module defines the solver-independent representation of an omega problem.
;; Both the FM solver and the SMT solver operate on these structures.
;; The Justification tree is the contract between solver and proof extraction.

(ns ansatz.tactic.omega.core
  "Solver-independent omega problem representation.

   Data structures:
   - Constraint: interval [lower, upper] with nil = unbounded
   - Justification: tagged derivation tree (the proof recipe)
   - Fact: coefficients + constraint + justification
   - Problem: the full constraint system with assumptions and disjunctions

   The Justification tags form the contract between solver and proof extraction:
   :assumption, :tidy, :negate, :normalize, :combine, :combo, :bmod"
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.omega.linear-combo :as lc]
            [ansatz.tactic.omega.coeffs :as cf]
            [ansatz.tactic.omega.constraint :as c]
            [ansatz.tactic.omega.omega-m :as om]))

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

(def mk-lc lc/mk-lc)
(def lc-coordinate lc/lc-coordinate)
(def lc-add lc/lc-add)
(def lc-sub lc/lc-sub)
(def lc-negate lc/lc-negate)
(def lc-scale lc/lc-scale)
(def lc-is-zero? lc/lc-is-zero?)
(def lc-clean lc/lc-clean)
(def int-bmod cf/int-bmod)
(def coeffs-bmod cf/coeffs-bmod)
(def min-nat-abs cf/min-nat-abs)
(def max-nat-abs cf/max-nat-abs)
(def mk-constraint c/mk-constraint)
(def constraint-exact c/constraint-exact)
(def constraint-geq c/constraint-geq)
(def constraint-leq c/constraint-leq)
(def constraint-trivial c/constraint-trivial)
(def constraint-impossible? c/constraint-impossible?)
(def constraint-is-exact? c/constraint-is-exact?)
(def constraint-combine c/constraint-combine)
(def constraint-negate c/constraint-negate)
(def constraint-scale c/constraint-scale)
(def constraint-combo c/constraint-combo)

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

(defn justification-negate
  "Positivize: negate coeffs (x -> -x) and flip+negate the constraint (s -> neg s).
   j proves s.sat' x v; result proves (neg s).sat' (neg x) v.
   Reconstructed via Constraint.neg_sat + IntList.dot_neg_left."
  [j new-s new-x]
  {:tag :negate :inner j :constraint new-s :coeffs new-x})

(defn justification-normalize
  "gcd=0 normalization (lean4 normalize? zero-gcd case): an all-zero-coefficient constraint
   that is unsatisfiable at 0 maps to Constraint.impossible. j proves s.sat' x v; result
   proves (normalizeConstraint s x).sat' (normalizeCoeffs s x) v — which reduces to
   impossible.sat' — reconstructed via Lean.Omega.normalize_sat. Replaces the old :trivial-zero
   (no dot_of_left_zero / decidableBAll needed: not_sat'_of_isImpossible discharges any coeffs)."
  [j]
  {:tag :normalize :inner j})

(defn justification-bmod
  "Bmod of a justification for hard equality solving.
   j proves (exact r).sat' x v.
   Result proves (exact (bmod r m)).sat' (bmod_coeffs m i x) v."
  [j m r i]
  (let [orig-coeffs (:coeffs j)
        ;; Coeffs.set zero-extends: fresh indices may exceed this fact's length.
        bmod-cs (coeffs-bmod orig-coeffs m)
        new-coeffs (assoc (into bmod-cs (repeat (max 0 (- (inc i) (count bmod-cs))) 0)) i m)
        new-r (int-bmod r m)]
    {:tag :bmod :inner j :m m :r r :i i
     :orig-coeffs orig-coeffs
     ;; `exact (Int.bmod r m)` — exactly `Justification.bmod`'s index in lean4
     ;; (Core.lean:58). `r` is already in dot-product units (see `solve-hard-equality`).
     :constraint (constraint-exact new-r)
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

(defn positivize-fact
  "Mirror lean4 positivizeConstraint: if the leading (first non-zero) coefficient is
   negative, negate the coeffs and flip+negate the constraint so the leading coeff is
   positive. This lets opposite-sign bounds on the SAME variable share a coeffs-key and
   COMBINE into an isImpossible constraint (caught at insertion) — instead of being
   Fourier-Motzkin-combo'd into a zero-coefficient one-sided constraint that would need a
   synthetic `dot zeros v = 0` fact (`:trivial-zero` / `dot_of_left_zero`). No-op when the
   leading coeff is already non-negative. Records a :negate justification (Constraint.neg_sat)."
  [{:keys [coeffs constraint] :as fact}]
  (let [lead (some (fn [c] (when-not (zero? c) c)) coeffs)]
    (if (and lead (neg? lead))
      (let [neg-coeffs (mapv -' coeffs)
            neg-constraint (constraint-negate constraint)]
        (mk-fact neg-coeffs neg-constraint
                 (justification-negate (:justification fact) neg-constraint neg-coeffs)))
      fact)))

(defn tidy-fact
  "Tidy a fact: POSITIVIZE, then divide constraint and coefficients by the GCD of the
   coefficients. Returns the fact unchanged if neither step does anything.
   Records a :tidy justification node for proof term construction via tidy_sat.
   Uses floor division (matching Lean's Int.div) for constraint bounds.

   The positivize step must come FIRST and must happen HERE, because the `:tidy`
   justification is reconstructed with lean4's `tidyConstraint`/`tidyCoeffs`, and
   lean4 defines `tidy = positivize ∘ normalize` (Init/Omega/Constraint.lean:341).
   Positivizing afterwards instead (as `add-constraint` does for facts that never
   pass through here) makes our model disagree with the reconstruction whenever the
   leading coefficient is negative: we would compute `neg (x / g)` while the kernel
   computes `(neg x) / g` and then negates it AGAIN for our `:negate` node. The
   resulting `Constraint.isImpossible` then evaluates to `false` and the kernel
   rejects the certificate."
  [fact]
  (let [{:keys [coeffs constraint justification] :as fact} (positivize-fact fact)
        g (gcd-list coeffs)]
    (cond
      ;; gcd=0 ⟺ all coefficients zero (lean4 normalize? zero-gcd case): the constraint is
      ;; `lower ≤ 0 ≤ upper`. If unsatisfiable at 0 → Constraint.impossible ({1,0}); the
      ;; :normalize justification reconstructs via normalize_sat and the impossibility is
      ;; discharged by not_sat'_of_isImpossible (no dot_of_left_zero). If satisfiable at 0 →
      ;; trivial (dropped by add-constraint). This replaces the :trivial-zero special case.
      (zero? g)
      (if (or (and (:lower constraint) (pos? (:lower constraint)))
              (and (:upper constraint) (neg? (:upper constraint))))
        (mk-fact coeffs {:lower 1 :upper 0} (justification-normalize justification))
        (mk-fact coeffs (constraint-trivial) justification))

      (<= g 1) fact
      :else
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
   :numVars 0
   :constraints {}     ;; coeffs-key -> Fact
   :equalities #{}     ;; set of coeffs-keys that are equalities
   :eliminations []    ;; list of [fact var-idx sign]
   :possible true
   :proveFalse? nil    ;; {:justification :constraint :coeffs}
   :explanation? nil})

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
           :proveFalse? {:justification justification
                         :constraint constraint
                         :coeffs coeffs}
           :explanation? justification)

    ;; (All-zero-coefficient unsatisfiable constraints are normalized to Constraint.impossible
    ;; by tidy-fact's gcd=0 branch before reaching here, so they hit the case above. No
    ;; :trivial-zero special case — matches lean4, which folds this into normalize.)

    :else
    (let [key (coeffs-key coeffs)]
      (-> problem
          (update :numVars max (count coeffs))
          (assoc-in [:constraints key] fact)
          (cond->
           (constraint-is-exact? constraint)
            (update :equalities conj key))))))

(defn add-constraint
  "Add a constraint, combining with existing constraint for same coefficients.
   Positivizes the incoming fact first (mirror lean4) so opposite-sign bounds on the same
   variable share a coeffs-key and COMBINE — applied here (not only at assumption time) so
   Fourier-Motzkin-derived facts are normalized consistently too."
  [problem fact]
  (if-not (:possible problem)
    problem
    (let [{:keys [coeffs constraint justification] :as fact} (positivize-fact fact)
          key (coeffs-key coeffs)]
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


(defn select-equality
  "Find the best equality to solve. Prefers ±1 coefficients."
  [problem]
  (let [eqs (:equalities problem)]
    (when (seq eqs)
      (let [best (reduce (fn [best key]
                           (let [coeffs key
                                 min-abs (apply min (map safe-abs
                                                         (filter (complement zero?) coeffs)))]
                             (if (or (nil? best) (< min-abs (:min-abs best))
                                     (and (= min-abs (:min-abs best))
                                          (< (max-nat-abs coeffs) (max-nat-abs (:key best)))))
                               {:key key :min-abs min-abs}
                               best)))
                         nil eqs)]
        (when best
          [(:key best) (:min-abs best)])))))

(defn- solve-easy-equality
  "Solve an equality with a ±1 coefficient by variable elimination."
  [problem coeffs-key]
  (let [coeffs coeffs-key
        i (first (keep-indexed (fn [idx c] (when (= 1 (safe-abs c)) idx))
                               coeffs))
        sign (if (pos? (nth coeffs i)) 1 -1)
        fact (get-in problem [:constraints coeffs-key])
        old-constraints (:constraints problem)
        problem (-> (assoc problem
                           :constraints {}
                           :equalities #{}
                           :eliminations (cons [fact i sign] (:eliminations problem)))
                    (assoc :numVars (:numVars problem)))]
    (reduce (fn [p [key other-fact]]
              ;; Core.solveEasyEquality visits every constraint. Charge the host
              ;; budget before either copying it or allocating a substitution.
              (om/charge!)
              (if (= key coeffs-key)
                p
                (let [ci (get (:coeffs other-fact) i 0)]
                  (if (zero? ci)
                    (add-constraint p other-fact)
                    (let [k (*' -1 sign ci)
                          new-coeffs (vec (map-indexed
                                           (fn [idx _]
                                             (+' (*' k (get (:coeffs fact) idx 0))
                                                 (get (:coeffs other-fact) idx 0)))
                                           (range (max (count (:coeffs fact))
                                                       (count (:coeffs other-fact))))))
                          new-s (constraint-combo k (:constraint fact)
                                                    1 (:constraint other-fact))
                          new-j (justification-combo k (:justification fact)
                                                       1 (:justification other-fact)
                                                       new-s new-coeffs)
                          combined (mk-fact new-coeffs new-s new-j)]
                      (add-constraint p (tidy-fact combined)))))))
            problem
            old-constraints)))

(defn deal-with-hard-equality
  "Solve a hard equality (all |coeff| > 1) by introducing a bmod equation.
   Returns [table' problem'] with the new atom registered in the table.
   build-bmod-expr-fn: (fn [m coeffs-lean-expr atoms-expr] -> Expr) builds the
   bmod_div_term Ansatz expression for the new atom."
  [table problem coeffs-key build-bmod-expr-fn build-atoms-expr-fn]
  (let [fact (get-in problem [:constraints coeffs-key])
        coeffs (:coeffs fact)
        ;; `r` is the value of the dot product `coeffs · atoms`, i.e. the constraint's
        ;; own bound — the same `r` as lean4's `dealWithHardEquality`
        ;; (Core.lean:340, `some ⟨some r, some r'⟩`). It is NOT negated: `add-equality`
        ;; already stores `constraint-exact (- const)`, so `:lower` is in dot-product
        ;; units. Negating it here made the bmod step disagree with the justification
        ;; it was supposed to certify (`bmod_sat` wants `(exact r).sat' x v`, and the
        ;; inner proof has exactly `exact (:lower …)`), and — for EVEN `m`, where
        ;; `Int.bmod` is asymmetric — also made the new constraint numerically wrong
        ;; while the coefficients were bmod'd unnegated.
        r (:lower (:constraint fact))
        m (+' (min-nat-abs coeffs) 1)
        i (:next-idx table)
        _ (when (< i (count coeffs))
            (throw (ex-info "omega: coefficient index has no allocated atom"
                            {:kind :omega-implementation-error :operation :deal-with-hard-equality
                             :numAtoms i :coeffs coeffs})))
        bmod-div-expr (build-bmod-expr-fn m coeffs table)
        [table' [actual fresh-facts]] (om/lookup table bmod-div-expr (constantly []))
        _ (when (or (not= i actual) (nil? fresh-facts) (seq fresh-facts))
            (throw (ex-info "omega: hard equality expected a fresh atom without facts"
                            {:kind :tactic-error :tactic :omega})))
        bmod-cs (coeffs-bmod coeffs m)
        padded-coeffs (vec (concat bmod-cs (repeat (- (inc i) (count bmod-cs)) 0)))
        new-coeffs (assoc padded-coeffs i m)
        new-r (int-bmod r m)
        new-constraint (constraint-exact new-r)
        new-j (justification-bmod (:justification fact) m r i)
        new-fact (mk-fact new-coeffs new-constraint new-j)
        problem (update problem :numVars max (inc i))]
    [table' (add-constraint problem (tidy-fact new-fact))]))

(defn solve-equalities
  "Solve all equalities by variable elimination.
   Returns [table' problem'].
   build-bmod-expr-fn and build-atoms-expr-fn are needed for hard equalities."
  [table problem build-bmod-expr-fn build-atoms-expr-fn]
  (loop [table table
         problem problem]
    (om/charge!)
    (if (not (:possible problem))
      [table problem]
      (if-let [[key min-abs] (select-equality problem)]
        (if (= 1 min-abs)
          (recur table (solve-easy-equality problem key))
          (let [[table' problem'] (deal-with-hard-equality table problem key
                                                       build-bmod-expr-fn build-atoms-expr-fn)]
            (recur table' problem')))
        [table problem]))))

;; ============================================================
;; Fourier-Motzkin elimination
;; ============================================================

(defn fourier-motzkin-data
  "Prepare Fourier-Motzkin data for each variable (mirror lean4 fourierMotzkinData).
   Classify each constraint by `(constraint.scale coeff_i)`: if the scaled constraint has a
   lower bound it bounds var i from below; an upper bound bounds it from above. A constraint
   can contribute to BOTH (interval/equality). Stores the SIGNED coefficient `c` so the
   elimination combo a*f + (-b)*g cancels var i regardless of sign — this is what makes
   positivized (mixed lower/upper) constraints classify and eliminate correctly."
  [problem]
  (let [n (:numVars problem)]
    (reduce (fn [data [_key fact]]
              (reduce (fn [d i]
                        ;; Core.fourierMotzkinData traverses each fact/coordinate;
                        ;; charge the host budget before classifying it.
                        (om/charge!)
                        (let [c (get (:coeffs fact) i 0)]
                          (if (zero? c)
                            (update-in d [i :irrelevant] conj fact)
                            (let [scaled (constraint-scale c (:constraint fact))]
                              (cond-> d
                                (some? (:lower scaled)) (update-in [i :lowerBounds] conj [fact c])
                                (some? (:lower scaled)) (update-in [i :lowerExact] #(and % (= 1 (safe-abs c))))
                                (some? (:upper scaled)) (update-in [i :upperBounds] conj [fact c])
                                (some? (:upper scaled)) (update-in [i :upperExact] #(and % (= 1 (safe-abs c)))))))))
                      data (range n)))
            (vec (for [i (range n)]
                   (do (om/charge!)
                       {:var i :irrelevant [] :lowerBounds [] :upperBounds [] :lowerExact true :upperExact true})))
            (:constraints problem))))

(defn fourier-motzkin-select
  "Select the best variable to eliminate."
  [data]
  (let [data (filter #(or (seq (:lowerBounds %)) (seq (:upperBounds %))) data)]
    (when (seq data)
      (first (sort-by (fn [d]
                        (let [size (* (count (:lowerBounds d)) (count (:upperBounds d)))]
                          [(if (zero? size) 0 1)
                           (if (or (:lowerExact d) (:upperExact d)) 0 1) size]))
                      data)))))

(defn fourier-motzkin
  "One step of Fourier-Motzkin elimination."
  [problem]
  (let [data (fourier-motzkin-data problem)
        selected (fourier-motzkin-select data)]
    (if-not selected
      problem
      (let [{:keys [irrelevant lowerBounds upperBounds]} selected
            base (reduce (fn [p fact]
                           (om/charge!)
                           (add-constraint p fact))
                         (assoc problem :constraints {} :equalities #{})
                         irrelevant)]
        ;; lean4 fourierMotzkin: for (f,b) in lower, (g,a) in upper: addConstraint (Fact.combo a f (-b) g).tidy
        ;; b,a are the SIGNED coeffs of var i in f,g. The combo a*f + (-b)*g cancels var i
        ;; (a*b + (-b)*a = 0). Constraint/justification use the same a and (-b).
        (reduce (fn [p [lb-fact b]]
                  (reduce (fn [p [ub-fact a]]
                            ;; Core.fourierMotzkin's cross product can dominate a
                            ;; step: charge before allocating each combination.
                            (om/charge!)
                            (let [nb (-' b)
                                  ;; Length must be max(|f|,|g|), NOT num-vars: the proof
                                  ;; reconstructs this step with lean4's `Coeffs.combo`, whose
                                  ;; `IntList.add` is a zipWithAll and so yields exactly
                                  ;; max(|f|,|g|). Padding to num-vars here makes our model's
                                  ;; coefficient vector longer than the one in the proof TYPE;
                                  ;; the values agree but the two `List Int`s are not
                                  ;; definitionally equal (`dot` on the longer list leaves
                                  ;; stuck `0 * vᵢ` summands), and `combine_sat'` — which forces
                                  ;; one `x` on both premises — is rejected by the kernel.
                                  ;; `solve-easy-equality` already does it this way.
                                  new-coeffs (vec (map-indexed
                                                   (fn [idx _]
                                                     (+' (*' a (get (:coeffs lb-fact) idx 0))
                                                         (*' nb (get (:coeffs ub-fact) idx 0))))
                                                   (range (max (count (:coeffs lb-fact))
                                                               (count (:coeffs ub-fact))))))
                                  new-s (constraint-combo a (:constraint lb-fact)
                                                            nb (:constraint ub-fact))
                                  new-j (justification-combo a (:justification lb-fact)
                                                               nb (:justification ub-fact)
                                                               new-s new-coeffs)
                                  combined (mk-fact new-coeffs new-s new-j)]
                              (add-constraint p (tidy-fact combined))))
                          p upperBounds))
                base lowerBounds)))))

;; ============================================================
;; Public API
;; ============================================================

(defn elimination
  "Core.elimination: eliminate until impossible or structurally empty."
  [table problem build-bmod-expr-fn build-atoms-expr-fn]
  (loop [table table problem problem]
    (om/charge!)
    (if (or (not (:possible problem)) (empty? (:constraints problem)))
      [table problem]
      (let [[table problem] (solve-equalities table (fourier-motzkin problem)
                                              build-bmod-expr-fn build-atoms-expr-fn)]
        (recur table problem)))))

(defn run-omega
  "Core.runOmega: solve equalities, then eliminate (real shadow only, as in Lean)."
  [table problem build-bmod-expr-fn build-atoms-expr-fn]
  (let [[table problem] (solve-equalities table problem build-bmod-expr-fn build-atoms-expr-fn)]
    (elimination table problem build-bmod-expr-fn build-atoms-expr-fn)))

(def solve-hard-equality deal-with-hard-equality)
(def solve run-omega)
(def mk-atom-table om/mk-state)

;; Core.proof/proveFalse and the Init.Omega eval certificate builders.
(def omega-names
  "Cache of Name objects for Lean.Omega constants."
  (let [n name/from-string]
    {:linear-combo           (n "Lean.Omega.LinearCombo")
     :linear-combo-mk        (n "Lean.Omega.LinearCombo.mk")
     :linear-combo-eval      (n "Lean.Omega.LinearCombo.eval")
     :linear-combo-add       (n "Lean.Omega.LinearCombo.instAdd") ;; HAdd instance
     :linear-combo-sub       (n "Lean.Omega.LinearCombo.instSub")
     :linear-combo-neg       (n "Lean.Omega.LinearCombo.instNeg")
     :linear-combo-coordinate (n "Lean.Omega.LinearCombo.coordinate")
     :add-eval               (n "Lean.Omega.LinearCombo.add_eval")
     :sub-eval               (n "Lean.Omega.LinearCombo.sub_eval")
     :neg-eval               (n "Lean.Omega.LinearCombo.neg_eval")
     :coordinate-eval        (n "Lean.Omega.LinearCombo.coordinate_eval")
     :coordinate-eval-0      (n "Lean.Omega.LinearCombo.coordinate_eval_0")
     :coordinate-eval-1      (n "Lean.Omega.LinearCombo.coordinate_eval_1")
     :coordinate-eval-2      (n "Lean.Omega.LinearCombo.coordinate_eval_2")
     :constraint             (n "Lean.Omega.Constraint")
     :constraint-mk          (n "Lean.Omega.Constraint.mk")
     :constraint-sat         (n "Lean.Omega.Constraint.sat")
     :constraint-sat'        (n "Lean.Omega.Constraint.sat'")
     :constraint-combine     (n "Lean.Omega.Constraint.combine")
     :constraint-combo       (n "Lean.Omega.Constraint.combo")
     :constraint-scale       (n "Lean.Omega.Constraint.scale")
     :constraint-is-impossible (n "Lean.Omega.Constraint.isImpossible")
     :combine-sat'           (n "Lean.Omega.Constraint.combine_sat'")
     :combo-sat              (n "Lean.Omega.Constraint.combo_sat")
     :combo-sat'             (n "Lean.Omega.combo_sat'")
     :coeffs-combo           (n "Lean.Omega.Coeffs.combo")
     :scale-sat              (n "Lean.Omega.Constraint.scale_sat")
     :tidy-sat               (n "Lean.Omega.tidy_sat")
     :tidy-constraint        (n "Lean.Omega.tidyConstraint")
     :tidy-coeffs            (n "Lean.Omega.tidyCoeffs")
     :normalize-sat          (n "Lean.Omega.normalize_sat")
     :normalize-constraint   (n "Lean.Omega.normalizeConstraint")
     :normalize-coeffs       (n "Lean.Omega.normalizeCoeffs")
     :positivize-sat         (n "Lean.Omega.positivize_sat")
     :positivize-constraint  (n "Lean.Omega.positivizeConstraint")
     :positivize-coeffs      (n "Lean.Omega.positivizeCoeffs")
     :not-sat-impossible     (n "Lean.Omega.Constraint.not_sat'_of_isImpossible")
     :add-inequality-sat     (n "Lean.Omega.Constraint.addInequality_sat")
     :add-equality-sat       (n "Lean.Omega.Constraint.addEquality_sat")
     :coeffs                 (n "Lean.Omega.Coeffs")
     :coeffs-get             (n "Lean.Omega.Coeffs.get")
     :int-list-dot           (n "Lean.Omega.IntList.dot")
     :constraint-neg         (n "Lean.Omega.Constraint.neg")
     :constraint-neg-sat     (n "Lean.Omega.Constraint.neg_sat")
     :intlist-neg            (n "Lean.Omega.IntList.neg")
     :intlist-dot-neg-left   (n "Lean.Omega.IntList.dot_neg_left")
     ;; Arithmetic
     :nat-name               (n "Nat")
     :int-name               (n "Int")
     :nat-add                (n "Nat.add")
     :nat-sub                (n "Nat.sub")
     :nat-mul                (n "Nat.mul")
     :nat-succ               (n "Nat.succ")
     :nat-zero               (n "Nat.zero")
     :nat-div                (n "Nat.div")
     :nat-mod                (n "Nat.mod")
     :hadd                   (n "HAdd.hAdd")
     :hsub                   (n "HSub.hSub")
     :hmul                   (n "HMul.hMul")
     :hdiv                   (n "HDiv.hDiv")
     :hmod                   (n "HMod.hMod")
     :ofnat                  (n "OfNat.ofNat")
     ;; Propositions
     :eq-name                (n "Eq")
     :eq-refl                (n "Eq.refl")
     :eq-trans               (n "Eq.trans")
     :le-name                (n "LE.le")
     :lt-name                (n "LT.lt")
     :ge-name                (n "GE.ge")
     :gt-name                (n "GT.gt")
     :and-name               (n "And")
     :or-name                (n "Or")
     :not-name               (n "Not")
     :ne-name                (n "Ne")
     :false-name             (n "False")
     :true-name              (n "True")
     :nat-le                 (n "Nat.le")
     :bool-name              (n "Bool")
     :bool-true              (n "Bool.true")
     :bool-false             (n "Bool.false")
     ;; Bool→Prop bridge (see `bool-cmp-bridge`): `grind`/`simp` case-split a
     ;; `Nat.ble`/`Nat.blt` discriminant through `Bool.rec` and hand omega a
     ;; BOOLEAN equation rather than an arithmetic one.
     :nat-ble                (n "Nat.ble")
     :nat-blt                (n "Nat.blt")
     :nat-le-of-ble-eq-true  (n "Nat.le_of_ble_eq_true")     ;; ble n m = true → n ≤ m
     :nat-not-le-of-not-ble  (n "Nat.not_le_of_not_ble_eq_true") ;; ¬(ble n m = true) → ¬(n ≤ m)
     :bool-noconfusion       (n "Bool.noConfusion")
     :option-name            (n "Option")
     :option-some            (n "Option.some")
     :option-none            (n "Option.none")
     ;; Conversion lemmas (Nat → Int, hypothesis proof chain)
     :int-ofnat              (n "Int.ofNat")
     :int-negsucc            (n "Int.negSucc")
     :int-ofnat-le           (n "Int.ofNat_le")
     :int-ofnat-lt           (n "Int.ofNat_lt")
     :int-sub-nonneg-of-le   (n "Int.sub_nonneg_of_le")
     :int-sub-eq-zero-of-eq  (n "Int.sub_eq_zero_of_eq")
     :int-add-one-le-of-lt   (n "Int.add_one_le_of_lt")
     :le-of-le-of-eq         (n "le_of_le_of_eq")
     :iff-mpr                (n "Iff.mpr")
     :iff-mp                 (n "Iff.mp")
     :eq-symm                (n "Eq.symm")
     :congr-fn               (n "congr")
     :congr-arg              (n "congrArg")
     :nat-le-of-not-lt       (n "Nat.le_of_not_lt")
     :nat-lt-of-not-le       (n "Nat.lt_of_not_le")
     :nat-zero-le            (n "Nat.zero_le")
     ;; Classical.propDecidable is NONCOMPUTABLE (it is defined through the
     ;; `Classical.choice` axiom), so `decide p (Classical.propDecidable p)` is
     ;; STUCK — it never reduces to `Bool.true` and the kernel rejects any
     ;; `Eq.refl Bool Bool.true` offered as a proof of `decide p = true`.
     ;; It is therefore only usable where the INSTANCE itself is the payload
     ;; (`Decidable.byContradiction`), never under `of_decide_eq_true`; those
     ;; sites must use a computable instance (`Nat.decLt`, `Nat.decLe`, …).
     :classical-prop-dec     (n "Classical.propDecidable")
     :nat-dec-lt             (n "Nat.decLt")
     :nat-dec-le             (n "Nat.decLe")
     :of-decide-eq-true      (n "of_decide_eq_true")
     :decidable-by-contra    (n "Decidable.byContradiction")
     :absurd                 (n "absurd")
     :int-inst-le            (n "Int.instLEInt")
     :inst-le-nat            (n "instLENat")
     :inst-lt-nat            (n "instLTNat")
     ;; Nat → Int for atoms
     :nat-succ-le-of-lt      (n "Nat.succ_le_of_lt")
     :nat-lt-of-succ-le      (n "Nat.lt_of_succ_le")
     ;; GE/GT conversion
     :ge-iff-le              (n "ge_iff_le")
     :gt-iff-lt              (n "gt_iff_lt")
     :int-inst-lt            (n "Int.instLTInt")
     ;; Eq negation → disjunction
     :int-lt-or-gt-of-ne     (n "Int.lt_or_gt_of_ne")
     :nat-lt-or-gt-of-ne     (n "Nat.lt_or_gt_of_ne")
     :or-elim                (n "Or.elim")
     :false-elim             (n "False.elim")
     ;; Int negation lemmas (Iffs, use with Iff.mp)
     :int-not-lt             (n "Int.not_lt")   ;; ¬(a < b) ↔ (b ≤ a)
     :int-not-le             (n "Int.not_le")   ;; ¬(a ≤ b) ↔ (b < a)
     ;; ¬(P ∧ Q) → ¬P ∨ ¬Q. Lean core spells this `Classical.not_and_iff_not_or_not`
     ;; ({a b : Prop}, no instance) — `not_and_or` is the MATHLIB name and does not
     ;; exist in Init. The `Decidable.` variant would additionally want a
     ;; `[Decidable a]`; the Classical one is the drop-in.
     :not-and-or             (n "Classical.not_and_iff_not_or_not")
     ;; ¬(P ∨ Q) → ¬P ∧ ¬Q
     :not-or                 (n "not_or")
     :and-left               (n "And.left")
     :and-right              (n "And.right")
     ;; Nat.sub dichotomy
     :nat-le-total           (n "Nat.le_total")       ;; (m n : Nat) → m ≤ n ∨ n ≤ m
     :int-ofnat-sub          (n "Int.ofNat_sub")       ;; {m n : Nat} → n ≤ m → ↑(m - n) = ↑m - ↑n
     :nat-sub-eq-zero-of-le  (n "Nat.sub_eq_zero_of_le") ;; {n m : Nat} → n ≤ m → m - n = 0
     :and-intro              (n "And.intro")
     ;; Divisibility
     :dvd-name               (n "Dvd.dvd")
     :int-emod-eq-zero-of-dvd (n "Int.emod_eq_zero_of_dvd")   ;; a ∣ b → b % a = 0
     :int-emod-pos-of-not-dvd (n "Int.emod_pos_of_not_dvd")   ;; ¬(a ∣ b) → a = 0 ∨ 0 < b % a
     ;; Iff
     :iff-name               (n "Iff")
     :dec-not-iff            (n "Decidable.not_iff") ;; {b} {a} [dec b] : ¬(a ↔ b) ↔ (¬a ↔ b)
     ;; (P ↔ Q) ↔ ((P∧Q)∨(¬P∧¬Q)). Core has ONLY the Decidable form —
     ;; `Decidable.iff_iff_and_or_not_and_not {a b : Prop} [Decidable b]` — so unlike
     ;; the ∧/→ cases there is no instance-free drop-in and the call site must supply
     ;; a `Decidable Q`. (`iff_iff_and_or_not_and_not` is the Mathlib name.)
     :iff-iff-and-or         (n "Decidable.iff_iff_and_or_not_and_not")
     ;; Implication
     :not-or-of-imp          (n "Decidable.not_or_of_imp") ;; (P → Q) → ¬P ∨ Q
     ;; ¬(P → Q) ↔ (P ∧ ¬Q). Core name is `Classical.not_imp` ({a b : Prop}, no
     ;; instance); bare `not_imp` is Mathlib's.
     :not-imp                (n "Classical.not_imp")
     ;; Neg.neg
     :neg-name               (n "Neg.neg")
     :int-inst-neg           (n "Int.instNegInt")
     ;; Div/mod bounds
     :nat-div-mul-le-self    (n "Nat.div_mul_le_self")     ;; (m n) → m / n * n ≤ m
     :nat-mod-lt             (n "Nat.mod_lt")              ;; (x y) → 0 < y → x % y < y
     :nat-mod-add-div        (n "Nat.mod_add_div")         ;; (m k) → m % k + k * (m / k) = m
     :nat-mod-zero           (n "Nat.mod_zero")            ;; (a) → a % 0 = a
     :int-mul-ediv-self-le   (n "Int.mul_ediv_self_le")    ;; (x k) → k ≠ 0 → k*(x/k) ≤ x
     :int-lt-mul-ediv-self-add (n "Int.lt_mul_ediv_self_add") ;; (x k) → 0 < k → x < k*(x/k)+k
     ;; Dvd proof terms
     :nat-mod-eq-zero-of-dvd (n "Nat.mod_eq_zero_of_dvd")  ;; m ∣ n → n % m = 0
     :nat-emod-pos-of-not-dvd (n "Nat.emod_pos_of_not_dvd") ;; ¬(m ∣ n) → 0 < n % m
     ;; Int.ofNat cast lemma. `Int.ofNat` is a CONSTRUCTOR, so it has no `.eq_def`
     ;; equation lemma — the old `Int.ofNat.eq_def` spelling could never resolve in any
     ;; store. The real core constant is `Int.ofNat_eq_natCast (n : Nat) : Int.ofNat n = ↑n`.
     ;; Currently unreferenced (`nat-to-int` builds the cast directly); kept so the name
     ;; in this table is the one that exists.
     :int-ofnat-eq-natcast   (n "Int.ofNat_eq_natCast")
     :nat-cast-nonneg        (n "Int.natCast_nonneg")
     ;; min / max (see `reify-min-max`). There is no `Nat.min_def` in the bundled
     ;; slice. Nat min/max are transported with Lean.Omega.Int.ofNat_min/max,
     ;; then split through Int.min_def/max_def as in Frontend.handleNatCast.
     :ofnat-min             (n "Lean.Omega.Int.ofNat_min")
     :ofnat-max             (n "Lean.Omega.Int.ofNat_max")
     :int-min-def           (n "Int.min_def")
     :int-max-def           (n "Int.max_def")
     :int-inst-min          (n "Int.instMin")
     :int-inst-max          (n "Int.instMax")
     :min-name               (n "Min.min")
     :max-name               (n "Max.max")
     :min-of-le              (n "minOfLe")
     :max-of-le              (n "maxOfLe")
     :if-pos                 (n "if_pos")   ;; (c) (inst) (hc : c) (α) (t e) : ite α c inst t e = t
     :if-neg                 (n "if_neg")   ;; (c) (inst) (hc : ¬c) (α) (t e) : ite α c inst t e = e
     :decidable-em           (n "Decidable.em") ;; (p) [Decidable p] : p ∨ ¬p
     :or-inl                 (n "Or.inl")
     :or-inr                 (n "Or.inr")
     ;; Bmod (hard equality) support
     :bmod-sat               (n "Lean.Omega.bmod_sat")
     :bmod-coeffs            (n "Lean.Omega.bmod_coeffs")
     :bmod-div-term          (n "Lean.Omega.bmod_div_term")
     :intlist-bmod            (n "Lean.Omega.IntList.bmod")
     :coeffs-set              (n "Lean.Omega.Coeffs.set")}))

(def int-type (e/const' (:int-name omega-names) []))
(def u1 (lvl/succ lvl/zero))

(defn nat-to-int
  "Wrap a Nat expression in Int.ofNat."
  [nat-expr]
  (e/app (e/const' (:int-ofnat omega-names) []) nat-expr))


(declare to-lean-linear-combo)

(defn mk-eq-refl-int
  "Build @Eq.refl.{1} Int a : a = a"
  [a]
  (e/app* (e/const' (name/from-string "Eq.refl") [u1]) int-type a))

(defn mk-eq-symm
  "Build @Eq.symm.{1} Int a b prf : b = a
   given prf : a = b"
  [a b prf]
  (e/app* (e/const' (:eq-symm omega-names) [u1]) int-type a b prf))

(defn mk-eq-trans
  "Build @Eq.trans.{1} Int a b c prf1 prf2 : a = c
   given prf1 : a = b, prf2 : b = c"
  [a b c prf1 prf2]
  (e/app* (e/const' (name/from-string "Eq.trans") [u1]) int-type a b c prf1 prf2))

(defn mk-int-hadd
  "Build HAdd.hAdd Int Int Int instHAddInt."
  []
  (e/app* (e/const' (:hadd omega-names) [lvl/zero lvl/zero lvl/zero])
          int-type int-type int-type
          (e/app* (e/const' (name/from-string "instHAdd") [lvl/zero])
                  int-type (e/const' (name/from-string "Int.instAdd") []))))

(defn mk-int-hsub
  "Build HSub.hSub Int Int Int instHSubInt."
  []
  (e/app* (e/const' (:hsub omega-names) [lvl/zero lvl/zero lvl/zero])
          int-type int-type int-type
          (e/app* (e/const' (name/from-string "instHSub") [lvl/zero])
                  int-type (e/const' (name/from-string "Int.instSub") []))))

(defn mk-int-hmul
  "Build HMul.hMul Int Int Int instHMulInt."
  []
  (e/app* (e/const' (:hmul omega-names) [lvl/zero lvl/zero lvl/zero])
          int-type int-type int-type
          (e/app* (e/const' (name/from-string "instHMul") [lvl/zero])
                  int-type (e/const' (name/from-string "Int.instMul") []))))

(defn mk-int-mul
  "Build a * b : Int."
  [a b]
  (e/app* (mk-int-hmul) a b))

(defn mk-int-lit
  "Build Int.ofNat(n) for a Clojure long."
  [n]
  (e/app (e/const' (:int-ofnat omega-names) []) (e/lit-nat n)))

(defn mk-int-add
  "Build a + b : Int."
  [a b]
  (e/app* (mk-int-hadd) a b))

(defn mk-int-sub
  "Build a - b : Int."
  [a b]
  (e/app* (mk-int-hsub) a b))

(defn mk-int-add-congr
  "Build congruence proof for Int addition.
   From prf1 : a1 = a2 and prf2 : b1 = b2, produce a1 + b1 = a2 + b2.
   congrArg.{u,v} : {α : Sort u} → {β : Sort v} → {a1 a2 : α} → (f : α → β) → (h : a1 = a2) → f a1 = f a2
   congr.{u,v} : {α : Sort u} → {β : Sort v} → {f1 f2 : α → β} → {a1 a2 : α} → (hf : f1 = f2) → (ha : a1 = a2) → f1 a1 = f2 a2"
  [a1 a2 b1 b2 prf1 prf2]
  (let [hadd-fn (mk-int-hadd)
        int-to-int (e/arrow int-type int-type)
        ;; congrArg : {Int} → {Int→Int} → {a1} → {a2} → hadd → prf1 : hadd a1 = hadd a2
        step1 (e/app* (e/const' (:congr-arg omega-names) [u1 u1])
                      int-type     ;; α = Int
                      int-to-int   ;; β = Int → Int
                      a1 a2        ;; {a1} {a2}
                      hadd-fn      ;; f = hadd
                      prf1)        ;; h : a1 = a2
        ;; congr : {Int} → {Int} → {hadd a1} → {hadd a2} → {b1} → {b2} → step1 → prf2
        step2 (e/app* (e/const' (:congr-fn omega-names) [u1 u1])
                      int-type     ;; α = Int
                      int-type     ;; β = Int  (result type)
                      (e/app hadd-fn a1) ;; f1 = hadd a1
                      (e/app hadd-fn a2) ;; f2 = hadd a2
                      b1 b2        ;; {a1} {a2} in congr
                      step1        ;; hf : hadd a1 = hadd a2
                      prf2)]       ;; ha : b1 = b2
    step2))

(defn mk-int-sub-congr
  "Build congruence proof for Int subtraction.
   From prf1 : a1 = a2 and prf2 : b1 = b2, produce a1 - b1 = a2 - b2."
  [a1 a2 b1 b2 prf1 prf2]
  (let [hsub-fn (mk-int-hsub)
        int-to-int (e/arrow int-type int-type)
        step1 (e/app* (e/const' (:congr-arg omega-names) [u1 u1])
                      int-type int-to-int a1 a2 hsub-fn prf1)
        step2 (e/app* (e/const' (:congr-fn omega-names) [u1 u1])
                      int-type int-type
                      (e/app hsub-fn a1) (e/app hsub-fn a2)
                      b1 b2 step1 prf2)]
    step2))

;; Frontend.asLinearCombo delays certificate construction in MetaM. Each returned
;; eval closure enters the host work/depth guard before descending into children.
;; Eval proof functions return {:proof Expr, :lhs Expr, :rhs Expr}
;; where proof proves lhs = rhs, lhs = lc.eval atoms, rhs = int-expression.

(defn mk-lc-eval-expr
  "Build the Ansatz expression: lc.eval atoms"
  [lc atoms-expr]
  (e/app* (e/const' (:linear-combo-eval omega-names) []) (to-lean-linear-combo lc) atoms-expr))

(defn mk-eval-rfl-proof
  "Build an eval proof by reflexivity (for ground expressions where lc.eval reduces to expr)."
  [lc]
  (om/guarded (fn [atoms-expr]
    (let [eval-expr (mk-lc-eval-expr lc atoms-expr)]
      {:proof (mk-eq-refl-int eval-expr)
       :lhs eval-expr
       :rhs eval-expr}))))

(defn mk-coordinate-eval-proof
  "Build eval proof for a coordinate (atom):
   coordinate_eval i v : (coordinate i).eval v = Coeffs.get v i
   Coeffs.get v i is definitionally equal to atoms[i]."
  [idx]
  (om/guarded (fn [atoms-expr]
    (let [lc (lc-coordinate idx)
          lhs (mk-lc-eval-expr lc atoms-expr)
          rhs (e/app* (e/const' (name/from-string "Lean.Omega.Coeffs.get") [])
                      atoms-expr (e/lit-nat idx))]
      {:proof (e/app* (e/const' (:coordinate-eval omega-names) [])
                      (e/lit-nat idx) atoms-expr)
       :lhs lhs
       :rhs rhs}))))

(defn mk-add-eval-proof
  "Build eval proof for addition.
   Given prf-fn1 : l1.eval atoms = e1 and prf-fn2 : l2.eval atoms = e2,
   produce: (l1 + l2).eval atoms = e1 + e2.
   Chain: Eq.trans (add_eval) (congr prf1 prf2)"
  [lc1 lc2 proof-fn1 proof-fn2]
  (om/guarded (fn [atoms-expr]
    (let [lc1-expr (to-lean-linear-combo lc1)
          lc2-expr (to-lean-linear-combo lc2)
          result-lc (lc-add lc1 lc2)
          result-lhs (mk-lc-eval-expr result-lc atoms-expr)
          ;; add_eval l1 l2 v : (l1 + l2).eval v = l1.eval v + l2.eval v
          eval1 (mk-lc-eval-expr lc1 atoms-expr)
          eval2 (mk-lc-eval-expr lc2 atoms-expr)
          mid-expr (mk-int-add eval1 eval2)
          add-eval-prf (e/app* (e/const' (:add-eval omega-names) []) lc1-expr lc2-expr atoms-expr)
          ;; Get proofs and values from sub-proofs
          p1 (if (fn? proof-fn1) (proof-fn1 atoms-expr) proof-fn1)
          p2 (if (fn? proof-fn2) (proof-fn2 atoms-expr) proof-fn2)
          rhs1 (:rhs p1) rhs2 (:rhs p2)
          result-rhs (mk-int-add rhs1 rhs2)
          ;; congr proof: l1.eval + l2.eval = rhs1 + rhs2
          congr-prf (mk-int-add-congr eval1 rhs1 eval2 rhs2 (:proof p1) (:proof p2))]
      ;; Chain: (l1+l2).eval = l1.eval + l2.eval = rhs1 + rhs2
      {:proof (mk-eq-trans result-lhs mid-expr result-rhs add-eval-prf congr-prf)
       :lhs result-lhs
       :rhs result-rhs}))))

(defn mk-sub-eval-proof
  "Build eval proof for subtraction.
   Given prf-fn1 : l1.eval atoms = e1 and prf-fn2 : l2.eval atoms = e2,
   produce: (l1 - l2).eval atoms = e1 - e2."
  [lc1 lc2 proof-fn1 proof-fn2]
  (om/guarded (fn [atoms-expr]
    (let [lc1-expr (to-lean-linear-combo lc1)
          lc2-expr (to-lean-linear-combo lc2)
          result-lc (lc-sub lc1 lc2)
          result-lhs (mk-lc-eval-expr result-lc atoms-expr)
          eval1 (mk-lc-eval-expr lc1 atoms-expr)
          eval2 (mk-lc-eval-expr lc2 atoms-expr)
          mid-expr (mk-int-sub eval1 eval2)
          sub-eval-prf (e/app* (e/const' (:sub-eval omega-names) []) lc1-expr lc2-expr atoms-expr)
          p1 (if (fn? proof-fn1) (proof-fn1 atoms-expr) proof-fn1)
          p2 (if (fn? proof-fn2) (proof-fn2 atoms-expr) proof-fn2)
          rhs1 (:rhs p1) rhs2 (:rhs p2)
          result-rhs (mk-int-sub rhs1 rhs2)
          congr-prf (mk-int-sub-congr eval1 rhs1 eval2 rhs2 (:proof p1) (:proof p2))]
      {:proof (mk-eq-trans result-lhs mid-expr result-rhs sub-eval-prf congr-prf)
       :lhs result-lhs
       :rhs result-rhs}))))

(defn mk-int-neg
  "Build the Ansatz expression for Int negation: @Neg.neg Int Int.instNegInt c"
  [c-ansatz]
  ;; Neg.neg.{u} takes a Type u; Int : Type 0. See Init/Prelude.lean, Neg,
  ;; and Init/Omega/LinearCombo.lean, neg_eval.
  (e/app* (e/const' (name/from-string "Neg.neg") [lvl/zero])
          int-type
          (e/const' (name/from-string "Int.instNegInt") [])
          c-ansatz))

(defn mk-neg-eval-proof
  "Build eval proof for negation.
   Given prf-fn : l.eval atoms = e, produce: (-l).eval atoms = -e."
  [lc proof-fn]
  (om/guarded (fn [atoms-expr]
    (let [result-lc (lc-negate lc)
          result-lhs (mk-lc-eval-expr result-lc atoms-expr)
          eval1 (mk-lc-eval-expr lc atoms-expr)
          lc-expr (to-lean-linear-combo lc)
          neg-eval-prf (e/app* (e/const' (:neg-eval omega-names) []) lc-expr atoms-expr)
          p1 (if (fn? proof-fn) (proof-fn atoms-expr) proof-fn)
          rhs1 (:rhs p1)
          ;; neg-eval: (-lc).eval atoms = -(lc.eval atoms)
          ;; p1.proof: lc.eval atoms = rhs1
          ;; We need: (-lc).eval atoms = -rhs1
          ;; congrArg (Neg.neg Int instNegInt) p1.proof : -(lc.eval atoms) = -(rhs1)
          neg-rhs (mk-int-neg rhs1)
          neg-eval1 (mk-int-neg eval1)
          neg-fn (e/lam "_" int-type
                        (mk-int-neg (e/bvar 0))
                        :default)
          congr-prf (e/app* (e/const' (:congr-arg omega-names) [u1 u1])
                            int-type int-type eval1 rhs1 neg-fn (:proof p1))
          result-rhs neg-rhs]
      {:proof (mk-eq-trans result-lhs neg-eval1 result-rhs neg-eval-prf congr-prf)
       :lhs result-lhs
       :rhs result-rhs}))))

(defn mk-nat-hadd
  "Build HAdd.hAdd Nat Nat Nat instHAddNat a b."
  [a b]
  (e/app* (e/const' (:hadd omega-names) [lvl/zero lvl/zero lvl/zero])
          (e/const' (:nat-name omega-names) [])
          (e/const' (:nat-name omega-names) [])
          (e/const' (:nat-name omega-names) [])
          (e/app* (e/const' (name/from-string "instHAdd") [lvl/zero])
                  (e/const' (:nat-name omega-names) [])
                  (e/const' (name/from-string "instAddNat") []))
          a b))

(defn mk-nat-hmul
  "Build HMul.hMul Nat Nat Nat instHMulNat a b."
  [a b]
  (e/app* (e/const' (:hmul omega-names) [lvl/zero lvl/zero lvl/zero])
          (e/const' (:nat-name omega-names) [])
          (e/const' (:nat-name omega-names) [])
          (e/const' (:nat-name omega-names) [])
          (e/app* (e/const' (name/from-string "instHMul") [lvl/zero])
                  (e/const' (:nat-name omega-names) [])
                  (e/const' (name/from-string "instMulNat") []))
          a b))

(defn mk-nat-ofnat-lit
  "Build OfNat.ofNat Nat k (instOfNatNat k) for a ground literal k."
  [k]
  (e/app* (e/const' (:ofnat omega-names) [lvl/zero])
          (e/const' (:nat-name omega-names) [])
          (e/lit-nat k)
          (e/app (e/const' (name/from-string "instOfNatNat") []) (e/lit-nat k))))

(defn mk-eq-trans-nat
  "Build @Eq.trans.{1} Nat a b c prf1 prf2 : a = c"
  [a b c prf1 prf2]
  (e/app* (e/const' (:eq-trans omega-names) [u1])
          (e/const' (:nat-name omega-names) []) a b c prf1 prf2))

(defn mk-eq-symm-nat
  "Build @Eq.symm.{1} Nat a b prf : b = a"
  [a b prf]
  (e/app* (e/const' (:eq-symm omega-names) [u1])
          (e/const' (:nat-name omega-names) []) a b prf))

(defn mk-congr-arg-nat
  "Build congrArg.{1,1} Nat Nat a1 a2 f prf : f a1 = f a2
   given prf : a1 = a2"
  [a1 a2 f prf]
  (e/app* (e/const' (:congr-arg omega-names) [u1 u1])
          (e/const' (:nat-name omega-names) [])
          (e/const' (:nat-name omega-names) [])
          a1 a2 f prf))

(defn mk-nat-add-chain
  "Build the Nat expression: var + var + ... + var (k times) using HAdd.
   Returns var for k=1."
  [var-nat k]
  (loop [i 1 acc var-nat]
    (om/charge!)
    (if (>= i k)
      acc
      (recur (inc i) (mk-nat-hadd acc var-nat)))))

(defn mk-right-mul-expand
  "Build proof: HMul var (OfNat k) = var + var + ... + var (k times).
   Returns {:proof Expr, :lhs Expr (the HMul), :rhs Expr (the add chain)}.
   Uses Nat.mul_one for k=1 and Nat.mul_succ var (k-1) + a recursive proof for
   k>=2. (k=2 deliberately has NO special case: the obvious `Nat.mul_two` is not
   part of the bundled Init slice, and the generic Nat.mul_succ chain proves it
   just as well — `var * 2 ≡ var * succ 1 = var * 1 + var = var + var`.)"
  [var-nat k]
  (let [lhs (mk-nat-hmul var-nat (mk-nat-ofnat-lit k))]
    (cond
      (== k 1)
      ;; Nat.mul_one var : var * 1 = var
      {:proof (e/app (e/const' (name/from-string "Nat.mul_one") []) var-nat)
       :lhs lhs
       :rhs var-nat}

      :else
      ;; Nat.mul_succ var (k-1) : var * succ(k-1) = var * (k-1) + var
      ;; Since succ(OfNat (k-1)) is def-eq to OfNat k, this proves var * k = var * (k-1) + var
      (let [sub (mk-right-mul-expand var-nat (dec k))
            ;; mul_succ var (OfNat (k-1)) : HMul var (succ(OfNat(k-1))) = HMul var (OfNat(k-1)) + var
            mul-succ-prf (e/app* (e/const' (name/from-string "Nat.mul_succ") [])
                                 var-nat (mk-nat-ofnat-lit (dec k)))
            ;; sub.proof : HMul var (k-1) = add-chain_{k-1}
            ;; congrArg (fun x => HAdd x var) sub.proof : HAdd (HMul var (k-1)) var = HAdd add-chain var
            hadd-var-fn (e/lam nil (e/const' (:nat-name omega-names) [])
                               (mk-nat-hadd (e/bvar 0) (e/lift var-nat 1 0))
                               :default)
            congr-prf (mk-congr-arg-nat (:lhs sub) (:rhs sub) hadd-var-fn (:proof sub))
            ;; mid = HAdd (HMul var (k-1)) var = HAdd (lhs of sub) var
            mid (mk-nat-hadd (:lhs sub) var-nat)
            ;; result rhs = HAdd add-chain_{k-1} var
            new-rhs (mk-nat-hadd (:rhs sub) var-nat)]
        {:proof (mk-eq-trans-nat lhs mid new-rhs mul-succ-prf congr-prf)
         :lhs lhs
         :rhs new-rhs}))))

(defn mk-nat-mul-expand-proof
  "Build a Nat-level proof that mul-expr = var + var + ... + var (k times).
   literal-pos is :left (k * var, e.g. Nat.mul k var) or :right (var * k).
   k must be >= 2. Returns nil for k < 2.

   For :right: uses Nat.mul_succ chain directly.
   For :left: uses Nat.mul_comm k var, then the :right chain."
  [var-nat k literal-pos]
  (when (>= k 2)
    (case literal-pos
      :right
      ;; Direct: var * k = var + var + ... + var
      (let [{:keys [proof rhs]} (mk-right-mul-expand var-nat k)]
        proof)

      :left
      ;; k * var = var * k = var + var + ... + var
      ;; Step 1: Nat.mul_comm (OfNat k) var : HMul (OfNat k) var = HMul var (OfNat k)
      (let [k-expr (mk-nat-ofnat-lit k)
            comm-prf (e/app* (e/const' (name/from-string "Nat.mul_comm") [])
                             k-expr var-nat)
            ;; Step 2: right-chain proves HMul var k = add-chain
            right (mk-right-mul-expand var-nat k)
            ;; Chain: HMul k var = HMul var k = add-chain
            lhs (mk-nat-hmul k-expr var-nat)]
        (mk-eq-trans-nat lhs (:lhs right) (:rhs right) comm-prf (:proof right))))))

(defn mk-scale-eval-proof
  "Build eval proof for scalar multiplication.
   Strategy: expand k*x as x+x+...+x using mk-add-eval-proof, then bridge to
   Int.ofNat(original_mul_expr) using Nat.mul_succ/Nat.mul_comm chains.

   The proof chain:
   1. lc.eval atoms = rhs_a + rhs_a + ...           (by repeated add_eval)
   2. rhs_a + rhs_a + ... defEq Int.ofNat(a+a+...)  (by kernel reduction)
   3. Int.ofNat(a+a+...) = Int.ofNat(mul_expr)       (by congrArg Int.ofNat (Eq.symm bridge))
   Final: lc.eval atoms = Int.ofNat(mul_expr)  via Eq.trans.

   Parameters:
   - lc, k, proof-fn: as before
   - var-nat-expr: the Nat expression for the variable (a)
   - original-nat-expr: the original Nat mul expression (a*k or k*a)
   - literal-pos: :left if literal is first arg (k*a), :right if second (a*k)"
  [lc k proof-fn var-nat-expr original-nat-expr literal-pos]
  (cond
    (zero? k)
    (mk-eval-rfl-proof (mk-lc 0))

    (== k 1)
    proof-fn

    :else
    ;; Step 1: Build repeated addition eval proof
    (let [add-prf (loop [i 1 acc-lc lc acc-proof proof-fn]
                    ;; Charge before allocating each delayed addition node. Lean
                    ;; uses mul_eval; this retained Nat bridge is linear in k.
                    (om/charge!)
                    (if (>= i k)
                      acc-proof
                      (recur (inc i) (lc-add acc-lc lc)
                             (mk-add-eval-proof acc-lc lc acc-proof proof-fn))))
          ;; Step 2: Build Nat-level bridge proof: mul_expr = a+a+...+a
          nat-bridge (mk-nat-mul-expand-proof var-nat-expr k literal-pos)]
      (if (nil? nat-bridge)
        ;; Should not happen for k >= 2, but fall back just in case
        add-prf
        (let [original-int (nat-to-int original-nat-expr)
              nat-add-expr (mk-nat-add-chain var-nat-expr k)]
          (om/guarded (fn [atoms-expr]
            (let [p-add (if (fn? add-prf) (add-prf atoms-expr) add-prf)
                  add-rhs (:rhs p-add)
                  add-lhs (:lhs p-add)
                  ;; nat-bridge : mul_expr = a+a+... (Nat level)
                  ;; congrArg Int.ofNat nat-bridge : Int.ofNat(mul_expr) = Int.ofNat(a+a+...)
                  congr-proof (e/app* (e/const' (:congr-arg omega-names) [u1 u1])
                                      (e/const' (:nat-name omega-names) [])
                                      int-type
                                      original-nat-expr  ;; a1 = mul_expr
                                      nat-add-expr        ;; a2 = a+a+...
                                      (e/const' (:int-ofnat omega-names) [])
                                      nat-bridge)
                  ;; Eq.symm : Int.ofNat(a+a+...) = Int.ofNat(mul_expr)
                  bridge-proof (mk-eq-symm (nat-to-int original-nat-expr)
                                           (nat-to-int nat-add-expr)
                                           congr-proof)
                  ;; Final: Eq.trans p-add.proof bridge-proof
                  final-proof (mk-eq-trans add-lhs add-rhs original-int
                                           (:proof p-add) bridge-proof)]
              {:proof final-proof
               :lhs add-lhs
               :rhs original-int}))))))))

;; ============================================================
;; Reification: Ansatz expr → LinearCombo + eval proof
;; ============================================================
;;
;; reify-term returns [atom-table linear-combo eval-proof-fn]
;; where eval-proof-fn : atoms-expr → proof of (lc.eval atoms = int-version-of-expr)


(defn to-lean-int
  "Build a Ansatz expression for an Int literal."
  [n]
  (if (>= n 0)
    (e/app (e/const' (name/from-string "Int.ofNat") []) (e/lit-nat n))
    (e/app (e/const' (name/from-string "Int.negSucc") []) (e/lit-nat (dec (- n))))))

(defn to-lean-coeffs
  "Build a Ansatz expression for Coeffs (= List Int).
   List.cons.{u} : (α : Sort (u+1)) → ... ; for Int : Type 0, u = 0."
  [coeffs]
  (let [int-t (e/const' (:int-name omega-names) [])]
    (reduce (fn [acc c]
              (e/app* (e/const' (name/from-string "List.cons") [lvl/zero])
                      int-t (to-lean-int c) acc))
            (e/app (e/const' (name/from-string "List.nil") [lvl/zero]) int-t)
            (reverse coeffs))))

(defn to-lean-option-int
  "Build Option Int expression.
   Option.some.{u} : (α : Sort (u+1)) → α → Option.{u} α
   For α = Int : Type 0 = Sort 1, we need u = 0."
  [v]
  (let [int-t (e/const' (:int-name omega-names) [])]
    (if (nil? v)
      (e/app (e/const' (:option-none omega-names) [lvl/zero]) int-t)
      (e/app* (e/const' (:option-some omega-names) [lvl/zero]) int-t (to-lean-int v)))))

(defn to-lean-constraint
  "Build a Ansatz Lean.Omega.Constraint expression."
  [{:keys [lower upper]}]
  (e/app* (e/const' (:constraint-mk omega-names) [])
          (to-lean-option-int lower)
          (to-lean-option-int upper)))

(defn to-lean-linear-combo
  "Build a Ansatz Lean.Omega.LinearCombo expression."
  [{:keys [const coeffs]}]
  (e/app* (e/const' (:linear-combo-mk omega-names) [])
          (to-lean-int const)
          (to-lean-coeffs coeffs)))

;; ============================================================
;; Problem: add inequality/equality from reification
;; ============================================================

(defn mk-add-inequality-proof
  "Build a delayed proof fn for an inequality assumption.
   Given proof-fn producing `c + dot(x, v) ≥ 0`,
   returns fn that given atoms-expr and num-vars produces {:proof :constraint-ansatz :coeffs-ansatz}
   where constraint matches the addInequality_sat result type exactly:
     Constraint.mk (some (-c)) none
   Note: coefficients are NOT padded here — the proof_fn's w argument was built with
   unpadded coefficients. Padding happens via Coeffs.combo's zipWithAll at combo time."
  [const coeffs proof-fn]
  (om/guarded (fn [atoms-expr _num-vars]
    (let [c-ansatz (to-lean-int const)
          x-ansatz (to-lean-coeffs coeffs)
          neg-c (mk-int-neg c-ansatz)
          ;; Constraint as it appears in addInequality_sat's result type
          s-ansatz (e/app* (e/const' (name/from-string "Lean.Omega.Constraint.mk") [])
                           (e/app* (e/const' (name/from-string "Option.some") [lvl/zero])
                                   int-type neg-c)
                           (e/app (e/const' (name/from-string "Option.none") [lvl/zero])
                                  int-type))]
      {:proof (e/app* (e/const' (:add-inequality-sat omega-names) [])
                      c-ansatz x-ansatz atoms-expr
                      (if (fn? proof-fn) (proof-fn atoms-expr) proof-fn))
       :constraint-ansatz s-ansatz
       :coeffs-ansatz x-ansatz}))))

(defn mk-add-equality-proof
  "Build a delayed proof fn for an equality assumption.
   Given proof-fn producing `c + dot(x, v) = 0`,
   returns fn that given atoms-expr and num-vars produces {:proof :constraint-ansatz :coeffs-ansatz}
   where constraint matches the addEquality_sat result type exactly:
     Constraint.mk (some (-c)) (some (-c))
   Note: coefficients are NOT padded here."
  [const coeffs proof-fn]
  (om/guarded (fn [atoms-expr _num-vars]
    (let [c-ansatz (to-lean-int const)
          x-ansatz (to-lean-coeffs coeffs)
          neg-c (mk-int-neg c-ansatz)
          some-neg-c (e/app* (e/const' (name/from-string "Option.some") [lvl/zero])
                             int-type neg-c)
          s-ansatz (e/app* (e/const' (name/from-string "Lean.Omega.Constraint.mk") [])
                           some-neg-c some-neg-c)]
      {:proof (e/app* (e/const' (:add-equality-sat omega-names) [])
                      c-ansatz x-ansatz atoms-expr
                      (if (fn? proof-fn) (proof-fn atoms-expr) proof-fn))
       :constraint-ansatz s-ansatz
       :coeffs-ansatz x-ansatz}))))


(declare build-atoms-expr)

(defn mk-bmod-expr
  "Build Ansatz bmod_div_term expression for hard equality solving."
  [m coeffs table]
  (e/app* (e/const' (:bmod-div-term omega-names) [])
          (e/lit-nat m)
          (to-lean-coeffs coeffs)
          (build-atoms-expr table)))

(defn run-omega-solver
  "Run the FM omega solver. Returns [table problem]."
  [table problem]
  (solve table (update problem :numVars max (:next-idx table)) mk-bmod-expr build-atoms-expr))

;; ============================================================
;; Proof term construction from Justification tree
;; ============================================================

(defn pad-coeffs
  "Pad a coefficient vector with zeros to length n."
  [coeffs n]
  (let [len (count coeffs)]
    (if (>= len n)
      coeffs
      (vec (concat coeffs (repeat (- n len) 0))))))

(defn extract-proof
  "Extract a proof term from a Justification tree.
   `atoms-expr` is the Ansatz expression for the atoms list (v : List Int).
   `assumptions` is a vector of delayed proof fns.
   `num-vars` is the total number of variables — all coefficient lists are padded to this length.
   Returns {:proof expr :constraint-ansatz expr :coeffs-ansatz expr} where:
   - proof is a proof of `s.sat' x v = true`
   - constraint-ansatz is the Ansatz expression for `s` as it appears in the proof type
   - coeffs-ansatz is the Ansatz expression for `x` as it appears in the proof type
   This ensures parent steps (combo, combine) use the exact type expressions."
  [justification atoms-expr assumptions num-vars]
  (case (:tag justification)
    :assumption
    ;; assumptions[i] is a delayed proof fn returning {:proof :constraint-ansatz :coeffs-ansatz}
    ;; The constraint-ansatz and coeffs-ansatz match the proof's actual type (from addInequality_sat
    ;; or addEquality_sat), avoiding Ansatz expression mismatches (e.g. Neg.neg vs Int.ofNat).
    ;; num-vars is passed so coefficients are padded to consistent length.
    (let [proof-fn (nth assumptions (:idx justification))
          result (if (fn? proof-fn) (proof-fn atoms-expr num-vars) proof-fn)]
      (if (map? result)
        result
        ;; Legacy: plain proof expression (shouldn't happen with new proof fns)
        {:proof result
         :constraint-ansatz (to-lean-constraint (:constraint justification))
         :coeffs-ansatz (to-lean-coeffs (pad-coeffs (:coeffs justification) num-vars))}))

    :tidy
    ;; tidy_sat : sat' s x v → sat' (tidyConstraint s x) (tidyCoeffs s x) v
    ;; s and x must match the inner proof's actual Ansatz expressions (not rebuilt from stored data)
    (let [inner (extract-proof (:inner justification) atoms-expr assumptions num-vars)
          ;; Use inner proof's Ansatz expressions — these match the proof type exactly
          orig-s-ansatz (:constraint-ansatz inner)
          orig-x-ansatz (:coeffs-ansatz inner)
          proof (e/app* (e/const' (:tidy-sat omega-names) [])
                        orig-s-ansatz orig-x-ansatz atoms-expr (:proof inner))]
      {:proof proof
       :constraint-ansatz (e/app* (e/const' (name/from-string "Lean.Omega.tidyConstraint") [])
                                  orig-s-ansatz orig-x-ansatz)
       :coeffs-ansatz (e/app* (e/const' (name/from-string "Lean.Omega.tidyCoeffs") [])
                              orig-s-ansatz orig-x-ansatz)})

    :combine
    ;; combine_sat' : sat' s x v → sat' t x v → sat' (s.combine t) x v
    ;; Both children have the SAME coefficients x.
    (let [left (extract-proof (:left justification) atoms-expr assumptions num-vars)
          right (extract-proof (:right justification) atoms-expr assumptions num-vars)
          proof (e/app* (e/const' (:combine-sat' omega-names) [])
                        (:constraint-ansatz left) (:constraint-ansatz right)
                        (:coeffs-ansatz left) atoms-expr
                        (:proof left) (:proof right))]
      {:proof proof
       :constraint-ansatz (e/app* (e/const' (name/from-string "Lean.Omega.Constraint.combine") [])
                                  (:constraint-ansatz left) (:constraint-ansatz right))
       :coeffs-ansatz (:coeffs-ansatz left)})

    :combo
    ;; combo_sat' : ∀ s t a x b y v, sat' s x v → sat' t y v →
    ;;              sat' (combo a s b t) (Coeffs.combo a x b y) v
    (let [{:keys [a left b right]} justification
          left-r (extract-proof left atoms-expr assumptions num-vars)
          right-r (extract-proof right atoms-expr assumptions num-vars)
          a-int (to-lean-int a)
          b-int (to-lean-int b)
          proof (e/app* (e/const' (:combo-sat' omega-names) [])
                        (:constraint-ansatz left-r) (:constraint-ansatz right-r)
                        a-int (:coeffs-ansatz left-r)
                        b-int (:coeffs-ansatz right-r)
                        atoms-expr
                        (:proof left-r) (:proof right-r))]
      {:proof proof
       :constraint-ansatz (e/app* (e/const' (name/from-string "Lean.Omega.Constraint.combo") [])
                                  a-int (:constraint-ansatz left-r)
                                  b-int (:constraint-ansatz right-r))
       :coeffs-ansatz (e/app* (e/const' (name/from-string "Lean.Omega.Coeffs.combo") [])
                              a-int (:coeffs-ansatz left-r)
                              b-int (:coeffs-ansatz right-r))})

    :bmod
    ;; bmod_sat : (m : Nat) → (r : Int) → (i : Nat) → (x v : Coeffs) →
    ;;            (h : x.length ≤ i) → (p : Coeffs.get v i = bmod_div_term m x v) →
    ;;            (w : (exact r).sat' x v) → (exact (bmod r m)).sat' (bmod_coeffs m i x) v
    (let [{:keys [inner m r i orig-coeffs]} justification
          inner-r (extract-proof inner atoms-expr assumptions num-vars)
          m-nat (e/lit-nat m)
          r-int (to-lean-int r)
          i-nat (e/lit-nat i)
          ;; Use inner proof's coefficients — must match the proof type exactly
          x-coeffs (:coeffs-ansatz inner-r)
          nat-type (e/const' (:nat-name omega-names) [])
          bool-type (e/const' (:bool-name omega-names) [])
          bool-true (e/const' (:bool-true omega-names) [])
          ;; h : x.length ≤ i — both are concrete, so prove by decide
          len-expr (e/app* (e/const' (name/from-string "List.length") [lvl/zero])
                           int-type x-coeffs)
          le-prop (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                          nat-type (e/const' (:inst-le-nat omega-names) [])
                          len-expr i-nat)
          le-dec (e/app* (e/const' (name/from-string "Nat.decLe") [])
                         len-expr i-nat)
          decide-le (e/app* (e/const' (name/from-string "Decidable.decide") [])
                            le-prop le-dec)
          decide-le-eq (e/app* (e/const' (:eq-name omega-names) [u1])
                               bool-type decide-le bool-true)
          le-refl (e/app* (e/const' (:eq-refl omega-names) [u1]) bool-type bool-true)
          h-le (e/app* (e/const' (name/from-string "of_decide_eq_true") [])
                       le-prop le-dec le-refl)
          ;; p : Coeffs.get v i = bmod_div_term m x v — both reduce to same value, so rfl
          get-vi (e/app* (e/const' (:coeffs-get omega-names) []) atoms-expr i-nat)
          bmod-div (e/app* (e/const' (:bmod-div-term omega-names) [])
                           m-nat x-coeffs atoms-expr)
          p-eq-prop (e/app* (e/const' (:eq-name omega-names) [u1])
                            int-type get-vi bmod-div)
          p-refl (e/app* (e/const' (:eq-refl omega-names) [u1]) int-type get-vi)
          ;; bmod result: (exact (Int.bmod r m)).sat' (bmod_coeffs m i x) v
          new-r (int-bmod r m)]
      {:proof (e/app* (e/const' (:bmod-sat omega-names) [])
                      m-nat r-int i-nat x-coeffs atoms-expr
                      h-le p-refl (:proof inner-r))
       :constraint-ansatz (to-lean-constraint (constraint-exact new-r))
       ;; `Lean.Omega.bmod_coeffs (m i : Nat) (x : Coeffs) : Coeffs` — the name
       ;; `bmod_sat`'s own conclusion uses. It is NOT in the `Coeffs` namespace
       ;; (`Lean.Omega.Coeffs.bmod_coeffs` does not exist), and naming it wrongly here
       ;; made every bmod justification build an unresolvable term, which the caller
       ;; swallowed — the whole hard-equality route was dead.
       :coeffs-ansatz (e/app* (e/const' (:bmod-coeffs omega-names) [])
                              m-nat i-nat x-coeffs)})

    :negate
    ;; Positivize — lean4's `positivize_sat` verbatim:
    ;;   positivize_sat : s.sat' x v → (positivizeConstraint s x).sat' (positivizeCoeffs s x) v
    ;; The `:negate` node is emitted by `positivize-fact` exactly when x's leading
    ;; coefficient is negative, which is precisely when `positivizeConstraint`/
    ;; `positivizeCoeffs` negate — so the reconstructed constraint agrees with the
    ;; solver's model by construction.
    ;;
    ;; (This used to be hand-rolled from `Constraint.neg_sat` + `IntList.dot_neg_left`,
    ;; which produced a `Constraint.sat`-shaped statement rather than a `sat'`-shaped
    ;; one and left every parent step to close the gap by unfolding.)
    (let [inner (extract-proof (:inner justification) atoms-expr assumptions num-vars)
          s-in  (:constraint-ansatz inner)
          x-in  (:coeffs-ansatz inner)
          proof (e/app* (e/const' (:positivize-sat omega-names) [])
                        s-in x-in atoms-expr (:proof inner))]
      {:proof proof
       :constraint-ansatz (e/app* (e/const' (:positivize-constraint omega-names) []) s-in x-in)
       :coeffs-ansatz (e/app* (e/const' (:positivize-coeffs omega-names) []) s-in x-in)})

    :normalize
    ;; gcd=0 normalization (lean4 normalize_sat): from inner `s.sat' x v = true` build
    ;; `(normalizeConstraint s x).sat' (normalizeCoeffs s x) v = true`. For an all-zero-coeff
    ;; constraint unsat at 0, normalizeConstraint reduces to Constraint.impossible, so the
    ;; result is discharged by not_sat'_of_isImpossible (no dot_of_left_zero / decidableBAll).
    (let [inner (extract-proof (:inner justification) atoms-expr assumptions num-vars)
          s-in  (:constraint-ansatz inner)
          x-in  (:coeffs-ansatz inner)
          pi    (:proof inner)
          proof (e/app* (e/const' (:normalize-sat omega-names) []) s-in x-in atoms-expr pi)]
      {:proof proof
       :constraint-ansatz (e/app* (e/const' (:normalize-constraint omega-names) []) s-in x-in)
       :coeffs-ansatz (e/app* (e/const' (:normalize-coeffs omega-names) []) s-in x-in)})))

(defn build-atoms-expr
  "Build the Ansatz expression for the atoms list: [atom0, atom1, ...] : List Int.
   Uses the Int versions of atoms stored in :idx->int-expr.
   List.cons.{u} : (α : Sort (u+1)) → α → List.{u} α → List.{u} α
   For α = Int : Type 0, u = 0."
  [atom-table]
  (let [n (:next-idx atom-table)
        ;; Build atom expressions, using Int.ofNat(0) as placeholder for missing indices
        zero-int (e/app (e/const' (name/from-string "Int.ofNat") []) (e/lit-nat 0))
        atoms (for [i (range n)]
                (or (get-in atom-table [:idx->int-expr i])
                    (when-let [expr (get-in atom-table [:idx->expr i])]
                      (nat-to-int expr))
                    zero-int))]
    (reduce (fn [acc atom-expr]
              (e/app* (e/const' (name/from-string "List.cons") [lvl/zero])
                      int-type atom-expr acc))
            (e/app (e/const' (name/from-string "List.nil") [lvl/zero]) int-type)
            (reverse atoms))))

(defn build-decide-proof
  "Build a `decide` proof for a Bool equality proposition.
   of_decide_eq_true : (p : Prop) → (inst : Decidable p) → decide p inst = true → p
   For p = (f x = true), inst = instDecidableEqBool (f x) true."
  [env prop]
  ;; prop is: @Eq Bool expr Bool.true
  ;; Extract expr from prop
  (let [[_head args] (e/get-app-fn-args prop)
        ;; args = [Bool, expr, Bool.true]
        bool-expr (nth args 1)
        bool-true (e/const' (:bool-true omega-names) [])
        bool-type (e/const' (:bool-name omega-names) [])
        ;; Decidable instance: instDecidableEqBool expr true
        dec-inst (e/app* (e/const' (name/from-string "instDecidableEqBool") [])
                         bool-expr bool-true)]
    (e/app* (e/const' (name/from-string "of_decide_eq_true") [])
            prop
            dec-inst
            (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                    bool-type bool-true))))

(defn prove-false-from-justification
  "Build a proof of False from a Justification proving an impossible constraint.

   Uses: not_sat'_of_isImpossible : isImpossible s → ¬ s.sat' x v
   Which means: isImpossible s → s.sat' x v → False

   We have:
   - sat-proof: proof that s.sat' x v (from Justification tree)
   - impossible-proof: decide proof that isImpossible s = true

   Final term: not_sat'_of_isImpossible s impossible x v sat-proof"
  [env result atoms-expr]
  (let [{:keys [justification constraint coeffs]} (:proveFalse? result)
        ;; Build the sat' proof from the Justification tree
        ;; Returns {:proof :constraint-ansatz :coeffs-ansatz} with Ansatz expressions matching proof types
        sat-result (extract-proof justification atoms-expr (:assumptions result)
                                  (or (:numVars result) 0))
        sat-proof (:proof sat-result)
        ;; Use the Ansatz expressions from the proof type — these must be consistent
        ;; throughout not_sat'_of_isImpossible's arguments
        s-ansatz (:constraint-ansatz sat-result)
        x-ansatz (:coeffs-ansatz sat-result)
        ;; Build the isImpossible proof using s-ansatz (the proof's constraint).
        ;; s-ansatz may be Constraint.combine(Constraint.combo(...)) etc. but all inputs
        ;; are concrete, so isImpossible s-ansatz reduces to true via the kernel.
        impossible-prop (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                                (e/const' (:bool-name omega-names) [])
                                (e/app (e/const' (:constraint-is-impossible omega-names) []) s-ansatz)
                                (e/const' (:bool-true omega-names) []))
        impossible-proof (build-decide-proof env impossible-prop)]
    ;; not_sat'_of_isImpossible : {s} → isImpossible s = true → x → v → sat' s x v = true → False
    ;; All uses of s must be the same Ansatz expression — use s-ansatz from the proof.
    (e/app* (e/const' (:not-sat-impossible omega-names) [])
            s-ansatz
            impossible-proof
            x-ansatz
            atoms-expr
            sat-proof)))

;; ============================================================
;; Public API
;; ============================================================


(doseq [v [#'extract-proof #'mk-scale-eval-proof #'mk-right-mul-expand #'mk-nat-add-chain
           #'mk-nat-mul-expand-proof]]
  (alter-var-root v om/guarded))

(doseq [v [#'run-omega #'elimination #'solve-equalities]]
  (alter-var-root v om/guarded))
(defn solve [& args] (apply run-omega args))
