;; Tactic layer — linarith: linear arithmetic over ordered fields.
;;
;; Closes goals that follow from linear arithmetic over hypotheses.
;; Unlike omega (which handles Nat/Int), linarith works on any
;; ordered field (Real, Rat, etc.) by finding a non-negative linear
;; combination of hypotheses that proves the goal.
;;
;; Strategy:
;; 1. Collect linear hypotheses from the local context
;; 2. Negate the goal to get another constraint
;; 3. Find a non-negative linear combination yielding contradiction
;; 4. Construct a proof using linarith lemmas or fall back to decide
;;
;; Follows Lean 4 Mathlib's linarith tactic semantics.

(ns ansatz.tactic.linarith
  "Linear arithmetic decision procedure for ordered fields.

   Supports:
   - LE, LT, Eq, GE, GT relations
   - Linear expressions: c₁x₁ + c₂x₂ + ... + c
   - Hypotheses from the local context
   - Types with LinearOrder/Preorder (Real, Rat, Int, Nat)

   Algorithm:
   1. Collect hypotheses of the form a ≤ b, a < b, a = b
   2. Normalize to linear combinations ≥ 0
   3. Negate the goal and add to constraints
   4. Use Fourier-Motzkin elimination to find contradiction
   5. Certify: construct proof from hypothesis combination"
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.decide :as decide-tac]
            [ansatz.tactic.basic :as basic]))

;; ============================================================
;; Well-known names
;; ============================================================

(def ^:private eq-name (name/from-string "Eq"))
(def ^:private le-name (name/from-string "LE.le"))
(def ^:private lt-name (name/from-string "LT.lt"))
(def ^:private ge-name (name/from-string "GE.ge"))
(def ^:private gt-name (name/from-string "GT.gt"))
(def ^:private hadd-name (name/from-string "HAdd.hAdd"))
(def ^:private hsub-name (name/from-string "HSub.hSub"))
(def ^:private hmul-name (name/from-string "HMul.hMul"))
(def ^:private hneg-name (name/from-string "Neg.neg"))
(def ^:private ofnat-name (name/from-string "OfNat.ofNat"))
(def ^:private nat-zero-name (name/from-string "Nat.zero"))
(defn- tactic-error! [msg data]
  (throw (ex-info (str "linarith: " msg) (merge {:kind :tactic-error} data))))

;; ============================================================
;; Linear combination representation
;; ============================================================

(defn- mk-lc
  "Make a linear combination: const + Σ coeffs[i] * x_i"
  ([c] {:const (long c) :coeffs {}})
  ([c coeffs] {:const (long c) :coeffs (into {} (remove (fn [[_ v]] (zero? v))) coeffs)}))

(defn- lc-add [a b]
  (let [coeffs (merge-with + (:coeffs a) (:coeffs b))
        coeffs (into {} (remove (fn [[_ v]] (zero? v))) coeffs)]
    (mk-lc (+ (:const a) (:const b)) coeffs)))

(defn- lc-sub [a b]
  (lc-add a (mk-lc (- (:const b))
                   (into {} (map (fn [[k v]] [k (- v)])) (:coeffs b)))))

(defn- lc-scale [lc c]
  (mk-lc (* c (:const lc))
         (into {} (map (fn [[k v]] [k (* c v)])) (:coeffs lc))))

(defn- lc-negate [lc] (lc-scale lc -1))

(defn- lc-var [idx] (mk-lc 0 {idx 1}))
(defn- lc-const [c] (mk-lc c))

;; ============================================================
;; Reification: Ansatz expression → linear combination
;; ============================================================

(declare reify-linear)

(defn- intern-atom
  "Intern an opaque atom (non-linear subexpression) as a fresh variable."
  [table st expr]
  (let [w (#'tc/cached-whnf st expr)]
    (if-let [idx (get (:expr->idx table) w)]
      [table idx]
      ;; Try def-eq match with existing atoms
      (let [match (some (fn [[e idx]]
                          (when (try (tc/is-def-eq st e w) (catch Exception _ false))
                            idx))
                        (:expr->idx table))]
        (if match
          [table match]
          (let [idx (:next-idx table)
                table' (-> table
                           (assoc-in [:expr->idx w] idx)
                           (assoc-in [:idx->expr idx] w)
                           (update :next-idx inc))]
            [table' idx]))))))

(defn- try-match-head [st expr]
  (let [[head args] (e/get-app-fn-args expr)]
    (if (e/const? head)
      [(e/const-name head) (vec args)]
      (let [w (#'tc/cached-whnf st expr)
            [whead wargs] (e/get-app-fn-args w)]
        (when (e/const? whead)
          [(e/const-name whead) (vec wargs)])))))

(defn- reify-linear
  "Reify a Ansatz expression as a linear combination.
   Returns [atom-table linear-combination]."
  [st table expr]
  (let [w (#'tc/cached-whnf st expr)]
    (cond
      ;; Nat literal → constant
      (e/lit-nat? w) [table (lc-const (e/lit-nat-val w))]

      ;; Nat.zero
      (and (e/const? w) (= (e/const-name w) nat-zero-name))
      [table (lc-const 0)]

      ;; Application
      (e/app? w)
      (if-let [[hname args] (try-match-head st w)]
        (cond
          ;; OfNat.ofNat α n inst → reify n
          (and (= hname ofnat-name) (= 3 (count args)))
          (reify-linear st table (nth args 1))

          ;; HAdd.hAdd _ _ _ _ a b → a + b
          (and (= hname hadd-name) (= 6 (count args)))
          (let [[table' la] (reify-linear st table (nth args 4))
                [table'' lb] (reify-linear st table' (nth args 5))]
            [table'' (lc-add la lb)])

          ;; HSub.hSub _ _ _ _ a b → a - b
          (and (= hname hsub-name) (= 6 (count args)))
          (let [[table' la] (reify-linear st table (nth args 4))
                [table'' lb] (reify-linear st table' (nth args 5))]
            [table'' (lc-sub la lb)])

          ;; HMul.hMul _ _ _ _ a b → check if one side is constant
          (and (= hname hmul-name) (= 6 (count args)))
          (let [aw (#'tc/cached-whnf st (nth args 4))
                bw (#'tc/cached-whnf st (nth args 5))]
            (cond
              ;; c * x (c is literal)
              (e/lit-nat? aw)
              (let [[table' lb] (reify-linear st table (nth args 5))]
                [table' (lc-scale lb (e/lit-nat-val aw))])

              ;; x * c (c is literal)
              (e/lit-nat? bw)
              (let [[table' la] (reify-linear st table (nth args 4))]
                [table' (lc-scale la (e/lit-nat-val bw))])

              ;; Non-linear: intern as atom
              :else
              (let [[table' idx] (intern-atom table st w)]
                [table' (lc-var idx)])))

          ;; Neg.neg _ _ a → -a
          (and (= hname hneg-name) (= 3 (count args)))
          (let [[table' la] (reify-linear st table (nth args 2))]
            [table' (lc-negate la)])

          ;; Unknown head → atom
          :else
          (let [[table' idx] (intern-atom table st w)]
            [table' (lc-var idx)]))

        ;; Not a constant-headed app → atom
        (let [[table' idx] (intern-atom table st w)]
          [table' (lc-var idx)]))

      ;; FVar → atom
      (e/fvar? w)
      (let [[table' idx] (intern-atom table st w)]
        [table' (lc-var idx)])

      ;; Fallback → atom
      :else
      (let [[table' idx] (intern-atom table st w)]
        [table' (lc-var idx)]))))

;; ============================================================
;; Constraint extraction from hypotheses and goal
;; ============================================================

(defn- extract-constraint
  "Extract a linear constraint from a proposition type.
   Returns [atom-table {:lc LinearCombo :kind :geq/:eq}] or nil."
  [st table ty]
  (let [[head args] (e/get-app-fn-args ty)]
    (when (e/const? head)
      (let [hname (e/const-name head)]
        (cond
          ;; a ≤ b → b - a ≥ 0
          (and (= hname le-name) (>= (count args) 3))
          (let [a (nth args (- (count args) 2))
                b (nth args (- (count args) 1))
                [table' la] (reify-linear st table a)
                [table'' lb] (reify-linear st table' b)]
            [table'' {:lc (lc-sub lb la) :kind :geq}])

          ;; a < b → b - a - 1 ≥ 0 (for integers; for reals, just b - a > 0)
          (and (= hname lt-name) (>= (count args) 3))
          (let [a (nth args (- (count args) 2))
                b (nth args (- (count args) 1))
                [table' la] (reify-linear st table a)
                [table'' lb] (reify-linear st table' b)]
            ;; Treat as strict: b - a ≥ 0 with strict flag
            [table'' {:lc (lc-sub lb la) :kind :gt}])

          ;; a = b → a - b = 0
          (and (= hname eq-name) (= 3 (count args)))
          (let [a (nth args 1)
                b (nth args 2)
                [table' la] (reify-linear st table a)
                [table'' lb] (reify-linear st table' b)]
            [table'' {:lc (lc-sub la lb) :kind :eq}])

          ;; a ≥ b → a - b ≥ 0
          (and (= hname ge-name) (>= (count args) 3))
          (let [a (nth args (- (count args) 2))
                b (nth args (- (count args) 1))
                [table' la] (reify-linear st table a)
                [table'' lb] (reify-linear st table' b)]
            [table'' {:lc (lc-sub la lb) :kind :geq}])

          ;; a > b → a - b > 0
          (and (= hname gt-name) (>= (count args) 3))
          (let [a (nth args (- (count args) 2))
                b (nth args (- (count args) 1))
                [table' la] (reify-linear st table a)
                [table'' lb] (reify-linear st table' b)]
            [table'' {:lc (lc-sub la lb) :kind :gt}])

          :else nil)))))

;; ============================================================
;; Fourier-Motzkin variable elimination
;; ============================================================

(defn- fm-eliminate-var
  "Eliminate variable idx from a set of constraints via Fourier-Motzkin.
   Returns the new constraint set."
  [constraints idx]
  (let [;; Partition into positive, negative, and zero-coefficient
        pos (filter #(pos? (get-in % [:lc :coeffs idx] 0)) constraints)
        neg (filter #(neg? (get-in % [:lc :coeffs idx] 0)) constraints)
        zero (filter #(zero? (get-in % [:lc :coeffs idx] 0)) constraints)
        ;; Combine each positive with each negative
        combined (for [p pos n neg]
                   (let [pc (get-in p [:lc :coeffs idx])
                         nc (- (get-in n [:lc :coeffs idx]))
                         ;; Scale: nc * p + pc * n eliminates idx
                         new-lc (lc-add (lc-scale (:lc p) nc)
                                        (lc-scale (:lc n) pc))
                         ;; Remove the eliminated variable
                         new-lc (update new-lc :coeffs dissoc idx)
                         new-kind (if (or (= :gt (:kind p)) (= :gt (:kind n)))
                                    :gt :geq)]
                     {:lc new-lc :kind new-kind}))]
    (concat zero combined)))

(defn- fm-check-contradiction
  "Check if any constraint is contradictory (no variables, negative constant)."
  [constraints]
  (some (fn [{:keys [lc kind]}]
          (when (empty? (:coeffs lc))
            (case kind
              :geq (neg? (:const lc))        ;; c ≥ 0 is false if c < 0
              :gt (not (pos? (:const lc)))    ;; c > 0 is false if c ≤ 0
              :eq (not (zero? (:const lc)))   ;; c = 0 is false if c ≠ 0
              false)))
        constraints))

(defn- fm-solve
  "Run Fourier-Motzkin elimination on constraints.
   Returns true if a contradiction is found (goal is provable)."
  [constraints variables]
  (loop [cs constraints vars (seq (sort variables))]
    (if (fm-check-contradiction cs)
      true
      (if vars
        (recur (fm-eliminate-var cs (first vars)) (rest vars))
        false))))

;; ============================================================
;; linarith tactic
;; ============================================================

(defn linarith
  "Close the current goal using linear arithmetic over hypotheses.

   1. Collects all linear hypotheses from the local context
   2. Negates the goal to get one more constraint
   3. Runs Fourier-Motzkin elimination
   4. If contradiction found, certifies via decide or apply chain

   Falls back to omega/decide for ground integer goals."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        env (:env ps)
        st (tc/mk-tc-state env)
        st (assoc st :lctx (:lctx goal))
        table {:expr->idx {} :idx->expr {} :next-idx 0}]
    ;; Strategy 1: Try decide directly (handles ground cases)
    (or (try (decide-tac/decide ps) (catch Exception _ nil))
        ;; Strategy 2: Collect constraints and run FM
        (let [;; Collect hypothesis constraints
              [table hyp-constraints]
              (reduce (fn [[tbl cs] [id decl]]
                        (if (= :local (:tag decl))
                          (if-let [[tbl' c] (extract-constraint st tbl (:type decl))]
                            [tbl' (conj cs (assoc c :source {:kind :hyp :id id}))]
                            [tbl cs])
                          [tbl cs]))
                      [table []]
                      (:lctx goal))
              ;; Negate the goal and add as constraint
              [table goal-constraint]
              (if-let [[table' c] (extract-constraint st table (:type goal))]
                ;; Negate: if goal is a ≤ b, we add a > b (i.e. a - b > 0)
                (let [negated (case (:kind c)
                                :geq {:lc (lc-negate (:lc c)) :kind :gt}
                                :gt {:lc (lc-negate (:lc c)) :kind :geq}
                                :eq {:lc (:lc c) :kind :gt}  ;; negate equality = disequality
                                c)]
                  [table' negated])
                [table nil])
              all-constraints (if goal-constraint
                                (conj hyp-constraints (assoc goal-constraint :source {:kind :goal}))
                                hyp-constraints)
              ;; Collect all variable indices
              variables (into #{} (mapcat (fn [c] (keys (get-in c [:lc :coeffs]))))
                              all-constraints)]
          (when-not (seq all-constraints)
            (tactic-error! "no linear hypotheses found" {:goal (:type goal)}))
          ;; Run Fourier-Motzkin
          (if (fm-solve all-constraints variables)
            ;; FM found contradiction — goal is provable.
            ;; Try decide to certify (most reliable).
            (try (decide-tac/decide ps)
                 (catch Exception _
                   ;; Decide failed. Try omega.
                   (try
                     (let [omega-fn (requiring-resolve 'ansatz.tactic.omega/omega)]
                       (omega-fn ps))
                     (catch Exception _
                       ;; Last resort: try simp with relevant lemmas
                       (try
                         (let [simp-fn (requiring-resolve 'ansatz.tactic.simp/simp)]
                           (simp-fn ps ["le_refl" "Nat.zero_le" "Nat.le_refl"
                                        "le_antisymm" "le_of_eq"]))
                         (catch Exception _
                           (tactic-error! "FM found proof but certification failed"
                                          {:goal (:type goal)
                                           :hint "The goal is provable by linear arithmetic but we cannot certify it yet"})))))))
            ;; FM did not find contradiction
            (tactic-error! "could not derive contradiction from hypotheses"
                           {:goal (:type goal)
                            :num-constraints (count all-constraints)
                            :num-variables (count variables)}))))))
