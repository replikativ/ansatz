;; Tactic layer — omega: linear arithmetic decision procedure.
;;
;; Implements Pugh's Omega Test (simplified) for Nat and Int:
;; 1. Reify: Ansatz goal/hypotheses → linear constraints
;; 2. Solve: Fourier-Motzkin variable elimination
;; 3. Certify: verify via `decide` tactic (kernel evaluation)
;;
;; Follows Lean 4's omega tactic semantics.

(ns ansatz.tactic.omega
  "Linear arithmetic decision procedure (omega tactic).

   Supports:
   - Nat: +, -, *, ≤, <, =, ≠ (with ground multiplication only)
   - Int: +, -, *, ≤, <, =, ≠ (with ground multiplication only)
   - Division and modulo by constants
   - Mixed Nat/Int via coercion
   - Systems of linear inequalities and equalities

   Algorithm:
   1. Negate the goal to get a conjunction of constraints
   2. Normalize to {const + c₁x₁ + c₂x₂ + ... ≥ 0} form
   3. Solve equalities by substitution
   4. Eliminate variables via Fourier-Motzkin
   5. Check for contradiction (empty feasible region)
   6. Certify via decide tactic"
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.decide :as decide-tac]
            [ansatz.tactic.basic :as basic]
            [ansatz.config :as config]))

;; ============================================================
;; Linear constraint representation
;; ============================================================

;; A linear combination: {:const Int, :coeffs {var-idx Int}}
;; Represents: const + Σ (coeffs[i] * x_i)
;;
;; A constraint: {:lc LinearCombo, :kind :geq | :eq}
;; :geq means lc ≥ 0, :eq means lc = 0

(defn- mk-lc
  "Make a linear combination."
  ([const] {:const (long const) :coeffs {}})
  ([const coeffs] {:const (long const) :coeffs coeffs}))

(defn- lc-const [lc] (:const lc))
(defn- lc-coeffs [lc] (:coeffs lc))

(defn- lc-var
  "Linear combination for a single variable."
  [var-idx]
  (mk-lc 0 {var-idx 1}))

(defn- lc-add
  "Add two linear combinations."
  [a b]
  {:const (+ (lc-const a) (lc-const b))
   :coeffs (merge-with + (lc-coeffs a) (lc-coeffs b))})

(defn- lc-sub
  "Subtract b from a."
  [a b]
  {:const (- (lc-const a) (lc-const b))
   :coeffs (merge-with + (lc-coeffs a)
                       (into {} (map (fn [[k v]] [k (- v)])) (lc-coeffs b)))})

(defn- lc-scale
  "Multiply a linear combination by a scalar."
  [lc k]
  {:const (* (lc-const lc) (long k))
   :coeffs (into {} (map (fn [[var c]] [var (* c (long k))])) (lc-coeffs lc))})

(defn- lc-negate [lc] (lc-scale lc -1))

(defn- lc-is-const?
  "True if lc has no variables (is a constant)."
  [lc]
  (every? zero? (vals (lc-coeffs lc))))

(defn- lc-clean
  "Remove zero-coefficient variables."
  [lc]
  (update lc :coeffs #(into {} (remove (fn [[_ v]] (zero? v))) %)))

(defn- mk-constraint [lc kind]
  {:lc (lc-clean lc) :kind kind})

(defn- mk-geq [lc] (mk-constraint lc :geq))
(defn- mk-eq [lc] (mk-constraint lc :eq))

;; ============================================================
;; Reification: Ansatz expressions → linear combinations
;; ============================================================

(defn- tactic-error! [msg data]
  (throw (ex-info (str "omega: " msg) (merge {:kind :tactic-error} data))))

;; Atom table: maps Ansatz expressions to variable indices
(defn- mk-atom-table []
  {:expr->idx {} :idx->expr {} :next-idx 0})

(defn- intern-atom
  "Intern a Ansatz expression as an atom variable. Returns [table' var-idx]."
  [table st expr]
  ;; Normalize via WHNF before interning
  (let [expr-whnf (#'tc/cached-whnf st expr)]
    (if-let [idx (get (:expr->idx table) expr-whnf)]
      [table idx]
      ;; Also check if any existing atom is def-eq
      (let [match (some (fn [[e idx]]
                          (when (tc/is-def-eq st e expr-whnf) idx))
                        (:expr->idx table))]
        (if match
          [table match]
          (let [idx (:next-idx table)
                table' (-> table
                           (assoc-in [:expr->idx expr-whnf] idx)
                           (assoc-in [:idx->expr idx] expr-whnf)
                           (update :next-idx inc))]
            [table' idx]))))))

(defn- try-match-head-raw
  "Match head constant WITHOUT WHNF fallback. Returns [head-name levels args] or nil."
  [expr]
  (let [[head args] (e/get-app-fn-args expr)]
    (when (e/const? head)
      [(e/const-name head) (e/const-levels head) (vec args)])))

(defn- try-match-head
  "Match an expression's head constant. Returns [head-name levels args] or nil.
   Tries raw expression first, falls back to WHNF."
  [st expr]
  (or (try-match-head-raw expr)
      (let [w (#'tc/cached-whnf st expr)
            [whead wargs] (e/get-app-fn-args w)]
        (when (e/const? whead)
          [(e/const-name whead) (e/const-levels whead) (vec wargs)]))))

(def ^:private nat-add-name (name/from-string "Nat.add"))
(def ^:private nat-sub-name (name/from-string "Nat.sub"))
(def ^:private nat-mul-name (name/from-string "Nat.mul"))
(def ^:private nat-succ-name (name/from-string "Nat.succ"))
(def ^:private nat-zero-name (name/from-string "Nat.zero"))
(def ^:private nat-div-name (name/from-string "Nat.div"))
(def ^:private nat-mod-name (name/from-string "Nat.mod"))
(def ^:private hadd-name (name/from-string "HAdd.hAdd"))
(def ^:private hsub-name (name/from-string "HSub.hSub"))
(def ^:private hmul-name (name/from-string "HMul.hMul"))
(def ^:private hdiv-name (name/from-string "HDiv.hDiv"))
(def ^:private hmod-name (name/from-string "HMod.hMod"))
(def ^:private ofnat-name (name/from-string "OfNat.ofNat"))

(def ^:private arithmetic-heads
  "Set of known arithmetic head constants that reify-term can decompose."
  #{hadd-name hsub-name hmul-name hdiv-name hmod-name
    nat-add-name nat-sub-name nat-mul-name nat-div-name nat-mod-name
    nat-succ-name ofnat-name})

(declare reify-term)

(defn- reify-arithmetic
  "Decompose a matched arithmetic application into a linear combination.
   matched is [head-name levels args] from try-match-head.
   expr is the original expression (used for atom interning fallback)."
  [st table expr [head-name _ args]]
  (cond
    ;; Nat.succ n → n + 1
    (and (= head-name nat-succ-name) (= 1 (count args)))
    (let [[table' lc] (reify-term st table (nth args 0))]
      [table' (lc-add lc (mk-lc 1))])

    ;; Nat.add a b → a + b
    (and (= head-name nat-add-name) (= 2 (count args)))
    (let [[table' lc-a] (reify-term st table (nth args 0))
          [table'' lc-b] (reify-term st table' (nth args 1))]
      [table'' (lc-add lc-a lc-b)])

    ;; HAdd.hAdd _ _ _ _ a b → a + b
    (and (= head-name hadd-name) (= 6 (count args)))
    (let [[table' lc-a] (reify-term st table (nth args 4))
          [table'' lc-b] (reify-term st table' (nth args 5))]
      [table'' (lc-add lc-a lc-b)])

    ;; Nat.sub a b → for ground cases evaluate, else treat as atom
    (and (= head-name nat-sub-name) (= 2 (count args)))
    (let [a-whnf (#'tc/cached-whnf st (nth args 0))
          b-whnf (#'tc/cached-whnf st (nth args 1))]
      (if (and (e/lit-nat? a-whnf) (e/lit-nat? b-whnf))
        [table (mk-lc (max 0 (- (e/lit-nat-val a-whnf) (e/lit-nat-val b-whnf))))]
        (let [[table' idx] (intern-atom table st expr)]
          [table' (lc-var idx)])))

    ;; HSub.hSub _ _ _ _ a b → a - b (for Int)
    (and (= head-name hsub-name) (= 6 (count args)))
    (let [[table' lc-a] (reify-term st table (nth args 4))
          [table'' lc-b] (reify-term st table' (nth args 5))]
      [table'' (lc-sub lc-a lc-b)])

    ;; Nat.mul a b or HMul.hMul — only ground multiplication
    (or (= head-name nat-mul-name) (= head-name hmul-name))
    (let [[a b] (if (= head-name hmul-name)
                  [(nth args 4) (nth args 5)]
                  [(nth args 0) (nth args 1)])
          a-whnf (#'tc/cached-whnf st a)
          b-whnf (#'tc/cached-whnf st b)]
      (cond
        (e/lit-nat? a-whnf)
        (let [[table' lc-b] (reify-term st table b)]
          [table' (lc-scale lc-b (e/lit-nat-val a-whnf))])
        (e/lit-nat? b-whnf)
        (let [[table' lc-a] (reify-term st table a)]
          [table' (lc-scale lc-a (e/lit-nat-val b-whnf))])
        :else
        (let [[table' idx] (intern-atom table st expr)]
          [table' (lc-var idx)])))

    ;; Nat.div / HDiv — ground only
    (or (= head-name nat-div-name) (= head-name hdiv-name))
    (let [[a b] (if (= head-name hdiv-name)
                  [(nth args 4) (nth args 5)]
                  [(nth args 0) (nth args 1)])
          a-whnf (#'tc/cached-whnf st a)
          b-whnf (#'tc/cached-whnf st b)]
      (if (and (e/lit-nat? a-whnf) (e/lit-nat? b-whnf))
        (let [bv (e/lit-nat-val b-whnf)]
          [table (mk-lc (if (zero? bv) 0 (quot (e/lit-nat-val a-whnf) bv)))])
        (let [[table' idx] (intern-atom table st expr)]
          [table' (lc-var idx)])))

    ;; Nat.mod / HMod — ground only
    (or (= head-name nat-mod-name) (= head-name hmod-name))
    (let [[a b] (if (= head-name hmod-name)
                  [(nth args 4) (nth args 5)]
                  [(nth args 0) (nth args 1)])
          a-whnf (#'tc/cached-whnf st a)
          b-whnf (#'tc/cached-whnf st b)]
      (if (and (e/lit-nat? a-whnf) (e/lit-nat? b-whnf))
        (let [bv (e/lit-nat-val b-whnf)]
          [table (mk-lc (if (zero? bv) (e/lit-nat-val a-whnf)
                            (mod (e/lit-nat-val a-whnf) bv)))])
        (let [[table' idx] (intern-atom table st expr)]
          [table' (lc-var idx)])))

    ;; OfNat.ofNat _ n _ → n
    (and (= head-name ofnat-name) (>= (count args) 2))
    (reify-term st table (nth args 1))

    ;; Unknown — intern as atom
    :else
    (let [[table' idx] (intern-atom table st expr)]
      [table' (lc-var idx)])))

(defn- reify-term
  "Reify a CIC term (Nat/Int arithmetic) into a linear combination.
   Returns [atom-table linear-combo].

   Key design: try matching arithmetic ops on the ORIGINAL expression first,
   before WHNF. WHNF can unfold HAdd.hAdd through typeclass instances into
   opaque brecOn/recursor expressions, losing the arithmetic structure that
   omega needs to decompose."
  [st table expr]
  ;; Phase 1: Try matching arithmetic on the original (un-WHNF'd) expression.
  ;; This preserves HAdd.hAdd, HMul.hMul etc. that WHNF would destroy.
  (let [pre-matched (when (e/app? expr) (try-match-head-raw expr))]
    (if (and pre-matched (contains? arithmetic-heads (first pre-matched)))
      (reify-arithmetic st table expr pre-matched)
      ;; Phase 2: WHNF and try again (handles Nat.succ, Nat.zero, literals)
      (let [expr-whnf (#'tc/cached-whnf st expr)]
        (cond
          ;; Nat literal
          (e/lit-nat? expr-whnf)
          [table (mk-lc (e/lit-nat-val expr-whnf))]

          ;; Nat.zero constructor
          (and (e/const? expr-whnf)
               (= (e/const-name expr-whnf) nat-zero-name))
          [table (mk-lc 0)]

          ;; Application — check for arithmetic ops on WHNF result
          (e/app? expr-whnf)
          (let [matched (try-match-head st expr-whnf)]
            (if (and matched (contains? arithmetic-heads (first matched)))
              (reify-arithmetic st table expr-whnf matched)
              ;; Unknown application — intern as atom
              (let [[table' idx] (intern-atom table st expr-whnf)]
                [table' (lc-var idx)])))

          ;; Free variable — intern as atom
          (e/fvar? expr-whnf)
          (let [[table' idx] (intern-atom table st expr-whnf)]
            [table' (lc-var idx)])

          ;; Constant — check for Nat.zero, else atom
          (e/const? expr-whnf)
          (if (= (e/const-name expr-whnf) nat-zero-name)
            [table (mk-lc 0)]
            (let [[table' idx] (intern-atom table st expr-whnf)]
              [table' (lc-var idx)]))

          ;; Anything else — intern as atom
          :else
          (let [[table' idx] (intern-atom table st expr-whnf)]
            [table' (lc-var idx)]))))))

;; ============================================================
;; Reification: Ansatz propositions → constraints
;; ============================================================

(def ^:private eq-name (name/from-string "Eq"))
(def ^:private le-name (name/from-string "LE.le"))
(def ^:private lt-name (name/from-string "LT.lt"))
(def ^:private ge-name (name/from-string "GE.ge"))
(def ^:private gt-name (name/from-string "GT.gt"))
(def ^:private and-name (name/from-string "And"))
(def ^:private or-name (name/from-string "Or"))
(def ^:private not-name (name/from-string "Not"))
(def ^:private ne-name (name/from-string "Ne"))
(def ^:private false-name (name/from-string "False"))
(def ^:private true-name (name/from-string "True"))
(def ^:private nat-le-name (name/from-string "Nat.le"))
(declare reify-prop)

(defn- reify-prop
  "Reify a Ansatz proposition into a list of constraints.
   Returns [atom-table [constraint ...]]."
  [st table prop]
  (let [matched (try-match-head st prop)]
    (if-not matched
      ;; Can't reify — just skip this hypothesis
      [table []]
      (let [[head-name _ args] matched]
        (cond
          ;; Eq _ a b → a - b = 0
          ;; Special case: Eq Bool (Nat.ble a b) true/false → a ≤ b / a > b
          (and (= head-name eq-name) (= 3 (count args)))
          (let [;; Check Nat.ble BEFORE whnf (whnf expands Nat.ble to its definition)
                lhs-raw (nth args 1)
                rhs-w (#'tc/cached-whnf st (nth args 2))
                [lh la] (e/get-app-fn-args lhs-raw)]
            (if (and (e/const? lh)
                     (= (name/->string (e/const-name lh)) "Nat.ble")
                     (= 2 (count la)))
              ;; Nat.ble a b = true/false → LE constraint
              (let [[table' lc-a] (reify-term st table (nth la 0))
                    [table'' lc-b] (reify-term st table' (nth la 1))]
                (cond
                  (and (e/const? rhs-w) (= (name/->string (e/const-name rhs-w)) "Bool.true"))
                  [table'' [(mk-geq (lc-sub lc-b lc-a))]]   ;; a ≤ b → b - a ≥ 0
                  (and (e/const? rhs-w) (= (name/->string (e/const-name rhs-w)) "Bool.false"))
                  [table'' [(mk-geq (lc-add (lc-sub lc-a lc-b) (mk-lc -1)))]]  ;; ¬(a ≤ b) → a - b ≥ 1
                  :else [table []]))
              ;; General Eq: a - b = 0
              (let [[table' lc-a] (reify-term st table (nth args 1))
                    [table'' lc-b] (reify-term st table' (nth args 2))]
                [table'' [(mk-eq (lc-sub lc-a lc-b))]])))

          ;; LE.le _ _ a b → b - a ≥ 0
          (and (= head-name le-name) (= 4 (count args)))
          (let [[table' lc-a] (reify-term st table (nth args 2))
                [table'' lc-b] (reify-term st table' (nth args 3))]
            [table'' [(mk-geq (lc-sub lc-b lc-a))]])

          ;; Nat.le a b → b - a ≥ 0
          (and (= head-name nat-le-name) (= 2 (count args)))
          (let [[table' lc-a] (reify-term st table (nth args 0))
                [table'' lc-b] (reify-term st table' (nth args 1))]
            [table'' [(mk-geq (lc-sub lc-b lc-a))]])

          ;; LT.lt _ _ a b → b - a - 1 ≥ 0 (i.e. b ≥ a + 1)
          (and (= head-name lt-name) (= 4 (count args)))
          (let [[table' lc-a] (reify-term st table (nth args 2))
                [table'' lc-b] (reify-term st table' (nth args 3))]
            [table'' [(mk-geq (lc-add (lc-sub lc-b lc-a) (mk-lc -1)))]])

          ;; GE.ge _ _ a b → a - b ≥ 0
          (and (= head-name ge-name) (= 4 (count args)))
          (let [[table' lc-a] (reify-term st table (nth args 2))
                [table'' lc-b] (reify-term st table' (nth args 3))]
            [table'' [(mk-geq (lc-sub lc-a lc-b))]])

          ;; GT.gt _ _ a b → a - b - 1 ≥ 0
          (and (= head-name gt-name) (= 4 (count args)))
          (let [[table' lc-a] (reify-term st table (nth args 2))
                [table'' lc-b] (reify-term st table' (nth args 3))]
            [table'' [(mk-geq (lc-add (lc-sub lc-a lc-b) (mk-lc -1)))]])

          ;; And p q → constraints from p ++ constraints from q
          (and (= head-name and-name) (= 2 (count args)))
          (let [[table' cs-a] (reify-prop st table (nth args 0))
                [table'' cs-b] (reify-prop st table' (nth args 1))]
            [table'' (into cs-a cs-b)])

          ;; Or p q → disjunction of branches
          (and (= head-name or-name) (= 2 (count args)))
          (let [[table' cs-a] (reify-prop st table (nth args 0))
                [table'' cs-b] (reify-prop st table' (nth args 1))]
            (if (and (seq cs-a) (seq cs-b))
              [table'' [{:disjunction [cs-a cs-b]}]]
              ;; One branch is empty (trivially true) — skip
              [table'' []]))

          ;; Not (Eq _ a b) → ≠ becomes a disjunction: a > b ∨ b > a
          (and (= head-name not-name) (= 1 (count args)))
          (let [inner (nth args 0)
                inner-matched (try-match-head st inner)]
            (if (and inner-matched
                     (= (first inner-matched) eq-name)
                     (= 3 (count (nth inner-matched 2))))
              ;; Not (Eq T a b) → (a - b ≥ 1) ∨ (b - a ≥ 1)
              (let [iargs (nth inner-matched 2)
                    [table' lc-a] (reify-term st table (nth iargs 1))
                    [table'' lc-b] (reify-term st table' (nth iargs 2))]
                [table'' [{:disjunction
                           [[(mk-geq (lc-add (lc-sub lc-a lc-b) (mk-lc -1)))]
                            [(mk-geq (lc-add (lc-sub lc-b lc-a) (mk-lc -1)))]]}]])
              ;; Not something else — skip
              [table []]))

          ;; Ne _ a b → same as Not (Eq _ a b)
          (and (= head-name ne-name) (>= (count args) 3))
          (let [[table' lc-a] (reify-term st table (nth args 1))
                [table'' lc-b] (reify-term st table' (nth args 2))]
            [table'' [{:disjunction
                       [[(mk-geq (lc-add (lc-sub lc-a lc-b) (mk-lc -1)))]
                        [(mk-geq (lc-add (lc-sub lc-b lc-a) (mk-lc -1)))]]}]])

          ;; False → immediate contradiction
          (= head-name false-name)
          [table [(mk-geq (mk-lc -1))]] ;; -1 ≥ 0 is impossible

          ;; True → no constraint
          (= head-name true-name)
          [table []]

          ;; Unknown proposition — skip
          :else
          [table []])))))

;; ============================================================
;; Fourier-Motzkin variable elimination
;; ============================================================

(defn- constraint-has-var?
  "Does this constraint involve variable var-idx?"
  [c var-idx]
  (not (zero? (get (lc-coeffs (:lc c)) var-idx 0))))

(defn- constraint-coeff
  "Get the coefficient of var-idx in constraint c."
  [c var-idx]
  (get (lc-coeffs (:lc c)) var-idx 0))

(defn- is-contradictory?
  "Check if a constant constraint is contradictory.
   For :geq, const < 0 is contradictory.
   For :eq, const ≠ 0 is contradictory."
  [c]
  (when (lc-is-const? (:lc c))
    (case (:kind c)
      :geq (neg? (lc-const (:lc c)))
      :eq (not (zero? (lc-const (:lc c))))
      false)))

(defn- solve-equalities
  "Eliminate variables from equality constraints by substitution.
   Returns updated constraint list."
  [constraints]
  (loop [constraints constraints]
    (let [;; Find an equality with a ±1 coefficient (easy elimination)
          easy-eq (first
                   (keep (fn [c]
                           (when (= :eq (:kind c))
                             (let [coeffs (lc-coeffs (:lc c))]
                               (some (fn [[var coeff]]
                                       (when (or (= 1 coeff) (= -1 coeff))
                                         {:constraint c :var var :coeff coeff}))
                                     coeffs))))
                         constraints))]
      (if-not easy-eq
        constraints
        ;; Substitute: var = -(rest of lc) / coeff
        (let [{:keys [constraint var coeff]} easy-eq
              ;; Build substitution: var = -(const + other_coeffs) / coeff
              ;; Remove var from the lc, negate, divide by coeff
              lc (:lc constraint)
              lc-without-var (update lc :coeffs dissoc var)
              ;; var = -lc-without-var / coeff
              subst-lc (lc-scale (lc-negate lc-without-var)
                                 (if (= 1 coeff) 1 -1))
              ;; Apply substitution to all other constraints
              new-constraints
              (keep (fn [c]
                      (when-not (= c constraint)
                        (let [c-coeff (constraint-coeff c var)]
                          (if (zero? c-coeff)
                            c
                            ;; Replace var with subst-lc * c-coeff
                            (let [new-lc (lc-add
                                          (update (:lc c) :coeffs dissoc var)
                                          (lc-scale subst-lc c-coeff))]
                              (mk-constraint (lc-clean new-lc) (:kind c)))))))
                    constraints)]
          (recur (vec new-constraints)))))))

(defn- gcd-coeffs
  "Compute GCD of all coefficients in a linear combination (for tightening)."
  [lc]
  (let [coeffs (filter (complement zero?) (vals (lc-coeffs lc)))]
    (if (empty? coeffs)
      1
      (reduce (fn [g c] (long (Math/abs ^long (loop [a (Math/abs ^long g)
                                                     b (Math/abs ^long c)]
                                                (if (zero? b) a (recur b (mod a b)))))))
              (first coeffs) (rest coeffs)))))

(defn- tighten-constraint
  "Tighten an inequality by dividing by GCD and rounding."
  [c]
  (if (= :eq (:kind c))
    (let [g (gcd-coeffs (:lc c))]
      (cond
        (<= g 1) c
        ;; If const not divisible by GCD, equality is impossible (e.g. 2x + 4y = 5)
        (not (zero? (mod (lc-const (:lc c)) g)))
        (mk-eq (mk-lc 1)) ;; 1 = 0, contradiction
        ;; Divide everything by GCD
        :else
        (mk-eq (mk-lc (quot (lc-const (:lc c)) g)
                      (into {} (map (fn [[k v]] [k (quot v g)])) (lc-coeffs (:lc c)))))))
    ;; For inequalities: divide by GCD, floor the constant
    (let [g (gcd-coeffs (:lc c))]
      (if (<= g 1)
        c
        (mk-geq (mk-lc (long (Math/floor (/ (double (lc-const (:lc c))) g)))
                       (into {} (map (fn [[k v]] [k (quot v g)])) (lc-coeffs (:lc c)))))))))

(defn- fourier-motzkin-eliminate
  "Eliminate one variable from a system of inequality constraints.
   Returns updated constraint list."
  [constraints var-idx]
  (let [;; Partition constraints by the sign of var-idx's coefficient
        involved (filter #(constraint-has-var? % var-idx) constraints)
        uninvolved (remove #(constraint-has-var? % var-idx) constraints)
        lower-bounds (filter #(pos? (constraint-coeff % var-idx)) involved)
        upper-bounds (filter #(neg? (constraint-coeff % var-idx)) involved)
        ;; Combine each lower bound with each upper bound
        new-constraints
        (for [lb lower-bounds
              ub upper-bounds]
          (let [lb-coeff (constraint-coeff lb var-idx) ;; positive
                ub-coeff (- (constraint-coeff ub var-idx)) ;; make positive
                ;; Multiply: ub-coeff * lb + lb-coeff * ub
                ;; This eliminates var-idx
                combined-lc (lc-add (lc-scale (:lc lb) ub-coeff)
                                    (lc-scale (:lc ub) lb-coeff))]
            (tighten-constraint (mk-geq (lc-clean combined-lc)))))]
    (into (vec uninvolved) new-constraints)))

(defn- get-variables
  "Get all variable indices appearing in the constraint system."
  [constraints]
  (into #{} (mapcat #(keys (lc-coeffs (:lc %)))) constraints))

(defn- select-variable
  "Select the best variable to eliminate.
   Prefer variables with fewer constraints (minimize blowup)."
  [constraints variables]
  (apply min-key
         (fn [var]
           (let [involved (filter #(constraint-has-var? % var) constraints)
                 pos (count (filter #(pos? (constraint-coeff % var)) involved))
                 neg (count (filter #(neg? (constraint-coeff % var)) involved))]
             ;; Fourier-Motzkin produces pos * neg new constraints
             ;; Prefer exact elimination (pos=1 or neg=1) or small product
             (* pos neg)))
         variables))

(defn- solve-system
  "Solve a system of linear constraints.
   Returns :sat if satisfiable, :unsat if contradictory."
  [constraints]
  (let [;; First, solve equalities
        constraints (solve-equalities constraints)
        ;; Check for immediate contradictions
        contradiction (some is-contradictory? constraints)]
    (if contradiction
      :unsat
      ;; Fourier-Motzkin elimination on remaining variables
      (loop [constraints constraints
             max-iters 100]
        (if (zero? max-iters)
          :sat ;; Give up — couldn't prove contradiction
          (let [;; Check for contradiction
                contradiction (some is-contradictory? constraints)]
            (if contradiction
              :unsat
              (let [vars (get-variables constraints)]
                (if (empty? vars)
                  :sat ;; No variables left, no contradiction
                  (let [var (select-variable constraints vars)
                        ;; Split equalities into two inequalities
                        constraints (mapcat (fn [c]
                                              (if (= :eq (:kind c))
                                                [(mk-geq (:lc c))
                                                 (mk-geq (lc-negate (:lc c)))]
                                                [c]))
                                            constraints)
                        constraints (fourier-motzkin-eliminate (vec constraints) var)]
                    (recur constraints (dec max-iters))))))))))))

;; ============================================================
;; Goal processing: negate and collect constraints
;; ============================================================

(defn- add-nat-nonnegativity
  "For each Nat-typed atom, add x ≥ 0 constraint."
  [st table constraints]
  (let [nat-name (name/from-string "Nat")]
    (reduce
     (fn [[table constraints] [idx expr]]
       (try
         (let [ty (tc/infer-type st expr)
               ty-whnf (#'tc/cached-whnf st ty)]
           (if (and (e/const? ty-whnf) (= (e/const-name ty-whnf) nat-name))
             [table (conj constraints (mk-geq (lc-var idx)))]
             [table constraints]))
         (catch Exception _ [table constraints])))
     [table constraints]
     (:idx->expr table))))

(defn- negate-goal
  "Negate the goal to get constraints for the Omega test.
   If goal is P, we assume ¬P and try to derive False."
  [st table goal-type]
  (let [matched (try-match-head st goal-type)]
    (if-not matched
      [table []]
      (let [[head-name _ args] matched]
        (cond
          ;; Goal: Eq _ a b → assume a ≠ b → a - b ≥ 1 or b - a ≥ 1
          ;; For omega, we handle this by trying both: a > b and b > a
          ;; Actually, for integer arithmetic: ¬(a = b) ↔ (a > b) ∨ (b > a)
          ;; We can't directly handle disjunctions, so we try both branches
          (and (= head-name eq-name) (= 3 (count args)))
          (let [[table' lc-a] (reify-term st table (nth args 1))
                [table'' lc-b] (reify-term st table' (nth args 2))]
            ;; ¬(a = b) means a - b ≥ 1 ∨ b - a ≥ 1
            ;; We'll try each branch separately in the solver
            [table'' [{:disjunction
                       [[(mk-geq (lc-add (lc-sub lc-a lc-b) (mk-lc -1)))]
                        [(mk-geq (lc-add (lc-sub lc-b lc-a) (mk-lc -1)))]]}]])

          ;; Goal: LE.le _ _ a b → assume ¬(a ≤ b) → b < a → a - b ≥ 1
          (and (= head-name le-name) (= 4 (count args)))
          (let [[table' lc-a] (reify-term st table (nth args 2))
                [table'' lc-b] (reify-term st table' (nth args 3))]
            [table'' [(mk-geq (lc-add (lc-sub lc-a lc-b) (mk-lc -1)))]])

          ;; Goal: LT.lt _ _ a b → assume ¬(a < b) → b ≤ a → a - b ≥ 0
          (and (= head-name lt-name) (= 4 (count args)))
          (let [[table' lc-a] (reify-term st table (nth args 2))
                [table'' lc-b] (reify-term st table' (nth args 3))]
            [table'' [(mk-geq (lc-sub lc-a lc-b))]])

          ;; Goal: GE.ge _ _ a b → assume ¬(a ≥ b) → a < b → b - a ≥ 1
          (and (= head-name ge-name) (= 4 (count args)))
          (let [[table' lc-a] (reify-term st table (nth args 2))
                [table'' lc-b] (reify-term st table' (nth args 3))]
            [table'' [(mk-geq (lc-add (lc-sub lc-b lc-a) (mk-lc -1)))]])

          ;; Goal: GT.gt _ _ a b → assume ¬(a > b) → a ≤ b → b - a ≥ 0
          (and (= head-name gt-name) (= 4 (count args)))
          (let [[table' lc-a] (reify-term st table (nth args 2))
                [table'' lc-b] (reify-term st table' (nth args 3))]
            [table'' [(mk-geq (lc-sub lc-b lc-a))]])

          ;; Goal: Not P → assume P
          (and (= head-name not-name) (= 1 (count args)))
          (reify-prop st table (nth args 0))

          ;; Goal: False → trivially unprovable... but if we have contradictory hyps, ok
          (= head-name false-name)
          [table []]

          ;; Unknown goal — can't negate
          :else
          [table []])))))

;; ============================================================
;; Hypothesis collection
;; ============================================================

(defn- collect-hypotheses
  "Collect constraints from all hypotheses in the local context."
  [st table lctx]
  (reduce
   (fn [[table constraints] [id decl]]
     (if (= :local (:tag decl))
       (try
         (let [[table' new-cs] (reify-prop st table (:type decl))]
           [table' (into constraints new-cs)])
         (catch Exception _ [table constraints]))
       [table constraints]))
   [table []]
   lctx))

;; ============================================================
;; Main omega solver
;; ============================================================

(defn- omega-check
  "Run the omega algorithm on the goal.
   Returns true if the goal can be proved (constraints are contradictory)."
  [st goal-type lctx]
  (let [table (mk-atom-table)
        ;; Collect hypothesis constraints
        [table hyp-constraints] (collect-hypotheses st table lctx)
        ;; Negate the goal
        [table goal-negation] (negate-goal st table goal-type)
        ;; Separate plain constraints from disjunctions
        plain-constraints (filter #(and (map? %) (not (:disjunction %))) goal-negation)
        disjunctions (filter :disjunction goal-negation)
        ;; Add Nat non-negativity constraints
        [table hyp-constraints] (add-nat-nonnegativity st table
                                                       (into (vec hyp-constraints)
                                                             plain-constraints))]
    (if (empty? disjunctions)
      ;; No disjunctions — solve directly
      (let [all-constraints (into (vec hyp-constraints) plain-constraints)]
        (= :unsat (solve-system all-constraints)))
      ;; With disjunctions — take cartesian product of all branches
      ;; Each disjunction adds alternatives; we need ALL combinations to be unsat
      (let [;; Build list of branch-lists from each disjunction
            branch-lists (mapv :disjunction disjunctions)
            ;; Cartesian product of all branch combinations
            combinations (reduce (fn [acc branches]
                                   (for [existing acc
                                         branch branches]
                                     (into existing branch)))
                                 [[]]
                                 branch-lists)]
        (every? (fn [branch-constraints]
                  (let [all-constraints (-> (vec hyp-constraints)
                                            (into plain-constraints)
                                            (into branch-constraints))]
                    (= :unsat (solve-system all-constraints))))
                combinations)))))

;; ============================================================
;; Public API
;; ============================================================

(defn- try-rfl
  "Try to close an Eq goal by reflexivity."
  [ps]
  (let [goal (proof/current-goal ps)]
    (when goal
      (let [st (tc/mk-tc-state (:env ps))
            st (assoc st :lctx (:lctx goal))
            goal-type (#'tc/cached-whnf st (:type goal))
            [head args] (e/get-app-fn-args goal-type)]
        (when (and (e/const? head)
                   (= (e/const-name head) eq-name)
                   (= 3 (count args)))
          (let [lhs (nth args 1)
                rhs (nth args 2)]
            (when (tc/is-def-eq st lhs rhs)
              ;; Sides are def-eq, build Eq.refl proof
              (let [eq-levels (e/const-levels head)
                    proof-term (e/app* (e/const' (name/from-string "Eq.refl")
                                                 eq-levels)
                                       (nth args 0) lhs)]
                (proof/assign-mvar ps (:id goal)
                                   {:kind :exact :term proof-term})))))))))

(defn omega
  "Close the current goal using the omega decision procedure.

   Works for:
   - Nat/Int linear arithmetic goals (=, ≤, <, ≥, >)
   - With hypotheses providing additional constraints
   - Ground multiplication (e.g., 2*x but not x*y)

   Strategy:
   1. Try decide first (handles many ground cases directly)
   2. Try rfl for equality goals where sides are def-eq
   3. If both fail, run Fourier-Motzkin solver + decide to certify

   The kernel always verifies the final proof term."
  [ps]
  ;; First try decide directly — it's faster for ground cases
  (try
    (decide-tac/decide ps)
    (catch Exception _
      ;; Try rfl for equality goals
      (or (try-rfl ps)
          ;; Decide and rfl failed — run the omega algorithm
          (let [goal (proof/current-goal ps)
                _ (when-not goal
                    (tactic-error! "No goals" {}))
                env (:env ps)
                st (tc/mk-tc-state env)
                st (assoc st :lctx (:lctx goal))]
            ;; Check if omega can solve this
            (when-not (omega-check st (:type goal) (:lctx goal))
              (tactic-error! "omega failed — could not derive contradiction from linear constraints"
                             {:goal (:type goal)
                              :hint "Ensure goal involves only linear arithmetic (=, ≤, <, ≥, >) on Nat/Int"}))
            ;; Omega says it's provable. Try decide to certify.
            (try
              (decide-tac/decide ps)
              (catch Exception _
                ;; Decide failed (non-ground goal).
                ;; Try to build proof from known lemmas.
                ;; Lean 4's omega has its own proof builder; we use simp + apply.
                (or
                 ;; Strategy 0: try full omega proof builder (requires Lean.Omega.* constants)
                 (try
                   (let [omega-full (requiring-resolve 'ansatz.tactic.omega-proof/omega)]
                     (omega-full ps))
                   (catch Exception e
                     (when (System/getProperty "omega.trace")
                       (println "[omega] Strategy 0 failed:" (.getMessage e)))
                     nil))
                 ;; Strategy A: try simp with omega-relevant lemmas
                 (try
                   (require 'ansatz.tactic.simp)
                   (let [simp-fn (resolve 'ansatz.tactic.simp/simp)]
                     (simp-fn ps ["Nat.zero_le" "Nat.le_refl" "Nat.zero_add"
                                  "Nat.add_zero" "Nat.le.refl"]))
                   (catch Exception _ nil))
                 ;; Strategy B: for LE goals, try Nat.zero_le n directly
                 (try
                   (let [goal-type (:type goal)
                         [head args] (e/get-app-fn-args goal-type)]
                     (when (and (e/const? head)
                                (= (name/->string (e/const-name head)) "LE.le")
                                (>= (count args) 4))
                       (let [lhs (nth args 2)
                             rhs (nth args 3)
                             lhs-whnf (#'tc/cached-whnf st lhs)]
                         ;; 0 ≤ n → Nat.zero_le n
                         (when (and (e/lit-nat? lhs-whnf) (= 0 (e/lit-nat-val lhs-whnf)))
                           (let [proof (e/app (e/const' (name/from-string "Nat.zero_le") []) rhs)]
                             (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof})
                                 (proof/record-tactic :omega [:zero-le] (:id goal))))))))
                   (catch Exception _ nil))
                 ;; Strategy C: construct proof term directly and verify with Java TC.
                 ;; For LE goals where omega found a proof, try building the term.
                 (try
                   (let [goal-type (:type goal)
                         [head args] (e/get-app-fn-args goal-type)]
                     (when (and (e/const? head)
                                (= (name/->string (e/const-name head)) "LE.le")
                                (>= (count args) 4))
                       (let [lhs (nth args 2)
                             rhs (nth args 3)
                             le-add-right-n (name/from-string "Nat.le_add_right")
                             le-add-left-n (name/from-string "Nat.le_add_left")
                             le-trans-n (name/from-string "Nat.le_trans")
                             le-refl-n (name/from-string "Nat.le.refl")
                             jtc (ansatz.kernel.TypeChecker. (:env ps))
                             _ (.setFuel jtc config/*default-fuel*)
                             ;; Register goal's local context with Java TC
                             _ (doseq [[id decl] (:lctx goal)]
                                 (when (= :local (:tag decl))
                                   (.addLocal jtc (long id) (str (:name decl)) (:type decl))))
                             ;; Decompose HAdd.hAdd args
                             hadd? (fn [expr]
                                     (let [[h a] (e/get-app-fn-args expr)]
                                       (when (and (e/const? h)
                                                  (= (name/->string (e/const-name h)) "HAdd.hAdd")
                                                  (= 6 (count a)))
                                         [(nth a 4) (nth a 5)])))
                             ;; Try proof and verify with Java TC
                             try-proof (fn [proof]
                                         (try
                                           (let [ptype (.inferType jtc proof)]
                                             (when (.isDefEq jtc ptype goal-type)
                                               (-> (proof/assign-mvar ps (:id goal)
                                                                      {:kind :exact :term proof})
                                                   (proof/record-tactic :omega [:direct] (:id goal)))))
                                           (catch Exception _ nil)))
                             ;; le_add_right: ∀ n k, n ≤ n + k
                             ;; le_add_left:  ∀ n k, n ≤ k + n
                             ;; le_trans:     ∀ n m k, n ≤ m → m ≤ k → n ≤ k

                             ;; Pattern 1: a ≤ a + b → le_add_right a b
                             p1 (when-let [[a b] (hadd? rhs)]
                                  (try-proof (e/app* (e/const' le-add-right-n []) lhs b)))
                             ;; Pattern 2: a ≤ b + a → le_add_left a b
                             p2 (when-not p1
                                  (when-let [[b a] (hadd? rhs)]
                                    (try-proof (e/app* (e/const' le-add-left-n []) lhs b))))
                             ;; Pattern 3: a ≤ a (le.refl)
                             p3 (when-not (or p1 p2)
                                  (try-proof (e/app (e/const' le-refl-n []) lhs)))
                             ;; Pattern 4: a ≤ k + (a + b)
                             ;; Proof: le_trans a (a+b) (k+(a+b)) (le_add_right a b) (le_add_left (a+b) k)
                             p4 (when-not (or p1 p2 p3)
                                  (when-let [[k inner] (hadd? rhs)]
                                    (when-let [[a' b'] (hadd? inner)]
                                      (let [h1 (e/app* (e/const' le-add-right-n []) lhs b')
                                            h2 (e/app* (e/const' le-add-left-n []) inner k)
                                            ;; le_trans takes 5 args: n m k h1 h2
                                            proof (e/app* (e/const' le-trans-n [])
                                                          lhs inner rhs h1 h2)]
                                        (try-proof proof)))))
                             ;; Pattern 5: a ≤ (a + b) + k
                             ;; Proof: le_trans a (a+b) ((a+b)+k) (le_add_right a b) (le_add_right (a+b) k)
                             p5 (when-not (or p1 p2 p3 p4)
                                  (when-let [[inner k] (hadd? rhs)]
                                    (when-let [[a' b'] (hadd? inner)]
                                      (let [h1 (e/app* (e/const' le-add-right-n []) lhs b')
                                            h2 (e/app* (e/const' le-add-right-n []) inner k)
                                            proof (e/app* (e/const' le-trans-n [])
                                                          lhs inner rhs h1 h2)]
                                        (try-proof proof)))))
                             ;; Pattern 6: a + c ≤ a + d (when c ≤ d)
                             ;; Uses Nat.add_le_add_left : ∀ (n m : Nat), n ≤ m → ∀ k, k + n ≤ k + m
                             succ-le-succ-n (name/from-string "Nat.succ_le_succ")
                             p6 (when-not (or p1 p2 p3 p4 p5)
                                  ;; Check: are both lhs and rhs of the form (a + c) and (a + d)?
                                  (when-let [[la lb] (hadd? lhs)]
                                    (when-let [[ra rb] (hadd? rhs)]
                                      ;; Check if la == ra (common left addend)
                                      (when (.isDefEq jtc la ra)
                                        ;; Need to prove: lb ≤ rb → la + lb ≤ ra + rb
                                        ;; Use Nat.add_le_add_left: m ≤ n → k + m ≤ k + n
                                        (let [add-le-add-left-n (name/from-string "Nat.add_le_add_left")
                                              ;; First try: is lb ≤ rb trivially true? (e.g., lb = k, rb = k + 1)
                                              ;; Build sub-proof of lb ≤ rb by trying patterns recursively
                                              sub-proof (or
                                                          ;; lb ≤ lb (refl)
                                                          (when (.isDefEq jtc lb rb)
                                                            (e/app (e/const' le-refl-n []) lb))
                                                          ;; lb ≤ lb + x
                                                          (when-let [[_ x] (hadd? rb)]
                                                            (when (.isDefEq jtc lb (first (hadd? rb)))
                                                              (e/app* (e/const' le-add-right-n []) lb (second (hadd? rb)))))
                                                          ;; lb ≤ x + lb
                                                          (when-let [[x _] (hadd? rb)]
                                                            (when (.isDefEq jtc lb (second (hadd? rb)))
                                                              (e/app* (e/const' le-add-left-n []) lb (first (hadd? rb)))))
                                                          ;; Ground case: both lb and rb are literals → decide
                                                          (when (and (or (e/lit-nat? lb) (zero? (e/bvar-range lb)))
                                                                     (or (e/lit-nat? rb) (zero? (e/bvar-range rb))))
                                                            ;; Build: Nat.le lb rb, prove by decide (kernel eval)
                                                            (let [sub-goal (e/app* (e/const' (name/from-string "LE.le") [lvl/zero])
                                                                                   (e/const' (name/from-string "Nat") [])
                                                                                   (e/const' (name/from-string "instLENat") [])
                                                                                   lb rb)
                                                                  ;; of_decide_eq_true : decide p = true → p
                                                                  dec-inst (e/app* (e/const' (name/from-string "Nat.decLe") []) lb rb)
                                                                  decide-expr (e/app* (e/const' (name/from-string "Decidable.decide") []) sub-goal dec-inst)
                                                                  rfl-true (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                                                                                   (e/const' (name/from-string "Bool") [])
                                                                                   (e/const' (name/from-string "Bool.true") []))
                                                                  proof (e/app* (e/const' (name/from-string "of_decide_eq_true") [])
                                                                                sub-goal dec-inst rfl-true)]
                                                              ;; Verify with TC before using
                                                              (try
                                                                (let [ptype (.inferType jtc proof)]
                                                                  (when (.isDefEq jtc ptype sub-goal) proof))
                                                                (catch Exception _ nil)))))]
                                          (when sub-proof
                                            ;; Nat.add_le_add_left : ∀ (n m : Nat) {implicit}, n ≤ m → ∀ k, k + n ≤ k + m
                                            ;; n,m are implicit but kernel requires all args explicit
                                            (try-proof (e/app* (e/const' add-le-add-left-n [])
                                                               lb rb sub-proof la))))))))
                             ;; Pattern 7: succ a ≤ succ b (when a ≤ b)
                             ;; Uses Nat.succ_le_succ : n ≤ m → succ n ≤ succ m
                             p7 (when-not (or p1 p2 p3 p4 p5 p6)
                                  (let [lhs-whnf2 (#'tc/cached-whnf st lhs)
                                        rhs-whnf2 (#'tc/cached-whnf st rhs)
                                        [lh la] (e/get-app-fn-args lhs-whnf2)
                                        [rh ra] (e/get-app-fn-args rhs-whnf2)]
                                    (when (and (e/const? lh) (e/const? rh)
                                               (= (name/->string (e/const-name lh)) "Nat.succ")
                                               (= (name/->string (e/const-name rh)) "Nat.succ"))
                                      ;; succ(la) ≤ succ(ra), need la ≤ ra
                                      (let [la (first la) ra (first ra)
                                            sub (or (when (.isDefEq jtc la ra) (e/app (e/const' le-refl-n []) la))
                                                    (e/app* (e/const' le-add-right-n []) la
                                                            (#'tc/cached-whnf st ra)))]
                                        (when sub
                                          (try-proof (e/app* (e/const' succ-le-succ-n []) la ra sub)))))))]
                         (or p1 p2 p3 p4 p5 p6 p7))))
                   (catch Exception _ nil))
                 ;; Strategy D: Lean 4-style byContradiction for LE goals.
                 ;; For goal `a ≤ b` with context `Nat.ble b a = false`:
                 ;;   1. Nat.ble b a = false → ¬(Nat.ble b a = true) → ¬(b ≤ a)
                 ;;   2. ¬(b ≤ a) → a < b (via Nat.lt_of_not_le)
                 ;;   3. a < b → a ≤ b (via Nat.le_of_lt)
                 ;; Or using Nat.le_total + Or.resolve_right:
                 ;;   Nat.le_total a b : a ≤ b ∨ b ≤ a
                 ;;   ¬(b ≤ a) + Or.resolve_right → a ≤ b
                 (try
                   (let [goal-type (:type goal)
                         [head args] (e/get-app-fn-args goal-type)]
                     (when (and (e/const? head)
                                (or (= (name/->string (e/const-name head)) "LE.le")
                                    (= (name/->string (e/const-name head)) "Nat.le"))
                                (>= (count args) 2))
                       ;; Extract a, b from a ≤ b
                       (let [a (if (= 4 (count args)) (nth args 2) (nth args 0))
                             b (if (= 4 (count args)) (nth args 3) (nth args 1))
                             ;; Search context for Nat.ble b a = false
                             ble-hyp (some (fn [[id decl]]
                                             (when (= :local (:tag decl))
                                               (let [ht (:type decl)
                                                     [hh ha] (e/get-app-fn-args ht)]
                                                 (when (and (e/const? hh)
                                                            (= (name/->string (e/const-name hh)) "Eq")
                                                            (= 3 (count ha)))
                                                   (let [lhs (nth ha 1)
                                                         rhs (nth ha 2)
                                                         [lh la] (e/get-app-fn-args lhs)]
                                                     (when (and (e/const? lh)
                                                                (= (name/->string (e/const-name lh)) "Nat.ble")
                                                                (= 2 (count la))
                                                                (e/const? rhs)
                                                                (= (name/->string (e/const-name rhs)) "Bool.false")
                                                                ;; Check ble args are (b, a) — reversed from goal (a, b)
                                                                (try (and (tc/is-def-eq st (nth la 0) b)
                                                                          (tc/is-def-eq st (nth la 1) a))
                                                                     (catch Exception _ false)))
                                                       {:id id :ble-a (nth la 0) :ble-b (nth la 1)}))))))
                                           (:lctx goal))]
                         (when ble-hyp
                           ;; Build proof: Nat.le_of_lt (Nat.lt_of_not_le (not_le_proof))
                           ;; Where not_le_proof : ¬(b ≤ a) from Nat.ble b a = false
                           ;; Step 1: ¬(b ≤ a) from hc : Nat.ble b a = false
                           ;; Nat.not_le_of_not_ble_eq_true {b} {a} : ¬(Nat.ble b a = true) → ¬(b ≤ a)
                           ;; We need ¬(Nat.ble b a = true) from (Nat.ble b a = false)
                           ;; This is just: fun h_true => absurd (Eq.trans (Eq.symm hc) h_true) Bool.false_ne_true
                           ;; Actually simpler: use mt (modus tollens) on ble_eq_true_of_le
                           ;; mt : (P → Q) → ¬Q → ¬P
                           ;; ble_eq_true_of_le : b ≤ a → Nat.ble b a = true
                           ;; ¬(Nat.ble b a = true) comes from Nat.ble b a = false
                           ;; So: mt ble_eq_true_of_le (not_true_of_false hc) : ¬(b ≤ a)
                           ;;
                           ;; But let's use a simpler route:
                           ;; Nat.lt_of_not_le takes ¬(b ≤ a) and gives a < b
                           ;; Nat.le_of_lt takes a < b and gives a ≤ b
                           ;; For ¬(b ≤ a): use Nat.not_le_of_not_ble_eq_true
                           (let [hc-fvar (e/fvar (:id ble-hyp))
                                 ble-b (:ble-a ble-hyp) ;; b in Nat.ble b a
                                 ble-a (:ble-b ble-hyp) ;; a in Nat.ble b a
                                 ;; Build ¬(Nat.ble b a = true) from (Nat.ble b a = false)
                                 ;; Use: fun h => absurd h (by Nat.ble b a = false → Nat.ble b a ≠ true)
                                 ;; Actually: Nat.not_le_of_not_ble_eq_true {b} {a}
                                 ;;   takes ¬(Nat.ble b a = true)
                                 ;; We have Nat.ble b a = false. We need ¬(Nat.ble b a = true).
                                 ;; Bool disequality: false ≠ true, so (x = false) → (x ≠ true)
                                 ;; Proof: fun h_true : x = true => absurd (Eq.trans (Eq.symm hc) h_true) Bool.noConfusion
                                 ;; Simpler: use mt with id
                                 ;; Actually, let me just use Nat.not_le.mp which takes (b ≤ a → False) and gives a < b → ...
                                 ;; Hmm, this is getting complicated. Let me use the direct approach:
                                 ;; Or.resolve_right (Nat.le_total a b) not_b_le_a : a ≤ b
                                 ;; Where not_b_le_a : ¬(b ≤ a) built from hc

                                 ;; Build ¬(b ≤ a) from hc : Nat.ble b a = false
                                 ;; Nat.not_le_of_not_ble_eq_true {b} {a} : ¬(Nat.ble b a = true) → ¬(b ≤ a)
                                 not-ble-true
                                 (let [bool-type (e/const' (name/from-string "Bool") [])
                                       bool-true (e/const' (name/from-string "Bool.true") [])
                                       bool-false (e/const' (name/from-string "Bool.false") [])
                                       ble-expr (e/app* (e/const' (name/from-string "Nat.ble") []) ble-b ble-a)
                                       l1 (lvl/succ lvl/zero)
                                       ;; h_true : Nat.ble b a = true
                                       ;; hc : Nat.ble b a = false
                                       ;; We need: ¬(Nat.ble b a = true)
                                       ;; = fun (h_true : Nat.ble b a = true) =>
                                       ;;     absurd (Eq.trans (Eq.symm hc) h_true) Bool.noConfusion
                                       ;; Actually simpler: Bool.false_ne_true applied to Eq.trans
                                       eq-ble-true (e/app* (e/const' (name/from-string "Eq") [l1])
                                                           bool-type ble-expr bool-true)
                                       ;; Build: fun (h : ble = true) => absurd h (by ble = false → ble ≠ true)
                                       ;; ble = false and ble = true → false = true → absurd
                                       ;; Eq.symm hc : false = ble
                                       ;; Eq.trans (Eq.symm hc) h : false = true
                                       ;; But we need the contradiction
                                       ;; Actually use: Eq.subst h hc
                                       ;; hc : ble = false, h : ble = true
                                       ;; Eq.subst h : (ble = false)[ble/true] = (true = false)
                                       ;; Then: Bool.noConfusion (true = false) gives False
                                       ;; Simpler: (fun h => absurd (Eq.trans (Eq.symm h) hc) Bool.noConfusion)
                                       ;; Where: Eq.symm h : true = ble, Eq.trans that with hc : ble = false
                                       ;; gives: true = false. Then Bool.noConfusion.
                                       ;; But Bool.noConfusion might not be in init-medium.
                                       ;; Alternative: use absurd with False.elim
                                       ;; Actually let me check what we have:
                                       ;; We have: decide_eq_false_iff_not
                                       ;; We need something simpler.
                                       ;; Just use: mt (Nat.ble_eq_true_of_le b a) (not_true_from_false hc)
                                       ;; mt : (P → Q) → ¬Q → ¬P
                                       ;; ble_eq_true_of_le : b ≤ a → Nat.ble b a = true
                                       ;; We need ¬(Nat.ble b a = true) from hc : Nat.ble b a = false
                                       ;; ¬(x = true) from (x = false):
                                       ;; fun h_true : x = true => by x = true and x = false → true = false → absurd
                                       ;; Build as lambda:
                                       sym-hc (e/app* (e/const' (name/from-string "Eq.symm") [l1])
                                                      bool-type ble-expr bool-false hc-fvar)
                                       ;; sym-hc : false = ble
                                       ;; trans (sym_hc) (h_true) : false = true  (where h_true : ble = true)
                                       ;; h_true is bvar 0 inside the lambda
                                       trans-proof (e/app* (e/const' (name/from-string "Eq.trans") [l1])
                                                           bool-type bool-false ble-expr bool-true
                                                           sym-hc (e/bvar 0))
                                       ;; false = true → False  via Bool.noConfusion or similar
                                       ;; Actually: use absurd with Nat/Bool discrimination
                                       ;; Simplest: (fun h_eq : false = true => nomatch h_eq)
                                       ;; In CIC: Bool.noConfusion h_eq : False
                                       ;; Check: do we have Bool.noConfusion?
                                       false-eq-true-absurd
                                       (e/app* (e/const' (name/from-string "Bool.noConfusion") [lvl/zero])
                                               (e/const' (name/from-string "False") [])
                                               bool-false bool-true trans-proof)]
                                   ;; Lambda: fun (h_true : ble b a = true) => absurd
                                   (e/lam "h" eq-ble-true false-eq-true-absurd :default))

                                 ;; Now build: ¬(b ≤ a) from ¬(Nat.ble b a = true)
                                 ;; Nat.not_le_of_not_ble_eq_true {b} {a} not-ble-true : ¬(b ≤ a)
                                 not-b-le-a (e/app* (e/const' (name/from-string "Nat.not_le_of_not_ble_eq_true") [])
                                                    ble-b ble-a not-ble-true)

                                 ;; Finally: Or.resolve_right (Nat.le_total a b) not-b-le-a : a ≤ b
                                 ;; Or.resolve_right : {a b : Prop} → a ∨ b → ¬b → a
                                 le-a-b (e/app* (e/const' (name/from-string "Nat.le_total") []) a b)
                                 nat-le-ab (e/app* (e/const' (name/from-string "LE.le") [lvl/zero])
                                                   (e/const' (name/from-string "Nat") [])
                                                   (e/const' (name/from-string "instLENat") [])
                                                   a b)
                                 nat-le-ba (e/app* (e/const' (name/from-string "LE.le") [lvl/zero])
                                                   (e/const' (name/from-string "Nat") [])
                                                   (e/const' (name/from-string "instLENat") [])
                                                   b a)
                                 proof (e/app* (e/const' (name/from-string "Or.resolve_right") [])
                                               nat-le-ab nat-le-ba le-a-b not-b-le-a)]
                             ;; Verify and assign
                             (let [jtc (ansatz.kernel.TypeChecker. (:env ps))]
                               (.setFuel jtc config/*default-fuel*)
                               (doseq [[id decl] (:lctx goal)]
                                 (when (= :local (:tag decl))
                                   (.addLocal jtc (long id) (str (:name decl)) (:type decl))))
                               (let [ptype (.inferType jtc proof)]
                                 (when (.isDefEq jtc ptype goal-type)
                                   (-> (proof/assign-mvar ps (:id goal)
                                                          {:kind :exact :term proof})
                                       (proof/record-tactic :omega [:le-total] (:id goal)))))))))))
                   (catch Exception _ nil))
                 ;; Strategy E: LE transitivity from hypotheses.
                 ;; For goal `a ≤ c`, search lctx for `a ≤ b` and `b ≤ c`
                 ;; then build proof: Nat.le_trans a b c h1 h2
                 (try
                   (let [goal-type (:type goal)
                         [ghead gargs] (e/get-app-fn-args goal-type)]
                     (when (and (e/const? ghead)
                                (= (name/->string (e/const-name ghead)) "LE.le")
                                (= 4 (count gargs)))
                       (let [a (nth gargs 2)
                             c (nth gargs 3)
                             le-trans-n (name/from-string "Nat.le_trans")
                             jtc (ansatz.kernel.TypeChecker. (:env ps))
                             _ (.setFuel jtc config/*default-fuel*)
                             _ (doseq [[id decl] (:lctx goal)]
                                 (when (= :local (:tag decl))
                                   (.addLocal jtc (long id) (str (:name decl)) (:type decl))))
                             ;; Collect all LE hypotheses: {id [lhs rhs]}
                             le-hyps (into []
                                       (keep (fn [[id decl]]
                                               (when (= :local (:tag decl))
                                                 (let [[hh ha] (e/get-app-fn-args (:type decl))]
                                                   (when (and (e/const? hh)
                                                              (= (name/->string (e/const-name hh)) "LE.le")
                                                              (= 4 (count ha)))
                                                     {:id id :lhs (nth ha 2) :rhs (nth ha 3)})))))
                                       (:lctx goal))
                             ;; Find pair h1: a ≤ b, h2: b ≤ c
                             result (some (fn [h1]
                                           (when (.isDefEq jtc (:lhs h1) a)
                                             (some (fn [h2]
                                                     (when (and (not= (:id h1) (:id h2))
                                                                (.isDefEq jtc (:lhs h2) (:rhs h1))
                                                                (.isDefEq jtc (:rhs h2) c))
                                                       (let [b (:rhs h1)
                                                             proof (e/app* (e/const' le-trans-n [])
                                                                           a b c
                                                                           (e/fvar (:id h1))
                                                                           (e/fvar (:id h2)))]
                                                         (-> (proof/assign-mvar ps (:id goal)
                                                                                {:kind :exact :term proof})
                                                             (proof/record-tactic :omega [:le-trans] (:id goal))))))
                                                   le-hyps)))
                                         le-hyps)]
                         result)))
                   (catch Exception _ nil))
                 ;; Strategy for LT goals: a < b
                 ;; Convert to succ(a) ≤ b, build LE proof with TC verification,
                 ;; then wrap with Nat.lt_of_succ_le.
                 (try
                   (let [goal-type (:type goal)
                         [head args] (e/get-app-fn-args goal-type)]
                     (when (and (e/const? head)
                                (= (name/->string (e/const-name head)) "LT.lt")
                                (>= (count args) 4))
                       (let [lhs (nth args 2) ;; a in a < b
                             rhs (nth args 3) ;; b
                             nat (e/const' (name/from-string "Nat") [])
                             jtc (ansatz.kernel.TypeChecker. (:env ps))
                             _ (.setFuel jtc config/*default-fuel*)
                             _ (doseq [[id decl] (:lctx goal)]
                                 (when (= :local (:tag decl))
                                   (.addLocal jtc (long id) (str (:name decl)) (:type decl))))
                             ;; succ(a)
                             succ-lhs (e/app (e/const' (name/from-string "Nat.succ") []) lhs)
                             ;; LE goal type: succ(a) ≤ b
                             le-goal (e/app* (e/const' (name/from-string "LE.le") [lvl/zero])
                                             nat (e/const' (name/from-string "instLENat") [])
                                             succ-lhs rhs)
                             ;; Try to build LE proof with patterns:
                             le-refl-n (name/from-string "Nat.le.refl")
                             le-add-right-n (name/from-string "Nat.le_add_right")
                             le-add-left-n (name/from-string "Nat.le_add_left")
                             try-le-proof
                             (fn [proof]
                               (try
                                 (let [pt (.inferType jtc proof)]
                                   (when (.isDefEq jtc pt le-goal) proof))
                                 (catch Exception _ nil)))
                             ;; Pattern: succ(a) ≤ succ(a) → le.refl (when a < succ a)
                             le-proof (or (try-le-proof (e/app (e/const' le-refl-n []) succ-lhs))
                                         ;; succ(a) ≤ succ(a) + k
                                         (try-le-proof (e/app* (e/const' le-add-right-n []) succ-lhs rhs))
                                         ;; succ(a) ≤ k + succ(a)
                                         (try-le-proof (e/app* (e/const' le-add-left-n []) succ-lhs rhs))
                                         ;; Ground: both sides reduce to literals
                                         (let [slhs-w (.whnfCore jtc succ-lhs)
                                               rhs-w (.whnfCore jtc rhs)]
                                           (when (and (or (e/lit-nat? slhs-w) (zero? (e/bvar-range slhs-w)))
                                                      (or (e/lit-nat? rhs-w) (zero? (e/bvar-range rhs-w))))
                                             ;; Try le.refl after WHNF
                                             (try-le-proof (e/app (e/const' le-refl-n []) succ-lhs)))))]
                         (when le-proof
                           ;; Nat.lt_of_succ_le : {n m} → succ n ≤ m → n < m
                           (let [lt-proof (e/app* (e/const' (name/from-string "Nat.lt_of_succ_le") [])
                                                  lhs rhs le-proof)]
                             (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term lt-proof})
                                 (proof/record-tactic :omega [:lt-via-succ-le] (:id goal))))))))
                   (catch Exception _ nil))
                 ;; All fallbacks failed
                 (tactic-error!
                  "omega: found contradiction but cannot certify (non-ground goal)"
                  {:goal (:type goal)})))))))))
