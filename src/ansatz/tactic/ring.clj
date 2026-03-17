;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; Tactic layer — ring: polynomial identity decision procedure.
;;
;; Implements polynomial normalization for CommRing/CommSemiring:
;; 1. Reify: Ansatz ring expression → sparse polynomial
;; 2. Normalize: expand, collect, sort by grevlex
;; 3. Check: lhs - rhs = 0 polynomial
;; 4. Certify: verify via `decide` tactic or `rfl`
;;
;; Follows Lean 4's ring tactic semantics (grind ring subsystem).

(ns ansatz.tactic.ring
  "Polynomial identity decision procedure (ring tactic).

   Supports:
   - CommRing and CommSemiring goals
   - Polynomial identities: (a+b)^2 = a^2 + 2ab + b^2
   - Ground arithmetic on Nat, Int
   - Distributivity, commutativity, associativity
   - Power expansion (small exponents)

   Algorithm:
   1. Reify both sides of an Eq goal into polynomials
   2. Normalize to canonical form (sorted monomials, collected coefficients)
   3. Check if lhs - rhs = 0 polynomial
   4. Certify via decide or rfl"
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.decide :as decide-tac]))

;; ============================================================
;; Sparse polynomial representation
;; ============================================================

;; A monomial: sorted vector of [var-idx exponent] pairs
;; e.g., x^2*y = [[0 2] [1 1]]
;; The unit monomial is []

;; A polynomial: sorted vector of [coefficient monomial] pairs
;; e.g., 3x^2 + 2xy - 1 = [[-1 []] [2 [[0 1] [1 1]]] [3 [[0 2]]]]
;; Sorted by grevlex on monomials, zero coefficients removed

(defn- mon-unit [] [])

(defn- mon-var
  "Monomial for a single variable."
  [var-idx]
  [[var-idx 1]])

(defn- mon-mul
  "Multiply two monomials."
  [a b]
  (let [merged (reduce (fn [m [var exp]]
                         (update m var (fnil + 0) exp))
                       (into {} a) b)]
    (vec (sort-by first (filter (fn [[_ e]] (pos? e)) merged)))))

(defn- mon-degree
  "Total degree of a monomial."
  [m]
  (reduce + 0 (map second m)))

(defn- mon-compare
  "Graded reverse lexicographic comparison.
   Returns negative if a < b, 0 if equal, positive if a > b."
  [a b]
  (let [da (mon-degree a)
        db (mon-degree b)]
    (if (not= da db)
      (compare da db)
      ;; Same degree — reverse lex (compare from last variable)
      (let [a-map (into {} a)
            b-map (into {} b)
            all-vars (sort (into #{} (concat (map first a) (map first b))))]
        (loop [vars (reverse all-vars)]
          (if (empty? vars)
            0
            (let [v (first vars)
                  ea (get a-map v 0)
                  eb (get b-map v 0)]
              (if (not= ea eb)
                ;; Reverse lex: HIGHER exponent on LAST var = SMALLER
                (compare eb ea)
                (recur (rest vars))))))))))

;; Polynomial operations

(defn- poly-const
  "Polynomial for a constant."
  [c]
  (if (zero? c) [] [[c (mon-unit)]]))

(defn- poly-var
  "Polynomial for a single variable."
  [var-idx]
  [[1 (mon-var var-idx)]])

(defn- poly-normalize
  "Normalize a polynomial: sort monomials, collect like terms, remove zeros."
  [p]
  (let [;; Group by monomial
        grouped (reduce (fn [m [coeff mon]]
                          (update m mon (fnil + 0) coeff))
                        {} p)
        ;; Remove zero coefficients and sort
        terms (sort-by second mon-compare
                       (filter (fn [[_ c]] (not (zero? c)))
                               (map (fn [[mon coeff]] [coeff mon]) grouped)))]
    (vec terms)))

(defn- poly-add
  "Add two polynomials."
  [a b]
  (poly-normalize (into (vec a) b)))

(defn- poly-sub
  "Subtract b from a."
  [a b]
  (poly-add a (mapv (fn [[c m]] [(- c) m]) b)))

(defn- poly-scale
  "Multiply polynomial by a scalar."
  [p k]
  (if (zero? k) []
      (poly-normalize (mapv (fn [[c m]] [(* c k) m]) p))))

(defn- poly-mul
  "Multiply two polynomials."
  [a b]
  (poly-normalize
   (for [[ca ma] a
         [cb mb] b]
     [(* ca cb) (mon-mul ma mb)])))

(defn- poly-pow
  "Raise a polynomial to a non-negative integer power."
  [p n]
  (cond
    (zero? n) (poly-const 1)
    (= 1 n) p
    :else (let [half (poly-pow p (quot n 2))
                sq (poly-mul half half)]
            (if (even? n) sq (poly-mul sq p)))))

(defn- poly-is-zero?
  "Check if a polynomial is the zero polynomial."
  [p]
  (every? (fn [[c _]] (zero? c)) p))

;; ============================================================
;; Reification: Ansatz expressions → polynomials
;; ============================================================

(defn- tactic-error! [msg data]
  (throw (ex-info (str "ring: " msg) (merge {:kind :tactic-error} data))))

;; Atom table (same pattern as omega)
(defn- mk-atom-table []
  {:expr->idx {} :idx->expr {} :next-idx 0})

(defn- intern-atom [table st expr]
  (let [expr-whnf (#'tc/cached-whnf st expr)]
    (if-let [idx (get (:expr->idx table) expr-whnf)]
      [table idx]
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

(defn- try-match-head [st expr]
  (let [[head args] (e/get-app-fn-args expr)]
    (if (e/const? head)
      [(e/const-name head) (e/const-levels head) (vec args)]
      (let [w (#'tc/cached-whnf st expr)
            [whead wargs] (e/get-app-fn-args w)]
        (when (e/const? whead)
          [(e/const-name whead) (e/const-levels whead) (vec wargs)])))))

(def ^:private hadd-name (name/from-string "HAdd.hAdd"))
(def ^:private hsub-name (name/from-string "HSub.hSub"))
(def ^:private hmul-name (name/from-string "HMul.hMul"))
(def ^:private hpow-name (name/from-string "HPow.hPow"))
(def ^:private hneg-name (name/from-string "Neg.neg"))
(def ^:private nat-add-name (name/from-string "Nat.add"))
(def ^:private nat-sub-name (name/from-string "Nat.sub"))
(def ^:private nat-mul-name (name/from-string "Nat.mul"))
(def ^:private nat-succ-name (name/from-string "Nat.succ"))
(def ^:private nat-zero-name (name/from-string "Nat.zero"))
(def ^:private ofnat-name (name/from-string "OfNat.ofNat"))
(def ^:private nat-pow-name (name/from-string "Nat.pow"))

(declare reify-ring-term)

(defn- reify-ring-term
  "Reify a Ansatz term into a polynomial.
   Returns [atom-table polynomial]."
  [st table expr]
  (let [expr-whnf (#'tc/cached-whnf st expr)]
    (cond
      ;; Nat literal
      (e/lit-nat? expr-whnf)
      [table (poly-const (e/lit-nat-val expr-whnf))]

      ;; Nat.zero
      (and (e/const? expr-whnf)
           (= (e/const-name expr-whnf) nat-zero-name))
      [table (poly-const 0)]

      ;; Application
      (e/app? expr-whnf)
      (let [matched (try-match-head st expr-whnf)]
        (if-not matched
          (let [[table' idx] (intern-atom table st expr-whnf)]
            [table' (poly-var idx)])
          (let [[head-name _ args] matched]
            (cond
              ;; Nat.sub a b → for ground cases evaluate, else atom
              (and (= head-name nat-sub-name) (= 2 (count args)))
              (let [a-whnf (#'tc/cached-whnf st (nth args 0))
                    b-whnf (#'tc/cached-whnf st (nth args 1))]
                (if (and (e/lit-nat? a-whnf) (e/lit-nat? b-whnf))
                  [table (poly-const (max 0 (- (e/lit-nat-val a-whnf) (e/lit-nat-val b-whnf))))]
                  (let [[table' idx] (intern-atom table st expr-whnf)]
                    [table' (poly-var idx)])))

              ;; Nat.succ n → n + 1
              (and (= head-name nat-succ-name) (= 1 (count args)))
              (let [[table' p] (reify-ring-term st table (nth args 0))]
                [table' (poly-add p (poly-const 1))])

              ;; HAdd.hAdd _ _ _ _ a b → a + b
              (and (= head-name hadd-name) (= 6 (count args)))
              (let [[table' pa] (reify-ring-term st table (nth args 4))
                    [table'' pb] (reify-ring-term st table' (nth args 5))]
                [table'' (poly-add pa pb)])

              ;; Nat.add a b → a + b
              (and (= head-name nat-add-name) (= 2 (count args)))
              (let [[table' pa] (reify-ring-term st table (nth args 0))
                    [table'' pb] (reify-ring-term st table' (nth args 1))]
                [table'' (poly-add pa pb)])

              ;; HSub.hSub _ _ _ _ a b → a - b
              (and (= head-name hsub-name) (= 6 (count args)))
              (let [[table' pa] (reify-ring-term st table (nth args 4))
                    [table'' pb] (reify-ring-term st table' (nth args 5))]
                [table'' (poly-sub pa pb)])

              ;; HMul.hMul _ _ _ _ a b → a * b
              (and (= head-name hmul-name) (= 6 (count args)))
              (let [[table' pa] (reify-ring-term st table (nth args 4))
                    [table'' pb] (reify-ring-term st table' (nth args 5))]
                [table'' (poly-mul pa pb)])

              ;; Nat.mul a b → a * b
              (and (= head-name nat-mul-name) (= 2 (count args)))
              (let [[table' pa] (reify-ring-term st table (nth args 0))
                    [table'' pb] (reify-ring-term st table' (nth args 1))]
                [table'' (poly-mul pa pb)])

              ;; HPow.hPow _ _ _ _ a n → a ^ n (n must be a ground Nat)
              (and (= head-name hpow-name) (= 6 (count args)))
              (let [exp-whnf (#'tc/cached-whnf st (nth args 5))]
                (if (e/lit-nat? exp-whnf)
                  (let [n (e/lit-nat-val exp-whnf)
                        [table' pa] (reify-ring-term st table (nth args 4))]
                    [table' (poly-pow pa n)])
                  ;; Non-ground exponent — intern as atom
                  (let [[table' idx] (intern-atom table st expr-whnf)]
                    [table' (poly-var idx)])))

              ;; Nat.pow a n → a ^ n
              (and (= head-name nat-pow-name) (= 2 (count args)))
              (let [exp-whnf (#'tc/cached-whnf st (nth args 1))]
                (if (e/lit-nat? exp-whnf)
                  (let [n (e/lit-nat-val exp-whnf)
                        [table' pa] (reify-ring-term st table (nth args 0))]
                    [table' (poly-pow pa n)])
                  (let [[table' idx] (intern-atom table st expr-whnf)]
                    [table' (poly-var idx)])))

              ;; Neg.neg _ _ a → -a
              (and (= head-name hneg-name) (= 3 (count args)))
              (let [[table' pa] (reify-ring-term st table (nth args 2))]
                [table' (poly-scale pa -1)])

              ;; OfNat.ofNat _ n _ → n
              (and (= head-name ofnat-name) (>= (count args) 2))
              (reify-ring-term st table (nth args 1))

              ;; Unknown — intern as atom
              :else
              (let [[table' idx] (intern-atom table st expr-whnf)]
                [table' (poly-var idx)])))))

      ;; Free variable
      (e/fvar? expr-whnf)
      (let [[table' idx] (intern-atom table st expr-whnf)]
        [table' (poly-var idx)])

      ;; Constant
      (e/const? expr-whnf)
      (if (= (e/const-name expr-whnf) nat-zero-name)
        [table (poly-const 0)]
        (let [[table' idx] (intern-atom table st expr-whnf)]
          [table' (poly-var idx)]))

      ;; Anything else — atom
      :else
      (let [[table' idx] (intern-atom table st expr-whnf)]
        [table' (poly-var idx)]))))

;; ============================================================
;; Ring check
;; ============================================================

(def ^:private eq-name (name/from-string "Eq"))

(defn- ring-check
  "Check if a goal can be solved by polynomial normalization.
   Returns true if lhs and rhs normalize to the same polynomial."
  [st goal-type]
  (let [goal-whnf (#'tc/cached-whnf st goal-type)
        [head args] (e/get-app-fn-args goal-whnf)]
    (when (and (e/const? head)
               (= (e/const-name head) eq-name)
               (= 3 (count args)))
      (let [table (mk-atom-table)
            [table' p-lhs] (reify-ring-term st table (nth args 1))
            [table'' p-rhs] (reify-ring-term st table' (nth args 2))
            diff (poly-sub p-lhs p-rhs)]
        (poly-is-zero? diff)))))

;; ============================================================
;; Public API
;; ============================================================

(defn ring
  "Close the current goal using polynomial ring normalization.

   Works for Eq goals where both sides are polynomial expressions.
   Normalizes both sides and checks if they are equal.

   Strategy:
   1. Try decide first (handles ground cases)
   2. Try rfl (for def-eq sides)
   3. Normalize both sides as polynomials and check equality
   4. If equal, certify via decide or rfl"
  [ps]
  ;; Try decide first
  (try
    (decide-tac/decide ps)
    (catch Exception _
      ;; Try rfl
      (let [goal (proof/current-goal ps)
            _ (when-not goal (tactic-error! "No goals" {}))
            env (:env ps)
            st (tc/mk-tc-state env)
            st (assoc st :lctx (:lctx goal))
            goal-type (:type goal)]
        ;; Try rfl
        (let [goal-whnf (#'tc/cached-whnf st goal-type)
              [head args] (e/get-app-fn-args goal-whnf)]
          (if (and (e/const? head)
                   (= (e/const-name head) eq-name)
                   (= 3 (count args)))
            (let [lhs (nth args 1)
                  rhs (nth args 2)]
              (if (tc/is-def-eq st lhs rhs)
                ;; rfl
                (let [eq-levels (e/const-levels head)
                      proof-term (e/app* (e/const' (name/from-string "Eq.refl")
                                                   eq-levels)
                                         (nth args 0) lhs)]
                  (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof-term})
                      (proof/record-tactic :ring [] (:id goal))))
                ;; Check polynomial equality
                (if (ring-check st goal-type)
                  ;; Polynomials match — try decide to certify
                  (try
                    (decide-tac/decide ps)
                    (catch Exception _
                      (tactic-error!
                       "ring: polynomials match but cannot certify (non-ground)"
                       {:goal goal-type})))
                  (tactic-error! "ring: sides are not equal as polynomials"
                                 {:goal goal-type}))))
            (tactic-error! "ring: goal is not an Eq" {:goal goal-type})))))))
