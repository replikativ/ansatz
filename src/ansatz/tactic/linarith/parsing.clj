;; Port of Mathlib/Tactic/Linarith/Parsing.lean and the Comp/Linexp part of
;; Mathlib/Tactic/Linarith/Datatypes.lean, plus Mathlib/Data/Ineq.lean (`ineq?`) and
;; Mathlib/Lean/Expr/Basic.lean (`numeral?`).
(ns ansatz.tactic.linarith.parsing
  "Linear forms of comparison proofs.

   An expression is read as a polynomial — a `Sum`, mapping monomials to integer
   coefficients, a monomial (`Monom`) mapping atom indices to powers — with products and
   numeral powers multiplied out, as Mathlib's `linearFormOfExpr` does. Each distinct
   monomial then becomes one variable of a linear `Comp` (`{:str ineq :coeffs {var c}}`).
   Atoms are matched syntactically (Mathlib matches them up to reducible defeq)."
  (:refer-clojure :exclude [zero?])
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]))

;; ------------------------------------------------------------------
;; expression shapes
;; ------------------------------------------------------------------

(defn strip-mdata [x] (if (e/mdata? x) (recur (e/mdata-expr x)) x))

(defn head-args
  "[head-name-string args] of an application spine (mdata stripped), or nil."
  [x]
  (let [x (strip-mdata x)
        [h args] (e/get-app-fn-args x)]
    (when (e/const? h) [(name/->string (e/const-name h)) (vec args)])))

(defn numeral?
  "Mathlib's `Expr.numeral?`: a raw literal, `OfNat.ofNat _ n _`, `Nat.zero`, `Nat.succ n`.
   `Int.ofNat n` is accepted as well: the kernel reduces Int numerals to it."
  [x]
  (let [x (strip-mdata x)]
    (if (e/lit-nat? x)
      (e/lit-nat-val x)
      (when-let [[h args] (head-args x)]
        (case h
          "Nat.succ" (when (= 1 (count args)) (some-> (numeral? (first args)) inc'))
          "OfNat.ofNat" (when (= 3 (count args)) (numeral? (nth args 1)))
          "Nat.zero" (when (empty? args) 0)
          "Int.ofNat" (when (= 1 (count args)) (numeral? (first args)))
          nil)))))

(defn zero? [x] (= 0 (numeral? x)))

(defn not?
  "`¬ p` (or `p → False`) → p."
  [x]
  (let [x (strip-mdata x)]
    (or (when-let [[h args] (head-args x)]
          (cond
            (and (= h "Not") (= 1 (count args))) (first args)
            ;; `a ≠ b` is reducibly `a = b → False`
            (and (= h "Ne") (= 3 (count args)))
            (let [hd (first (e/get-app-fn-args x))]
              (e/app* (e/const' (name/from-string "Eq") (e/const-levels hd))
                      (nth args 0) (nth args 1) (nth args 2)))))
        (when (and (e/forall? x) (not (e/has-loose-bvars? (e/forall-body x))))
          (let [b (strip-mdata (e/forall-body x))]
            (when (and (e/const? b) (= "False" (name/->string (e/const-name b))))
              (e/forall-type x)))))))

(defn ineq?
  "Mathlib's `Expr.ineq?`: [ineq type lhs rhs] for `a = b`, `a ≤ b`, `a < b` (and `a ≥ b`,
   `a > b`, which reducibly unfold to the swapped `≤`/`<`), else nil."
  [x]
  (when-let [[h args] (head-args x)]
    (let [n (count args)]
      (case h
        "Eq" (when (= n 3) [:eq (nth args 0) (nth args 1) (nth args 2)])
        "LE.le" (when (= n 4) [:le (nth args 0) (nth args 2) (nth args 3)])
        "LT.lt" (when (= n 4) [:lt (nth args 0) (nth args 2) (nth args 3)])
        "GE.ge" (when (= n 4) [:le (nth args 0) (nth args 3) (nth args 2)])
        "GT.gt" (when (= n 4) [:lt (nth args 0) (nth args 3) (nth args 2)])
        nil))))

(defn ineq-or-not-ineq?
  "[positive? ineq type lhs rhs] for a comparison or the negation of one."
  [x]
  (if-let [r (ineq? x)]
    (into [true] r)
    (when-let [p (not? x)]
      (when-let [r (ineq? p)] (into [false] r)))))

(defn ne?
  "`a ≠ b` / `¬ a = b` → [type a b]."
  [x]
  (or (when-let [[h args] (head-args x)]
        (when (and (= h "Ne") (= 3 (count args))) args))
      (when-let [p (not? x)]
        (when-let [[iq t a b] (ineq? p)] (when (= iq :eq) [t a b])))))

;; ------------------------------------------------------------------
;; Ineq (Mathlib/Data/Ineq.lean)
;; ------------------------------------------------------------------

(def ^:private ineq-rank {:eq 0 :le 1 :lt 2})
(defn ineq-max [a b] (if (>= (ineq-rank a) (ineq-rank b)) a b))

;; ------------------------------------------------------------------
;; Monom / Sum
;; ------------------------------------------------------------------

(defn- compare-lists [xs ys]
  (loop [xs (seq xs) ys (seq ys)]
    (cond
      (and (nil? xs) (nil? ys)) 0
      (nil? xs) -1
      (nil? ys) 1
      :else (let [c (compare (first xs) (first ys))]
              (if (clojure.core/zero? c) (recur (next xs) (next ys)) c)))))

(defn monom-compare
  "Monom.lt: keys lexicographically, then powers."
  [a b]
  (let [c (compare-lists (keys a) (keys b))]
    (if (clojure.core/zero? c) (compare-lists (vals a) (vals b)) c)))

(def monom-one (sorted-map))
(defn- empty-sum [] (sorted-map-by monom-compare))

(defn sum-add [s t]
  (reduce-kv (fn [m k v] (let [x (+' (get m k 0) v)]
                           (if (clojure.core/zero? x) (dissoc m k) (assoc m k x))))
             s t))

(defn sum-neg [s] (reduce-kv (fn [m k v] (assoc m k (-' v))) (empty-sum) s))

(defn- monom-mul [a b] (merge-with +' a b))

(defn sum-mul [s t]
  (reduce-kv (fn [acc m1 c1]
               (sum-add acc (reduce-kv (fn [m m2 c2] (assoc m (monom-mul m1 m2) (*' c1 c2)))
                                       (empty-sum) t)))
             (empty-sum) s))

(defn scalar [z] (if (clojure.core/zero? z) (empty-sum) (assoc (empty-sum) monom-one z)))
(def sum-one (scalar 1))
(defn var-sum [n] (assoc (empty-sum) (sorted-map n 1) 1))

(defn sum-pow [s n]
  (cond
    (clojure.core/zero? n) sum-one
    (= n 1) s
    :else (let [a (sum-pow s (quot n 2))
                a2 (sum-mul a a)]
            (if (even? n) a2 (sum-mul a2 s)))))

;; ------------------------------------------------------------------
;; linearFormOfExpr
;; ------------------------------------------------------------------

(defn- atom-index
  "linearFormOfAtom: the index of `x` in `atoms` (a vector; index = position + 1)."
  [atoms x]
  (let [x (strip-mdata x)]
    (if-let [i (first (keep-indexed (fn [i a] (when (= a x) i)) atoms))]
      [atoms (inc i)]
      [(conj atoms x) (inc (count atoms))])))

(defn linear-form-of-expr
  "[atoms Sum] for expression `x`."
  [atoms x]
  (let [x (strip-mdata x)]
    (if-let [n (numeral? x)]
      [atoms (scalar n)]
      (let [[h args] (head-args x)
            n (count args)
            bin (fn [f a b]
                  (let [[atoms s1] (linear-form-of-expr atoms a)
                        [atoms s2] (linear-form-of-expr atoms b)]
                    [atoms (f s1 s2)]))
            atom (fn [] (let [[atoms i] (atom-index atoms x)] [atoms (var-sum i)]))]
        (cond
          (and (= h "HMul.hMul") (= n 6)) (bin sum-mul (nth args 4) (nth args 5))
          (and (= h "HAdd.hAdd") (= n 6)) (bin sum-add (nth args 4) (nth args 5))
          (and (= h "HSub.hSub") (= n 6)) (bin #(sum-add %1 (sum-neg %2)) (nth args 4) (nth args 5))
          (and (= h "Neg.neg") (= n 3))
          (let [[atoms s] (linear-form-of-expr atoms (nth args 2))] [atoms (sum-neg s)])
          (and (= h "HPow.hPow") (= n 6))
          (if-let [k (numeral? (nth args 5))]
            (let [[atoms s] (linear-form-of-expr atoms (nth args 4))] [atoms (sum-pow s k)])
            (atom))
          ;; The concrete Int operations the ansatz surface may emit for `Int` arithmetic.
          (and (= h "Int.mul") (= n 2)) (bin sum-mul (nth args 0) (nth args 1))
          (and (= h "Int.add") (= n 2)) (bin sum-add (nth args 0) (nth args 1))
          (and (= h "Int.sub") (= n 2)) (bin #(sum-add %1 (sum-neg %2)) (nth args 0) (nth args 1))
          (and (= h "Int.neg") (= n 1))
          (let [[atoms s] (linear-form-of-expr atoms (nth args 0))] [atoms (sum-neg s)])
          (and (= h "Int.pow") (= n 2))
          (if-let [k (numeral? (nth args 1))]
            (let [[atoms s] (linear-form-of-expr atoms (nth args 0))] [atoms (sum-pow s k)])
            (atom))
          (and (= h "Int.negSucc") (= n 1) (numeral? (first args)))
          [atoms (scalar (-' (inc' (numeral? (first args)))))]
          :else (atom))))))

;; ------------------------------------------------------------------
;; Linexp / Comp
;; ------------------------------------------------------------------

(defn elim-monom
  "Replace each monomial of `s` by its index in `mm` (assigning fresh indices in order)."
  [s mm]
  (reduce-kv (fn [[mm out] mon c]
               (if-let [k (get mm mon)]
                 [mm (assoc out k c)]
                 (let [k (count mm)] [(assoc mm mon k) (assoc out k c)])))
             [mm (sorted-map)] s))

(defn parse-comp-and-expr
  "`t R 0` → [R t]."
  [ty]
  (when-let [[iq _ t z] (ineq? ty)]
    (when (zero? z) [iq t])))

(defn to-comp
  [ty atoms mm]
  (let [[iq t] (or (parse-comp-and-expr ty)
                   (throw (ex-info "linarith: invalid comparison, rhs not zero"
                                   {:kind :tactic-error :type ty})))
        [atoms s] (linear-form-of-expr atoms t)
        [mm coeffs] (elim-monom s mm)]
    [{:str iq :coeffs coeffs} atoms mm]))

(defn linear-forms-and-max-var
  "Comps for the given comparison types, and the largest variable index."
  [types]
  (let [[comps _ mm] (reduce (fn [[cs atoms mm] ty]
                               (let [[c atoms mm] (to-comp ty atoms mm)] [(conj cs c) atoms mm]))
                             [[] [] {}] types)]
    [comps (dec (count mm)) mm]))
