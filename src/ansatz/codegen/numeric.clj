(ns ansatz.codegen.numeric
  "Exact, total integer operations for executable Lean terms. These implement the
   runtime contract, independently of kernel reduction. Inputs have their Lean
   domains (in particular, pow's exponent and Nat operands are natural numbers).")

(defn pow
  "Integer power with a Nat exponent, by squaring. Never converts through double
   or narrows the exponent; trivial bases also handle arbitrarily large exponents."
  [base exponent]
  (when-not (and (integer? exponent) (not (neg? exponent)))
    (throw (IllegalArgumentException. "Lean integer power requires a Nat exponent")))
  (cond
    (zero? exponent) 1
    (zero? base) 0
    (= base 1) 1
    (= base -1) (if (odd? exponent) -1 1)
    :else
    (loop [acc 1 b base n exponent]
      (let [acc (if (odd? n) (*' acc b) acc)
            n (quot n 2)]
        (if (zero? n) acc (recur acc (*' b b) n))))))

(defn tdiv
  "Lean Int.tdiv (also Nat.div on natural inputs): total truncating division."
  [x y]
  (cond
    (zero? y) 0
    ;; Clojure quot silently wraps for this one machine-integer quotient.
    (and (= x Long/MIN_VALUE) (= y -1)) (-' x)
    :else (quot x y)))

(defn tmod
  "Lean Int.tmod (also Nat.mod on natural inputs): total truncating remainder."
  [x y]
  (if (zero? y) x (rem x y)))

(defn ediv
  "Lean Int.ediv, used by Div Int: remainder is nonnegative, for either divisor sign."
  [x y]
  (let [q (tdiv x y)]
    (if (and (not (zero? y)) (neg? (rem x y)))
      (if (pos? y) (dec' q) (inc' q))
      q)))

(defn emod
  "Lean Int.emod: x mod 0 = x, otherwise 0 <= remainder < |y|."
  [x y]
  (let [r (tmod x y)]
    (if (and (not (zero? y)) (neg? r))
      (+' r (if (neg? y) (-' y) y))
      r)))

(defn fdiv
  "Lean Int.fdiv: total division rounded toward negative infinity."
  [x y]
  (let [q (tdiv x y) r (tmod x y)]
    (if (and (not (zero? r)) (not (zero? y)) (not= (neg? x) (neg? y)))
      (dec' q)
      q)))

(defn fmod
  "Lean Int.fmod: total remainder with the divisor's sign."
  [x y]
  (let [r (tmod x y)]
    (if (and (not (zero? r)) (not (zero? y)) (not= (neg? x) (neg? y)))
      (+' r y)
      r)))

(defn nat-sub [x y] (max 0 (-' x y)))
(defn nat-abs [x] (if (neg? x) (-' x) x))
