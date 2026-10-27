;; Port of Init/Omega/LinearCombo.lean: coordinate, add, sub, mul, eval, Lean checkout 55f80e10.
(ns ansatz.tactic.omega.linear-combo)

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
