;; Port of Init/Omega/Coeffs.lean and IntList.lean: bmod, minNatAbs, maxNatAbs, Lean checkout 55f80e10.
(ns ansatz.tactic.omega.coeffs)

(defn safe-abs [x] (if (neg? x) (-' x) x))

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
