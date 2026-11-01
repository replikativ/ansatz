;; Port of Mathlib/Tactic/Linarith/Oracle/SimplexAlgorithm/{Datatypes,Gauss,SimplexAlgorithm,
;; PositiveVector}.lean and Oracle/SimplexAlgorithm.lean (the default linarith oracle,
;; `CertificateOracle.simplexAlgorithmSparse`).
(ns ansatz.tactic.linarith.simplex
  "Certificate search for linarith as a linear program, solved by the simplex method with
   Bland's rule, exactly as Mathlib does it.

   Given comparisons `tᵢ Rᵢ 0` (as `{:str :coeffs}`), find natural numbers `kᵢ`, not all
   zero on the strict ones, with `Σ kᵢ tᵢ = 0` coefficientwise. Arithmetic is exact
   (Clojure rationals and big integers); a sparse matrix is a vector of row maps
   `col → value` holding only nonzero entries.")

;; ------------------------------------------------------------------
;; sparse matrices over ℚ (Datatypes.lean: SparseMatrix)
;; ------------------------------------------------------------------

(defn- get-elem [mat i j] (get (nth mat i) j 0))

(defn- set-elem [mat i j v]
  (if (zero? v)
    (update mat i dissoc j)
    (update mat i assoc j v)))

(defn- of-values [n vals]
  (reduce (fn [m [i j v]] (if (zero? v) m (update m i assoc j v)))
          (vec (repeat n {})) vals))

(defn- get-values [mat]
  (for [[i row] (map-indexed vector mat) [j v] row] [i j v]))

(defn- swap-rows [mat i j]
  (if (= i j) mat (assoc mat i (nth mat j) j (nth mat i))))

(defn- subtract-row
  "row_j -= coef * row_i"
  [mat i j coef]
  (let [src (nth mat i)]
    (update mat j (fn [row]
                    (reduce-kv (fn [cur k val]
                                 (let [nv (- (get cur k 0) (* coef val))]
                                   (if (zero? nv) (dissoc cur k) (assoc cur k nv))))
                               row src)))))

(defn- divide-row [mat i coef]
  (update mat i (fn [row] (reduce-kv (fn [cur k v] (assoc cur k (/ v coef))) {} row))))

;; ------------------------------------------------------------------
;; Gauss.lean: getTableau
;; ------------------------------------------------------------------

(defn- find-nonzero-row [mat n row-start col]
  (some #(when-not (zero? (get-elem mat % col)) %) (range row-start n)))

(defn get-tableau
  "Solve `A x = 0` by Gaussian elimination: a tableau `{:basic :free :mat}` where row i of
   `mat` expresses `basic[i]` as a combination of the `free` variables."
  [mat n m]
  (loop [mat mat free [] basic [] row 0 col 0]
    (if (and (< row n) (< col m))
      (if-let [r (find-nonzero-row mat n row col)]
        (let [mat (swap-rows mat row r)
              mat (divide-row mat row (get-elem mat row col))
              mat (reduce (fn [mat i]
                            (if (= i row) mat
                                (let [coef (get-elem mat i col)]
                                  (if (zero? coef) mat (subtract-row mat row i coef)))))
                          mat (range n))]
          (recur mat free (conj basic col) (inc row) (inc col)))
        (recur mat (conj free col) basic row (inc col)))
      (let [free (into free (range col m))
            free-idx (into {} (map-indexed (fn [k j] [j k]) free))
            vals (keep (fn [[i j v]]
                         (when (and (< i (count basic)) (not= j (nth basic i)))
                           [i (free-idx j) (- v)]))
                       (get-values mat))]
        {:basic basic :free free :mat (of-values (count basic) vals)}))))

;; ------------------------------------------------------------------
;; SimplexAlgorithm.lean
;; ------------------------------------------------------------------

(defn- do-pivot [{:keys [basic free mat]} exit-idx enter-idx]
  (let [intersect (get-elem mat exit-idx enter-idx)
        mat (reduce (fn [mat i]
                      (if (= i exit-idx) mat
                          (let [coef (/ (get-elem mat i enter-idx) intersect)
                                mat (if (zero? coef) mat (subtract-row mat exit-idx i coef))]
                            (set-elem mat i enter-idx coef))))
                    mat (range (count basic)))
        mat (set-elem mat exit-idx enter-idx -1)
        mat (divide-row mat exit-idx (- intersect))]
    {:basic (assoc basic exit-idx (nth free enter-idx))
     :free (assoc free enter-idx (nth basic exit-idx))
     :mat mat}))

(defn- check-success [{:keys [basic free mat]}]
  (let [last-idx (dec (count free))]
    (and (pos? (get-elem mat 0 last-idx))
         (every? #(>= (get-elem mat % last-idx) 0) (range (count basic))))))

(defn- choose-entering [{:keys [free mat]}]
  ;; among the free variables with positive objective coefficient, the smallest index
  (reduce (fn [best i]
            (if (and (pos? (get-elem mat 0 i))
                     (or (nil? best) (< (nth free i) (nth free best))))
              i best))
          nil (range (dec (count free)))))

(defn- choose-exiting [{:keys [basic free mat]} enter-idx]
  ;; the strictest limit on the entering variable, ties broken by smallest index
  (let [last-idx (dec (count free))]
    (first
     (reduce (fn [[best min-coef min-idx :as acc] i]
               (let [a (get-elem mat i enter-idx)]
                 (if (>= a 0) acc
                     (let [coef (/ (- (get-elem mat i last-idx)) a)]
                       (if (or (nil? best) (< coef min-coef)
                               (and (== coef min-coef) (< (nth basic i) min-idx)))
                         [i coef (nth basic i)]
                         acc)))))
             [nil nil nil] (range 1 (count basic))))))

(def ^:dynamic *max-pivots* 100000)

(defn run-simplex
  "Run the simplex method from a feasible tableau. Returns the final tableau, or nil when
   the problem is infeasible (no entering variable)."
  [tableau]
  (loop [t tableau k 0]
    (cond
      (check-success t) t
      (> k *max-pivots*) (throw (ex-info "linarith: simplex pivot limit reached"
                                         {:kind :tactic-error :pivots k}))
      :else
      (if-let [enter (choose-entering t)]
        (let [exit (choose-exiting t enter)]
          (if (nil? exit)
            nil ; unbounded cannot happen for the bounded LP; treat as failure
            (recur (do-pivot t exit enter) (inc k))))
        nil))))

;; ------------------------------------------------------------------
;; PositiveVector.lean
;; ------------------------------------------------------------------

(defn- state-lp
  "Mathlib's stateLP: columns are f (objective), z (slack), the m unknowns, then y (the
   homogenized 1); rows are the objective, the bound `z + Σx = y`, then A."
  [a-values n m strict-indexes]
  (let [objective (cons [0 0 -1] (map (fn [idx] [0 (+ idx 2) 1]) strict-indexes))
        constraint (concat [[1 1 1] [1 (+ m 2) -1]] (map (fn [i] [1 (+ i 2) 1]) (range m)))
        shifted (map (fn [[i j v]] [(+ i 2) (+ j 2) v]) a-values)]
    (of-values (+ n 2) (concat objective constraint shifted))))

(defn- extract-solution [{:keys [basic free mat]} m]
  (let [last-idx (dec (count free))]
    (reduce (fn [ans i]
              (let [b (nth basic i)]
                ;; Mathlib writes `ans[basic[i] - 2]` with natural-number subtraction, so the
                ;; slack z (column 1) lands on index 0 when it is basic; the auxiliary
                ;; columns carry no hypothesis, so they are skipped here.
                (if (and (>= b 2) (< (- b 2) m))
                  (assoc ans (- b 2) (get-elem mat i last-idx))
                  ans)))
            (vec (repeat m 0)) (range 1 (count basic)))))

(defn find-positive-vector
  "A nonnegative vector v with `A v = 0` and Σ_{strict} vᵢ > 0, or nil."
  [a-values n m strict-indexes]
  (let [b (state-lp a-values n m strict-indexes)
        t (get-tableau b (+ n 2) (+ m 3))
        res (run-simplex t)]
    (when res (extract-solution res m))))

;; ------------------------------------------------------------------
;; Oracle/SimplexAlgorithm.lean
;; ------------------------------------------------------------------

(defn- lcm' [a b] (if (or (zero? a) (zero? b)) 0 (quot (abs (* a b)) (.gcd (biginteger a) (biginteger b)))))

(defn- postprocess [vec]
  (let [den (reduce (fn [acc x] (lcm' acc (if (ratio? x) (denominator x) 1))) 1 vec)]
    ;; `(x * common_den).floor.toNat`
    (into {} (keep-indexed (fn [idx x]
                             (let [v (* x den)
                                   ;; the solution is nonnegative, so quot is floor
                                   v (if (ratio? v) (bigint (quot (numerator v) (denominator v)))
                                         (bigint v))]
                               (when (pos? v) [idx v])))
                           vec))))

(defn produce-certificate
  "CertificateOracle.simplexAlgorithmSparse: comps → {hyp-index natural-coefficient}, or
   nil when the comparisons are satisfiable."
  [comps max-var]
  (let [values (for [[idx comp] (map-indexed vector comps)
                     [v c] (:coeffs comp)]
                 [v idx c])
        strict (keep-indexed (fn [i c] (when (= :lt (:str c)) i)) comps)
        vec (find-positive-vector values (inc max-var) (count comps) strict)]
    (when vec (postprocess vec))))
