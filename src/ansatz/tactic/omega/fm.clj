;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; Fourier-Motzkin elimination solver backend for omega.
;;
;; Takes a prepared omega problem and returns a solved problem
;; with Justification tree for proof extraction.

(ns ansatz.tactic.omega.fm
  "Fourier-Motzkin elimination solver for omega problems.

   Solves equalities first (easy: ±1 coefficients, hard: balanced mod),
   then eliminates variables via Fourier-Motzkin pairing.

   Produces Justification trees using :combine, :combo, :tidy, :bmod tags."
  (:require [ansatz.tactic.omega.problem :as p]))

;; ============================================================
;; Equality solving
;; ============================================================

(defn- select-equality
  "Find the best equality to solve. Prefers ±1 coefficients."
  [problem]
  (let [eqs (:equalities problem)]
    (when (seq eqs)
      (let [best (reduce (fn [best key]
                           (let [coeffs key
                                 min-abs (apply min (map p/safe-abs
                                                         (filter (complement zero?) coeffs)))]
                             (if (or (nil? best) (< min-abs (:min-abs best)))
                               {:key key :min-abs min-abs}
                               best)))
                         nil eqs)]
        (when best
          [(:key best) (:min-abs best)])))))

(defn- solve-easy-equality
  "Solve an equality with a ±1 coefficient by variable elimination."
  [problem coeffs-key]
  (let [coeffs coeffs-key
        i (first (keep-indexed (fn [idx c] (when (= 1 (p/safe-abs c)) idx))
                               coeffs))
        sign (if (pos? (nth coeffs i)) 1 -1)
        fact (get-in problem [:constraints coeffs-key])
        old-constraints (:constraints problem)
        problem (-> (assoc problem
                           :constraints {}
                           :equalities #{}
                           :eliminations (cons [fact i sign] (:eliminations problem)))
                    (assoc :num-vars (:num-vars problem)))]
    (reduce (fn [p [key other-fact]]
              (if (= key coeffs-key)
                p
                (let [ci (get (:coeffs other-fact) i 0)]
                  (if (zero? ci)
                    (p/add-constraint p other-fact)
                    (let [k (*' -1 sign ci)
                          new-coeffs (vec (map-indexed
                                           (fn [idx _]
                                             (+' (*' k (get (:coeffs fact) idx 0))
                                                 (get (:coeffs other-fact) idx 0)))
                                           (range (max (count (:coeffs fact))
                                                       (count (:coeffs other-fact))))))
                          new-s (p/constraint-combo k (:constraint fact)
                                                    1 (:constraint other-fact))
                          new-j (p/justification-combo k (:justification fact)
                                                       1 (:justification other-fact)
                                                       new-s new-coeffs)
                          combined (p/mk-fact new-coeffs new-s new-j)]
                      (p/add-constraint p (p/tidy-fact combined)))))))
            problem
            old-constraints)))

(defn- solve-hard-equality
  "Solve a hard equality (all |coeff| > 1) by introducing a bmod equation.
   Returns [table' problem'] with the new atom registered in the table.
   build-bmod-expr-fn: (fn [m coeffs-lean-expr atoms-expr] -> Expr) builds the
   bmod_div_term Ansatz expression for the new atom."
  [table problem coeffs-key build-bmod-expr-fn build-atoms-expr-fn]
  (let [fact (get-in problem [:constraints coeffs-key])
        coeffs (:coeffs fact)
        r (-' (:lower (:constraint fact)))
        m (+' (p/min-nat-abs coeffs) 1)
        i (:num-vars problem)
        bmod-div-expr (build-bmod-expr-fn m coeffs table)
        table' (-> table
                   (assoc-in [:idx->expr i] bmod-div-expr)
                   (assoc-in [:idx->int-expr i] bmod-div-expr)
                   (assoc-in [:expr->idx bmod-div-expr] i)
                   (assoc :next-idx (inc i)))
        bmod-cs (p/coeffs-bmod coeffs m)
        padded-coeffs (vec (concat bmod-cs (repeat (- (inc i) (count bmod-cs)) 0)))
        new-coeffs (assoc padded-coeffs i m)
        new-r (p/int-bmod r m)
        new-constraint (p/constraint-exact (-' new-r))
        new-j (p/justification-bmod (:justification fact) m r i)
        new-fact (p/mk-fact new-coeffs new-constraint new-j)
        problem (update problem :num-vars inc)]
    [table' (p/add-constraint problem (p/tidy-fact new-fact))]))

(defn solve-equalities
  "Solve all equalities by variable elimination.
   Returns [table' problem'].
   build-bmod-expr-fn and build-atoms-expr-fn are needed for hard equalities."
  [table problem build-bmod-expr-fn build-atoms-expr-fn]
  (loop [table table
         problem problem
         fuel 100]
    (if (or (not (:possible problem)) (zero? fuel))
      [table problem]
      (if-let [[key min-abs] (select-equality problem)]
        (if (= 1 min-abs)
          (recur table (solve-easy-equality problem key) (dec fuel))
          (let [[table' problem'] (solve-hard-equality table problem key
                                                       build-bmod-expr-fn build-atoms-expr-fn)]
            (recur table' problem' (dec fuel))))
        [table problem]))))

;; ============================================================
;; Fourier-Motzkin elimination
;; ============================================================

(defn- fm-data
  "Prepare Fourier-Motzkin data for each variable."
  [problem]
  (let [n (:num-vars problem)]
    (reduce (fn [data [key fact]]
              (reduce (fn [d i]
                        (let [c (get (:coeffs fact) i 0)]
                          (if (zero? c)
                            (update-in d [i :irrelevant] conj fact)
                            (if (pos? c)
                              (update-in d [i :lower] conj [fact c])
                              (update-in d [i :upper] conj [fact (-' c)])))))
                      data (range n)))
            (vec (for [i (range n)]
                   {:var i :irrelevant [] :lower [] :upper []}))
            (:constraints problem))))

(defn- fm-select
  "Select the best variable to eliminate."
  [data]
  (let [data (filter #(or (seq (:lower %)) (seq (:upper %))) data)]
    (when (seq data)
      (apply min-key
             (fn [d] (* (count (:lower d)) (count (:upper d))))
             data))))

(defn- fourier-motzkin-step
  "One step of Fourier-Motzkin elimination."
  [problem]
  (let [data (fm-data problem)
        selected (fm-select data)]
    (if-not selected
      problem
      (let [{:keys [irrelevant lower upper]} selected
            base (reduce p/add-constraint
                         (assoc problem :constraints {} :equalities #{})
                         irrelevant)]
        (reduce (fn [p [lb-fact lb-coeff]]
                  (reduce (fn [p [ub-fact ub-coeff]]
                            (let [new-coeffs (vec (map-indexed
                                                   (fn [idx _]
                                                     (+' (*' ub-coeff (get (:coeffs lb-fact) idx 0))
                                                         (*' lb-coeff (get (:coeffs ub-fact) idx 0))))
                                                   (range (:num-vars problem))))
                                  new-s (p/constraint-combo ub-coeff (:constraint lb-fact)
                                                            lb-coeff (:constraint ub-fact))
                                  new-j (p/justification-combo ub-coeff (:justification lb-fact)
                                                               lb-coeff (:justification ub-fact)
                                                               new-s new-coeffs)
                                  combined (p/mk-fact new-coeffs new-s new-j)]
                              (p/add-constraint p (p/tidy-fact combined))))
                          p upper))
                base lower)))))

;; ============================================================
;; Public API
;; ============================================================

(defn solve
  "Run the FM omega solver: solve equalities, then FM elimination.
   Returns [table problem].
   build-bmod-expr-fn: (fn [m coeffs table] -> Expr) for hard equality atoms.
   build-atoms-expr-fn: (fn [table] -> Expr) for Ansatz atoms list."
  [table problem build-bmod-expr-fn build-atoms-expr-fn]
  (loop [[table problem] (solve-equalities table problem build-bmod-expr-fn build-atoms-expr-fn)
         max-iters 100]
    (cond
      (not (:possible problem)) [table problem]
      (zero? max-iters) [table problem]
      (empty? (:constraints problem)) [table problem]
      :else (let [problem' (fourier-motzkin-step problem)]
              (recur (solve-equalities table problem' build-bmod-expr-fn build-atoms-expr-fn)
                     (dec max-iters))))))
