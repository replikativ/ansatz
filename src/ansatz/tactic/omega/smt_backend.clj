;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; SMT solver backend for omega — uses zustand with Farkas certificates.
;;
;; Takes a prepared omega problem, translates constraints to SMT,
;; runs zustand, extracts Farkas certificate, and reconstructs
;; a Justification tree compatible with the FM solver's output.

(ns ansatz.tactic.omega.smt-backend
  "SMT solver backend for omega problems.

   Translates omega constraints to zustand integer arithmetic,
   runs the solver, and on UNSAT extracts a Farkas certificate.
   The certificate is mapped back to a Justification tree using
   :combo nodes, producing the same tree shape as FM.

   The solver is untrusted — the Justification tree is verified
   by kernel type-checking of the extracted proof term."
  (:require [ansatz.solver.smt :as smt]
            [ansatz.tactic.omega.problem :as p]))

;; ============================================================
;; Problem -> SMT translation
;; ============================================================

(defn constraints->zustand-assertions
  "Convert omega problem constraints to zustand SMT assertions.
   Each constraint is: lower <= dot(coeffs, atoms) <= upper.

   Creates integer variables :v0, :v1, ... and asserts bounds directly.

   Returns {:solver zustand-solver-state
            :assertion-map [{:fact fact :bound :lower/:upper} ...]}
   The assertion-map tracks which zustand constraint ID maps to which fact+bound."
  [problem]
  (let [constraints (:constraints problem)
        fact-list (vec (vals constraints))
        n (:num-vars problem)
        var-kws (mapv #(keyword (str "v" %)) (range n))
        solver (reduce (fn [s kw] (smt/declare-var s kw :int))
                       (smt/make-solver)
                       var-kws)
        build-sum (fn [coeffs]
                    (let [terms (keep-indexed
                                 (fn [i c]
                                   (when-not (zero? c)
                                     (if (= 1 c)
                                       (nth var-kws i)
                                       [:* c (nth var-kws i)])))
                                 coeffs)]
                      (case (count terms)
                        0 0
                        1 (first terms)
                        (reduce (fn [a b] [:+ a b]) terms))))]
    (loop [solver solver
           assertion-map []
           facts fact-list]
      (if (empty? facts)
        {:solver solver :assertion-map assertion-map}
        (let [fact (first facts)
              {:keys [coeffs constraint]} fact
              {:keys [lower upper]} constraint
              sum-expr (build-sum coeffs)
              [solver' amap']
              (let [s1 (if lower
                         [(smt/assert-constraint solver [:>= sum-expr lower])
                          (conj assertion-map {:fact fact :bound :lower})]
                         [solver assertion-map])
                    s2 (if upper
                         [(smt/assert-constraint (first s1) [:<= sum-expr upper])
                          (conj (second s1) {:fact fact :bound :upper})]
                         s1)]
                s2)]
          (recur solver' amap' (rest facts)))))))

;; ============================================================
;; Farkas certificate -> Justification tree
;; ============================================================

(defn farkas-justification
  "Build a Justification tree from a Farkas certificate.
   The certificate says: a weighted sum of the bound constraints yields a contradiction.

   assertion-map tracks which zustand constraint ID maps to which fact and bound direction.
   We group certificate entries by fact, combine lower+upper bounds for same fact,
   then chain all facts using :combo nodes.

   Returns {:justification :constraint :coeffs} or nil."
  [problem assertion-map certificate]
  (let [entries (:entries certificate)]
    (when (seq entries)
      (let [mapped (keep (fn [{:keys [constraint-id farkas-coeff]}]
                           (when (< constraint-id (count assertion-map))
                             (let [{:keys [fact bound]} (nth assertion-map constraint-id)]
                               {:fact fact :weight farkas-coeff :bound bound})))
                         entries)
            by-fact (group-by :fact mapped)]
        (when (seq by-fact)
          (let [combined-entries
                (for [[fact entries] by-fact]
                  (let [lower-w (reduce +' 0 (map :weight (filter #(= :lower (:bound %)) entries)))
                        upper-w (reduce +' 0 (map :weight (filter #(= :upper (:bound %)) entries)))
                        {:keys [lower upper]} (:constraint fact)
                        weighted-lower (when (and lower (pos? lower-w))
                                         (*' lower-w lower))
                        weighted-upper (when (and upper (pos? upper-w))
                                         (*' upper-w upper))
                        total-w (+' lower-w upper-w)]
                    {:fact fact
                     :weight (if (pos? total-w) total-w 1)
                     :constraint {:lower weighted-lower :upper weighted-upper}}))]
            (when (seq combined-entries)
              (let [entries-vec (vec combined-entries)
                    first-e (first entries-vec)]
                (reduce (fn [{:keys [justification constraint coeffs weight]} entry]
                          (let [a weight
                                b (:weight entry)
                                right-j (:justification (:fact entry))
                                nv (:num-vars problem)
                                new-coeffs (vec (for [idx (range nv)]
                                                  (+' (*' a (get coeffs idx 0))
                                                      (*' b (get (:coeffs (:fact entry)) idx 0)))))
                                new-s (p/constraint-combo a constraint
                                                          b (:constraint (:fact entry)))
                                new-j (p/justification-combo a justification
                                                             b right-j
                                                             new-s new-coeffs)]
                            {:justification new-j :constraint new-s
                             :coeffs new-coeffs :weight 1}))
                        {:justification (:justification (:fact first-e))
                         :constraint (:constraint (:fact first-e))
                         :coeffs (:coeffs (:fact first-e))
                         :weight (:weight first-e)}
                        (rest entries-vec))))))))))

;; ============================================================
;; Public API
;; ============================================================

(defn solve
  "Run the SMT solver on the reified omega problem.
   Returns the problem with :possible false and :proof-false set, or nil."
  [problem]
  (when (seq (:constraints problem))
    (try
      (let [{:keys [solver assertion-map]} (constraints->zustand-assertions problem)
            result (smt/check solver)]
        (when (= :unsat (:result result))
          (let [cert (smt/get-farkas-certificate solver)]
            (when cert
              (let [farkas (farkas-justification problem assertion-map cert)]
                (when farkas
                  (let [fact (p/mk-fact (:coeffs farkas) (:constraint farkas)
                                        (:justification farkas))]
                    (when (p/is-impossible? fact)
                      (let [result (p/insert-constraint
                                    (assoc problem :possible true :proof-false nil)
                                    fact)]
                        (when-not (:possible result)
                          result))))))))))
      (catch Exception _
        nil))))
