;; Copyright (c) 2026 Simmis GmbH. All rights reserved.
;; Tactic layer — search infrastructure for proof exploration.

(ns cic.tactic.search
  "Search infrastructure for automated and semi-automated proof construction.
   Implements the heuristic plugin interface from the research design:
   any function (proof-state → [{:ps proof-state :weight double}]) can serve
   as a search heuristic.

   Supports:
   - Breadth-first and best-first search over tactic applications
   - Sequential Monte Carlo (SMC) resampling over proof branches
   - Tactic enumeration for automated search
   - Trace collection for strategy learning"
  (:require [cic.tactic.proof :as proof]
            [cic.tactic.basic :as basic]
            [cic.tactic.extract :as extract]
            [cic.kernel.expr :as e]
            [cic.kernel.reduce :as red]))

;; ============================================================
;; Tactic enumeration — generate candidate tactics for a goal
;; ============================================================

(defn enumerate-tactics
  "Given a proof state, enumerate applicable tactics for the current goal.
   Returns a seq of {:tactic fn :name keyword :args vector :weight double}.
   Weight represents prior probability of success."
  [ps]
  (when-let [goal (proof/current-goal ps)]
    (let [tactics (transient [])]
      ;; intro — if goal is forall
      (try
        (basic/intro ps)
        (conj! tactics {:tactic basic/intro :name :intro :args [] :weight 0.8})
        (catch Exception _))

      ;; assumption — if any hyp matches
      (try
        (basic/assumption ps)
        (conj! tactics {:tactic basic/assumption :name :assumption :args [] :weight 0.9})
        (catch Exception _))

      ;; rfl — if goal is Eq
      (try
        (basic/rfl ps)
        (conj! tactics {:tactic basic/rfl :name :rfl :args [] :weight 0.95})
        (catch Exception _))

      ;; constructor — if goal head is inductive
      (try
        (basic/constructor ps)
        (conj! tactics {:tactic basic/constructor :name :constructor :args [] :weight 0.5})
        (catch Exception _))

      ;; apply with each hypothesis that has a function type
      (doseq [[id decl] (:lctx goal)]
        (when (= :local (:tag decl))
          (try
            (basic/apply-tac ps (e/fvar id))
            (conj! tactics {:tactic #(basic/apply-tac % (e/fvar id))
                            :name :apply-hyp
                            :args [id]
                            :weight 0.3})
            (catch Exception _))))

      (persistent! tactics))))

;; ============================================================
;; Search strategies
;; ============================================================

(defn try-tactic
  "Try applying a tactic function, returning the new ps or nil on failure."
  [ps tactic-fn & args]
  (try
    (apply tactic-fn ps args)
    (catch Exception _ nil)))

(defn auto-solve
  "Try to automatically solve the current goal using simple tactics.
   Returns solved ps or nil."
  [ps max-depth]
  (when (and (pos? max-depth) (not (proof/solved? ps)))
    (let [candidates (enumerate-tactics ps)]
      (some (fn [{:keys [tactic]}]
              (when-let [ps' (try (tactic ps) (catch Exception _ nil))]
                (if (proof/solved? ps')
                  ps'
                  (auto-solve ps' (dec max-depth)))))
            ;; Sort by weight descending (best first)
            (sort-by :weight > candidates)))))

;; ============================================================
;; Branching and SMC
;; ============================================================

(defn fork
  "Fork a proof state into multiple branches by applying different tactics.
   tactics is a seq of {:name keyword :fn (fn [ps] → ps')}.
   Returns a seq of {:name keyword :ps proof-state :weight double} for
   successful branches."
  [ps tactics]
  (->> tactics
       (keep (fn [{:keys [name fn weight] :or {weight 1.0}}]
               (when-let [ps' (try (fn ps) (catch Exception _ nil))]
                 {:name name
                  :ps (proof/adjust-weight ps' weight)
                  :weight (* (:weight ps') weight)})))
       vec))

(defn resample
  "SMC resampling: given a seq of {:ps :weight} particles, resample
   proportional to weight. Returns n particles (with replacement)."
  [particles n]
  (when (seq particles)
    (let [total-weight (reduce + (map :weight particles))
          normalized (map #(update % :weight / total-weight) particles)]
      (loop [result [] remaining n]
        (if (zero? remaining)
          result
          (let [r (rand)
                selected (loop [ps normalized cum 0.0]
                           (let [p (first ps)
                                 cum' (+ cum (:weight p))]
                             (if (or (>= cum' r) (nil? (next ps)))
                               p
                               (recur (next ps) cum'))))]
            (recur (conj result (proof/set-weight (:ps selected) 1.0))
                   (dec remaining))))))))

(defn beam-search
  "Beam search over tactic applications.
   At each step, expand the best beam-width states, keeping the top ones.
   Returns the first solved state, or nil after max-steps."
  [ps beam-width max-steps]
  (loop [beam [{:ps ps :weight 1.0}]
         step 0]
    (when (< step max-steps)
      ;; Check if any state is solved
      (if-let [solved (first (filter #(proof/solved? (:ps %)) beam))]
        (:ps solved)
        ;; Expand each state
        (let [expanded (mapcat
                        (fn [{:keys [ps weight]}]
                          (let [candidates (enumerate-tactics ps)]
                            (keep (fn [{:keys [tactic weight tac-weight] :as c}]
                                    (when-let [ps' (try (tactic ps) (catch Exception _ nil))]
                                      {:ps ps'
                                       :weight (* weight (or (:weight c) 0.5))}))
                                  candidates)))
                        beam)
              ;; Keep top beam-width by weight
              top (take beam-width (sort-by :weight > expanded))]
          (if (empty? top)
            nil
            (recur top (inc step))))))))

;; ============================================================
;; Trace analysis
;; ============================================================

(defn trace-summary
  "Summarize the tactic trace from a proof state."
  [ps]
  {:tactics (mapv :tactic (:trace ps))
   :num-steps (count (:trace ps))
   :solved (proof/solved? ps)
   :open-goals (count (:goals ps))
   :weight (:weight ps)})
