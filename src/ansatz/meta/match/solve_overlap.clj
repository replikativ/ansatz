(ns ansatz.meta.match.solve-overlap
  "Proof of splitter precedence premises, following Lean/Meta/Match/SolveOverlap.lean.
   Uses the tactic proof state on the existing meta goal so all assignments remain
   in the match compiler's metavariable context."
  (:require [ansatz.meta.tactic.cases :as c]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.meta.constructions.util :as u]
            [ansatz.meta.fvar-subst :as subst]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.proof :as proof]))

(defn- free-fvar-ids [term]
  (let [ids (volatile! #{})]
    (subst/map-expr-fvars (fn [id] (vswap! ids conj id) (e/fvar id)) term)
    @ids))

(defn- constructor-contradiction [ctx ps]
  (let [goal (proof/current-goal ps)]
    (when (= (:type goal) (u/const' "False" []))
      (some
       (fn [[id d]]
         (try
           (let [[h args] (e/get-app-fn-args (:type d))]
             (when (and (e/const? h)
                        (= (e/const-name h) (name/from-string "Eq"))
                        (= 3 (count args)))
               (c/set-lctx! ctx (:lctx goal))
               (let [term (c/mk-no-confusion ctx (:type goal)
                                             (first args) (second args) (nth args 2)
                                             (e/fvar id))]
                 ((requiring-resolve 'ansatz.tactic.basic/exact)
                  (assoc ps :env (:env @ctx)) term))))
           (catch Exception _ nil)))
       (:lctx goal)))))

(defn solve-overlap! [ctx id]
  (c/with-goal! ctx id)
  (let [run (requiring-resolve 'ansatz.core/run-tactic)
        allowed (set (keys (:lctx (c/goal-decl ctx id))))
        ps {:env (:env @ctx)
            :goals [id]
            :meta-mctx (c/mctx ctx)
            :next-id (inc @(:next-id @ctx))
            :root-mvar id
            :trace []
            :weight 1.0}
        ps ((requiring-resolve 'ansatz.tactic.basic/intros) ps)
        candidate (some (fn [f]
                          (when-let [p (try (f) (catch clojure.lang.ExceptionInfo _ nil))]
                            (when (proof/solved? p)
                              (let [term (extract/extract p)]
                                (when (every? allowed (free-fvar-ids term))
                                  [p term])))))
                        (cons #(constructor-contradiction ctx ps)
                              (map #(fn [] (run ps %))
                                   ['(contradiction) '(simp_all) '(omega)])))]
    (when-not candidate
      (throw (ex-info "Failed to solve splitter overlap premise"
                      {:kind :match-overlap-proof-failure
                       :goal (proof/format-goals ps)})))
    (let [[ps term] candidate]
      (reset! (:meta-mctx @ctx) (:meta-mctx ps))
      (reset! (:next-id @ctx) (max @(:next-id @ctx) (:next-id ps)))
      term)))
