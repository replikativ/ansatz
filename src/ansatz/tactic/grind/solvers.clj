(ns ansatz.tactic.grind.solvers
  "Lean Grind/Types.lean Solvers.mkAction and Finish.lean mkFinish, v4.33.1.
   Interim omega adapter for Cutsat: asserted branch facts in, False proof out."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.grind.egraph :as eg]
            [ansatz.tactic.grind.proof :as gp]
            [ansatz.kernel.reduce :as red]
            [ansatz.meta :as meta]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.omega :as omega]
            [ansatz.tactic.omega-proof :as omega-proof]))

(defn- new-eqs [branch]
  ;; Grind/Types.lean PendingSolverPropagations.propagate sends newEq to
  ;; subscribed solvers. The batch omega adapter consumes the numeric class
  ;; equalities here, reconstructing their checked proofs only on success.
  (let [graph (:graph branch) st (:tc branch)
        numeric #{(e/const' (name/from-string "Nat") [])
                  (e/const' (name/from-string "Int") [])}]
    (keep (fn [[expr _]]
            (let [root (eg/get-root graph expr)]
              (when-not (identical? expr root)
                (let [type (tc/infer-type st expr)]
                  (when (and (contains? numeric type)
                             (= type (tc/infer-type st root)))
                    [(e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) type expr root)
                     {:proof (delay (gp/mk-eq-proof graph st expr root))}])))))
          (:enodes graph))))

(defn check
  "Return a contradiction proof, or nil when omega finds no contradiction.
   The public proof-free preflight distinguishes not-applicable from certificate
   failures: no exception from inference, search or reconstruction is caught."
  [branch]
  (let [false-expr (e/const' (name/from-string "False") [])
        ;; Derived facts have proof expressions, not necessarily local fvars.
        ;; Give omega local assumptions, then discharge them with those proofs.
        [ps lctx bindings]
        (reduce (fn [[ps lctx bindings] [prop {:keys [proof]}]]
                  (let [[ps id] (proof/alloc-id ps)]
                    [ps (red/lctx-add-local lctx id "arith" prop)
                     (conj bindings [id prop proof])]))
                [(:ps branch) (:lctx (:tc branch)) []] (concat (:facts branch) (new-eqs branch)))]
    (when (omega-proof/decides? (:env ps) false-expr lctx)
      (let [[ps gid] (proof/fresh-mvar (assoc ps :goals []) false-expr lctx)
            ps (omega/omega ps)
            term (meta/zonk-expr (:meta-mctx ps) (e/mvar gid))]
        (reduce (fn [body [id prop hp]]
                  (let [abstracted (e/abstract1 body id)]
                    (if (identical? body abstracted) body
                        (e/let' "arith" prop (if (delay? hp) @hp hp) abstracted))))
                term (rseq bindings))))))
