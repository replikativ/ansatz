(ns ansatz.tactic.grind.solvers
  "Lean Grind/Types.lean Solvers.mkAction and Finish.lean mkFinish, v4.33.1.
   Interim omega adapter for Cutsat: asserted branch facts in, False proof out."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.reduce :as red]
            [ansatz.meta :as meta]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.omega :as omega]
            [ansatz.tactic.omega-proof :as omega-proof]))

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
                [(:ps branch) (:lctx (:tc branch)) []] (:facts branch))]
    (when (omega-proof/decides? (:env ps) false-expr lctx)
      (let [[ps gid] (proof/fresh-mvar (assoc ps :goals []) false-expr lctx)
            ps (omega/omega ps)
            term (meta/zonk-expr (:meta-mctx ps) (e/mvar gid))]
        (reduce (fn [body [id prop hp]]
                  (e/let' "arith" prop hp (e/abstract1 body id)))
                term (rseq bindings))))))
