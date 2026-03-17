;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; Tactic layer — SAT decision procedure with DRAT-verified proofs.

(ns ansatz.tactic.sat-decide
  "The `sat-decide` tactic closes goals using SAT solving + DRAT verification.

   Unlike `decide` (which uses kernel evaluation), this tactic:
   1. Translates Ansatz propositions to propositional SAT (via Tseitin encoding)
   2. Solves with the zustand CDCL SAT solver
   3. Verifies the UNSAT certificate via DRAT proof checking
   4. Closes the goal via a trusted axiom (externally verified, not kernel-checked)

   This enables proving hard finite combinatorial results (Schur numbers, Ramsey
   bounds, etc.) that are too expensive for kernel evaluation.

   The `sat-oracle` axiom is unsound in isolation but is only used after
   successful SAT solving + DRAT verification, providing external soundness.

   For direct SAT encoding (bypassing Ansatz→SAT translation), use `sat-decide-raw`
   which takes pre-built DIMACS clauses."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.decide :as decide]))

;; ============================================================
;; SAT Oracle axiom
;; ============================================================

(def ^:private sat-oracle-name (name/from-string "SATOracle"))

(defn sat-oracle-type
  "Type of the SAT oracle axiom: ∀ (P : Prop), P"
  []
  (e/forall' "P" (e/sort' lvl/zero) (e/bvar 0) :default))

(defn add-sat-oracle
  "Add the SATOracle axiom to an environment. Returns the updated env.
   This axiom is marked unsafe — it is only sound when guarded by
   external SAT+DRAT verification."
  [env]
  (let [ci (env/mk-axiom sat-oracle-name [] (sat-oracle-type) :unsafe? true)]
    (env/add-constant env ci)))

(defn ensure-sat-oracle
  "Ensure the SATOracle axiom is in the environment. Returns the env
   (unchanged if already present)."
  [env]
  (if (env/lookup env sat-oracle-name)
    env
    (add-sat-oracle env)))

;; ============================================================
;; Ansatz → SAT translation (propositional fragment via Tseitin)
;; ============================================================

;; The translation works on the same fragment as prop->smt but produces
;; a CNF formula (list of clauses) instead of SMT-LIB s-expressions.
;;
;; Variables: each atomic proposition gets a DIMACS variable (1-indexed).
;; Tseitin encoding introduces auxiliary variables for sub-formulas.

(defn- alloc-var
  "Allocate a fresh DIMACS variable. Returns [state new-var]."
  [state]
  (let [v (:next-var state)]
    [(update state :next-var inc) v]))

(defn- add-clause
  "Add a clause (vector of DIMACS literals) to the state."
  [state clause]
  (update state :clauses conj clause))

(declare prop->cnf*)

(defn- term->nat
  "Try to extract a ground Nat value from a Ansatz term (for atomic comparisons)."
  [term]
  (when (e/lit-nat? term)
    (e/lit-nat-val term)))

(defn- prop->cnf*
  "Recursively translate a Ansatz proposition to CNF via Tseitin encoding.
   Returns [state var] where var is the DIMACS variable representing this prop.
   The state accumulates clauses that constrain var to equal the proposition."
  [state env prop]
  (let [st (tc/mk-tc-state env)]
    ;; Try to match the head constant
    (if-let [[head-name _levels args] (decide/try-match-prop st prop)]
      (let [head (name/->string head-name)]
        (case head
          ;; True → always true
          "True"
          (let [[state v] (alloc-var state)]
            [(add-clause state [v]) v])

          ;; False → always false
          "False"
          (let [[state v] (alloc-var state)]
            [(add-clause state [(- v)]) v])

          ;; And P Q → Tseitin: v ↔ (p ∧ q)
          "And"
          (let [[state vp] (prop->cnf* state env (nth args 0))
                [state vq] (prop->cnf* state env (nth args 1))
                [state v] (alloc-var state)]
            ;; v → p, v → q, ¬v ∨ p, ¬v ∨ q, ¬p ∨ ¬q ∨ v
            [(-> state
                 (add-clause [(- v) vp])
                 (add-clause [(- v) vq])
                 (add-clause [(- vp) (- vq) v]))
             v])

          ;; Or P Q → Tseitin: v ↔ (p ∨ q)
          "Or"
          (let [[state vp] (prop->cnf* state env (nth args 0))
                [state vq] (prop->cnf* state env (nth args 1))
                [state v] (alloc-var state)]
            [(-> state
                 (add-clause [(- v) vp vq])
                 (add-clause [(- vp) v])
                 (add-clause [(- vq) v]))
             v])

          ;; Not P → Tseitin: v ↔ ¬p
          "Not"
          (let [[state vp] (prop->cnf* state env (nth args 0))
                [state v] (alloc-var state)]
            [(-> state
                 (add-clause [(- v) (- vp)])
                 (add-clause [vp v]))
             v])

          ;; Eq T a b (for ground Nat) → atomic variable
          "Eq"
          (let [a (term->nat (nth args 1))
                b (term->nat (nth args 2))]
            (if (and a b)
              ;; Ground equality — resolve directly
              (let [[state v] (alloc-var state)]
                [(add-clause state [(if (= a b) v (- v))]) v])
              ;; Non-ground — treat as opaque atom
              (let [key [:eq (e/->string (nth args 1)) (e/->string (nth args 2))]
                    existing (get (:atoms state) key)]
                (if existing
                  [state existing]
                  (let [[state v] (alloc-var state)]
                    [(assoc-in state [:atoms key] v) v])))))

          ;; Decidable.decide — skip the wrapper
          "Decidable" (prop->cnf* state env (nth args 0))

          ;; Default: treat as opaque atomic proposition
          (let [key [:const head (mapv e/->string args)]
                existing (get (:atoms state) key)]
            (if existing
              [state existing]
              (let [[state v] (alloc-var state)]
                [(assoc-in state [:atoms key] v) v])))))

      ;; Not a recognized pattern — opaque atom
      (let [key [:opaque (e/->string prop)]
            existing (get (:atoms state) key)]
        (if existing
          [state existing]
          (let [[state v] (alloc-var state)]
            [(assoc-in state [:atoms key] v) v]))))))

(defn prop->cnf
  "Translate a Ansatz proposition to CNF.
   Returns {:clauses [[lit ...] ...] :num-vars int :root-var int}."
  [env prop]
  (let [init-state {:next-var 1 :clauses [] :atoms {}}
        [state root-var] (prop->cnf* init-state env prop)]
    {:clauses (conj (:clauses state) [root-var]) ;; assert the root is true
     :num-vars (dec (:next-var state))
     :root-var root-var}))

;; ============================================================
;; SAT-decide tactic
;; ============================================================

(defn sat-decide
  "Close the current goal using SAT solving + DRAT verification.

   1. Translate goal proposition to CNF (Tseitin encoding)
   2. Solve with zustand CDCL solver
   3. If UNSAT: verify DRAT certificate, close goal via SATOracle axiom
   4. If SAT: report countermodel (proposition is false)

   Returns updated proof state.
   Throws on failure (SAT result, translation error, DRAT verification failure)."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal
            (throw (ex-info "Tactic error: No goals" {:kind :tactic-error})))
        env (ensure-sat-oracle (:env ps))
        ps (assoc ps :env env)
        prop (:type goal)]
    ;; Translate to CNF
    (let [{:keys [clauses]} (prop->cnf env prop)
          ;; Solve and verify
          result (((requiring-resolve 'zustand.drat/solve-and-verify)) clauses)]
      (case (:result result)
        :unsat
        (if (:verified result)
          ;; DRAT-verified UNSAT — close with SATOracle
          (let [proof-term (e/app (e/const' sat-oracle-name []) prop)]
            (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof-term})
                (proof/record-tactic :sat-decide
                                     {:stats (:stats result)} (:id goal))))
          ;; UNSAT but DRAT verification failed
          (throw (ex-info "SAT: UNSAT result but DRAT verification failed"
                          {:kind :tactic-error :stats (:stats result)})))

        :sat
        (throw (ex-info "SAT: proposition has a countermodel (formula is SAT)"
                        {:kind :tactic-error :model (:model result)}))

        ;; Unknown or error
        (throw (ex-info "SAT: solver returned unexpected result"
                        {:kind :tactic-error :result result}))))))

(defn sat-decide-raw
  "Close the current goal using pre-built SAT clauses + DRAT verification.

   This is the 'escape hatch' for problems with custom SAT encodings
   (e.g., Schur numbers, Ramsey bounds) where the encoding is manually
   verified to correspond to the Ansatz proposition.

   clauses: vector of vectors of DIMACS literals, e.g. [[1 2] [-1 -3] ...]
   The caller is responsible for ensuring the encoding is correct.

   Returns updated proof state."
  [ps clauses]
  (let [goal (proof/current-goal ps)
        _ (when-not goal
            (throw (ex-info "Tactic error: No goals" {:kind :tactic-error})))
        env (ensure-sat-oracle (:env ps))
        ps (assoc ps :env env)
        prop (:type goal)
        result (((requiring-resolve 'zustand.drat/solve-and-verify)) clauses)]
    (case (:result result)
      :unsat
      (if (:verified result)
        (let [proof-term (e/app (e/const' sat-oracle-name []) prop)]
          (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof-term})
              (proof/record-tactic :sat-decide-raw
                                   {:stats (:stats result)
                                    :num-clauses (count clauses)} (:id goal))))
        (throw (ex-info "SAT: UNSAT but DRAT verification failed"
                        {:kind :tactic-error :stats (:stats result)})))

      :sat
      (throw (ex-info "SAT: formula is satisfiable (proposition may be false)"
                      {:kind :tactic-error :model (:model result)}))

      (throw (ex-info "SAT: unexpected result"
                      {:kind :tactic-error :result result})))))
