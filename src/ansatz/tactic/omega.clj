;; Tactic layer — omega: the user-facing entry point of the linear arithmetic
;; decision procedure.
;;
;; This namespace is a FRONT END only. All the arithmetic — reification, the
;; Fourier-Motzkin solver, and the proof reconstruction — lives in
;; `ansatz.tactic.omega-proof` (with `ansatz.tactic.omega.problem` and
;; `ansatz.tactic.omega.fm` underneath it).
;;
;; It used to contain a SECOND, complete omega: its own sparse-map linear-combination
;; layer, its own reify-term/reify-prop/negate-goal/collect-hypotheses, its own
;; proof-free Fourier-Motzkin, and ~440 lines of hand-rolled proof-shape fallbacks.
;; Every arithmetic feature had to be built twice and the two copies could disagree —
;; which is exactly how the symbolic-division bug arose: the proof-free procedure
;; answered "unprovable" and vetoed the real engine, which could have proved it. There
;; is now one engine, so a verdict and a proof can no longer come apart.

(ns ansatz.tactic.omega
  "Linear arithmetic decision procedure (omega tactic) — user-facing entry point.

   Supports (see ansatz.tactic.omega-proof for the implementation):
   - Nat: +, -, *, /, %, min, max, ≤, <, =, ≠ (ground multiplication/division only)
   - Int: the same, including negative literals
   - Mixed Nat/Int via coercion, Bool→Prop bridges (Nat.ble/Nat.blt)
   - Systems of linear inequalities, equalities and disjunctions

   Strategy:
   1. `decide`     — kernel evaluation, closes ground goals outright
   2. `rfl`        — equality goals whose sides are definitionally equal
   3. `assumption` — the goal is literally a hypothesis (common after a Bool→Prop
                     bridge normalises a carried fact to the goal's own shape)
   4. omega-proof  — reify, solve, and reconstruct a kernel-checkable proof term

   The kernel always verifies the final proof term."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.decide :as decide-tac]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.omega-proof :as omega-proof]))

(defn- tactic-error! [msg data]
  (throw (ex-info (str "omega: " msg) (merge {:kind :tactic-error} data))))

(def ^:private eq-name (name/from-string "Eq"))

(defn- try-rfl
  "Try to close an Eq goal by reflexivity."
  [ps]
  (let [goal (proof/current-goal ps)]
    (when goal
      (let [st (tc/mk-tc-state (:env ps))
            st (assoc st :lctx (:lctx goal))
            goal-type (#'tc/cached-whnf st (:type goal))
            [head args] (e/get-app-fn-args goal-type)]
        (when (and (e/const? head)
                   (= (e/const-name head) eq-name)
                   (= 3 (count args)))
          (let [lhs (nth args 1)
                rhs (nth args 2)]
            (when (tc/is-def-eq st lhs rhs)
              ;; Sides are def-eq, build Eq.refl proof
              (let [eq-levels (e/const-levels head)
                    proof-term (e/app* (e/const' (name/from-string "Eq.refl")
                                                 eq-levels)
                                       (nth args 0) lhs)]
                (proof/assign-mvar ps (:id goal)
                                   {:kind :exact :term proof-term})))))))))

(defn- try-assumption
  "The goal matches a hypothesis directly. omega often normalises to a Prop that is
   exactly a carried fact (e.g. a refinement's `.property` after a Bool→Prop bridge);
   `decide` cannot certify a non-ground goal, but `assumption` closes it."
  [ps]
  (try
    (let [ps' (basic/assumption ps)]
      (when (proof/solved? ps') ps'))
    (catch Exception _ nil)))

(defn omega
  "Close the current goal using the omega decision procedure.

   Works for:
   - Nat/Int linear arithmetic goals (=, ≤, <, ≥, >, ≠)
   - With hypotheses providing additional constraints
   - Ground multiplication and division (e.g. 2*x and x/3, but not x*y)

   Everything past the `decide`/`rfl`/`assumption` fast paths is delegated to
   `ansatz.tactic.omega-proof/omega`, which produces a proof term the kernel checks.
   Its own failure message already distinguishes \"could not derive contradiction\"
   from \"found contradiction but cannot certify\" — that distinction now comes from
   the solver that actually knows, so it is reported verbatim."
  [ps]
  ;; First try decide directly — it's faster for ground cases
  (try
    (decide-tac/decide ps)
    (catch Exception _
      (or (try-rfl ps)
          (try-assumption ps)
          (let [goal (proof/current-goal ps)]
            (when-not goal (tactic-error! "No goals" {}))
            (omega-proof/omega ps))))))
