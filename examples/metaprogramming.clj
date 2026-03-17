(require '[ansatz.core :as a])
(a/init! "/var/tmp/ansatz-mathlib" "mathlib")

(println "\n╔═══════════════════════════════════════════════════════════╗")
(println "║  Metaprogramming — Extending Ansatz                      ║")
(println "╚═══════════════════════════════════════════════════════════╝\n")

;; ============================================================
;; 1. Custom Tactics (Lean 4's @[tactic])
;; ============================================================
;;
;; Ansatz tactics are functions (fn [ps args] → ps') where:
;;   ps   = proof state (immutable Clojure map)
;;   args = vector of s-expression arguments
;;
;; You have full access to the CIC kernel:
;;   - ansatz.kernel.tc/infer-type, cached-whnf, is-def-eq
;;   - ansatz.tactic.proof/current-goal, assign-mvar, fresh-mvar
;;   - ansatz.kernel.env/lookup (search 648K+ Mathlib declarations)
;;
;; This is the Clojure equivalent of Lean 4's TacticM monad.

(println "━━━ 1. Custom Tactic ━━━\n")

(require '[ansatz.kernel.expr :as e])
(require '[ansatz.kernel.name :as nm])
(require '[ansatz.kernel.tc :as tc])
(require '[ansatz.tactic.proof :as proof])
(require '[ansatz.tactic.basic :as basic])

;; Example: a tactic that tries `rfl`, then `assumption`, then `omega`
(a/register-tactic! 'auto
  (fn [ps _args]
    (or (try (basic/rfl ps) (catch Exception _ nil))
        (try (basic/assumption ps) (catch Exception _ nil))
        (try ((requiring-resolve 'ansatz.tactic.omega/omega) ps) (catch Exception _ nil))
        (throw (ex-info "auto: no strategy worked" {})))))

;; Use it in a proof:
(a/theorem auto-demo-1 []
  (= Nat (+ 1 1) 2)
  (auto))  ;; solved by rfl

(a/theorem auto-demo-2 [n :- Nat]
  (<= Nat 0 n)
  (auto))  ;; solved by omega (via Nat.zero_le)

(println "  auto tactic registered and working!\n")

;; Example: a tactic that applies a specific lemma pattern
;; (like Mathlib's @[positivity] extensions)
(a/register-tactic! 'by-zero-le
  (fn [ps _args]
    (let [goal (proof/current-goal ps)
          st (tc/mk-tc-state (a/env))
          ;; Try to apply Nat.zero_le to the goal
          term (e/const' (nm/from-string "Nat.zero_le") [])]
      (basic/apply-tac ps term))))

(a/theorem by-zero-le-demo [n :- Nat]
  (<= Nat 0 (+ n 1))
  (by-zero-le))

(println "  by-zero-le tactic registered and working!\n")

;; ============================================================
;; 2. Custom Elaboration Forms (Lean 4's elab_rules)
;; ============================================================
;;
;; Elaboration hooks let you define new syntax forms that produce
;; kernel expressions (Expr). Your function receives:
;;   env   = kernel environment
;;   scope = bvar scope (for function params)
;;   depth = current de Bruijn depth
;;   args  = vector of sub-expressions (as s-expressions)
;;   lctx  = local context (for match field fvars)
;;
;; This is the Clojure equivalent of Lean 4's TermElabM.

(println "━━━ 2. Custom Elaboration Form ━━━\n")

;; Example: (double x) elaborates to (+ x x)
(a/register-elaborator! 'double
  (fn [env scope depth args lctx]
    (let [x (#'ansatz.core/sexp->ansatz env scope depth (first args) lctx)]
      ;; Build: HAdd.hAdd Nat Nat Nat inst x x
      (let [nat (e/const' (nm/from-string "Nat") [])
            lz ansatz.kernel.level/zero
            hadd (e/const' (nm/from-string "HAdd.hAdd") [lz lz lz])
            inst (e/app* (e/const' (nm/from-string "instHAdd") [lz])
                          nat (e/const' (nm/from-string "instAddNat") []))]
        (e/app* hadd nat nat nat inst x x)))))

(a/defn test-double [n :- Nat] Nat (double n))
(println "  (test-double 21) =" ((test-double 21)))

(a/theorem double-is-add [n :- Nat]
  (= Nat (double n) (+ n n))
  (rfl))

(println "  double elaborator registered — (double n) = n + n, proved by rfl!\n")

;; ============================================================
;; 3. Custom Simprocs (Lean 4's @[simproc])
;; ============================================================
;;
;; Simprocs are called during `simp` to simplify subexpressions.
;; Your function receives (st expr) and returns either:
;;   {:expr simplified :proof eq-proof}  — simplified with proof
;;   nil                                  — can't simplify
;;
;; This is the Clojure equivalent of Lean 4's Simproc type.
;; Simprocs registered via register-simproc! are always active.

(println "━━━ 3. Custom Simproc (info only) ━━━\n")

;; Example pattern (not executable without Mathlib domain):
;; (a/register-simproc! 'matrix/eval
;;   (fn [st expr]
;;     (when (is-matrix-literal? expr)
;;       (let [result (evaluate-matrix expr)
;;             proof  (build-matrix-eq-proof expr result)]
;;         {:expr result :proof proof}))))

(println "  Simproc registration API available via (a/register-simproc! name fn)")
(println "  Functions receive (st expr), return {:expr :proof} or nil")
(println "  Registered simprocs are automatically called during simp\n")

;; ============================================================
;; Summary
;; ============================================================
(println "━━━ Summary ━━━")
(println "  Extension Points:")
(println "    (a/register-tactic! name fn)     — custom proof tactics")
(println "    (a/register-elaborator! name fn) — custom term forms")
(println "    (a/register-simproc! name fn)    — custom simp procedures")
(println "  All extensions have full access to the CIC kernel:")
(println "    tc/infer-type, tc/cached-whnf, tc/is-def-eq")
(println "    proof/current-goal, proof/assign-mvar")
(println "    env/lookup (648K+ Mathlib declarations)")
(println "  Same capabilities as Lean 4's TacticM/TermElabM/Simproc")
