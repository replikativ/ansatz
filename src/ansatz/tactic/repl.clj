;; Tactic layer — REPL convenience functions.

(ns ansatz.tactic.repl
  "REPL-friendly wrappers for interactive proof construction."
  (:require [clojure.string]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.search :as search]
            [ansatz.tactic.trace :as trace]
            [ansatz.tactic.decide :as decide-tac]
            [ansatz.tactic.omega :as omega-tac]
            [ansatz.tactic.omega-proof :as omega-proof-tac]
            [ansatz.tactic.ring :as ring-tac]
            [ansatz.tactic.simp :as simp-tac]
            [ansatz.surface.elaborate :as elab]))

(defn prove
  "Start a proof of the given type. Returns a proof state."
  [env goal-type]
  (first (proof/start-proof env goal-type)))

(defn- expr->string-with-names
  "Like e/->string but substitutes fvar ids with names from the local context."
  ([lctx e] (expr->string-with-names lctx e 0))
  ([lctx e depth]
   (if (> depth 20)
     "..."
     (let [d (inc depth)
           recurse (partial expr->string-with-names lctx)]
       (case (e/tag e)
         :bvar (str "#" (e/bvar-idx e))
         :sort (str "(Sort " (lvl/->string (e/sort-level e)) ")")
         :const (let [n (name/->string (e/const-name e))
                      ls (e/const-levels e)]
                  (if (seq ls)
                    (str n ".{" (clojure.string/join ", " (map lvl/->string ls)) "}")
                    n))
         :app (let [[head args] (e/get-app-fn-args e)]
                (str "(" (recurse head d) " "
                     (clojure.string/join " " (map #(recurse % d) args)) ")"))
         :lam (str "(fun : " (recurse (e/lam-type e) d) " => " (recurse (e/lam-body e) d) ")")
         :forall (str "(∀ : " (recurse (e/forall-type e) d) ", " (recurse (e/forall-body e) d) ")")
         :let (str "(let : " (recurse (e/let-type e) d) " := " (recurse (e/let-value e) d) " in " (recurse (e/let-body e) d) ")")
         :lit-nat (str (e/lit-nat-val e))
         :lit-str (pr-str (e/lit-str-val e))
         :mdata (recurse (e/mdata-expr e) d)
         :proj (str (name/->string (e/proj-type-name e)) "." (e/proj-idx e) "(" (recurse (e/proj-struct e) d) ")")
         :fvar (let [id (e/fvar-id e)
                     decl (get lctx id)]
                 (or (:name decl) (str "?fv" id))))))))

(defn show-goals
  "Pretty-print the open goals."
  [ps]
  (let [gs (proof/goals ps)]
    (if (empty? gs)
      (println "No goals.")
      (doseq [[i g] (map-indexed vector gs)]
        (println (str "Goal " (inc i) " of " (count gs) ":"))
        (let [lctx (:lctx g)]
          (doseq [[id decl] lctx]
            (when (= :local (:tag decl))
              (println (str "  " (or (:name decl) (str "?fv" id))
                            " : " (expr->string-with-names lctx (:type decl))))))
          (println (str "  ⊢ " (expr->string-with-names lctx (:type g)))))
        (println)))))

(defn intro
  "Apply intro tactic. Optionally provide a name."
  ([ps] (basic/intro ps))
  ([ps n] (basic/intro ps n)))

(defn intros
  "Introduce all leading forall binders."
  ([ps] (basic/intros ps))
  ([ps names] (basic/intros ps names)))

(defn exact
  "Close the goal with an exact term."
  [ps term]
  (basic/exact ps term))

(defn assumption
  "Close the goal using a hypothesis from the local context."
  [ps]
  (basic/assumption ps))

(defn apply-tac
  "Apply a term, generating subgoals for its arguments."
  [ps term]
  (basic/apply-tac ps term))

(defn rfl
  "Close an Eq goal by reflexivity."
  [ps]
  (basic/rfl ps))

(defn constructor
  "Apply the constructor of the goal's inductive type."
  [ps]
  (basic/constructor ps))

(defn rewrite
  "Rewrite the goal using an equality proof."
  ([ps eq-term] (basic/rewrite ps eq-term))
  ([ps eq-term reverse?] (basic/rewrite ps eq-term reverse?)))

(defn cases
  "Case analysis on an inductive hypothesis."
  [ps hyp-fvar-id]
  (basic/cases ps hyp-fvar-id))

(defn decide
  "Close a decidable proposition by kernel evaluation."
  [ps]
  (decide-tac/decide ps))

(defn omega
  "Close a goal using linear arithmetic (omega decision procedure)."
  [ps]
  (omega-tac/omega ps))

;; ============================================================
;; Interactive omega exploration
;; ============================================================

(defn omega-reify
  "Reify the current goal into an omega constraint problem.
   Returns a reified state that can be inspected, solved with different
   strategies, and then certified.

   Usage:
     (def r (omega-reify ps))
     (omega-show r)             ;; pretty-print constraints
     (def result (omega-solve-fm r))  ;; solve with FM
     (def ps2 (omega-certify r result))  ;; reconstruct proof
     (qed ps2)"
  [ps]
  (omega-proof-tac/reify-goal ps))

(defn omega-show
  "Pretty-print the reified omega problem: atoms, constraints, disjunctions."
  [reified]
  (omega-proof-tac/show-problem reified))

(defn omega-solve-fm
  "Run the Fourier-Motzkin solver on a reified problem."
  [reified]
  (omega-proof-tac/solve-fm reified))

(defn omega-certify
  "Reconstruct the proof term from a solver result and close the goal."
  [reified result]
  (omega-proof-tac/certify reified result))

(defn ring
  "Close a goal using polynomial ring normalization."
  [ps]
  (ring-tac/ring ps))

(defn simp
  "Simplify the goal using rewrite lemmas.
   Pass lemma names for 'simp only [...]' behavior."
  ([ps] (simp-tac/simp ps))
  ([ps lemma-names] (simp-tac/simp ps lemma-names)))

(defn dsimp
  "Definitional simplification (only beta/iota/projection reduction)."
  [ps]
  (simp-tac/dsimp ps))

(defn elab
  "Elaborate a surface s-expression in the context of the current goal.
   Local hypotheses are available as symbols.

   Example:
     (elab ps '(Eq.refl a))  ;; where 'a' is a hypothesis"
  [ps sexpr]
  (let [goal (proof/current-goal ps)]
    (when-not goal
      (throw (ex-info "No goals" {:kind :tactic-error})))
    (elab/elaborate-in-context (:env ps) (:lctx goal) sexpr)))

(defn exact-elab
  "Close the goal with an elaborated surface term.
   Combines elaborate-in-context + exact."
  [ps sexpr]
  (let [term (elab ps sexpr)]
    (basic/exact ps term)))

(defn apply-elab
  "Apply an elaborated surface term to the current goal.
   Combines elaborate-in-context + apply."
  [ps sexpr]
  (let [term (elab ps sexpr)]
    (basic/apply-tac ps term)))

(defn qed
  "Finish the proof: extract and verify the proof term."
  [ps]
  (let [term (extract/verify ps)]
    (println "Proof verified!")
    term))

;; ============================================================
;; Search wrappers
;; ============================================================

(defn auto
  "Try to automatically solve the proof. Returns solved ps or nil."
  ([ps] (auto ps 10))
  ([ps max-depth] (search/auto-solve ps max-depth)))

(defn suggest
  "Show applicable tactics for the current goal."
  [ps]
  (let [tactics (search/enumerate-tactics ps)]
    (if (empty? tactics)
      (println "No applicable tactics found.")
      (doseq [{:keys [name args weight]} tactics]
        (println (str "  " name
                      (when (seq args) (str " " (pr-str args)))
                      " (weight: " (format "%.2f" weight) ")"))))))

(defn fork
  "Fork the proof state: try multiple tactics, return successful branches."
  [ps tactics]
  (search/fork ps tactics))

(defn beam
  "Beam search over the proof. Returns solved ps or nil."
  ([ps] (beam ps 5 50))
  ([ps beam-width max-steps]
   (search/beam-search ps beam-width max-steps)))

(defn trace
  "Show the tactic trace summary."
  [ps]
  (let [s (search/trace-summary ps)]
    (println (str "Steps: " (:num-steps s)
                  " | Solved: " (:solved s)
                  " | Open goals: " (:open-goals s)
                  " | Weight: " (format "%.4f" (:weight s))))
    (doseq [t (:tactics s)]
      (println (str "  " t)))))

(defn export-trace
  "Export the proof trace to an NDJSON file."
  [ps path]
  (trace/write-trace-ndjson path ps)
  (println (str "Trace exported to " path)))

;; ============================================================
;; Definition macros
;; ============================================================

(defn theorem
  "Define and verify a theorem, adding it to the environment.
   tactic-fn is a function (fn [ps] → ps') that solves the proof.
   Returns the updated env.

   Example:
     (theorem env 'my_thm '(forall [a Nat] (Eq a a))
              (fn [ps] (-> ps (intro \"a\") rfl)))"
  [env thm-name type-sexpr tactic-fn]
  (let [type-expr (elab/elaborate env type-sexpr)
        ps (prove env type-expr)
        ps' (tactic-fn ps)
        term (extract/verify ps')
        cname (name/from-string (str thm-name))
        ci (ansatz.kernel.env/mk-thm cname [] type-expr term)]
    (ansatz.kernel.env/check-constant env ci)))

;; ============================================================
;; Interactive goal-state loop (the lean_goal / lean_multi_attempt analog)
;; ============================================================
;; Thin wrappers over the SAME machinery `a/theorem` uses (elab-signature → start-proof →
;; intros → run-tactic). `core/run-tactic` is reached via requiring-resolve so this REPL ns has
;; no static dependency on ansatz.core (cycle-safe). Nothing here mutates the global env.

(defn- core-fn [sym] (requiring-resolve (symbol "ansatz.core" (name sym))))

(defn setup-goal
  "Build the proof state for an `a/theorem`-style signature: elaborate `(params prop-form)` through
   the SAME elaborator a/theorem uses, start the proof, and intro the binders. Returns the `ps`
   positioned at the body goal. `env` defaults to the global env. Pure (no env mutation)."
  ([params prop-form] (setup-goal ((core-fn 'env)) params prop-form))
  ([env params prop-form]
   (let [pairs   ((core-fn 'parse-params) params)
         goal-ty (:type-ansatz ((core-fn 'elab-signature) env pairs prop-form))
         [ps _]  (proof/start-proof env goal-ty)]
     (if (seq pairs) (basic/intros ps (mapv (comp str first) pairs)) ps))))

(defn goal-at
  "Interactive goal inspection — the `lean_goal` analog. Set up `(params prop-form)`, run the first
   `n` surface tactic forms (default: all), print the resulting goal state, and RETURN the `ps` so
   you can keep stepping. Tactics are surface forms, e.g. `['(intro x) '(simp [List.map_map]) 'rfl]`.

     (goal-at '[xs :- (List Nat)] '(= ...) ['(induction xs)] 1)  ;; show state after `induction`"
  ([params prop-form tactics] (goal-at params prop-form tactics (count tactics)))
  ([params prop-form tactics n]
   (let [run (core-fn 'run-tactic)
         ps  (reduce run (setup-goal params prop-form) (take n tactics))]
     (show-goals ps)
     ps)))

(defn step
  "Apply ONE surface tactic to `ps`, print the resulting goals, return the new `ps`."
  [ps tac]
  (let [ps' ((core-fn 'run-tactic) ps tac)]
    (show-goals ps')
    ps'))

(defn attempt
  "Try each surface tactic form against `ps` INDEPENDENTLY — the `lean_multi_attempt` analog. Does
   not mutate `ps`. Returns a vector of {:tactic, :closed?, :remaining, :goals | :error}, so you can
   see which tactic closes the goal or makes progress.

     (attempt ps ['(simp [foo]) 'omega 'ring '(rfl)])"
  [ps tactics]
  (let [run (core-fn 'run-tactic)]
    (mapv (fn [t]
            (try
              (let [ps' (run ps t)]
                {:tactic t
                 :closed? (proof/solved? ps')
                 :remaining (count (proof/goals ps'))
                 :goals (proof/format-goals ps')})
              (catch Throwable e
                {:tactic t :error (.getMessage e)})))
          tactics)))

;; ============================================================
;; Term quotation — concrete surface syntax instead of e/app*/e/forall' construction
;; ============================================================
;; `(t <sexpr>)` elaborates a surface term to a kernel Expr in the global env; `(t-in ps <sexpr>)`
;; elaborates in the local context of ps's current goal (hypotheses available as symbols). The
;; fn forms (`t*`/`t-in*`) take an already-built/computed sexpr — what the law library uses to
;; replace hand-assembled `e/app*` trees with surface s-expressions.

(defn t*
  "Elaborate a surface s-expr to a kernel Expr. `env` defaults to the global env."
  ([sexpr] (t* ((core-fn 'env)) sexpr))
  ([env sexpr] (elab/elaborate env sexpr)))

(defn t-in*
  "Elaborate a surface s-expr in the local context of ps's current goal (hypothesis names are in
   scope as symbols). For building `exact`/`have` terms that mention the goal's fvars."
  [ps sexpr]
  (elab/elaborate-in-context (:env ps) (:lctx (first (proof/goals ps))) sexpr))

(defmacro t
  "Quote + elaborate a surface term to a kernel Expr in the global env — the concrete-syntax
   alternative to `(e/app* (e/const' …) …)`.   e.g.  (t (List.map f xs))"
  [sexpr] `(t* (quote ~sexpr)))

(defmacro t-in
  "Quote + elaborate a surface term in ps's current-goal context.   e.g.  (t-in ps (Eq a a))"
  [ps sexpr] `(t-in* ~ps (quote ~sexpr)))

(defn define
  "Define a term constant and add it to the environment.
   Returns the updated env.

   Example:
     (define env 'my_const 'Nat '(Nat.succ Nat.zero))"
  ([env def-name type-sexpr value-sexpr]
   (define env def-name type-sexpr value-sexpr {}))
  ([env def-name type-sexpr value-sexpr opts]
   (let [type-expr (elab/elaborate env type-sexpr)
         value-expr (elab/elaborate env value-sexpr type-expr)
         cname (name/from-string (str def-name))
         hints (get opts :hints :opaque)
         ci (ansatz.kernel.env/mk-def cname [] type-expr value-expr :hints hints)]
     (ansatz.kernel.env/check-constant env ci))))
