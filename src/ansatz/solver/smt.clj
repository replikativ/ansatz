;; Generic SMT solver service for tactic use.
;;
;; Wraps zustand (data-oriented SMT solver) with a clean protocol interface.
;; Any tactic (omega, simp, ring, decide) can use this to check satisfiability,
;; get models, or extract Farkas certificates.
;;
;; The solver has forkable persistent state — key for proof search branching.

(ns ansatz.solver.smt
  "Generic SMT solver service for use by any tactic.

   Provides a clean interface over zustand's data-oriented SMT solver.
   Supports: integer/real arithmetic, boolean logic, push/pop scopes,
   persistent snapshots, forking, Farkas certificates.

   Usage:
     (-> (make-solver)
         (declare-vars {:x :int :y :int})
         (assert-constraint [:>= :x 0])
         (assert-constraint [:<= [:+ :x :y] 10])
         (check))

   For proof search with branching:
     (let [base (-> (make-solver) (declare-vars ...) (assert-constraints ...))
           branch-a (fork base #(-> % (assert-constraint ...) (check)))
           branch-b (fork base #(-> % (assert-constraint ...) (check)))]
       ...)")

(defn- zsmt [sym]
  (or (requiring-resolve (symbol "zustand.smt" (name sym)))
      (throw (ex-info (str "zustand.smt/" sym " not available — add zustand to classpath")
                      {:sym sym}))))

;; ============================================================
;; Solver lifecycle
;; ============================================================

(defn make-solver
  "Create a new SMT solver instance."
  []
  ((zsmt :make-solver)))

(defn declare-var
  "Declare a typed variable. sort is :bool, :int, :real, or a vector like [:bv 32]."
  [solver name sort]
  ((zsmt :declare-const) solver name sort))

(defn declare-vars
  "Declare multiple variables. decls is a map of name->sort.
   (declare-vars solver {:x :int, :y :int, :z :bool})"
  [solver decls]
  ((zsmt :with-consts) solver decls))

;; ============================================================
;; Assertions
;; ============================================================

(defn assert-constraint
  "Assert a constraint expression. Returns solver for chaining.
   Expressions are nested vectors:
     [:and [:>= :x 0] [:<= :y 5]]
     [:or :a :b]
     [:eq :x :y]
     [:not [:eq :x :y]]
     42, true, false"
  [solver expr]
  ((zsmt :assert-expr) solver expr))

(defn assert-constraints
  "Assert multiple constraint expressions."
  [solver exprs]
  ((zsmt :assert-all) solver exprs))

;; ============================================================
;; Solving
;; ============================================================

(defn check
  "Check satisfiability. Returns a map:
   {:result :sat/:unsat/:unknown
    :model {name value ...}     ;; only on :sat
    :stats {:conflicts n ...}}"
  [solver]
  ((zsmt :solve) solver))

(defn sat?
  "Quick check: is the current constraint set satisfiable?"
  [solver]
  (= :sat (:result (check solver))))

(defn unsat?
  "Quick check: is the current constraint set unsatisfiable?"
  [solver]
  (= :unsat (:result (check solver))))

(defn get-model
  "After a :sat result, get the model (satisfying assignment).
   Returns {name value ...} or nil."
  [solver]
  (:model (check solver)))

;; ============================================================
;; Certificates (for proof construction)
;; ============================================================

(defn get-farkas-certificate
  "After an :unsat result, extract Farkas certificate from the arithmetic solver.
   Returns nil if no arithmetic conflict was involved.

   Each entry:
     {:constraint-id   int     ;; internal constraint index
      :farkas-coeff    ratio   ;; weight in infeasibility proof (> 0)
      :is-lower        bool    ;; lower (>=) or upper (<=) bound
      :orig-expr       Expr    ;; original comparison expression (Java Expr)
      :bound-val       ratio   ;; the bound value
      :bound-eps       int     ;; epsilon component (0 for non-strict)
      :sat-var         int}    ;; SAT variable controlling this bound

   The certificate proves: a non-negative linear combination of the
   bound constraints sums to a contradiction."
  [solver]
  ((zsmt :get-certificate) solver))

;; ============================================================
;; Scoping and forking (for proof search)
;; ============================================================

(defn push-scope
  "Push an assertion scope. Returns solver."
  ([solver] ((zsmt :push) solver))
  ([solver n] ((zsmt :push) solver n)))

(defn pop-scope
  "Pop an assertion scope. Returns solver."
  ([solver] ((zsmt :pop) solver))
  ([solver n] ((zsmt :pop) solver n)))

(defn seal
  "Seal the solver as an immutable snapshot. After this, mutations throw."
  [solver]
  ((zsmt :persistent!) solver))

(defn fork
  "Fork: seal state, create mutable copy, apply f, return result.
   Original remains unchanged. Cheap persistent copy.

   (fork solver #(-> % (assert-constraint [:>= :x 8]) (check)))"
  [solver f]
  ((zsmt :fork) solver f))

(defn editable?
  "Is this solver still mutable (not sealed)?"
  [solver]
  ((zsmt :editable?) solver))

;; ============================================================
;; Convenience: check with temporary constraints
;; ============================================================

(defn check-with
  "Check satisfiability with additional temporary constraints.
   Does not modify the original solver.

   (check-with solver [[:>= :x 5] [:<= :x 3]])
   => {:result :unsat ...}"
  [solver extra-constraints]
  (fork solver
        (fn [s]
          (let [s' (reduce assert-constraint s extra-constraints)]
            (check s')))))

(defn implies?
  "Check if the current constraints imply the given proposition.
   That is, check if (constraints ∧ ¬prop) is unsat.
   Returns true if the implication holds.

   (implies? solver [:>= :x 0])  ;; does the solver state imply x >= 0?"
  [solver prop]
  (= :unsat (:result (check-with solver [[:not prop]]))))
