;; Tactic layer — decide tactic, Ansatz→SMT-LIB translation, and smt tactic.

(ns ansatz.tactic.decide
  "The `decide` tactic closes goals of decidable propositions by:
   1. Resolving a Decidable instance for the goal type
   2. Constructing `@of_decide_eq_true P inst (Eq.refl Bool.true)`
   3. The kernel verifies this by evaluating `decide P inst` to `true`

   The `smt` tactic extends this with:
   1. Translating Ansatz propositions to SMT-LIB
   2. Calling an SMT solver (mock or real Z3)
   3. Using `decide` to verify the result in the kernel

   3. Using `decide` to verify the result in the kernel"
  (:require [clojure.string]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.instance :as instance])
            ;; zustand.smt is optional — loaded lazily for SMT-backed decide
  (:import [ansatz.kernel TypeChecker]))

;; ============================================================
;; Well-known names
;; ============================================================

(def ^:private of-decide-eq-true-name (name/from-string "of_decide_eq_true"))
(def ^:private eq-refl-name (name/from-string "Eq.refl"))
(def ^:private bool-name (name/from-string "Bool"))
(def ^:private bool-true-name (name/from-string "Bool.true"))
(def ^:private decidable-decide-name (name/from-string "Decidable.decide"))
(def ^:private decidable-name (name/from-string "Decidable"))

;; ============================================================
;; decide tactic
;; ============================================================

(defn- build-decide-proof
  "Build the proof term `@of_decide_eq_true P inst (Eq.refl Bool.true)`.
   Returns the Ansatz expression."
  [env prop inst]
  (let [u1 (lvl/succ lvl/zero)
        bool-type (e/const' bool-name [])
        bool-true (e/const' bool-true-name [])
        eq-refl-proof (e/app* (e/const' eq-refl-name [u1]) bool-type bool-true)]
    (e/app* (e/const' of-decide-eq-true-name []) prop inst eq-refl-proof)))

(defn- verify-decide
  "Verify that decide P inst reduces to Bool.true.
   Returns true if it does, false otherwise."
  [env prop inst]
  (let [st (tc/mk-tc-state env)
        decide-term (e/app* (e/const' decidable-decide-name []) prop inst)
        result (#'tc/cached-whnf st decide-term)
        bool-true (e/const' bool-true-name [])]
    (= result bool-true)))

(defn- get-instance-index
  "Get or build the instance index, caching it in the proof state."
  [ps]
  (if-let [idx (:instance-index ps)]
    [ps idx]
    (let [idx (instance/build-instance-index (:env ps))]
      [(assoc ps :instance-index idx) idx])))

(defn decide
  "Close the current goal by constructing a decision proof.

   1. Resolve a Decidable instance for the goal type
   2. Verify that `decide P inst` evaluates to `true`
   3. Assign the goal with the proof term

   Returns updated proof state."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal
            (throw (ex-info "Tactic error: No goals" {:kind :tactic-error})))
        [ps idx] (get-instance-index ps)
        env (:env ps)
        prop (:type goal)
        decidable-goal (e/app (e/const' decidable-name []) prop)
        inst (instance/synthesize env idx decidable-goal)]
    ;; Verify the decision evaluates to true
    (when-not (verify-decide env prop inst)
      (throw (ex-info "Tactic error: decide failed — proposition is false or undecidable at this point"
                      {:kind :tactic-error :prop prop})))
    (let [proof-term (build-decide-proof env prop inst)]
      ;; Double-check: type-check the proof
      (let [tc (TypeChecker. env)
            inferred (.inferType tc proof-term)]
        (when-not (.isDefEq tc inferred prop)
          (throw (ex-info "Tactic error: decide proof does not type-check"
                          {:kind :tactic-error :expected prop :inferred inferred}))))
      (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof-term})
          (proof/record-tactic :decide [] (:id goal))))))

;; ============================================================
;; Ansatz → SMT-LIB translation
;; ============================================================

(declare prop->smt* term->smt*)

(defn- smt-error! [msg data]
  (throw (ex-info (str "SMT translation: " msg) (merge {:kind :smt-error} data))))

(defn prop->smt
  "Translate a Ansatz proposition to SMT-LIB s-expression (as Clojure data).

   Supported fragment:
   - Eq Nat a b        → (= a b)
   - And p q           → (and p q)
   - Or p q            → (or p q)
   - Not p             → (not p)
   - True              → true
   - False             → false
   - LE.le Nat _ a b   → (<= a b)
   - LT.lt Nat _ a b   → (< a b)
   - Nat literals       → integer constants
   - Nat.succ           → (+ 1 ...)
   - Nat.add/HAdd.hAdd  → (+ ...)

   Returns: {:smt <sexp> :vars {name type} :assertions [<sexp>]}
   where :vars tracks free variables (bvars mapped to names)."
  [env prop & {:keys [var-names] :or {var-names {}}}]
  (let [st (tc/mk-tc-state env)]
    (prop->smt* st prop var-names)))

(defn try-match-prop
  "Try matching head constant on raw expr, then on WHNF.
   Returns [head-name levels args-vec] or nil."
  [st expr]
  (let [[head args] (e/get-app-fn-args expr)]
    (if (e/const? head)
      [(e/const-name head) (e/const-levels head) (vec args)]
      ;; Try WHNF
      (let [w (#'tc/cached-whnf st expr)
            [whead wargs] (e/get-app-fn-args w)]
        (when (e/const? whead)
          [(e/const-name whead) (e/const-levels whead) (vec wargs)])))))

(defn- prop->smt*
  [st prop var-names]
  (let [matched (try-match-prop st prop)]
    (if-not matched
      (smt-error! "unsupported proposition" {:prop prop})
      (let [[head-name levels args] matched]
        (cond
          (= head-name (name/from-string "True")) 'true
          (= head-name (name/from-string "False")) 'false

          (and (= head-name (name/from-string "Eq")) (= 3 (count args)))
          (list '= (term->smt* st (nth args 1) var-names)
                (term->smt* st (nth args 2) var-names))

          (and (= head-name (name/from-string "And")) (= 2 (count args)))
          (list 'and (prop->smt* st (nth args 0) var-names)
                (prop->smt* st (nth args 1) var-names))

          (and (= head-name (name/from-string "Or")) (= 2 (count args)))
          (list 'or (prop->smt* st (nth args 0) var-names)
                (prop->smt* st (nth args 1) var-names))

          (and (= head-name (name/from-string "Not")) (= 1 (count args)))
          (list 'not (prop->smt* st (nth args 0) var-names))

          (and (= head-name (name/from-string "LE.le")) (= 4 (count args)))
          (list '<= (term->smt* st (nth args 2) var-names)
                (term->smt* st (nth args 3) var-names))

          (and (= head-name (name/from-string "LT.lt")) (= 4 (count args)))
          (list '< (term->smt* st (nth args 2) var-names)
                (term->smt* st (nth args 3) var-names))

          :else
          (smt-error! "unsupported proposition" {:prop prop :head head-name}))))))

(defn- term->smt*
  "Translate a Ansatz term (Nat arithmetic) to SMT-LIB."
  [st term var-names]
  (let [term-whnf (#'tc/cached-whnf st term)]
    (cond
      ;; Nat literal
      (e/lit-nat? term-whnf)
      (e/lit-nat-val term-whnf)

      ;; Free variable (from binder context)
      (e/fvar? term-whnf)
      (let [id (e/fvar-id term-whnf)]
        (or (get var-names id)
            (symbol (str "x" id))))

      ;; Bound variable (shouldn't appear in WHNF but handle gracefully)
      (e/bvar? term-whnf)
      (symbol (str "bv" (e/bvar-idx term-whnf)))

      ;; Application — check for known functions
      (e/app? term-whnf)
      (let [[head args] (e/get-app-fn-args term-whnf)]
        (if (e/const? head)
          (let [cn (e/const-name head)]
            (cond
              ;; Nat.succ n → (+ n 1)
              (and (= cn (name/from-string "Nat.succ")) (= 1 (count args)))
              (list '+ (term->smt* st (nth args 0) var-names) 1)

              ;; HAdd.hAdd.{u,v,w} T T T inst a b → (+ a b)
              (and (= cn (name/from-string "HAdd.hAdd")) (= 6 (count args)))
              (list '+ (term->smt* st (nth args 4) var-names)
                    (term->smt* st (nth args 5) var-names))

              ;; Nat.add a b → (+ a b)
              (and (= cn (name/from-string "Nat.add")) (= 2 (count args)))
              (list '+ (term->smt* st (nth args 0) var-names)
                    (term->smt* st (nth args 1) var-names))

              ;; HSub.hSub.{u,v,w} T T T inst a b → (- a b)
              (and (= cn (name/from-string "HSub.hSub")) (= 6 (count args)))
              (list '- (term->smt* st (nth args 4) var-names)
                    (term->smt* st (nth args 5) var-names))

              ;; HMul.hMul.{u,v,w} T T T inst a b → (* a b)
              (and (= cn (name/from-string "HMul.hMul")) (= 6 (count args)))
              (list '* (term->smt* st (nth args 4) var-names)
                    (term->smt* st (nth args 5) var-names))

              ;; Zero and one constants
              (= cn (name/from-string "OfNat.ofNat"))
              ;; OfNat.ofNat.{u} T n inst → n
              (if (>= (count args) 2)
                (term->smt* st (nth args 1) var-names)
                (smt-error! "unsupported OfNat" {:term term}))

              :else
              (smt-error! "unsupported term head" {:name cn :term term})))
          (smt-error! "unsupported non-const application" {:term term})))

      ;; Constant (e.g. Nat.zero which is a ctor)
      (e/const? term-whnf)
      (let [cn (e/const-name term-whnf)]
        (cond
          (= cn (name/from-string "Nat.zero")) 0
          :else (smt-error! "unsupported constant" {:name cn})))

      :else
      (smt-error! "unsupported term" {:term term-whnf}))))

(defn smt-lib-string
  "Render an SMT-LIB s-expression as a string."
  [sexp]
  (cond
    (list? sexp)
    (str "(" (clojure.string/join " " (map smt-lib-string sexp)) ")")

    (symbol? sexp) (str sexp)
    (number? sexp) (str sexp)
    (string? sexp) (pr-str sexp)
    :else (str sexp)))

;; ============================================================
;; Mock Z3
;; ============================================================

(declare eval-smt)

(defn mock-z3
  "Mock Z3 solver. Evaluates simple SMT-LIB assertions.
   Returns :sat, :unsat, or :unknown.

   This is a placeholder for the real Z3 integration.
   Currently handles ground arithmetic on natural numbers."
  [assertion]
  (try
    (let [result (eval-smt assertion)]
      (if result :sat :unsat))
    (catch Exception _
      :unknown)))

(defn- eval-smt
  "Evaluate a ground SMT assertion (no free variables).
   Returns true/false."
  [sexp]
  (cond
    (= sexp 'true) true
    (= sexp 'false) false
    (number? sexp) sexp

    (list? sexp)
    (let [[op & args] sexp]
      (case op
        = (apply = (map eval-smt args))
        not (not (eval-smt (first args)))
        and (every? eval-smt args)
        or (some eval-smt args)
        <= (apply <= (map eval-smt args))
        < (apply < (map eval-smt args))
        >= (apply >= (map eval-smt args))
        > (apply > (map eval-smt args))
        + (apply + (map eval-smt args))
        - (apply - (map eval-smt args))
        * (apply * (map eval-smt args))
        (throw (ex-info "eval-smt: unknown operator" {:op op}))))

    :else (throw (ex-info "eval-smt: cannot evaluate" {:sexp sexp}))))

;; ============================================================
;; zustand SMT solver integration
;; ============================================================

(defn sexp->zustand
  "Convert an SMT-LIB s-expression (as produced by prop->smt) to zustand's
   data vector format.

   - (= a b)   → [:eq a' b']
   - (and p q)  → [:and p' q']
   - (or p q)   → [:or p' q']
   - (not p)    → [:not p']
   - (<= a b)   → [:<= a' b']
   - (< a b)    → [:< a' b']
   - (>= a b)   → [:>= a' b']
   - (> a b)    → [:> a' b']
   - (+ a b)    → [:+ a' b']
   - (- a b)    → [:- a' b']
   - (* a b)    → [:* a' b']
   - Symbols become keywords, numbers stay as numbers,
     true/false stay as booleans."
  [sexp]
  (cond
    (list? sexp)
    (let [[op & args] sexp
          ;; Map SMT-LIB operators to zustand operators
          op-kw (case (str op)
                  "="   :eq
                  "and" :and
                  "or"  :or
                  "not" :not
                  "<="  :<=
                  "<"   :<
                  ">="  :>=
                  ">"   :>
                  "+"   :+
                  "-"   :-
                  "*"   :*
                  (keyword (str op)))]
      (into [op-kw] (map sexp->zustand args)))

    (symbol? sexp)
    (let [s (str sexp)]
      (case s
        "true"  true
        "false" false
        (keyword s)))

    (number? sexp) sexp
    (true? sexp)   true
    (false? sexp)  false

    :else (throw (ex-info "sexp->zustand: unsupported value" {:value sexp}))))

(defn- collect-vars
  "Collect all keyword variables from a zustand expression.
   Returns a set of keywords."
  [expr]
  (cond
    (keyword? expr) #{expr}
    (vector? expr)  (reduce into #{} (map collect-vars (rest expr)))
    :else           #{}))

(defn zustand-check
  "Check validity of a Ansatz proposition using the zustand SMT solver.

   1. Translates prop to SMT s-expression via prop->smt
   2. Converts to zustand format via sexp->zustand
   3. Asserts the negation (to check validity: if ¬P is UNSAT then P is valid)
   4. Returns {:result :valid/:invalid/:unknown, :model ... (on :invalid)}

   The solver checks ¬P:
   - UNSAT  → P is valid in all models  → :valid
   - SAT    → P has a counterexample    → :invalid (with model)
   - else   → :unknown"
  [env prop]
  (try
    (let [smt-sexp (prop->smt env prop)
          zustand-expr (sexp->zustand smt-sexp)
          vars (collect-vars zustand-expr)
          make-solver (requiring-resolve 'ansatz.solver.smt/make-solver)
          declare-const (requiring-resolve 'ansatz.solver.smt/declare-const)
          assert-expr (requiring-resolve 'ansatz.solver.smt/assert-expr)
          solve (requiring-resolve 'ansatz.solver.smt/solve)
          solver (reduce (fn [s v] (declare-const s v :int))
                         (make-solver)
                         vars)
          solver (assert-expr solver [:not zustand-expr])
          result (solve solver)]
      (case (:result result)
        :unsat  {:result :valid}
        :sat    {:result :invalid :model (:model result)}
        {:result :unknown}))
    (catch Exception e
      {:result :error :message (.getMessage e)})))

;; ============================================================
;; smt tactic
;; ============================================================

(defn smt
  "Close the current goal using SMT solving + decide.

   Strategy:
   1. Try `decide` directly (fastest path for ground decidable props)
   2. If that fails, try zustand SMT solver as a pre-check
   3. If zustand is unavailable, fall back to mock-z3
   4. If the solver says valid (UNSAT on negation), retry `decide`
   5. If the solver says invalid (SAT on negation), report countermodel

   The SMT step is a *proposal* — the kernel always verifies via `decide`."
  ([ps] (smt ps mock-z3))
  ([ps fallback-solver]
   ;; Fast path: try decide directly
   (try
     (decide ps)
     (catch Exception decide-err
       ;; decide failed — try the SMT path
       (let [goal (proof/current-goal ps)
             env (:env ps)
             prop (:type goal)]
         (try
           ;; Try zustand first
           (let [zresult (zustand-check env prop)]
             (case (:result zresult)
               :valid
               ;; zustand says valid — decide should work but didn't.
               ;; Re-throw the original decide error (the prop is valid but
               ;; perhaps not in the decidable fragment the kernel can evaluate).
               (throw (ex-info "SMT: proposition is valid but decide cannot verify it in the kernel"
                               {:kind :tactic-error :smt-result zresult :decide-error decide-err}))

               :invalid
               (throw (ex-info (str "SMT: proposition has a counterexample: " (:model zresult))
                               {:kind :tactic-error :model (:model zresult)}))

               :unknown
               (throw (ex-info "SMT: zustand solver returned unknown"
                               {:kind :tactic-error}))

               ;; :error — zustand unavailable, fall back to mock-z3
               (try
                 (let [smt-expr (prop->smt env prop)
                       result (fallback-solver smt-expr)]
                   (case result
                     :sat (throw (ex-info "SMT: proposition is satisfiable (not a tautology)"
                                          {:kind :tactic-error :smt smt-expr}))
                     :unsat (throw (ex-info "SMT: proposition is unsatisfiable"
                                            {:kind :tactic-error :smt smt-expr}))
                     :unknown (throw (ex-info "SMT: solver returned unknown"
                                              {:kind :tactic-error :smt smt-expr}))))
                 (catch clojure.lang.ExceptionInfo e2
                   (if (= :smt-error (:kind (ex-data e2)))
                     (throw (ex-info (str "Tactic error: decide failed and SMT translation failed: "
                                          (.getMessage e2))
                                     {:kind :tactic-error :cause e2}))
                     (throw e2))))))
           (catch clojure.lang.ExceptionInfo e2
             (if (= :smt-error (:kind (ex-data e2)))
               ;; SMT translation itself failed — fall back to mock-z3
               (try
                 (let [smt-expr (prop->smt env prop)
                       result (fallback-solver smt-expr)]
                   (case result
                     :sat (throw (ex-info "SMT: proposition is satisfiable (not a tautology)"
                                          {:kind :tactic-error :smt smt-expr}))
                     :unsat (throw (ex-info "SMT: proposition is unsatisfiable"
                                            {:kind :tactic-error :smt smt-expr}))
                     :unknown (throw (ex-info "SMT: solver returned unknown"
                                              {:kind :tactic-error :smt smt-expr}))))
                 (catch clojure.lang.ExceptionInfo e3
                   (if (= :smt-error (:kind (ex-data e3)))
                     (throw (ex-info (str "Tactic error: decide failed and SMT translation failed: "
                                          (.getMessage e3))
                                     {:kind :tactic-error :cause e3}))
                     (throw e3))))
               (throw e2)))))))))
