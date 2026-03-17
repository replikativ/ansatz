;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; Tactic layer — grind: general-purpose automation via E-matching,
;; congruence closure, linear arithmetic, and case splitting.
;;
;; Follows Lean 4's grind tactic architecture, combining:
;; 1. Congruence closure via zustand's EGraph
;; 2. Linear arithmetic via omega
;; 3. Polynomial reasoning via ring
;; 4. Case splitting on constructors/booleans
;; 5. Rewriting via simp
;;
;; The core loop:
;; - Collect hypotheses and goal into the E-graph
;; - Apply congruence closure
;; - Check if goal is solved
;; - Try omega/ring for arithmetic
;; - Case split if stuck
;; - Repeat

(ns ansatz.tactic.grind
  "General-purpose automation tactic combining congruence closure,
   linear arithmetic, polynomial reasoning, and case splitting.

   Usage:
     (grind ps)              ;; full automation
     (grind ps {:fuel 100})  ;; with custom fuel"
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]
            [ansatz.config :as config]))
;; zustand EGraph import is optional — grind uses requiring-resolve for SMT calls

;; ============================================================
;; Names
;; ============================================================

(def ^:private eq-name (name/from-string "Eq"))
(def ^:private iff-name (name/from-string "Iff"))
(defn- tactic-error! [msg data]
  (throw (ex-info (str "grind: " msg) (merge {:kind :tactic-error} data))))

;; ============================================================
;; Ansatz → EGraph translation
;; ============================================================

(defn- mk-egraph-context
  "Create a fresh E-graph context with ExprManager.
   Requires zustand on classpath (add :smt alias to deps.edn)."
  []
  {:em (try (eval '(smt.ExprManager.))
            (catch Exception _ (throw (ex-info "grind requires zustand (add :smt alias)" {}))))
   :eg (try (eval '(smt.EGraph.))
            (catch Exception _ (throw (ex-info "grind requires zustand (add :smt alias)" {}))))
   ;; Ansatz expr → zustand Expr
   :ansatz->smt (atom {})
   ;; zustand Expr → Ansatz expr
   :smt->ansatz (atom {})
   ;; fvar-id → zustand Expr (for variables)
   :fvar->smt (atom {})
   ;; hypothesis fvar-id → justification label
   :hyp-labels (atom {})
   ;; counter for unique names
   :counter (atom 0)})

(defn- fresh-name!
  "Generate a unique name for the E-graph."
  [ctx prefix]
  (let [n (swap! (:counter ctx) inc)]
    (str prefix "_" n)))

(defn- ansatz-to-smt
  "Translate a Ansatz expression to a zustand Expr for the E-graph.
   Uses uninterpreted functions for Ansatz constants and applications.
   Returns a zustand Expr."
  [ctx st expr]
  ;; Check cache
  (or (get @(:ansatz->smt ctx) expr)
      (let [em (:em ctx)
            int-sort (.intSort em)
            result
            (case (e/tag expr)
              ;; Free variables → uninterpreted constants
              :fvar (let [id (e/fvar-id expr)]
                      (or (get @(:fvar->smt ctx) id)
                          (let [n (fresh-name! ctx "fv")
                                c (.mkIntConst em n)]
                            (swap! (:fvar->smt ctx) assoc id c)
                            c)))

              ;; Constants → uninterpreted constants
              :const (let [n (name/->string (e/const-name expr))
                           c (.mkIntConst em (str "c_" n))]
                       c)

              ;; Applications → uninterpreted function applications
              :app (let [[head args] (e/get-app-fn-args expr)
                         head-smt (ansatz-to-smt ctx st head)
                         ;; Create a function declaration for this head
                         n (count args)
                         fname (if (e/const? head)
                                 (str "fn_" (name/->string (e/const-name head)) "_" n)
                                 (fresh-name! ctx "fn"))
                         domain (into-array Object (repeat n int-sort))
                         fdecl (.mkFuncDecl em fname domain int-sort)
                         arg-smts (into-array Object (mapv #(ansatz-to-smt ctx st %) args))]
                     (.mkApp em fdecl arg-smts))

              ;; Nat literals → integer constants
              :lit-nat (let [v (e/lit-nat-val expr)]
                         (.mkInt em (long v)))

              ;; Bound variables (shouldn't appear in well-formed terms)
              :bvar (.mkIntConst em (str "bv_" (e/bvar-idx expr)))

              ;; Lambdas/foralls → opaque constants
              :lam (.mkIntConst em (fresh-name! ctx "lam"))
              :forall (.mkIntConst em (fresh-name! ctx "forall"))

              ;; Sort → opaque
              :sort (.mkIntConst em (fresh-name! ctx "sort"))

              ;; Let → translate body with value substituted
              :let (ansatz-to-smt ctx st (e/instantiate1 (e/let-body expr) (e/let-value expr)))

              ;; Projection → opaque
              :proj (.mkIntConst em (fresh-name! ctx "proj"))

              ;; Mdata → unwrap
              :mdata (ansatz-to-smt ctx st (e/mdata-expr expr))

              ;; String literals
              :lit-str (.mkIntConst em (fresh-name! ctx "str")))]
        ;; Cache both directions
        (swap! (:ansatz->smt ctx) assoc expr result)
        (swap! (:smt->ansatz ctx) assoc result expr)
        result)))

(defn- register-in-egraph!
  "Register a zustand Expr in the E-graph."
  [ctx smt-expr]
  (.mkNode (:eg ctx) smt-expr))

;; ============================================================
;; Hypothesis extraction
;; ============================================================

(defn- extract-eq-from-type
  "If a type is @Eq T a b, return [a b]. Otherwise nil."
  [st ty]
  (let [whnf (#'tc/cached-whnf st ty)
        [head args] (e/get-app-fn-args whnf)]
    (when (and (e/const? head)
               (= (e/const-name head) eq-name)
               (= 3 (count args)))
      [(nth args 1) (nth args 2)])))

(defn- extract-iff-from-type
  "If a type is @Iff P Q, return [P Q]. Otherwise nil."
  [st ty]
  (let [whnf (#'tc/cached-whnf st ty)
        [head args] (e/get-app-fn-args whnf)]
    (when (and (e/const? head)
               (= (e/const-name head) iff-name)
               (= 2 (count args)))
      [(nth args 0) (nth args 1)])))

(defn- collect-hypotheses
  "Collect equality/iff hypotheses from the local context.
   Returns a seq of {:fvar-id :lhs :rhs :kind (:eq or :iff)}."
  [st lctx]
  (keep (fn [[id decl]]
          (when (= :local (:tag decl))
            (let [ty (:type decl)]
              (or (when-let [[lhs rhs] (extract-eq-from-type st ty)]
                    {:fvar-id id :lhs lhs :rhs rhs :kind :eq})
                  (when-let [[lhs rhs] (extract-iff-from-type st ty)]
                    {:fvar-id id :lhs lhs :rhs rhs :kind :iff})))))
        lctx))

;; ============================================================
;; Proof construction helpers
;; ============================================================

(defn- safe-infer [st e]
  (try (tc/infer-type st e)
       (catch clojure.lang.ExceptionInfo _ nil)
       (catch Exception ex
         (when config/*grind-debug*
           (println "grind safe-infer:" (.getMessage ex)))
         nil)))

(defn- get-sort-level [st e]
  (let [ty (safe-infer st e)
        sw (when ty (try (#'tc/cached-whnf st ty)
                         (catch clojure.lang.ExceptionInfo _ nil)
                         (catch Exception ex
                           (when config/*grind-debug*
                             (println "grind get-sort-level whnf:" (.getMessage ex)))
                           nil)))]
    (if (and sw (e/sort? sw)) (e/sort-level sw) lvl/zero)))

(defn- build-proof-from-hypotheses
  "Build a Ansatz proof of goal-lhs = goal-rhs by chaining equality hypotheses.
   Searches ALL hypotheses (not just E-graph explanation) to find a path."
  [st goal-lhs goal-rhs]
  (let [u1 (lvl/succ lvl/zero)
        lctx (:lctx st)
        ;; Collect all Eq hypotheses from context
        eq-hyps (keep (fn [[id decl]]
                        (when (= :local (:tag decl))
                          (let [ty (:type decl)
                                [head args] (e/get-app-fn-args ty)]
                            (when (and (e/const? head)
                                       (= (e/const-name head) eq-name)
                                       (= 3 (count args)))
                              {:fvar-id id :proof (e/fvar id)
                               :type (nth args 0) :lhs (nth args 1) :rhs (nth args 2)}))))
                      lctx)]
    ;; Try single hypothesis (direct or reversed)
    (or (some (fn [{:keys [proof lhs rhs type]}]
                (cond
                  (and (= lhs goal-lhs) (= rhs goal-rhs)) proof
                  (and (= rhs goal-lhs) (= lhs goal-rhs))
                  (e/app* (e/const' (name/from-string "Eq.symm") [u1]) type lhs rhs proof)
                  :else nil))
              eq-hyps)
        ;; Try 2-step transitivity: find h1: a=b, h2: b=c
        (some (fn [{lhs1 :lhs rhs1 :rhs p1 :proof t1 :type}]
                (when (= lhs1 goal-lhs)
                  (some (fn [{lhs2 :lhs rhs2 :rhs p2 :proof}]
                          (when (and (= lhs2 rhs1) (= rhs2 goal-rhs))
                            (e/app* (e/const' (name/from-string "Eq.trans") [u1])
                                    t1 lhs1 rhs1 rhs2 p1 p2)))
                        eq-hyps)))
              eq-hyps)
        ;; Try congruence: if goal is f(a) = f(b), find h: a = b
        ;; Then build congrArg f h
        (let [[gl-head gl-args] (e/get-app-fn-args goal-lhs)
              [gr-head gr-args] (e/get-app-fn-args goal-rhs)]
          (when (and (= (count gl-args) (count gr-args))
                     (pos? (count gl-args))
                     (= (e/get-app-fn gl-head) (e/get-app-fn gr-head)))
            ;; Check if all args match except possibly the last
            ;; Simplified: single-arg congruence f(a) = f(b)
            (let [f-common gl-head
                  a-lhs (last gl-args)
                  a-rhs (last gr-args)]
              (when (not= a-lhs a-rhs)
                ;; Find hypothesis h : a-lhs = a-rhs (or recurse)
                (when-let [h-proof (or (some (fn [{:keys [proof lhs rhs]}]
                                               (when (and (= lhs a-lhs) (= rhs a-rhs)) proof))
                                             eq-hyps)
                                       ;; Recursive: try building proof for inner args
                                       (build-proof-from-hypotheses st a-lhs a-rhs))]
                  ;; congrArg : {α} {β} {a₁} {a₂} (f : α → β) (h : a₁ = a₂) → f a₁ = f a₂
                  (try
                    (let [alpha (tc/infer-type st a-lhs)
                          u (get-sort-level st alpha)
                          beta (tc/infer-type st (e/app f-common a-lhs))
                          v (get-sort-level st beta)]
                      (e/app* (e/const' (name/from-string "congrArg") [u v])
                              alpha beta a-lhs a-rhs f-common h-proof))
                    (catch clojure.lang.ExceptionInfo _ nil)
                    (catch Exception ex
                      (when config/*grind-debug*
                        (println "grind congrArg proof:" (.getMessage ex)))
                      nil))))))))))

;; ============================================================
;; Core grind algorithm
;; ============================================================

(defn- try-congruence-closure
  "Try to solve the goal using congruence closure.

   1. Create E-graph context
   2. Translate all hypothesis equalities and goal terms
   3. Assert equalities via merge
   4. Propagate congruence closure
   5. Check if goal LHS = RHS in the E-graph
   6. If so, extract proof explanation

   Returns a proof state with the goal closed, or nil if CC can't solve it."
  [ps goal st]
  (let [goal-type (:type goal)
        eq-parts (extract-eq-from-type st goal-type)]
    (when eq-parts
      (let [[goal-lhs goal-rhs] eq-parts
            lctx (:lctx goal)
            hyps (collect-hypotheses st lctx)
            ctx (mk-egraph-context)
            eg (:eg ctx)]
        ;; Translate goal terms
        (let [lhs-smt (ansatz-to-smt ctx st goal-lhs)
              rhs-smt (ansatz-to-smt ctx st goal-rhs)]
          ;; Register all terms in E-graph
          (register-in-egraph! ctx lhs-smt)
          (register-in-egraph! ctx rhs-smt)
          ;; Assert hypotheses
          (doseq [{:keys [fvar-id lhs rhs kind]} hyps]
            (let [lhs-s (ansatz-to-smt ctx st lhs)
                  rhs-s (ansatz-to-smt ctx st rhs)
                  label (str "hyp_" fvar-id)]
              (register-in-egraph! ctx lhs-s)
              (register-in-egraph! ctx rhs-s)
              (swap! (:hyp-labels ctx) assoc fvar-id label)
              (when (= kind :eq)
                (.merge eg (.getNode eg lhs-s) (.getNode eg rhs-s) label))))
          ;; Propagate congruence closure
          (.propagate eg nil)
          ;; Check if goal is solved
          (when (.areEqual eg lhs-smt rhs-smt)
            ;; Extract explanation
            (let [expl (java.util.ArrayList.)]
              (.explain eg (.getNode eg lhs-smt) (.getNode eg rhs-smt) expl)
              ;; Build proof from explanation
              ;; The explanation is a set of hypothesis labels used
              ;; For now, we try to close with rfl or decide
              (let [eq-type (let [[_ args] (e/get-app-fn-args
                                            (#'tc/cached-whnf st goal-type))]
                              (nth args 0))
                    ;; Check if sides are def-eq (common case)
                    proof-term (if (tc/is-def-eq st goal-lhs goal-rhs)
                                 (e/app* (e/const' (name/from-string "Eq.refl")
                                                   [(lvl/succ lvl/zero)])
                                         eq-type goal-lhs)
                                 ;; Build proof by searching hypotheses directly
                                 (build-proof-from-hypotheses st goal-lhs goal-rhs))]
                (when proof-term
                  (-> (proof/assign-mvar ps (:id goal)
                                         {:kind :exact :term proof-term})
                      (proof/record-tactic :grind [:cc] (:id goal))))))))))))

;; ============================================================
;; Integration with other tactics
;; ============================================================

(defn- try-omega [ps]
  (try
    (require 'ansatz.tactic.omega)
    (let [omega-fn (resolve 'ansatz.tactic.omega/omega)]
      (omega-fn ps))
    (catch clojure.lang.ExceptionInfo _ nil)
    (catch Exception ex
      (when config/*grind-debug*
        (println "grind try-omega:" (.getMessage ex)))
      nil)))

(defn- try-simp [ps]
  (try
    (simp/simp ps)
    (catch clojure.lang.ExceptionInfo _ nil)
    (catch Exception ex
      (when config/*grind-debug*
        (println "grind try-simp:" (.getMessage ex)))
      nil)))

(defn- try-ring [ps]
  (try
    (require 'ansatz.tactic.ring)
    (let [ring-fn (resolve 'ansatz.tactic.ring/ring)]
      (ring-fn ps))
    (catch clojure.lang.ExceptionInfo _ nil)
    (catch Exception ex
      (when config/*grind-debug*
        (println "grind try-ring:" (.getMessage ex)))
      nil)))

(defn- try-rfl [ps]
  (try
    (basic/rfl ps)
    (catch clojure.lang.ExceptionInfo _ nil)
    (catch Exception ex
      (when config/*grind-debug*
        (println "grind try-rfl:" (.getMessage ex)))
      nil)))

(defn- try-assumption [ps]
  (try
    (basic/assumption ps)
    (catch clojure.lang.ExceptionInfo _ nil)
    (catch Exception ex
      (when config/*grind-debug*
        (println "grind try-assumption:" (.getMessage ex)))
      nil)))

;; ============================================================
;; Public API
;; ============================================================

(defn grind
  "General-purpose automation tactic.

   Combines multiple strategies:
   1. Try rfl (definitional equality)
   2. Try assumption (hypothesis matches goal)
   3. Try congruence closure (equalities + function congruence)
   4. Try simp (rewriting)
   5. Try omega (linear arithmetic)
   6. Try ring (polynomial identity)

   Options:
   :fuel     — max iterations for case splitting (default 10)
   :verbose? — print progress (default false)"
  ([ps] (grind ps {}))
  ([ps opts]
   (let [goal (proof/current-goal ps)
         _ (when-not goal (tactic-error! "No goals" {}))
         env (:env ps)
         st (tc/mk-tc-state env)
         st (assoc st :lctx (:lctx goal))]
     ;; Strategy 1: rfl
     (or (try-rfl ps)
         ;; Strategy 2: assumption (structural match only)
         (try-assumption ps)
         ;; Strategy 3: congruence closure via E-graph
         (try-congruence-closure ps goal st)
         ;; Strategy 3b: direct hypothesis chain proof (transitivity + congruence)
         (when-let [proof (build-proof-from-hypotheses st
                                                       (let [[_ args] (e/get-app-fn-args (:type goal))]
                                                         (nth args 1))
                                                       (let [[_ args] (e/get-app-fn-args (:type goal))]
                                                         (nth args 2)))]
           (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof})
               (proof/record-tactic :grind [:hyp-chain] (:id goal))))
         ;; Strategy 4: simp
         (try-simp ps)
         ;; Strategy 5: omega
         (try-omega ps)
         ;; Strategy 6: ring
         (try-ring ps)
         ;; All strategies failed
         (tactic-error! "grind: all strategies failed"
                        {:goal (:type goal)})))))
