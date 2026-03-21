;; Tactic layer — positivity: prove non-negativity goals.
;;
;; Recursively proves goals of the form `0 ≤ expr` by decomposing
;; the expression and applying appropriate Mathlib lemmas.
;;
;; Follows Mathlib's Tactic.Positivity (Mathlib/Tactic/Positivity/).
;;
;; Key lemmas used:
;; - mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b
;; - pow_nonneg : 0 ≤ a → 0 ≤ a ^ n
;; - add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b
;; - sq_nonneg  : 0 ≤ a ^ 2
;; - le_refl    : 0 ≤ 0
;; - Nat.zero_le : 0 ≤ n (for Nat)
;; - norm_nonneg : 0 ≤ ‖x‖

(ns ansatz.tactic.positivity
  "Prove non-negativity (0 ≤ expr) goals recursively."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.instance :as instance])
  (:import [ansatz.kernel TypeChecker]))

;; ============================================================
;; Well-known names
;; ============================================================

(def ^:private le-name (name/from-string "LE.le"))
(def ^:private hadd-name (name/from-string "HAdd.hAdd"))
(def ^:private hmul-name (name/from-string "HMul.hMul"))
(def ^:private hpow-name (name/from-string "HPow.hPow"))
(def ^:private ofnat-name (name/from-string "OfNat.ofNat"))
(def ^:private mul-nonneg-name (name/from-string "mul_nonneg"))
(def ^:private pow-nonneg-name (name/from-string "pow_nonneg"))
(def ^:private add-nonneg-name (name/from-string "add_nonneg"))
(def ^:private le-refl-name (name/from-string "le_refl"))
(def ^:private nat-zero-le-name (name/from-string "Nat.zero_le"))

(defn- tactic-error! [msg data]
  (throw (ex-info (str "positivity: " msg) (merge {:kind :tactic-error} data))))

;; ============================================================
;; Goal decomposition
;; ============================================================

(defn- is-zero?
  "Check if expr is 0 (literal or OfNat.ofNat _ 0 _)."
  [st expr]
  (let [w (#'tc/cached-whnf st expr)]
    (or (and (e/lit-nat? w) (zero? (e/lit-nat-val w)))
        (let [[head args] (e/get-app-fn-args w)]
          (and (e/const? head)
               (= (e/const-name head) ofnat-name)
               (= 3 (count args))
               (e/lit-nat? (nth args 1))
               (zero? (e/lit-nat-val (nth args 1))))))))

(defn- decompose-le-zero
  "If goal is `0 ≤ rhs`, return [type-expr rhs], else nil."
  [st goal-type]
  (let [[head args] (e/get-app-fn-args goal-type)]
    (when (and (e/const? head) (= (e/const-name head) le-name))
      (let [nargs (count args)]
        ;; LE.le has varying arg counts depending on instance chain
        ;; The last two args are always lhs and rhs
        (when (>= nargs 2)
          (let [lhs (nth args (- nargs 2))
                rhs (nth args (- nargs 1))]
            (when (is-zero? st lhs)
              ;; Extract the type from args (first explicit type arg or infer)
              (let [type-expr (if (>= nargs 3) (nth args 0)
                                  (try (tc/infer-type st rhs) (catch Exception _ nil)))]
                [type-expr rhs]))))))))

(defn- decompose-expr
  "Decompose rhs into an arithmetic structure for positivity.
   Returns {:kind :mul/:add/:pow/:lit/:var, ...} or nil."
  [st expr]
  (let [w (#'tc/cached-whnf st expr)
        [head args] (e/get-app-fn-args w)]
    (when (e/const? head)
      (let [hname (e/const-name head)]
        (cond
          ;; HMul.hMul α β γ inst a b
          (and (= hname hmul-name) (= 6 (count args)))
          {:kind :mul :a (nth args 4) :b (nth args 5) :type (nth args 0)}

          ;; HAdd.hAdd α β γ inst a b
          (and (= hname hadd-name) (= 6 (count args)))
          {:kind :add :a (nth args 4) :b (nth args 5) :type (nth args 0)}

          ;; HPow.hPow α β γ inst a n
          (and (= hname hpow-name) (= 6 (count args)))
          {:kind :pow :base (nth args 4) :exp (nth args 5) :type (nth args 0)}

          ;; OfNat.ofNat α n inst — literal in a type
          (and (= hname ofnat-name) (= 3 (count args)))
          (let [n (nth args 1)]
            (when (e/lit-nat? n)
              {:kind :lit :val (e/lit-nat-val n) :type (nth args 0)}))

          :else nil)))))

;; ============================================================
;; Positivity core — recursive proof search
;; ============================================================

(declare prove-nonneg)

(defn- try-apply-lemma
  "Try to apply a named lemma and close remaining goals with assumption/recursion."
  [ps lemma-name]
  (try
    (let [env (:env ps)
          ^ansatz.kernel.ConstantInfo ci (env/lookup env lemma-name)]
      (when ci
        (let [lps (vec (.levelParams ci))
              levels (mapv (fn [_] lvl/zero) lps)
              term (e/const' lemma-name levels)]
          (-> ps
              (basic/apply-tac term)
              ;; Try to close all remaining goals with assumption/decide/positivity
              (basic/all-goals (fn [ps']
                                 (or (try (basic/assumption ps')
                                          (catch Exception _ nil))
                                     (try (let [decide-fn (requiring-resolve 'ansatz.tactic.decide/decide)]
                                            (decide-fn ps'))
                                          (catch Exception _ nil))
                                     ps')))))))
    (catch Exception _ nil)))

;; ============================================================
;; positivity tactic
;; ============================================================

(defn positivity
  "Prove the current goal by showing non-negativity recursively.

   Handles goals of the form `0 ≤ expr` where expr involves:
   - Products: 0 ≤ a * b (via mul_nonneg)
   - Sums: 0 ≤ a + b (via add_nonneg)
   - Powers: 0 ≤ a ^ n (via pow_nonneg)
   - Literals: 0 ≤ 42 (via decide or le_refl)
   - Hypotheses: 0 ≤ x (via assumption)

   Falls back to apply + assumption chain for complex cases."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        env (:env ps)
        st (tc/mk-tc-state env)
        st (assoc st :lctx (:lctx goal))]
    ;; Strategy 1: try assumption directly
    (or (try (basic/assumption ps) (catch Exception _ nil))
        ;; Strategy 2: try omega (handles 0 ≤ n for Nat via Nat.zero_le)
        (try (let [omega-fn (requiring-resolve 'ansatz.tactic.omega/omega)]
               (omega-fn ps))
             (catch Exception _ nil))
        ;; Strategy 3: try decide (for ground cases like 0 ≤ 3)
        (try (let [decide-fn (requiring-resolve 'ansatz.tactic.decide/decide)]
               (decide-fn ps))
             (catch Exception _ nil))
        ;; Strategy 3: decompose and apply lemmas
        (when-let [[type-expr rhs] (decompose-le-zero st (:type goal))]
          (when-let [decomp (decompose-expr st rhs)]
            (case (:kind decomp)
              ;; 0 ≤ a * b → mul_nonneg (0 ≤ a) (0 ≤ b)
              :mul (try-apply-lemma ps mul-nonneg-name)
              ;; 0 ≤ a + b → add_nonneg (0 ≤ a) (0 ≤ b)
              :add (try-apply-lemma ps add-nonneg-name)
              ;; 0 ≤ a ^ n → pow_nonneg (0 ≤ a)
              :pow (try-apply-lemma ps pow-nonneg-name)
              ;; 0 ≤ literal → decide
              :lit (try (let [decide-fn (requiring-resolve 'ansatz.tactic.decide/decide)]
                          (decide-fn ps))
                        (catch Exception _ nil))
              nil)))
        ;; Strategy 4: try le_refl (0 ≤ 0)
        (try-apply-lemma ps le-refl-name)
        ;; Strategy 5: try Nat.zero_le
        (try-apply-lemma ps nat-zero-le-name)
        (tactic-error! "could not prove non-negativity" {:goal (:type goal)}))))
