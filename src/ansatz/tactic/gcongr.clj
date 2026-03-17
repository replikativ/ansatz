;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; Tactic layer — gcongr: generalized congruence (monotonicity reasoning).
;;
;; Proves inequality goals by decomposing them into sub-inequalities
;; using monotonicity lemmas. For example:
;;   a ≤ b → c ≤ d → a * c ≤ b * d  (via mul_le_mul')
;;   a ≤ b → a + c ≤ b + c          (via add_le_add_right)
;;   0 ≤ a → a ≤ b → a ^ n ≤ b ^ n  (via pow_le_pow_left)
;;
;; Follows Mathlib's Tactic.GCongr — a @[gcongr]-tagged lemma database.

(ns ansatz.tactic.gcongr
  "Generalized congruence — monotonicity reasoning for inequalities."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]))

;; ============================================================
;; Well-known monotonicity lemmas
;; ============================================================
;; These are the core @[gcongr] lemmas from Mathlib.

(def ^:private gcongr-lemmas
  "Core monotonicity lemmas, ordered by priority.
   Each entry: [name description]"
  [;; Addition
   ["add_le_add"              "a ≤ b → c ≤ d → a + c ≤ b + d"]
   ["add_le_add_left"         "a ≤ b → c + a ≤ c + b"]
   ["add_le_add_right"        "a ≤ b → a + c ≤ b + c"]
   ;; Multiplication (with non-negativity side conditions)
   ["mul_le_mul_of_nonneg_left"  "a ≤ b → 0 ≤ c → c * a ≤ c * b"]
   ["mul_le_mul_of_nonneg_right" "a ≤ b → 0 ≤ c → a * c ≤ b * c"]
   ["mul_le_mul'"             "a ≤ b → c ≤ d → a * c ≤ b * d (with 0 ≤)"]
   ["mul_le_of_le_one_left"   "0 ≤ b → a ≤ 1 → a * b ≤ b"]
   ["mul_le_of_le_one_right"  "0 ≤ a → b ≤ 1 → a * b ≤ a"]
   ;; Powers
   ["pow_le_pow_left"         "0 ≤ a → a ≤ b → a ^ n ≤ b ^ n"]
   ["pow_le_one₀"             "0 ≤ a → a ≤ 1 → a ^ n ≤ 1"]
   ;; Subtraction
   ["sub_le_sub_left"         "a ≤ b → c - b ≤ c - a"]
   ["sub_le_sub_right"        "a ≤ b → a - c ≤ b - c"]])

(defn- tactic-error! [msg data]
  (throw (ex-info (str "gcongr: " msg) (merge {:kind :tactic-error} data))))

;; ============================================================
;; gcongr core — try monotonicity lemmas
;; ============================================================

(defn- try-gcongr-lemma
  "Try to apply a gcongr lemma and close side-conditions.
   Returns updated ps or nil."
  [ps lemma-str]
  (try
    (let [lname (name/from-string lemma-str)
          env (:env ps)
          ci (env/lookup env lname)]
      (when ci
        (let [term (e/const' lname [lvl/zero])
              ps' (basic/apply-tac ps term)]
          ;; Try to close all remaining goals with assumption or positivity
          (basic/all-goals ps'
                           (fn [ps'']
                             (or (try (basic/assumption ps'')
                                      (catch Exception _ nil))
                  ;; Try positivity for 0 ≤ x side conditions
                                 (try (let [pos-fn (requiring-resolve 'ansatz.tactic.positivity/positivity)]
                                        (pos-fn ps''))
                                      (catch Exception _ nil))
                                 ps''))))))
    (catch Exception _ nil)))

;; ============================================================
;; gcongr tactic
;; ============================================================

(defn gcongr
  "Prove inequality goals using monotonicity lemmas.

   Tries each @[gcongr]-tagged lemma in priority order.
   After applying a lemma, tries to close side-conditions
   with assumption and positivity.

   For convergence proofs, the key patterns are:
   - κ^n * e₀ ≤ e₀  (via mul_le_of_le_one_left + pow_le_one₀)
   - a * b ≤ c * d   (via mul_le_mul' + sub-inequalities)
   - a + b ≤ c + d   (via add_le_add)"
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))]
    ;; Strategy 1: try assumption
    (or (try (basic/assumption ps) (catch Exception _ nil))
        ;; Strategy 2: try each gcongr lemma
        (some (fn [[lname _desc]]
                (try-gcongr-lemma ps lname))
              gcongr-lemmas)
        (tactic-error! "no monotonicity lemma matched"
                       {:goal (:type goal)}))))
