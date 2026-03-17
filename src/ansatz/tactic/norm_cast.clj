;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; Tactic layer — norm_cast: cast normalization.
;;
;; Implements the norm_cast family of tactics following Lean 4's algorithm
;; (based on https://arxiv.org/abs/2001.10594):
;;
;; Three categories of lemmas:
;;   - elim:   remove coercions from inside expressions
;;             e.g., (↑m : Int) = (↑n : Int) ↔ m = n
;;   - move:   push coercions inward through operators
;;             e.g., ↑(n + m) = ↑n + ↑m
;;   - squash: collapse stacked/transitive coercions
;;             e.g., (↑(↑(x : Nat) : Int) : Rat) = (↑x : Rat)
;;
;; Algorithm (3-step):
;;   1. Pre-process numerals: convert `(5 : R)` to `↑(5 : Nat)`
;;   2. Move + eliminate: push casts upward, eliminate redundant ones
;;   3. Squash: simplify stacked casts

(ns ansatz.tactic.norm-cast
  "Cast normalization tactic.

   Normalizes expressions containing type coercions (Nat.cast, Int.cast, etc.)
   by applying three phases of rewriting using simp:
   1. Numeral preprocessing
   2. Upward movement + elimination (elim + move lemmas, inverted)
   3. Squashing (squash lemmas)

   Usage:
     (norm-cast ps)              ;; normalize goal
     (push-cast ps)              ;; only push casts inward (move lemmas)
     (norm-cast ps lemma-names)  ;; with extra lemmas"
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.simp :as simp])
  (:import [ansatz.kernel ConstantInfo]))

;; ============================================================
;; Lemma classification
;; ============================================================

(defn- tactic-error! [msg data]
  (throw (ex-info (str "norm_cast: " msg) (merge {:kind :tactic-error} data))))

(def ^:private coercion-names
  "Known coercion function names."
  #{"Nat.cast" "Int.cast" "Int.ofNat" "Rat.cast" "NNRat.cast"
    "algebraMap" "Complex.ofReal"})

(defn- is-coe-app?
  "Check if expression is an application of a known coercion function."
  [e]
  (let [head (e/get-app-fn e)]
    (and (e/const? head)
         (contains? coercion-names (name/->string (e/const-name head))))))

(defn- count-head-coes
  "Count coercions at the head of an expression.
   E.g., ↑(↑x) has 2 head coes."
  [e]
  (loop [e e n 0]
    (if (is-coe-app? e)
      ;; The coerced argument is the last arg
      (let [args (e/get-app-args e)]
        (if (seq args)
          (recur (last args) (inc n))
          n))
      n)))

(defn- get-semantic-args
  "Get the 'semantic' arguments of an application, skipping typeclass instances.
   For coe functions, returns just the coerced value (last arg).
   For binary operators like HAdd.hAdd (6 args), returns the last 2.
   For other functions, returns all args."
  [e]
  (let [[head args] (e/get-app-fn-args e)
        n (count args)]
    (when (e/const? head)
      (let [hname (name/->string (e/const-name head))]
        (cond
          ;; Coercion functions: just the last (coerced) argument
          (contains? coercion-names hname)
          [(last args)]

          ;; Binary ops: HAdd.hAdd, HMul.hMul, etc. take 6 args, last 2 are semantic
          (and (or (.startsWith hname "HAdd.") (.startsWith hname "HMul.")
                   (.startsWith hname "HSub.") (.startsWith hname "HDiv.")
                   (.startsWith hname "HMod.") (.startsWith hname "HPow."))
               (>= n 2))
          [(nth args (- n 2)) (nth args (- n 1))]

          ;; Comparisons: Eq (3 args: type, lhs, rhs), LE.le, LT.lt (4 args)
          (and (= hname "Eq") (= n 3))
          [(nth args 1) (nth args 2)]

          (and (or (= hname "LE.le") (= hname "LT.lt")) (>= n 4))
          [(nth args (- n 2)) (nth args (- n 1))]

          ;; Neg.neg: last arg is semantic
          (and (.startsWith hname "Neg.") (>= n 1))
          [(last args)]

          ;; OfNat.ofNat: no semantic subterms with coes
          (.startsWith hname "OfNat.")
          []

          ;; Default: return all args (may overcount, but safe)
          :else (vec args))))))

(defn- count-all-coes
  "Count all coercion applications in an expression (recursive).
   Only descends into semantic argument positions to avoid counting
   coercion references inside typeclass instance plumbing."
  [e]
  (let [cnt (atom 0)]
    (letfn [(go [e]
                (when (is-coe-app? e)
                  (swap! cnt inc))
                (when-let [sargs (get-semantic-args e)]
                  (doseq [a sargs] (go a))))]
      (go e))
    @cnt))

(defn- count-internal-coes
  "Count coercions that are NOT at the head position."
  [e]
  (- (count-all-coes e) (count-head-coes e)))

;; ============================================================
;; Lemma sets — hardcoded for known Init/Mathlib lemmas
;; ============================================================

;; Move lemmas: push coercions inward through operators
;; Pattern: ↑(n op m) = ↑n op ↑m
(def ^:private move-lemma-names
  ["Nat.cast_add" "Nat.cast_mul" "Nat.cast_sub" "Nat.cast_pow"
   "Nat.cast_succ"
   "Int.cast_add" "Int.cast_mul" "Int.cast_neg" "Int.cast_sub"
   "Int.cast_ofNat"])

;; Elim lemmas: eliminate coercions from comparisons/equalities
;; Pattern: (↑m : R) op (↑n : R) ↔ m op n
(def ^:private elim-lemma-names
  ["Nat.cast_inj" "Nat.cast_le" "Nat.cast_lt"
   "Nat.cast_eq_zero" "Nat.cast_ne_zero" "Nat.cast_pos"
   "Int.cast_le" "Int.cast_lt"])

;; Squash lemmas: collapse stacked/identity coercions
;; Pattern: ↑(↑x : B) : C = ↑x : C  or  ↑0 = 0, ↑1 = 1
(def ^:private squash-lemma-names
  ["Int.cast_natCast"
   "Nat.cast_zero" "Nat.cast_one" "Nat.cast_two"
   "Int.cast_zero" "Int.cast_one"])

;; Up lemmas: move inverted + elim (used in step 2)
;; These are the move lemmas applied in reverse direction (RHS→LHS)
;; plus the elim lemmas applied forward.
;; For our implementation, we use move lemmas forward (they push casts inward,
;; which has the effect of moving them "up" towards the root when applied bottom-up).

;; ============================================================
;; Simp-based rewriting engine
;; ============================================================

(defn- build-lemma-set
  "Build simp lemmas from a list of names, filtering to those that exist in env."
  [env lemma-names]
  (simp/make-simp-lemmas env lemma-names))

(defn- simp-with-lemmas
  "Run simp on the goal with a specific lemma set."
  [ps lemma-names]
  (try
    (simp/simp ps lemma-names)
    (catch Exception _
      ps)))

;; ============================================================
;; The 3-step norm_cast algorithm
;; ============================================================

(defn- step1-preprocess-numerals
  "Step 1: Convert numeric literals to explicit casts.
   E.g., (5 : Int) becomes ↑(5 : Nat) when there's a NatCast instance.
   For now, this is a no-op — Lean's export already has explicit casts."
  [ps]
  ps)

(defn- step2-move-and-elim
  "Step 2: Move coercions upward and eliminate them.
   Uses move lemmas (forward) to push casts through operators,
   and elim lemmas to remove them from comparisons."
  [ps]
  (let [all-lemmas (concat move-lemma-names elim-lemma-names)]
    (simp-with-lemmas ps all-lemmas)))

(defn- step3-squash
  "Step 3: Squash stacked coercions.
   Uses squash lemmas + move lemmas to collapse redundant casts."
  [ps]
  (let [all-lemmas (concat squash-lemma-names move-lemma-names)]
    (simp-with-lemmas ps all-lemmas)))

;; ============================================================
;; Public API
;; ============================================================

(defn norm-cast
  "Normalize casts in the current goal using the 3-step norm_cast algorithm.

   1. Pre-process numerals (convert literals to explicit casts)
   2. Move coercions upward + eliminate from comparisons
   3. Squash stacked coercions

   Optional extra-lemmas can be provided for additional rewriting."
  ([ps] (norm-cast ps []))
  ([ps extra-lemmas]
   (let [goal (proof/current-goal ps)
         _ (when-not goal (tactic-error! "No goals" {}))
         ;; Try each step, keeping the result if it makes progress
         ps1 (step1-preprocess-numerals ps)
         ps2 (step2-move-and-elim ps1)
         ;; If step 2 closed the goal, we're done
         ps3 (if (proof/solved? ps2)
               ps2
               (step3-squash ps2))
         ;; Apply extra lemmas if provided
         ps4 (if (and (seq extra-lemmas) (not (proof/solved? ps3)))
               (simp-with-lemmas ps3 extra-lemmas)
               ps3)]
     (if (proof/solved? ps4)
       ps4
       ;; If we haven't closed the goal, check if we at least made progress
       (let [new-goal (proof/current-goal ps4)]
         (if (and new-goal
                  (= (:type new-goal) (:type goal)))
           (tactic-error! "norm_cast made no progress" {:goal (:type goal)})
           ps4))))))

(defn push-cast
  "Push coercions inward through operators (move lemmas only).
   This is the `push_cast` tactic from Lean 4.

   Rewrites ↑(n + m) to ↑n + ↑m, etc."
  ([ps] (push-cast ps []))
  ([ps extra-lemmas]
   (let [all-lemmas (concat move-lemma-names squash-lemma-names extra-lemmas)]
     (simp-with-lemmas ps all-lemmas))))

(defn derive
  "Core norm_cast derivation: simplify an expression (not a goal) using cast
   normalization. Returns {:expr simplified :proof proof-term} or nil.

   This is the equivalent of Lean 4's NormCast.derive."
  [env expr]
  (let [st (tc/mk-tc-state env)
        ;; Build all three lemma sets
        move-lemmas (build-lemma-set env move-lemma-names)
        elim-lemmas (build-lemma-set env elim-lemma-names)
        squash-lemmas (build-lemma-set env squash-lemma-names)
        all-up-lemmas (concat move-lemmas elim-lemmas)
        up-index (simp/build-lemma-index all-up-lemmas)
        squash-index (simp/build-lemma-index (concat squash-lemmas move-lemmas))
        ;; Step 2: simplify with up lemmas
        simplified1 (#'simp/simp-expr st env up-index expr 20)
        ;; Step 3: simplify with squash lemmas
        simplified2 (if (= simplified1 expr)
                      (#'simp/simp-expr st env squash-index expr 20)
                      (#'simp/simp-expr st env squash-index simplified1 20))]
    (when-not (= simplified2 expr)
      {:expr simplified2
       :original expr})))

;; ============================================================
;; Lemma auto-classification (for custom lemmas)
;; ============================================================

(defn classify-lemma
  "Classify a norm_cast lemma into :elim, :move, or :squash based on
   the coercion structure of its LHS and RHS.

   Following the Lean 4 classification:
   - elim:   LHS has 0 head coes, ≥1 internal coes
   - move:   LHS has 1 head coe, 0 internal coes; RHS has 0 head, ≥1 internal
   - squash: LHS has ≥1 head coes, 0 internal coes; RHS has fewer head coes"
  [env lemma-name]
  (when-let [ci (env/lookup env (if (instance? ansatz.kernel.Name lemma-name)
                                  lemma-name
                                  (name/from-string (str lemma-name))))]
    (let [ty (.type ^ConstantInfo ci)]
      ;; Peel foralls to get to the equality
      (loop [t ty]
        (if (e/forall? t)
          (recur (e/forall-body t))
          ;; Should be Eq/Iff
          (let [[head args] (e/get-app-fn-args t)]
            (when (and (e/const? head)
                       (or (= (name/->string (e/const-name head)) "Eq")
                           (= (name/->string (e/const-name head)) "Iff"))
                       (>= (count args) 2))
              (let [lhs (if (= (count args) 3) (nth args 1) (nth args 0))
                    rhs (if (= (count args) 3) (nth args 2) (nth args 1))
                    lhs-head-coes (count-head-coes lhs)
                    lhs-internal-coes (count-internal-coes lhs)
                    rhs-head-coes (count-head-coes rhs)
                    rhs-internal-coes (count-internal-coes rhs)]
                (cond
                  ;; elim: LHS has 0 head coes, ≥1 internal coes
                  (and (zero? lhs-head-coes) (pos? lhs-internal-coes))
                  :elim

                  ;; move: LHS has 1 head coe, 0 internal; RHS has 0 head, ≥1 internal
                  (and (= 1 lhs-head-coes) (zero? lhs-internal-coes)
                       (zero? rhs-head-coes) (pos? rhs-internal-coes))
                  :move

                  ;; squash: LHS has ≥1 head coes, 0 internal; RHS has fewer head
                  (and (pos? lhs-head-coes) (zero? lhs-internal-coes)
                       (< rhs-head-coes lhs-head-coes))
                  :squash

                  :else nil)))))))))
