(ns ansatz.examples.no-self-regression
  "regressions xs xs = []  — proved + kernel-verified in the ansatz Lean-4 kernel.
   A worked example of recursive a/defn (memq/regressions/allmem lower via List.rec)
   plus an inductive a/theorem chain: vocabulary -> projections -> invariants -> capstone.
   Needs an Init store with Nat.beq/Nat.beq_refl + List/Bool recursors (init.ndjson or mathlib).

   Usage (load-file this, examples/ is not on the classpath):
     (ansatz.examples.no-self-regression/install!)
     (ansatz.examples.no-self-regression/verify!)"
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]))

(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))

(defn- install-one!
  "Install `form` (an a/defn or a/theorem) under name `nm` unless already present."
  [nm form]
  (when-not (has? nm) (eval form))
  nm)

;; ── Collect — domain vocabulary ───────────────────────────────────────────────

(defn- def-memq! []
  (install-one! "memq"
    '(ansatz.core/defn memq [x :- Nat, xs :- (List Nat)] Bool
       (match xs (List Nat) Bool
         (nil Bool.false)
         (cons [h t] (if (Nat.beq x h) Bool.true (memq x t)))))))

(defn- def-regressions! []
  (install-one! "regressions"
    '(ansatz.core/defn regressions [old :- (List Nat), new :- (List Nat)] (List Nat)
       (match new (List Nat) (List Nat)
         (nil (List.nil Nat))
         (cons [h t] (if (memq h old) (regressions old t)
                         (List.cons Nat h (regressions old t))))))))

(defn- def-allmem! []
  (install-one! "allmem"
    '(ansatz.core/defn allmem [new :- (List Nat), old :- (List Nat)] Bool
       (match new (List Nat) Bool
         (nil Bool.true)
         (cons [h t] (if (memq h old) (allmem t old) Bool.false))))))

;; ── Promote — raw fact -> richer fact ─────────────────────────────────────────

(defn- prove-memq-head! []
  (install-one! "memq_head"
    '(ansatz.core/theorem memq_head [h :- Nat, t :- (List Nat)]
       (= Bool (memq h (List.cons Nat h t)) Bool.true)
       (rewrite memq.eq_2) (rewrite Nat.beq_refl) (rfl))))

(defn- prove-memq-mono! []
  (install-one! "memq_mono"
    ;; rewrite hyp makes both Bool.rec branches Bool.true; case-split the
    ;; discriminant and iota-reduce each to close.
    '(ansatz.core/theorem memq_mono
       [x :- Nat, old :- (List Nat), a :- Nat, hyp :- (= Bool (memq x old) Bool.true)]
       (= Bool (memq x (List.cons Nat a old)) Bool.true)
       (rewrite memq.eq_2) (rewrite hyp)
       (cases hm (Nat.beq x a)) (all_goals (rewrite hm)) (all_goals (rfl)))))

(defn- prove-allmem-cons-head! []
  (install-one! "allmem_cons_head"
    ;; close the true branch by rfl, then reduce the surviving false branch
    ;; (ha reduced through allmem.eq_2 + hm) down to false = false.
    '(ansatz.core/theorem allmem_cons_head [h :- Nat, t :- (List Nat), old :- (List Nat)]
       (=> (= Bool (allmem (List.cons Nat h t) old) Bool.true)
           (= Bool (memq h old) Bool.true))
       (intro ha) (cases hm (memq h old))
       (all_goals (try (rfl)))
       (all_goals (try (rewrite <- ha))) (all_goals (try (rewrite allmem.eq_2)))
       (all_goals (try (rewrite hm)))   (all_goals (try (dsimp))))))

(defn- prove-allmem-cons-tail! []
  (install-one! "allmem_cons_tail"
    '(ansatz.core/theorem allmem_cons_tail [h :- Nat, t :- (List Nat), old :- (List Nat)]
       (=> (= Bool (allmem (List.cons Nat h t) old) Bool.true)
           (= Bool (allmem t old) Bool.true))
       (intro ha)
       (have hmt (= Bool (memq h old) Bool.true) (allmem_cons_head h t old ha))
       (rewrite <- ha) (rewrite allmem.eq_2) (rewrite hmt) (dsimp))))

;; ── Pipeline — pure orchestration ─────────────────────────────────────────────
;; Induction skeleton: (induction x)(all_goals (intro h))(all_goals (try (exact
;; <base-eq-lemma>))) closes the base case and leaves the step case as the SOLE
;; goal, so the goal-rotation rewrite performs is a no-op.

(defn- prove-allmem-mono! []
  (install-one! "allmem_mono"
    '(ansatz.core/theorem allmem_mono
       [old :- (List Nat), a :- Nat, new :- (List Nat)]
       (=> (= Bool (allmem new old) Bool.true)
           (= Bool (allmem new (List.cons Nat a old)) Bool.true))
       (induction new)
       (all_goals (intro hh))
       (all_goals (try (exact (allmem.eq_1 (List.cons Nat a old)))))
       (have hmt  (= Bool (memq head old) Bool.true) (allmem_cons_head head tail old hh))
       (have hat  (= Bool (allmem tail old) Bool.true) (allmem_cons_tail head tail old hh))
       (have hmc  (= Bool (memq head (List.cons Nat a old)) Bool.true) (memq_mono head old a hmt))
       (have hat2 (= Bool (allmem tail (List.cons Nat a old)) Bool.true) (ih_tail hat))
       (rewrite allmem.eq_2) (rewrite hmc) (dsimp) (exact hat2))))

(defn- prove-allmem-refl! []
  (install-one! "allmem_refl"
    '(ansatz.core/theorem allmem_refl [xs :- (List Nat)]
       (= Bool (allmem xs xs) Bool.true)
       (induction xs)
       (all_goals (try (exact (allmem.eq_1 (List.nil Nat)))))
       (have hmh  (= Bool (memq head (List.cons Nat head tail)) Bool.true) (memq_head head tail))
       (have hat2 (= Bool (allmem tail (List.cons Nat head tail)) Bool.true)
                  (allmem_mono tail head tail ih_tail))
       (rewrite allmem.eq_2) (rewrite hmh) (dsimp) (exact hat2))))

(defn- prove-regr-gen! []
  (install-one! "regr_gen"
    '(ansatz.core/theorem regr_gen [old :- (List Nat), new :- (List Nat)]
       (=> (= Bool (allmem new old) Bool.true)
           (= (List Nat) (regressions old new) (List.nil Nat)))
       (induction new)
       (all_goals (intro ha))
       (all_goals (try (exact (regressions.eq_1 old))))
       (have hmt (= Bool (memq head old) Bool.true) (allmem_cons_head head tail old ha))
       (have hat (= Bool (allmem tail old) Bool.true) (allmem_cons_tail head tail old ha))
       (have htn (= (List Nat) (regressions old tail) (List.nil Nat)) (ih_tail hat))
       (rewrite regressions.eq_2) (rewrite hmt) (dsimp) (exact htn))))

;; ── Boundary — capstone + effectful edge ──────────────────────────────────────

(defn- prove-regressions-self-empty! []
  (install-one! "regressions_self_empty"
    '(ansatz.core/theorem regressions_self_empty [xs :- (List Nat)]
       (= (List Nat) (regressions xs xs) (List.nil Nat))
       (exact (regr_gen xs xs (allmem_refl xs))))))

(defn install!
  "Install the development into the current env (idempotent). Returns :installed."
  []
  (def-memq!) (def-regressions!) (def-allmem!)
  (prove-memq-head!) (prove-memq-mono!) (prove-allmem-cons-head!) (prove-allmem-cons-tail!)
  (prove-allmem-mono!) (prove-allmem-refl!) (prove-regr-gen!)
  (prove-regressions-self-empty!)
  :installed)

(def ^:private theorems
  ["memq_head" "memq_mono" "allmem_cons_head" "allmem_cons_tail"
   "allmem_mono" "allmem_refl" "regr_gen" "regressions_self_empty"])

(defn verify!
  "Kernel check-constant on each theorem. Returns {:all-verified bool :results {..}}."
  []
  (let [e (a/env)
        results (into {}
                      (for [s theorems]
                        (let [ci (env/lookup e (nm/from-string s))]
                          [s (boolean (and ci (env/verifies? e (.type ci) (.value ci))))])))]
    {:all-verified (every? val results)
     :results results}))
