;; Copyright (c) 2026 Simmis GmbH. All rights reserved.
;; Tactic layer — omega proof term construction.
;;
;; Mirrors Lean 4's omega tactic proof architecture:
;; 1. Reify: CIC expr → Lean.Omega.LinearCombo + proof that lc.eval atoms = expr
;; 2. Solve: Fourier-Motzkin with Justification tracking
;; 3. Extract: Walk Justification tree → build CIC proof term via Init.Omega lemmas
;;
;; The proof term references Lean.Omega.* constants from Init.Omega,
;; which must be present in the environment.

(ns cic.tactic.omega-proof
  "Omega tactic with direct proof term construction.

   Instead of delegating to `decide` for certification, this implementation
   tracks justifications through the solver and constructs proof terms
   that reference Lean.Omega.* lemmas (Constraint.combine_sat', combo_sat,
   tidy_sat, etc.).

   This enables omega to work on non-ground goals.

   Architecture:
   - cic.tactic.omega.problem: constraint algebra, justification tree, problem data
   - cic.tactic.omega.fm: Fourier-Motzkin solver backend
   - cic.tactic.omega.smt-backend: zustand SMT solver backend with Farkas certificates
   - cic.solver.smt: generic SMT service (usable by any tactic)
   - This file: CIC proof term construction, reification, tactic entry points"
  (:require [cic.kernel.expr :as e]
            [cic.kernel.env :as env]
            [cic.kernel.name :as name]
            [cic.kernel.level :as lvl]
            [cic.kernel.tc :as tc]
            [cic.kernel.reduce :as red]
            [cic.tactic.proof :as proof]
            [cic.tactic.decide :as decide-tac]
            [cic.tactic.omega.problem :as op]
            [cic.tactic.omega.fm :as fm]
            [cic.tactic.omega.smt-backend :as smt-backend]))

;; ============================================================
;; CIC names for Lean.Omega.* constants
;; ============================================================

(def ^:private omega-names
  "Cache of Name objects for Lean.Omega constants."
  (let [n name/from-string]
    {:linear-combo           (n "Lean.Omega.LinearCombo")
     :linear-combo-mk        (n "Lean.Omega.LinearCombo.mk")
     :linear-combo-eval      (n "Lean.Omega.LinearCombo.eval")
     :linear-combo-add       (n "Lean.Omega.LinearCombo.instAdd") ;; HAdd instance
     :linear-combo-sub       (n "Lean.Omega.LinearCombo.instSub")
     :linear-combo-neg       (n "Lean.Omega.LinearCombo.instNeg")
     :linear-combo-coordinate (n "Lean.Omega.LinearCombo.coordinate")
     :add-eval               (n "Lean.Omega.LinearCombo.add_eval")
     :sub-eval               (n "Lean.Omega.LinearCombo.sub_eval")
     :neg-eval               (n "Lean.Omega.LinearCombo.neg_eval")
     :coordinate-eval        (n "Lean.Omega.LinearCombo.coordinate_eval")
     :coordinate-eval-0      (n "Lean.Omega.LinearCombo.coordinate_eval_0")
     :coordinate-eval-1      (n "Lean.Omega.LinearCombo.coordinate_eval_1")
     :coordinate-eval-2      (n "Lean.Omega.LinearCombo.coordinate_eval_2")
     :constraint             (n "Lean.Omega.Constraint")
     :constraint-mk          (n "Lean.Omega.Constraint.mk")
     :constraint-sat         (n "Lean.Omega.Constraint.sat")
     :constraint-sat'        (n "Lean.Omega.Constraint.sat'")
     :constraint-combine     (n "Lean.Omega.Constraint.combine")
     :constraint-combo       (n "Lean.Omega.Constraint.combo")
     :constraint-scale       (n "Lean.Omega.Constraint.scale")
     :constraint-is-impossible (n "Lean.Omega.Constraint.isImpossible")
     :combine-sat'           (n "Lean.Omega.Constraint.combine_sat'")
     :combo-sat              (n "Lean.Omega.Constraint.combo_sat")
     :combo-sat'             (n "Lean.Omega.combo_sat'")
     :coeffs-combo           (n "Lean.Omega.Coeffs.combo")
     :scale-sat              (n "Lean.Omega.Constraint.scale_sat")
     :tidy-sat               (n "Lean.Omega.tidy_sat")
     :tidy-constraint        (n "Lean.Omega.tidyConstraint")
     :tidy-coeffs            (n "Lean.Omega.tidyCoeffs")
     :normalize-sat          (n "Lean.Omega.normalize_sat")
     :normalize-constraint   (n "Lean.Omega.normalizeConstraint")
     :normalize-coeffs       (n "Lean.Omega.normalizeCoeffs")
     :positivize-sat         (n "Lean.Omega.positivize_sat")
     :positivize-constraint  (n "Lean.Omega.positivizeConstraint")
     :positivize-coeffs      (n "Lean.Omega.positivizeCoeffs")
     :not-sat-impossible     (n "Lean.Omega.Constraint.not_sat'_of_isImpossible")
     :add-inequality-sat     (n "Lean.Omega.Constraint.addInequality_sat")
     :add-equality-sat       (n "Lean.Omega.Constraint.addEquality_sat")
     :coeffs                 (n "Lean.Omega.Coeffs")
     :coeffs-get             (n "Lean.Omega.Coeffs.get")
     :int-list-dot           (n "Lean.Omega.IntList.dot")
     ;; Arithmetic
     :nat-name               (n "Nat")
     :int-name               (n "Int")
     :nat-add                (n "Nat.add")
     :nat-sub                (n "Nat.sub")
     :nat-mul                (n "Nat.mul")
     :nat-succ               (n "Nat.succ")
     :nat-zero               (n "Nat.zero")
     :nat-div                (n "Nat.div")
     :nat-mod                (n "Nat.mod")
     :hadd                   (n "HAdd.hAdd")
     :hsub                   (n "HSub.hSub")
     :hmul                   (n "HMul.hMul")
     :hdiv                   (n "HDiv.hDiv")
     :hmod                   (n "HMod.hMod")
     :ofnat                  (n "OfNat.ofNat")
     ;; Propositions
     :eq-name                (n "Eq")
     :eq-refl                (n "Eq.refl")
     :eq-trans               (n "Eq.trans")
     :le-name                (n "LE.le")
     :lt-name                (n "LT.lt")
     :ge-name                (n "GE.ge")
     :gt-name                (n "GT.gt")
     :and-name               (n "And")
     :or-name                (n "Or")
     :not-name               (n "Not")
     :ne-name                (n "Ne")
     :false-name             (n "False")
     :true-name              (n "True")
     :nat-le                 (n "Nat.le")
     :bool-name              (n "Bool")
     :bool-true              (n "Bool.true")
     :option-name            (n "Option")
     :option-some            (n "Option.some")
     :option-none            (n "Option.none")
     ;; Conversion lemmas (Nat → Int, hypothesis proof chain)
     :int-ofnat              (n "Int.ofNat")
     :int-ofnat-le           (n "Int.ofNat_le")
     :int-ofnat-lt           (n "Int.ofNat_lt")
     :int-sub-nonneg-of-le   (n "Int.sub_nonneg_of_le")
     :int-sub-eq-zero-of-eq  (n "Int.sub_eq_zero_of_eq")
     :int-add-one-le-of-lt   (n "Int.add_one_le_of_lt")
     :le-of-le-of-eq         (n "le_of_le_of_eq")
     :iff-mpr                (n "Iff.mpr")
     :iff-mp                 (n "Iff.mp")
     :eq-symm                (n "Eq.symm")
     :congr-fn               (n "congr")
     :congr-arg              (n "congrArg")
     :nat-le-of-not-lt       (n "Nat.le_of_not_lt")
     :nat-lt-of-not-le       (n "Nat.lt_of_not_le")
     :nat-zero-le            (n "Nat.zero_le")
     :classical-prop-dec     (n "Classical.propDecidable")
     :decidable-by-contra    (n "Decidable.byContradiction")
     :absurd                 (n "absurd")
     :int-inst-le            (n "Int.instLEInt")
     :inst-le-nat            (n "instLENat")
     :inst-lt-nat            (n "instLTNat")
     ;; Nat → Int for atoms
     :nat-succ-le-of-lt      (n "Nat.succ_le_of_lt")
     :nat-lt-of-succ-le      (n "Nat.lt_of_succ_le")
     ;; IntList dot/gcd lemmas for trivial-zero proof
     :intlist-gcd            (n "Lean.Omega.IntList.gcd")
     :intlist-gcd-eq-zero    (n "Lean.Omega.IntList.gcd_eq_zero")
     :intlist-dot-of-left-zero (n "Lean.Omega.IntList.dot_of_left_zero")
     ;; GE/GT conversion
     :ge-iff-le              (n "ge_iff_le")
     :gt-iff-lt              (n "gt_iff_lt")
     :int-inst-lt            (n "Int.instLTInt")
     ;; Eq negation → disjunction
     :int-lt-or-gt-of-ne     (n "Int.lt_or_gt_of_ne")
     :nat-lt-or-gt-of-ne     (n "Nat.lt_or_gt_of_ne")
     :or-elim                (n "Or.elim")
     :false-elim             (n "False.elim")
     ;; Int negation lemmas (Iffs, use with Iff.mp)
     :int-not-lt             (n "Int.not_lt")   ;; ¬(a < b) ↔ (b ≤ a)
     :int-not-le             (n "Int.not_le")   ;; ¬(a ≤ b) ↔ (b < a)
     ;; ¬(P ∧ Q) → ¬P ∨ ¬Q
     :not-and-or             (n "not_and_or")
     ;; ¬(P ∨ Q) → ¬P ∧ ¬Q
     :not-or                 (n "not_or")
     :and-left               (n "And.left")
     :and-right              (n "And.right")
     ;; Nat.sub dichotomy
     :nat-le-total           (n "Nat.le_total")       ;; (m n : Nat) → m ≤ n ∨ n ≤ m
     :int-ofnat-sub          (n "Int.ofNat_sub")       ;; {m n : Nat} → n ≤ m → ↑(m - n) = ↑m - ↑n
     :nat-sub-eq-zero-of-le  (n "Nat.sub_eq_zero_of_le") ;; {n m : Nat} → n ≤ m → m - n = 0
     :and-intro              (n "And.intro")
     ;; Divisibility
     :dvd-name               (n "Dvd.dvd")
     :int-emod-eq-zero-of-dvd (n "Int.emod_eq_zero_of_dvd")   ;; a ∣ b → b % a = 0
     :int-emod-pos-of-not-dvd (n "Int.emod_pos_of_not_dvd")   ;; ¬(a ∣ b) → a = 0 ∨ 0 < b % a
     ;; Iff
     :iff-name               (n "Iff")
     :dec-not-iff            (n "Decidable.not_iff") ;; {b a} [dec a] : ¬(a ↔ b) ↔ (¬a ↔ b)
     :iff-iff-and-or         (n "iff_iff_and_or_not_and_not") ;; (P ↔ Q) ↔ ((P∧Q)∨(¬P∧¬Q))
     ;; Implication
     :not-or-of-imp          (n "Decidable.not_or_of_imp") ;; (P → Q) → ¬P ∨ Q
     :not-imp                (n "not_imp")                 ;; ¬(P → Q) ↔ (P ∧ ¬Q)
     ;; Neg.neg
     :neg-name               (n "Neg.neg")
     :int-inst-neg           (n "Int.instNegInt")
     ;; Div/mod bounds
     :nat-div-mul-le-self    (n "Nat.div_mul_le_self")     ;; (m n) → m / n * n ≤ m
     :nat-mod-lt             (n "Nat.mod_lt")              ;; (x y) → 0 < y → x % y < y
     :int-mul-ediv-self-le   (n "Int.mul_ediv_self_le")    ;; (x k) → k ≠ 0 → k*(x/k) ≤ x
     :int-lt-mul-ediv-self-add (n "Int.lt_mul_ediv_self_add") ;; (x k) → 0 < k → x < k*(x/k)+k
     ;; Dvd proof terms
     :nat-mod-eq-zero-of-dvd (n "Nat.mod_eq_zero_of_dvd")  ;; m ∣ n → n % m = 0
     :nat-emod-pos-of-not-dvd (n "Nat.emod_pos_of_not_dvd") ;; ¬(m ∣ n) → 0 < n % m
     ;; Int.ofNat cast lemma
     :int-ofnat-eq-zero      (n "Int.ofNat.eq_def")   ;; helper
     :nat-cast-nonneg        (n "Int.natCast_nonneg")
     ;; Bmod (hard equality) support
     :bmod-sat               (n "Lean.Omega.bmod_sat")
     :bmod-coeffs            (n "Lean.Omega.bmod_coeffs")
     :bmod-div-term          (n "Lean.Omega.bmod_div_term")
     :intlist-bmod            (n "Lean.Omega.IntList.bmod")
     :coeffs-set              (n "Lean.Omega.Coeffs.set")}))

(def ^:private int-type (e/const' (:int-name omega-names) []))
(def ^:private u1 (lvl/succ lvl/zero))

(defn- nat-to-int
  "Wrap a Nat expression in Int.ofNat."
  [nat-expr]
  (e/app (e/const' (:int-ofnat omega-names) []) nat-expr))

;; ============================================================
;; Lean.Omega data structures mirrored in Clojure
;; ============================================================

;; A LinearCombo: {:const Int, :coeffs [Int ...]}
;; Dense representation: coeffs[i] is the coefficient of atom i
;; Evaluates to: const + Σ coeffs[i] * atoms[i]
;;
;; Solver arithmetic uses auto-promoting ops (*' +' -') to avoid
;; long overflow when tidying is disabled and coefficients grow
;; through Fourier-Motzkin elimination.

;; ============================================================
;; Delegations to cic.tactic.omega.problem
;; (kept as private vars for backward compat with test resolve)
;; ============================================================

(def ^:private safe-abs op/safe-abs)
(def ^:private mk-lc op/mk-lc)
(def ^:private lc-coordinate op/lc-coordinate)
(def ^:private lc-add op/lc-add)
(def ^:private lc-sub op/lc-sub)
(def ^:private lc-negate op/lc-negate)
(def ^:private lc-scale op/lc-scale)
(def ^:private lc-is-zero? op/lc-is-zero?)
(def ^:private lc-clean op/lc-clean)
(def ^:private int-bmod op/int-bmod)
(def ^:private coeffs-bmod op/coeffs-bmod)
(def ^:private min-nat-abs op/min-nat-abs)
(def ^:private max-nat-abs op/max-nat-abs)

(def ^:private mk-constraint op/mk-constraint)
(def ^:private constraint-exact op/constraint-exact)
(def ^:private constraint-geq op/constraint-geq)
(def ^:private constraint-leq op/constraint-leq)
(def ^:private constraint-trivial op/constraint-trivial)
(def ^:private constraint-impossible? op/constraint-impossible?)
(def ^:private constraint-is-exact? op/constraint-is-exact?)
(def ^:private constraint-combine op/constraint-combine)
(def ^:private constraint-combo op/constraint-combo)

(def ^:private justification-assumption op/justification-assumption)
(def ^:private justification-tidy op/justification-tidy)
(def ^:private justification-combine op/justification-combine)
(def ^:private justification-combo op/justification-combo)
(def ^:private justification-bmod op/justification-bmod)
(def ^:private mk-fact op/mk-fact)

(def ^:private gcd-list op/gcd-list)

(defn- tidy-fact
  "Delegate to op/tidy-fact."
  [fact]
  (op/tidy-fact fact))

;; Dead code below replaced by delegation — this block is now unreachable
;; but we keep the comment for the floor-div logic reference
(comment
  "Tidy a fact: divide constraint and coefficients by GCD of coefficients.
   Uses floor division (matching Lean's Int.div) for constraint bounds."
            floor-div (fn [a b]
                        (let [q (quot a b)
                              r (rem a b)]
                          (if (and (not (zero? r)) (not= (neg? a) (neg? b)))
                            (dec q) q)))
            new-constraint {:lower (when-let [l (:lower constraint)]
                                    (- (floor-div (- (long l)) (long g))))
                            :upper (when-let [u (:upper constraint)]
                                    (floor-div (long u) (long g)))}
            'see-op/tidy-fact)

(def ^:private mk-atom-table op/mk-atom-table)

(defn- intern-atom
  "Intern an expression as an atom. Returns [table' idx].
   Also stores the Int version of the atom for proof construction.
   If int-expr is provided, it's used as the Int expression; otherwise
   the expression itself is assumed to be Int."
  ([table st expr] (intern-atom table st expr nil))
  ([table st expr int-expr]
   (let [expr-whnf (#'tc/cached-whnf st expr)]
     (if-let [idx (get (:expr->idx table) expr-whnf)]
       [table idx]
       (let [match (some (fn [[e idx]]
                           (when (tc/is-def-eq st e expr-whnf) idx))
                         (:expr->idx table))]
         (if match
           [table match]
           (let [idx (:next-idx table)
                 ;; Store Int version: if provided use it, else wrap Nat in Int.ofNat
                 int-e (or int-expr (nat-to-int expr-whnf))
                 table' (-> table
                            (assoc-in [:expr->idx expr-whnf] idx)
                            (assoc-in [:idx->expr idx] expr-whnf)
                            (assoc-in [:idx->int-expr idx] int-e)
                            (update :next-idx inc))]
             [table' idx])))))))

;; ============================================================
;; Eval proof construction (asLinearCombo equivalent)
;; ============================================================

;; An eval proof is a delayed function: atoms-expr → proof that lc.eval atoms = original_expr
;; Used for building assumption proofs for non-ground goals.
;; The "original_expr" is an Int expression.

(declare to-lean-linear-combo)

(defn- mk-eq-refl-int
  "Build @Eq.refl.{1} Int a : a = a"
  [a]
  (e/app* (e/const' (name/from-string "Eq.refl") [u1]) int-type a))

(defn- mk-eq-symm
  "Build @Eq.symm.{1} Int a b prf : b = a
   given prf : a = b"
  [a b prf]
  (e/app* (e/const' (:eq-symm omega-names) [u1]) int-type a b prf))

(defn- mk-eq-trans
  "Build @Eq.trans.{1} Int a b c prf1 prf2 : a = c
   given prf1 : a = b, prf2 : b = c"
  [a b c prf1 prf2]
  (e/app* (e/const' (name/from-string "Eq.trans") [u1]) int-type a b c prf1 prf2))

(defn- mk-int-hadd
  "Build HAdd.hAdd Int Int Int instHAddInt."
  []
  (e/app* (e/const' (:hadd omega-names) [lvl/zero lvl/zero lvl/zero])
          int-type int-type int-type
          (e/app* (e/const' (name/from-string "instHAdd") [lvl/zero])
                  int-type (e/const' (name/from-string "Int.instAdd") []))))

(defn- mk-int-hsub
  "Build HSub.hSub Int Int Int instHSubInt."
  []
  (e/app* (e/const' (:hsub omega-names) [lvl/zero lvl/zero lvl/zero])
          int-type int-type int-type
          (e/app* (e/const' (name/from-string "instHSub") [lvl/zero])
                  int-type (e/const' (name/from-string "Int.instSub") []))))

(defn- mk-int-hmul
  "Build HMul.hMul Int Int Int instHMulInt."
  []
  (e/app* (e/const' (:hmul omega-names) [lvl/zero lvl/zero lvl/zero])
          int-type int-type int-type
          (e/app* (e/const' (name/from-string "instHMul") [lvl/zero])
                  int-type (e/const' (name/from-string "Int.instMul") []))))

(defn- mk-int-mul
  "Build a * b : Int."
  [a b]
  (e/app* (mk-int-hmul) a b))

(defn- mk-int-lit
  "Build Int.ofNat(n) for a Clojure long."
  [n]
  (e/app (e/const' (:int-ofnat omega-names) []) (e/lit-nat n)))

(defn- mk-int-add
  "Build a + b : Int."
  [a b]
  (e/app* (mk-int-hadd) a b))

(defn- mk-int-sub
  "Build a - b : Int."
  [a b]
  (e/app* (mk-int-hsub) a b))

(defn- mk-int-add-congr
  "Build congruence proof for Int addition.
   From prf1 : a1 = a2 and prf2 : b1 = b2, produce a1 + b1 = a2 + b2.
   congrArg.{u,v} : {α : Sort u} → {β : Sort v} → {a1 a2 : α} → (f : α → β) → (h : a1 = a2) → f a1 = f a2
   congr.{u,v} : {α : Sort u} → {β : Sort v} → {f1 f2 : α → β} → {a1 a2 : α} → (hf : f1 = f2) → (ha : a1 = a2) → f1 a1 = f2 a2"
  [a1 a2 b1 b2 prf1 prf2]
  (let [hadd-fn (mk-int-hadd)
        int-to-int (e/arrow int-type int-type)
        ;; congrArg : {Int} → {Int→Int} → {a1} → {a2} → hadd → prf1 : hadd a1 = hadd a2
        step1 (e/app* (e/const' (:congr-arg omega-names) [u1 u1])
                      int-type     ;; α = Int
                      int-to-int   ;; β = Int → Int
                      a1 a2        ;; {a1} {a2}
                      hadd-fn      ;; f = hadd
                      prf1)        ;; h : a1 = a2
        ;; congr : {Int} → {Int} → {hadd a1} → {hadd a2} → {b1} → {b2} → step1 → prf2
        step2 (e/app* (e/const' (:congr-fn omega-names) [u1 u1])
                      int-type     ;; α = Int
                      int-type     ;; β = Int  (result type)
                      (e/app hadd-fn a1) ;; f1 = hadd a1
                      (e/app hadd-fn a2) ;; f2 = hadd a2
                      b1 b2        ;; {a1} {a2} in congr
                      step1        ;; hf : hadd a1 = hadd a2
                      prf2)]       ;; ha : b1 = b2
    step2))

(defn- mk-int-sub-congr
  "Build congruence proof for Int subtraction.
   From prf1 : a1 = a2 and prf2 : b1 = b2, produce a1 - b1 = a2 - b2."
  [a1 a2 b1 b2 prf1 prf2]
  (let [hsub-fn (mk-int-hsub)
        int-to-int (e/arrow int-type int-type)
        step1 (e/app* (e/const' (:congr-arg omega-names) [u1 u1])
                      int-type int-to-int a1 a2 hsub-fn prf1)
        step2 (e/app* (e/const' (:congr-fn omega-names) [u1 u1])
                      int-type int-type
                      (e/app hsub-fn a1) (e/app hsub-fn a2)
                      b1 b2 step1 prf2)]
    step2))

;; Eval proof functions return {:proof Expr, :lhs Expr, :rhs Expr}
;; where proof proves lhs = rhs, lhs = lc.eval atoms, rhs = int-expression.

(defn- mk-lc-eval-expr
  "Build the CIC expression: lc.eval atoms"
  [lc atoms-expr]
  (e/app* (e/const' (:linear-combo-eval omega-names) []) (to-lean-linear-combo lc) atoms-expr))

(defn- mk-eval-rfl-proof
  "Build an eval proof by reflexivity (for ground expressions where lc.eval reduces to expr)."
  [lc]
  (fn [atoms-expr]
    (let [eval-expr (mk-lc-eval-expr lc atoms-expr)]
      {:proof (mk-eq-refl-int eval-expr)
       :lhs eval-expr
       :rhs eval-expr})))

(defn- mk-coordinate-eval-proof
  "Build eval proof for a coordinate (atom):
   coordinate_eval i v : (coordinate i).eval v = Coeffs.get v i
   Coeffs.get v i is definitionally equal to atoms[i]."
  [idx]
  (fn [atoms-expr]
    (let [lc (lc-coordinate idx)
          lhs (mk-lc-eval-expr lc atoms-expr)
          rhs (e/app* (e/const' (name/from-string "Lean.Omega.Coeffs.get") [])
                      atoms-expr (e/lit-nat idx))]
      {:proof (e/app* (e/const' (:coordinate-eval omega-names) [])
                      (e/lit-nat idx) atoms-expr)
       :lhs lhs
       :rhs rhs})))

(defn- mk-add-eval-proof
  "Build eval proof for addition.
   Given prf-fn1 : l1.eval atoms = e1 and prf-fn2 : l2.eval atoms = e2,
   produce: (l1 + l2).eval atoms = e1 + e2.
   Chain: Eq.trans (add_eval) (congr prf1 prf2)"
  [lc1 lc2 proof-fn1 proof-fn2]
  (fn [atoms-expr]
    (let [lc1-expr (to-lean-linear-combo lc1)
          lc2-expr (to-lean-linear-combo lc2)
          result-lc (lc-add lc1 lc2)
          result-lhs (mk-lc-eval-expr result-lc atoms-expr)
          ;; add_eval l1 l2 v : (l1 + l2).eval v = l1.eval v + l2.eval v
          eval1 (mk-lc-eval-expr lc1 atoms-expr)
          eval2 (mk-lc-eval-expr lc2 atoms-expr)
          mid-expr (mk-int-add eval1 eval2)
          add-eval-prf (e/app* (e/const' (:add-eval omega-names) []) lc1-expr lc2-expr atoms-expr)
          ;; Get proofs and values from sub-proofs
          p1 (if (fn? proof-fn1) (proof-fn1 atoms-expr) proof-fn1)
          p2 (if (fn? proof-fn2) (proof-fn2 atoms-expr) proof-fn2)
          rhs1 (:rhs p1) rhs2 (:rhs p2)
          result-rhs (mk-int-add rhs1 rhs2)
          ;; congr proof: l1.eval + l2.eval = rhs1 + rhs2
          congr-prf (mk-int-add-congr eval1 rhs1 eval2 rhs2 (:proof p1) (:proof p2))]
      ;; Chain: (l1+l2).eval = l1.eval + l2.eval = rhs1 + rhs2
      {:proof (mk-eq-trans result-lhs mid-expr result-rhs add-eval-prf congr-prf)
       :lhs result-lhs
       :rhs result-rhs})))

(defn- mk-sub-eval-proof
  "Build eval proof for subtraction.
   Given prf-fn1 : l1.eval atoms = e1 and prf-fn2 : l2.eval atoms = e2,
   produce: (l1 - l2).eval atoms = e1 - e2."
  [lc1 lc2 proof-fn1 proof-fn2]
  (fn [atoms-expr]
    (let [lc1-expr (to-lean-linear-combo lc1)
          lc2-expr (to-lean-linear-combo lc2)
          result-lc (lc-sub lc1 lc2)
          result-lhs (mk-lc-eval-expr result-lc atoms-expr)
          eval1 (mk-lc-eval-expr lc1 atoms-expr)
          eval2 (mk-lc-eval-expr lc2 atoms-expr)
          mid-expr (mk-int-sub eval1 eval2)
          sub-eval-prf (e/app* (e/const' (:sub-eval omega-names) []) lc1-expr lc2-expr atoms-expr)
          p1 (if (fn? proof-fn1) (proof-fn1 atoms-expr) proof-fn1)
          p2 (if (fn? proof-fn2) (proof-fn2 atoms-expr) proof-fn2)
          rhs1 (:rhs p1) rhs2 (:rhs p2)
          result-rhs (mk-int-sub rhs1 rhs2)
          congr-prf (mk-int-sub-congr eval1 rhs1 eval2 rhs2 (:proof p1) (:proof p2))]
      {:proof (mk-eq-trans result-lhs mid-expr result-rhs sub-eval-prf congr-prf)
       :lhs result-lhs
       :rhs result-rhs})))

(defn- mk-neg-eval-proof
  "Build eval proof for negation.
   Given prf-fn : l.eval atoms = e, produce: (-l).eval atoms = -e."
  [lc proof-fn]
  (fn [atoms-expr]
    (let [result-lc (lc-negate lc)
          result-lhs (mk-lc-eval-expr result-lc atoms-expr)
          eval1 (mk-lc-eval-expr lc atoms-expr)
          lc-expr (to-lean-linear-combo lc)
          neg-eval-prf (e/app* (e/const' (:neg-eval omega-names) []) lc-expr atoms-expr)
          p1 (if (fn? proof-fn) (proof-fn atoms-expr) proof-fn)
          rhs1 (:rhs p1)
          ;; neg-eval: (-lc).eval atoms = -(lc.eval atoms)
          ;; p1.proof: lc.eval atoms = rhs1
          ;; We need: (-lc).eval atoms = -rhs1
          ;; congrArg (Neg.neg Int instNegInt) p1.proof : -(lc.eval atoms) = -(rhs1)
          neg-rhs (e/app* (e/const' (:neg-name omega-names) [lvl/zero])
                          int-type (e/const' (:int-inst-neg omega-names) []) rhs1)
          neg-eval1 (e/app* (e/const' (:neg-name omega-names) [lvl/zero])
                            int-type (e/const' (:int-inst-neg omega-names) []) eval1)
          neg-fn (e/lam "_" int-type
                        (e/app* (e/const' (:neg-name omega-names) [lvl/zero])
                                int-type (e/const' (:int-inst-neg omega-names) []) (e/bvar 0))
                        :default)
          congr-prf (e/app* (e/const' (:congr-arg omega-names) [u1 u1])
                            int-type int-type eval1 rhs1 neg-fn (:proof p1))
          result-rhs neg-rhs]
      {:proof (mk-eq-trans result-lhs neg-eval1 result-rhs neg-eval-prf congr-prf)
       :lhs result-lhs
       :rhs result-rhs})))

(defn- mk-nat-hadd
  "Build HAdd.hAdd Nat Nat Nat instHAddNat a b."
  [a b]
  (e/app* (e/const' (:hadd omega-names) [lvl/zero lvl/zero lvl/zero])
          (e/const' (:nat-name omega-names) [])
          (e/const' (:nat-name omega-names) [])
          (e/const' (:nat-name omega-names) [])
          (e/app* (e/const' (name/from-string "instHAdd") [lvl/zero])
                  (e/const' (:nat-name omega-names) [])
                  (e/const' (name/from-string "instAddNat") []))
          a b))

(defn- mk-nat-hmul
  "Build HMul.hMul Nat Nat Nat instHMulNat a b."
  [a b]
  (e/app* (e/const' (:hmul omega-names) [lvl/zero lvl/zero lvl/zero])
          (e/const' (:nat-name omega-names) [])
          (e/const' (:nat-name omega-names) [])
          (e/const' (:nat-name omega-names) [])
          (e/app* (e/const' (name/from-string "instHMul") [lvl/zero])
                  (e/const' (:nat-name omega-names) [])
                  (e/const' (name/from-string "instMulNat") []))
          a b))

(defn- mk-nat-ofnat-lit
  "Build OfNat.ofNat Nat k (instOfNatNat k) for a ground literal k."
  [k]
  (e/app* (e/const' (:ofnat omega-names) [lvl/zero])
          (e/const' (:nat-name omega-names) [])
          (e/lit-nat k)
          (e/app (e/const' (name/from-string "instOfNatNat") []) (e/lit-nat k))))

(defn- mk-eq-trans-nat
  "Build @Eq.trans.{1} Nat a b c prf1 prf2 : a = c"
  [a b c prf1 prf2]
  (e/app* (e/const' (:eq-trans omega-names) [u1])
          (e/const' (:nat-name omega-names) []) a b c prf1 prf2))

(defn- mk-eq-symm-nat
  "Build @Eq.symm.{1} Nat a b prf : b = a"
  [a b prf]
  (e/app* (e/const' (:eq-symm omega-names) [u1])
          (e/const' (:nat-name omega-names) []) a b prf))

(defn- mk-congr-arg-nat
  "Build congrArg.{1,1} Nat Nat a1 a2 f prf : f a1 = f a2
   given prf : a1 = a2"
  [a1 a2 f prf]
  (e/app* (e/const' (:congr-arg omega-names) [u1 u1])
          (e/const' (:nat-name omega-names) [])
          (e/const' (:nat-name omega-names) [])
          a1 a2 f prf))

(defn- mk-nat-add-chain
  "Build the Nat expression: var + var + ... + var (k times) using HAdd.
   Returns var for k=1."
  [var-nat k]
  (loop [i 1 acc var-nat]
    (if (>= i k)
      acc
      (recur (inc i) (mk-nat-hadd acc var-nat)))))

(defn- mk-right-mul-expand
  "Build proof: HMul var (OfNat k) = var + var + ... + var (k times).
   Returns {:proof Expr, :lhs Expr (the HMul), :rhs Expr (the add chain)}.
   Uses Nat.mul_one for k=1, Nat.mul_two for k=2,
   Nat.mul_succ var (k-1) + recursive proof for k>=3."
  [var-nat k]
  (let [lhs (mk-nat-hmul var-nat (mk-nat-ofnat-lit k))]
    (cond
      (== k 1)
      ;; Nat.mul_one var : var * 1 = var
      {:proof (e/app (e/const' (name/from-string "Nat.mul_one") []) var-nat)
       :lhs lhs
       :rhs var-nat}

      (== k 2)
      ;; Nat.mul_two var : var * 2 = var + var
      (let [rhs (mk-nat-hadd var-nat var-nat)]
        {:proof (e/app (e/const' (name/from-string "Nat.mul_two") []) var-nat)
         :lhs lhs
         :rhs rhs})

      :else
      ;; Nat.mul_succ var (k-1) : var * succ(k-1) = var * (k-1) + var
      ;; Since succ(OfNat (k-1)) is def-eq to OfNat k, this proves var * k = var * (k-1) + var
      (let [sub (mk-right-mul-expand var-nat (dec k))
            ;; mul_succ var (OfNat (k-1)) : HMul var (succ(OfNat(k-1))) = HMul var (OfNat(k-1)) + var
            mul-succ-prf (e/app* (e/const' (name/from-string "Nat.mul_succ") [])
                                 var-nat (mk-nat-ofnat-lit (dec k)))
            ;; sub.proof : HMul var (k-1) = add-chain_{k-1}
            ;; congrArg (fun x => HAdd x var) sub.proof : HAdd (HMul var (k-1)) var = HAdd add-chain var
            hadd-var-fn (e/lam nil (e/const' (:nat-name omega-names) [])
                              (mk-nat-hadd (e/bvar 0) (e/lift var-nat 1 0))
                              :default)
            congr-prf (mk-congr-arg-nat (:lhs sub) (:rhs sub) hadd-var-fn (:proof sub))
            ;; mid = HAdd (HMul var (k-1)) var = HAdd (lhs of sub) var
            mid (mk-nat-hadd (:lhs sub) var-nat)
            ;; result rhs = HAdd add-chain_{k-1} var
            new-rhs (mk-nat-hadd (:rhs sub) var-nat)]
        {:proof (mk-eq-trans-nat lhs mid new-rhs mul-succ-prf congr-prf)
         :lhs lhs
         :rhs new-rhs}))))

(defn- mk-nat-mul-expand-proof
  "Build a Nat-level proof that mul-expr = var + var + ... + var (k times).
   literal-pos is :left (k * var, e.g. Nat.mul k var) or :right (var * k).
   k must be >= 2. Returns nil for k < 2.

   For :right: uses Nat.mul_succ chain directly.
   For :left: uses Nat.mul_comm k var, then the :right chain."
  [var-nat k literal-pos]
  (when (>= k 2)
    (case literal-pos
      :right
      ;; Direct: var * k = var + var + ... + var
      (let [{:keys [proof rhs]} (mk-right-mul-expand var-nat k)]
        proof)

      :left
      ;; k * var = var * k = var + var + ... + var
      ;; Step 1: Nat.mul_comm (OfNat k) var : HMul (OfNat k) var = HMul var (OfNat k)
      (let [k-expr (mk-nat-ofnat-lit k)
            comm-prf (e/app* (e/const' (name/from-string "Nat.mul_comm") [])
                             k-expr var-nat)
            ;; Step 2: right-chain proves HMul var k = add-chain
            right (mk-right-mul-expand var-nat k)
            ;; Chain: HMul k var = HMul var k = add-chain
            lhs (mk-nat-hmul k-expr var-nat)]
        (mk-eq-trans-nat lhs (:lhs right) (:rhs right) comm-prf (:proof right))))))

(defn- mk-scale-eval-proof
  "Build eval proof for scalar multiplication.
   Strategy: expand k*x as x+x+...+x using mk-add-eval-proof, then bridge to
   Int.ofNat(original_mul_expr) using Nat.mul_succ/Nat.mul_comm chains.

   The proof chain:
   1. lc.eval atoms = rhs_a + rhs_a + ...           (by repeated add_eval)
   2. rhs_a + rhs_a + ... defEq Int.ofNat(a+a+...)  (by kernel reduction)
   3. Int.ofNat(a+a+...) = Int.ofNat(mul_expr)       (by congrArg Int.ofNat (Eq.symm bridge))
   Final: lc.eval atoms = Int.ofNat(mul_expr)  via Eq.trans.

   Parameters:
   - lc, k, proof-fn: as before
   - var-nat-expr: the Nat expression for the variable (a)
   - original-nat-expr: the original Nat mul expression (a*k or k*a)
   - literal-pos: :left if literal is first arg (k*a), :right if second (a*k)"
  [lc k proof-fn var-nat-expr original-nat-expr literal-pos]
  (cond
    (zero? k)
    (mk-eval-rfl-proof (mk-lc 0))

    (== k 1)
    proof-fn

    :else
    ;; Step 1: Build repeated addition eval proof
    (let [add-prf (loop [i 1 acc-lc lc acc-proof proof-fn]
                    (if (>= i k)
                      acc-proof
                      (recur (inc i) (lc-add acc-lc lc)
                             (mk-add-eval-proof acc-lc lc acc-proof proof-fn))))
          ;; Step 2: Build Nat-level bridge proof: mul_expr = a+a+...+a
          nat-bridge (mk-nat-mul-expand-proof var-nat-expr k literal-pos)]
      (if (nil? nat-bridge)
        ;; Should not happen for k >= 2, but fall back just in case
        add-prf
        (let [original-int (nat-to-int original-nat-expr)
              nat-add-expr (mk-nat-add-chain var-nat-expr k)]
          (fn [atoms-expr]
            (let [p-add (if (fn? add-prf) (add-prf atoms-expr) add-prf)
                  add-rhs (:rhs p-add)
                  add-lhs (:lhs p-add)
                  ;; nat-bridge : mul_expr = a+a+... (Nat level)
                  ;; congrArg Int.ofNat nat-bridge : Int.ofNat(mul_expr) = Int.ofNat(a+a+...)
                  congr-proof (e/app* (e/const' (:congr-arg omega-names) [u1 u1])
                                      (e/const' (:nat-name omega-names) [])
                                      int-type
                                      original-nat-expr  ;; a1 = mul_expr
                                      nat-add-expr        ;; a2 = a+a+...
                                      (e/const' (:int-ofnat omega-names) [])
                                      nat-bridge)
                  ;; Eq.symm : Int.ofNat(a+a+...) = Int.ofNat(mul_expr)
                  bridge-proof (mk-eq-symm (nat-to-int original-nat-expr)
                                           (nat-to-int nat-add-expr)
                                           congr-proof)
                  ;; Final: Eq.trans p-add.proof bridge-proof
                  final-proof (mk-eq-trans add-lhs add-rhs original-int
                                           (:proof p-add) bridge-proof)]
              {:proof final-proof
               :lhs add-lhs
               :rhs original-int})))))))

;; ============================================================
;; Reification: CIC expr → LinearCombo + eval proof
;; ============================================================
;;
;; reify-term returns [atom-table linear-combo eval-proof-fn]
;; where eval-proof-fn : atoms-expr → proof of (lc.eval atoms = int-version-of-expr)

(defn- try-match-head [st expr]
  (let [[head args] (e/get-app-fn-args expr)]
    (if (e/const? head)
      [(e/const-name head) (e/const-levels head) (vec args)]
      (let [w (#'tc/cached-whnf st expr)
            [whead wargs] (e/get-app-fn-args w)]
        (when (e/const? whead)
          [(e/const-name whead) (e/const-levels whead) (vec wargs)])))))

(declare reify-term)

(defn- reify-term
  "Reify a CIC term into a LinearCombo (dense coefficients).
   Returns [atom-table linear-combo eval-proof-fn] where
   eval-proof-fn : atoms-expr → proof of (lc.eval atoms = Int-version-of-expr).
   For ground constants, eval-proof-fn uses rfl (definitional equality).
   For atoms, uses coordinate_eval."
  [st table expr]
  ;; Pre-WHNF check for Nat arithmetic ops (WHNF unfolds them to brecOn)
  (or (when (e/app? expr)
        (let [[head args] (e/get-app-fn-args expr)
              head-name (when (e/const? head) (e/const-name head))]
          (cond
            ;; Int.ofNat(x) → reify x as Nat (reuses Nat-level atoms)
            ;; This ensures ↑(a-b) creates the same atom as bare Nat.sub a b,
            ;; and ↑a creates the same atom as bare a.
            (and (= head-name (:int-ofnat omega-names)) (= 1 (count args)))
            (reify-term st table (nth args 0))

            ;; HSub.hSub _ _ _ _ a b → a - b (pre-WHNF to avoid unfolding to Int.sub)
            (and (= head-name (:hsub omega-names)) (= 6 (count args)))
            (let [[table' lc-a prf-a] (reify-term st table (nth args 4))
                  [table'' lc-b prf-b] (reify-term st table' (nth args 5))]
              [table'' (lc-sub lc-a lc-b) (mk-sub-eval-proof lc-a lc-b prf-a prf-b)])

            ;; HAdd.hAdd _ _ _ _ a b → a + b (pre-WHNF)
            (and (= head-name (:hadd omega-names)) (= 6 (count args)))
            (let [[table' lc-a prf-a] (reify-term st table (nth args 4))
                  [table'' lc-b prf-b] (reify-term st table' (nth args 5))]
              [table'' (lc-add lc-a lc-b) (mk-add-eval-proof lc-a lc-b prf-a prf-b)])

            ;; Nat.sub a b → ground or atom with dichotomy tag
            (and (= head-name (:nat-sub omega-names)) (= 2 (count args)))
            (let [a-whnf (#'tc/cached-whnf st (nth args 0))
                  b-whnf (#'tc/cached-whnf st (nth args 1))]
              (if (and (e/lit-nat? a-whnf) (e/lit-nat? b-whnf))
                (let [lc (mk-lc (max 0 (- (e/lit-nat-val a-whnf) (e/lit-nat-val b-whnf))))]
                  [table lc (mk-eval-rfl-proof lc)])
                (let [[table' idx] (intern-atom table st expr)
                      table' (assoc-in table' [:nat-sub-atoms idx]
                                       {:a (nth args 0) :b (nth args 1)})]
                  [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)])))

            ;; Nat.add a b → a + b
            (and (= head-name (:nat-add omega-names)) (= 2 (count args)))
            (let [[table' lc-a prf-a] (reify-term st table (nth args 0))
                  [table'' lc-b prf-b] (reify-term st table' (nth args 1))]
              [table'' (lc-add lc-a lc-b) (mk-add-eval-proof lc-a lc-b prf-a prf-b)])

            ;; Nat.succ n → n + 1
            (and (= head-name (:nat-succ omega-names)) (= 1 (count args)))
            (let [[table' lc prf] (reify-term st table (nth args 0))
                  one-lc (mk-lc 1)
                  result-lc (lc-add lc one-lc)]
              [table' result-lc (mk-add-eval-proof lc one-lc prf (mk-eval-rfl-proof one-lc))])

            ;; Nat.mul a b → handle if one operand is ground
            (and (= head-name (:nat-mul omega-names)) (= 2 (count args)))
            (let [a-whnf (#'tc/cached-whnf st (nth args 0))
                  b-whnf (#'tc/cached-whnf st (nth args 1))]
              (cond
                (e/lit-nat? a-whnf)
                (let [[table' lc-b prf-b] (reify-term st table (nth args 1))
                      k (e/lit-nat-val a-whnf)
                      result-lc (lc-scale lc-b k)]
                  [table' result-lc (mk-scale-eval-proof lc-b k prf-b (nth args 1) expr :left)])
                (e/lit-nat? b-whnf)
                (let [[table' lc-a prf-a] (reify-term st table (nth args 0))
                      k (e/lit-nat-val b-whnf)
                      result-lc (lc-scale lc-a k)]
                  [table' result-lc (mk-scale-eval-proof lc-a k prf-a (nth args 0) expr :right)])
                :else nil))  ;; fall through to WHNF path

            ;; HMul.hMul _ _ _ _ a b → a * b (pre-WHNF, handles ground operand)
            (and (= head-name (:hmul omega-names)) (= 6 (count args)))
            (let [a-whnf (#'tc/cached-whnf st (nth args 4))
                  b-whnf (#'tc/cached-whnf st (nth args 5))]
              (cond
                (e/lit-nat? a-whnf)
                (let [[table' lc-b prf-b] (reify-term st table (nth args 5))
                      k (e/lit-nat-val a-whnf)
                      result-lc (lc-scale lc-b k)]
                  [table' result-lc (mk-scale-eval-proof lc-b k prf-b (nth args 5) expr :left)])
                (e/lit-nat? b-whnf)
                (let [[table' lc-a prf-a] (reify-term st table (nth args 4))
                      k (e/lit-nat-val b-whnf)
                      result-lc (lc-scale lc-a k)]
                  [table' result-lc (mk-scale-eval-proof lc-a k prf-a (nth args 4) expr :right)])
                :else nil))  ;; fall through to WHNF path

            ;; HDiv.hDiv _ _ _ _ a b → intern as atom, tag for bounds generation
            (and (= head-name (:hdiv omega-names)) (= 6 (count args)))
            (let [type-arg (nth args 0)
                  type-whnf (#'tc/cached-whnf st type-arg)
                  type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                  a-arg (nth args 4) b-arg (nth args 5)
                  b-whnf (#'tc/cached-whnf st b-arg)
                  [table' idx] (intern-atom table st expr)
                  ;; Tag div atoms for bounds generation (only for literal divisor > 0)
                  table' (if (and (e/lit-nat? b-whnf) (pos? (e/lit-nat-val b-whnf)))
                           (assoc-in table' [:div-atoms idx]
                                     {:a a-arg :b b-arg :type-name type-name :expr expr})
                           table')]
              [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)])

            ;; HMod.hMod _ _ _ _ a b → decompose to a - b*(a/b) if b is ground
            (and (= head-name (:hmod omega-names)) (= 6 (count args)))
            (let [b-whnf (#'tc/cached-whnf st (nth args 5))]
              (when (and (e/lit-nat? b-whnf) (pos? (e/lit-nat-val b-whnf)))
                ;; a % b = a - b * (a / b)
                ;; Reify a, create div atom for a/b, compute a - b*div_atom
                (let [a-arg (nth args 4) b-arg (nth args 5)
                      [table' lc-a prf-a] (reify-term st table a-arg)
                      ;; Build the div expression with same type args
                      div-expr (e/app* (e/const' (:hdiv omega-names) [lvl/zero lvl/zero lvl/zero])
                                       (nth args 0) (nth args 1) (nth args 2)
                                       (e/app* (e/const' (name/from-string "instHDiv") [lvl/zero])
                                               (nth args 0)
                                               ;; Need type-specific div instance
                                               (let [type-whnf (#'tc/cached-whnf st (nth args 0))
                                                     tn (when (e/const? type-whnf) (e/const-name type-whnf))]
                                                 (if (= tn (:nat-name omega-names))
                                                   (e/const' (name/from-string "Nat.instDiv") [])
                                                   (e/const' (name/from-string "Int.instDiv") []))))
                                       a-arg b-arg)
                      [table'' lc-div prf-div] (reify-term st table' div-expr)
                      k (e/lit-nat-val b-whnf)
                      lc-bq (lc-scale lc-div k)
                      ;; Build b * div_expr as the "original" Nat mul expression
                      mul-expr (e/app* (e/const' (:hmul omega-names) [lvl/zero lvl/zero lvl/zero])
                                       (nth args 0) (nth args 1) (nth args 2)
                                       (e/app* (e/const' (name/from-string "instHMul") [lvl/zero])
                                               (nth args 0)
                                               (let [type-whnf (#'tc/cached-whnf st (nth args 0))
                                                     tn (when (e/const? type-whnf) (e/const-name type-whnf))]
                                                 (if (= tn (:nat-name omega-names))
                                                   (e/const' (name/from-string "instMulNat") [])
                                                   (e/const' (name/from-string "Int.instMul") []))))
                                       b-arg div-expr)
                      prf-bq (mk-scale-eval-proof lc-div k prf-div div-expr mul-expr :left)
                      result-lc (lc-sub lc-a lc-bq)]
                  [table'' result-lc (mk-sub-eval-proof lc-a lc-bq prf-a prf-bq)])))

            ;; Neg.neg α inst a → -a (pre-WHNF to avoid unfolding)
            (and (= head-name (:neg-name omega-names)) (= 3 (count args)))
            (let [[table' lc prf] (reify-term st table (nth args 2))]
              [table' (lc-negate lc) (mk-neg-eval-proof lc prf)])

            ;; Nat.zero → 0
            (and (e/const? head) (= head-name (:nat-zero omega-names)) (= 0 (count args)))
            (let [lc (mk-lc 0)]
              [table lc (mk-eval-rfl-proof lc)]))))
      (let [expr-whnf (#'tc/cached-whnf st expr)
            N (:nat-name omega-names)]
        (cond
      ;; Nat literal
      (e/lit-nat? expr-whnf)
      (let [lc (mk-lc (e/lit-nat-val expr-whnf))]
        [table lc (mk-eval-rfl-proof lc)])

      ;; Nat.zero
      (and (e/const? expr-whnf) (= (e/const-name expr-whnf) (:nat-zero omega-names)))
      (let [lc (mk-lc 0)]
        [table lc (mk-eval-rfl-proof lc)])

      ;; Application
      (e/app? expr-whnf)
      (let [matched (try-match-head st expr-whnf)]
        (if-not matched
          (let [[table' idx] (intern-atom table st expr-whnf)]
            [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)])
          (let [[head-name _ args] matched]
            (cond
              ;; Nat.succ n → n + 1
              (and (= head-name (:nat-succ omega-names)) (= 1 (count args)))
              (let [[table' lc prf] (reify-term st table (nth args 0))
                    one-lc (mk-lc 1)
                    result-lc (lc-add lc one-lc)]
                [table' result-lc (mk-add-eval-proof lc one-lc prf (mk-eval-rfl-proof one-lc))])

              ;; Nat.add a b → a + b
              (and (= head-name (:nat-add omega-names)) (= 2 (count args)))
              (let [[table' lc-a prf-a] (reify-term st table (nth args 0))
                    [table'' lc-b prf-b] (reify-term st table' (nth args 1))]
                [table'' (lc-add lc-a lc-b) (mk-add-eval-proof lc-a lc-b prf-a prf-b)])

              ;; HAdd.hAdd _ _ _ _ a b → a + b
              (and (= head-name (:hadd omega-names)) (= 6 (count args)))
              (let [[table' lc-a prf-a] (reify-term st table (nth args 4))
                    [table'' lc-b prf-b] (reify-term st table' (nth args 5))]
                [table'' (lc-add lc-a lc-b) (mk-add-eval-proof lc-a lc-b prf-a prf-b)])

              ;; Nat.sub a b → ground evaluate or atom
              (and (= head-name (:nat-sub omega-names)) (= 2 (count args)))
              (let [a-whnf (#'tc/cached-whnf st (nth args 0))
                    b-whnf (#'tc/cached-whnf st (nth args 1))]
                (if (and (e/lit-nat? a-whnf) (e/lit-nat? b-whnf))
                  (let [lc (mk-lc (max 0 (- (e/lit-nat-val a-whnf) (e/lit-nat-val b-whnf))))]
                    [table lc (mk-eval-rfl-proof lc)])
                  ;; Non-ground: intern as atom, tag for dichotomy generation
                  (let [[table' idx] (intern-atom table st expr-whnf)
                        table' (assoc-in table' [:nat-sub-atoms idx]
                                         {:a (nth args 0) :b (nth args 1)})]
                    [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)])))

              ;; HSub.hSub _ _ _ _ a b → a - b (Int subtraction)
              (and (= head-name (:hsub omega-names)) (= 6 (count args)))
              (let [[table' lc-a prf-a] (reify-term st table (nth args 4))
                    [table'' lc-b prf-b] (reify-term st table' (nth args 5))]
                [table'' (lc-sub lc-a lc-b) (mk-sub-eval-proof lc-a lc-b prf-a prf-b)])

              ;; Multiplication: Nat.mul or HMul
              (and (or (= head-name (:nat-mul omega-names))
                       (= head-name (:hmul omega-names))))
              (let [[a b] (if (= head-name (:hmul omega-names))
                            [(nth args 4) (nth args 5)]
                            [(nth args 0) (nth args 1)])
                    a-whnf (#'tc/cached-whnf st a)
                    b-whnf (#'tc/cached-whnf st b)]
                (cond
                  ;; Both ground: evaluate and use constant
                  (and (e/lit-nat? a-whnf) (e/lit-nat? b-whnf))
                  (let [val (* (e/lit-nat-val a-whnf) (e/lit-nat-val b-whnf))
                        lc (mk-lc val)]
                    [table lc (mk-eval-rfl-proof lc)])
                  (e/lit-nat? a-whnf)
                  (let [[table' lc-b prf-b] (reify-term st table b)
                        k (e/lit-nat-val a-whnf)
                        result-lc (lc-scale lc-b k)]
                    [table' result-lc (mk-scale-eval-proof lc-b k prf-b b expr-whnf :left)])
                  (e/lit-nat? b-whnf)
                  (let [[table' lc-a prf-a] (reify-term st table a)
                        k (e/lit-nat-val b-whnf)
                        result-lc (lc-scale lc-a k)]
                    [table' result-lc (mk-scale-eval-proof lc-a k prf-a a expr-whnf :right)])
                  :else
                  (let [[table' idx] (intern-atom table st expr-whnf)]
                    [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)])))

              ;; Ground div/mod
              (and (= head-name (:nat-div omega-names)) (= 2 (count args)))
              (let [a-whnf (#'tc/cached-whnf st (nth args 0))
                    b-whnf (#'tc/cached-whnf st (nth args 1))]
                (if (and (e/lit-nat? a-whnf) (e/lit-nat? b-whnf))
                  (let [bv (e/lit-nat-val b-whnf)
                        lc (mk-lc (if (zero? bv) 0 (quot (e/lit-nat-val a-whnf) bv)))]
                    [table lc (mk-eval-rfl-proof lc)])
                  (let [[table' idx] (intern-atom table st expr-whnf)]
                    [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)])))

              (and (= head-name (:nat-mod omega-names)) (= 2 (count args)))
              (let [a-whnf (#'tc/cached-whnf st (nth args 0))
                    b-whnf (#'tc/cached-whnf st (nth args 1))]
                (if (and (e/lit-nat? a-whnf) (e/lit-nat? b-whnf))
                  (let [bv (e/lit-nat-val b-whnf)
                        lc (mk-lc (if (zero? bv) (e/lit-nat-val a-whnf) (mod (e/lit-nat-val a-whnf) bv)))]
                    [table lc (mk-eval-rfl-proof lc)])
                  (let [[table' idx] (intern-atom table st expr-whnf)]
                    [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)])))

              ;; OfNat.ofNat _ n _ → n
              (and (= head-name (:ofnat omega-names)) (>= (count args) 2))
              (reify-term st table (nth args 1))

              ;; Unknown → atom
              :else
              (let [[table' idx] (intern-atom table st expr-whnf)]
                [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)])))))

      ;; Free variable → atom
      (e/fvar? expr-whnf)
      (let [[table' idx] (intern-atom table st expr-whnf)]
        [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)])

      ;; Constant
      (e/const? expr-whnf)
      (if (= (e/const-name expr-whnf) (:nat-zero omega-names))
        (let [lc (mk-lc 0)]
          [table lc (mk-eval-rfl-proof lc)])
        (let [[table' idx] (intern-atom table st expr-whnf)]
          [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)]))

      ;; Anything else → atom
      :else
      (let [[table' idx] (intern-atom table st expr-whnf)]
        [table' (lc-coordinate idx) (mk-coordinate-eval-proof idx)])))))

;; ============================================================
;; Problem: delegated to cic.tactic.omega.problem
;; ============================================================

(def ^:private mk-problem op/mk-problem)
(def ^:private queue-disjunction op/queue-disjunction)
(def ^:private coeffs-key op/coeffs-key)
(def ^:private all-zero-coeffs? op/all-zero-coeffs?)
(def ^:private constraint-unsat-at-zero? op/constraint-unsat-at-zero?)
(def ^:private is-impossible? op/is-impossible?)
(def ^:private insert-constraint op/insert-constraint)
(def ^:private add-constraint op/add-constraint)

;; ============================================================
;; CIC term builders for Lean.Omega data structures
;; ============================================================

(defn- to-lean-int
  "Build a CIC expression for an Int literal."
  [n]
  (if (>= n 0)
    (e/app (e/const' (name/from-string "Int.ofNat") []) (e/lit-nat n))
    (e/app (e/const' (name/from-string "Int.negSucc") []) (e/lit-nat (dec (- n))))))

(defn- to-lean-coeffs
  "Build a CIC expression for Coeffs (= List Int).
   List.cons.{u} : (α : Sort (u+1)) → ... ; for Int : Type 0, u = 0."
  [coeffs]
  (let [int-t (e/const' (:int-name omega-names) [])]
    (reduce (fn [acc c]
              (e/app* (e/const' (name/from-string "List.cons") [lvl/zero])
                      int-t (to-lean-int c) acc))
            (e/app (e/const' (name/from-string "List.nil") [lvl/zero]) int-t)
            (reverse coeffs))))

(defn- to-lean-option-int
  "Build Option Int expression.
   Option.some.{u} : (α : Sort (u+1)) → α → Option.{u} α
   For α = Int : Type 0 = Sort 1, we need u = 0."
  [v]
  (let [int-t (e/const' (:int-name omega-names) [])]
    (if (nil? v)
      (e/app (e/const' (:option-none omega-names) [lvl/zero]) int-t)
      (e/app* (e/const' (:option-some omega-names) [lvl/zero]) int-t (to-lean-int v)))))

(defn- to-lean-constraint
  "Build a CIC Lean.Omega.Constraint expression."
  [{:keys [lower upper]}]
  (e/app* (e/const' (:constraint-mk omega-names) [])
          (to-lean-option-int lower)
          (to-lean-option-int upper)))

(defn- to-lean-linear-combo
  "Build a CIC Lean.Omega.LinearCombo expression."
  [{:keys [const coeffs]}]
  (e/app* (e/const' (:linear-combo-mk omega-names) [])
          (to-lean-int const)
          (to-lean-coeffs coeffs)))

;; ============================================================
;; Problem: add inequality/equality from reification
;; ============================================================

(defn- mk-int-neg
  "Build the CIC expression for Int negation: @Neg.neg Int Int.instNegInt c"
  [c-cic]
  (e/app* (e/const' (name/from-string "Neg.neg") [lvl/zero])
          int-type
          (e/const' (name/from-string "Int.instNegInt") [])
          c-cic))

(defn- mk-add-inequality-proof
  "Build a delayed proof fn for an inequality assumption.
   Given proof-fn producing `c + dot(x, v) ≥ 0`,
   returns fn that given atoms-expr and num-vars produces {:proof :constraint-cic :coeffs-cic}
   where constraint matches the addInequality_sat result type exactly:
     Constraint.mk (some (-c)) none
   Note: coefficients are NOT padded here — the proof_fn's w argument was built with
   unpadded coefficients. Padding happens via Coeffs.combo's zipWithAll at combo time."
  [const coeffs proof-fn]
  (fn [atoms-expr _num-vars]
    (let [c-cic (to-lean-int const)
          x-cic (to-lean-coeffs coeffs)
          neg-c (mk-int-neg c-cic)
          ;; Constraint as it appears in addInequality_sat's result type
          s-cic (e/app* (e/const' (name/from-string "Lean.Omega.Constraint.mk") [])
                        (e/app* (e/const' (name/from-string "Option.some") [lvl/zero])
                                int-type neg-c)
                        (e/app (e/const' (name/from-string "Option.none") [lvl/zero])
                               int-type))]
      {:proof (e/app* (e/const' (:add-inequality-sat omega-names) [])
                      c-cic x-cic atoms-expr
                      (if (fn? proof-fn) (proof-fn atoms-expr) proof-fn))
       :constraint-cic s-cic
       :coeffs-cic x-cic})))

(defn- mk-add-equality-proof
  "Build a delayed proof fn for an equality assumption.
   Given proof-fn producing `c + dot(x, v) = 0`,
   returns fn that given atoms-expr and num-vars produces {:proof :constraint-cic :coeffs-cic}
   where constraint matches the addEquality_sat result type exactly:
     Constraint.mk (some (-c)) (some (-c))
   Note: coefficients are NOT padded here."
  [const coeffs proof-fn]
  (fn [atoms-expr _num-vars]
    (let [c-cic (to-lean-int const)
          x-cic (to-lean-coeffs coeffs)
          neg-c (mk-int-neg c-cic)
          some-neg-c (e/app* (e/const' (name/from-string "Option.some") [lvl/zero])
                             int-type neg-c)
          s-cic (e/app* (e/const' (name/from-string "Lean.Omega.Constraint.mk") [])
                        some-neg-c some-neg-c)]
      {:proof (e/app* (e/const' (:add-equality-sat omega-names) [])
                      c-cic x-cic atoms-expr
                      (if (fn? proof-fn) (proof-fn atoms-expr) proof-fn))
       :constraint-cic s-cic
       :coeffs-cic x-cic})))

(defn- add-inequality
  "Add: const + dot(coeffs, atoms) >= 0.
   Stored as: coeffs in [-const, infinity).
   proof-fn: delayed fn producing a proof of `const + dot(coeffs, atoms) >= 0`."
  [problem const coeffs proof-fn]
  (op/add-inequality problem const coeffs proof-fn mk-add-inequality-proof))

(defn- add-equality
  "Add: const + dot(coeffs, atoms) = 0.
   Stored as: coeffs in {-const}.
   proof-fn: delayed fn producing a proof of `const + dot(coeffs, atoms) = 0`."
  [problem const coeffs proof-fn]
  (op/add-equality problem const coeffs proof-fn mk-add-equality-proof))

;; ============================================================
;; Equality solving
;; ============================================================

;; ============================================================
;; Solver: delegated to cic.tactic.omega.fm
;; ============================================================

(declare build-atoms-expr)

(defn- mk-bmod-expr
  "Build CIC bmod_div_term expression for hard equality solving."
  [m coeffs table]
  (e/app* (e/const' (:bmod-div-term omega-names) [])
          (e/lit-nat m)
          (to-lean-coeffs coeffs)
          (build-atoms-expr table)))

(defn- run-omega-solver
  "Run the FM omega solver. Returns [table problem]."
  [table problem]
  (fm/solve table problem mk-bmod-expr build-atoms-expr))

;; ============================================================
;; Proof term construction from Justification tree
;; ============================================================

(defn- pad-coeffs
  "Pad a coefficient vector with zeros to length n."
  [coeffs n]
  (let [len (count coeffs)]
    (if (>= len n)
      coeffs
      (vec (concat coeffs (repeat (- n len) 0))))))

(defn- extract-trivial-zero
  "Build a proof of sat'(constraint, zeros, v) = true for a trivial-zero justification,
   using the given `coeffs-expr` CIC expression for the coefficient list.
   This is called from :combine when the right child is :trivial-zero, to ensure
   the coefficient expression matches the left child's (avoiding length mismatches)."
  [justification atoms-expr coeffs-expr]
  (let [s-expr (to-lean-constraint (:constraint justification))
        nat-type (e/const' (:nat-name omega-names) [])
        bool-type (e/const' (:bool-name omega-names) [])
        bool-true (e/const' (:bool-true omega-names) [])
        intlist-type (e/app (e/const' (name/from-string "List") [lvl/zero]) int-type)
        mem-inst (e/app (e/const' (name/from-string "List.instMembership") [lvl/zero]) int-type)
        zero-int (e/app (e/const' (:int-ofnat omega-names) []) (e/lit-nat 0))

        ;; Step 1: Build p = ∀ (x : Int) (_ : x ∈ zeros), x = 0
        mem-of-bvar0 (e/app* (e/const' (name/from-string "Membership.mem") [lvl/zero lvl/zero])
                             int-type intlist-type mem-inst coeffs-expr (e/bvar 0))
        p-prop (e/forall' "x" int-type
                 (e/forall' "_" mem-of-bvar0
                   (e/app* (e/const' (:eq-name omega-names) [u1]) int-type
                           (e/bvar 1) zero-int)
                   :default)
                 :default)

        ;; Step 2: Decidable instance for p
        eq-zero-pred (e/lam "x" int-type
                       (e/app* (e/const' (:eq-name omega-names) [u1]) int-type
                               (e/bvar 0) zero-int)
                       :default)
        dec-pred (e/lam "x" int-type
                   (e/app* (e/const' (name/from-string "Int.decEq") [])
                           (e/bvar 0) zero-int)
                   :default)
        dec-inst (e/app* (e/const' (name/from-string "List.decidableBAll") [lvl/zero])
                         int-type eq-zero-pred dec-pred coeffs-expr)

        ;; Step 3: Prove p via of_decide_eq_true
        decide-expr (e/app* (e/const' (name/from-string "Decidable.decide") [])
                            p-prop dec-inst)
        decide-refl (e/app* (e/const' (:eq-refl omega-names) [u1]) bool-type bool-true)
        h-mem (e/app* (e/const' (name/from-string "of_decide_eq_true") [])
                      p-prop dec-inst decide-refl)

        ;; Step 4: Prove dot(zeros, atoms) = 0 via IntList.dot_of_left_zero
        h-dot (e/app* (e/const' (:intlist-dot-of-left-zero omega-names) [])
                      coeffs-expr atoms-expr h-mem)

        ;; Step 5: congrArg (Constraint.sat s) h-dot : sat(s, dot(...)) = sat(s, 0)
        dot-expr (e/app* (e/const' (:int-list-dot omega-names) []) coeffs-expr atoms-expr)
        sat-fn (e/app (e/const' (:constraint-sat omega-names) []) s-expr)
        h-congr (e/app* (e/const' (:congr-arg omega-names) [u1 u1])
                        int-type bool-type dot-expr zero-int sat-fn h-dot)

        ;; Step 6: sat(s, 0) = true by Eq.refl (ground computation)
        sat-of-dot (e/app sat-fn dot-expr)
        sat-of-zero (e/app sat-fn zero-int)
        h-sat0 (e/app* (e/const' (:eq-refl omega-names) [u1]) bool-type sat-of-zero)

        ;; Step 7: Eq.trans h-congr h-sat0 : sat(s, dot(...)) = true
        h-final (e/app* (e/const' (name/from-string "Eq.trans") [u1])
                        bool-type sat-of-dot sat-of-zero bool-true
                        h-congr h-sat0)]
    {:proof h-final
     :constraint-cic s-expr
     :coeffs-cic coeffs-expr}))

(defn- extract-proof
  "Extract a proof term from a Justification tree.
   `atoms-expr` is the CIC expression for the atoms list (v : List Int).
   `assumptions` is a vector of delayed proof fns.
   `num-vars` is the total number of variables — all coefficient lists are padded to this length.
   Returns {:proof expr :constraint-cic expr :coeffs-cic expr} where:
   - proof is a proof of `s.sat' x v = true`
   - constraint-cic is the CIC expression for `s` as it appears in the proof type
   - coeffs-cic is the CIC expression for `x` as it appears in the proof type
   This ensures parent steps (combo, combine) use the exact type expressions."
  [justification atoms-expr assumptions num-vars]
  (case (:tag justification)
    :assumption
    ;; assumptions[i] is a delayed proof fn returning {:proof :constraint-cic :coeffs-cic}
    ;; The constraint-cic and coeffs-cic match the proof's actual type (from addInequality_sat
    ;; or addEquality_sat), avoiding CIC expression mismatches (e.g. Neg.neg vs Int.ofNat).
    ;; num-vars is passed so coefficients are padded to consistent length.
    (let [proof-fn (nth assumptions (:idx justification))
          result (if (fn? proof-fn) (proof-fn atoms-expr num-vars) proof-fn)]
      (if (map? result)
        result
        ;; Legacy: plain proof expression (shouldn't happen with new proof fns)
        {:proof result
         :constraint-cic (to-lean-constraint (:constraint justification))
         :coeffs-cic (to-lean-coeffs (pad-coeffs (:coeffs justification) num-vars))}))

    :tidy
    ;; tidy_sat : sat' s x v → sat' (tidyConstraint s x) (tidyCoeffs s x) v
    ;; s and x must match the inner proof's actual CIC expressions (not rebuilt from stored data)
    (let [inner (extract-proof (:inner justification) atoms-expr assumptions num-vars)
          ;; Use inner proof's CIC expressions — these match the proof type exactly
          orig-s-cic (:constraint-cic inner)
          orig-x-cic (:coeffs-cic inner)
          proof (e/app* (e/const' (:tidy-sat omega-names) [])
                        orig-s-cic orig-x-cic atoms-expr (:proof inner))]
      {:proof proof
       :constraint-cic (e/app* (e/const' (name/from-string "Lean.Omega.tidyConstraint") [])
                               orig-s-cic orig-x-cic)
       :coeffs-cic (e/app* (e/const' (name/from-string "Lean.Omega.tidyCoeffs") [])
                            orig-s-cic orig-x-cic)})

    :combine
    ;; combine_sat' : sat' s x v → sat' t x v → sat' (s.combine t) x v
    ;; Both children must have the SAME coefficients x. If the right child is :trivial-zero,
    ;; it needs to use the left's coefficients (they may differ in length due to zipWithAll).
    (let [left (extract-proof (:left justification) atoms-expr assumptions num-vars)
          right (if (= :trivial-zero (:tag (:right justification)))
                  ;; Build trivial-zero proof using left's coefficients
                  (extract-trivial-zero (:right justification) atoms-expr (:coeffs-cic left))
                  (extract-proof (:right justification) atoms-expr assumptions num-vars))
          proof (e/app* (e/const' (:combine-sat' omega-names) [])
                        (:constraint-cic left) (:constraint-cic right)
                        (:coeffs-cic left) atoms-expr
                        (:proof left) (:proof right))]
      {:proof proof
       :constraint-cic (e/app* (e/const' (name/from-string "Lean.Omega.Constraint.combine") [])
                               (:constraint-cic left) (:constraint-cic right))
       :coeffs-cic (:coeffs-cic left)})

    :combo
    ;; combo_sat' : ∀ s t a x b y v, sat' s x v → sat' t y v →
    ;;              sat' (combo a s b t) (Coeffs.combo a x b y) v
    (let [{:keys [a left b right]} justification
          left-r (extract-proof left atoms-expr assumptions num-vars)
          right-r (extract-proof right atoms-expr assumptions num-vars)
          a-int (to-lean-int a)
          b-int (to-lean-int b)
          proof (e/app* (e/const' (:combo-sat' omega-names) [])
                        (:constraint-cic left-r) (:constraint-cic right-r)
                        a-int (:coeffs-cic left-r)
                        b-int (:coeffs-cic right-r)
                        atoms-expr
                        (:proof left-r) (:proof right-r))]
      {:proof proof
       :constraint-cic (e/app* (e/const' (name/from-string "Lean.Omega.Constraint.combo") [])
                               a-int (:constraint-cic left-r)
                               b-int (:constraint-cic right-r))
       :coeffs-cic (e/app* (e/const' (name/from-string "Lean.Omega.Coeffs.combo") [])
                            a-int (:coeffs-cic left-r)
                            b-int (:coeffs-cic right-r))})

    :bmod
    ;; bmod_sat : (m : Nat) → (r : Int) → (i : Nat) → (x v : Coeffs) →
    ;;            (h : x.length ≤ i) → (p : Coeffs.get v i = bmod_div_term m x v) →
    ;;            (w : (exact r).sat' x v) → (exact (bmod r m)).sat' (bmod_coeffs m i x) v
    (let [{:keys [inner m r i orig-coeffs]} justification
          inner-r (extract-proof inner atoms-expr assumptions num-vars)
          m-nat (e/lit-nat m)
          r-int (to-lean-int r)
          i-nat (e/lit-nat i)
          ;; Use inner proof's coefficients — must match the proof type exactly
          x-coeffs (:coeffs-cic inner-r)
          nat-type (e/const' (:nat-name omega-names) [])
          bool-type (e/const' (:bool-name omega-names) [])
          bool-true (e/const' (:bool-true omega-names) [])
          ;; h : x.length ≤ i — both are concrete, so prove by decide
          len-expr (e/app (e/const' (name/from-string "List.length") [lvl/zero])
                          int-type x-coeffs)
          le-prop (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                          nat-type (e/const' (:inst-le-nat omega-names) [])
                          len-expr i-nat)
          le-dec (e/app* (e/const' (name/from-string "Nat.decLe") [])
                         len-expr i-nat)
          decide-le (e/app* (e/const' (name/from-string "Decidable.decide") [])
                            le-prop le-dec)
          decide-le-eq (e/app* (e/const' (:eq-name omega-names) [u1])
                               bool-type decide-le bool-true)
          le-refl (e/app* (e/const' (:eq-refl omega-names) [u1]) bool-type bool-true)
          h-le (e/app* (e/const' (name/from-string "of_decide_eq_true") [])
                       le-prop le-dec le-refl)
          ;; p : Coeffs.get v i = bmod_div_term m x v — both reduce to same value, so rfl
          get-vi (e/app* (e/const' (:coeffs-get omega-names) []) atoms-expr i-nat)
          bmod-div (e/app* (e/const' (:bmod-div-term omega-names) [])
                           m-nat x-coeffs atoms-expr)
          p-eq-prop (e/app* (e/const' (:eq-name omega-names) [u1])
                            int-type get-vi bmod-div)
          p-refl (e/app* (e/const' (:eq-refl omega-names) [u1]) int-type get-vi)
          ;; bmod result: (exact (bmod r m)).sat' (bmod_coeffs m i x) v
          new-r (int-bmod r m)]
      {:proof (e/app* (e/const' (:bmod-sat omega-names) [])
                      m-nat r-int i-nat x-coeffs atoms-expr
                      h-le p-refl (:proof inner-r))
       :constraint-cic (to-lean-constraint (constraint-exact (- new-r)))
       :coeffs-cic (e/app* (e/const' (name/from-string "Lean.Omega.Coeffs.bmod_coeffs") [])
                            m-nat i-nat x-coeffs)})

    :trivial-zero
    ;; Delegate to extract-trivial-zero with its own stored coefficients
    (extract-trivial-zero justification atoms-expr
                          (to-lean-coeffs (:coeffs justification)))))

(defn- build-atoms-expr
  "Build the CIC expression for the atoms list: [atom0, atom1, ...] : List Int.
   Uses the Int versions of atoms stored in :idx->int-expr.
   List.cons.{u} : (α : Sort (u+1)) → α → List.{u} α → List.{u} α
   For α = Int : Type 0, u = 0."
  [atom-table]
  (let [n (:next-idx atom-table)
        ;; Build atom expressions, using Int.ofNat(0) as placeholder for missing indices
        zero-int (e/app (e/const' (name/from-string "Int.ofNat") []) (e/lit-nat 0))
        atoms (for [i (range n)]
                (or (get-in atom-table [:idx->int-expr i])
                    (when-let [expr (get-in atom-table [:idx->expr i])]
                      (nat-to-int expr))
                    zero-int))]
    (reduce (fn [acc atom-expr]
              (e/app* (e/const' (name/from-string "List.cons") [lvl/zero])
                      int-type atom-expr acc))
            (e/app (e/const' (name/from-string "List.nil") [lvl/zero]) int-type)
            (reverse atoms))))

(defn- build-decide-proof
  "Build a `decide` proof for a Bool equality proposition.
   of_decide_eq_true : (p : Prop) → (inst : Decidable p) → decide p inst = true → p
   For p = (f x = true), inst = instDecidableEqBool (f x) true."
  [env prop]
  ;; prop is: @Eq Bool expr Bool.true
  ;; Extract expr from prop
  (let [[_head args] (e/get-app-fn-args prop)
        ;; args = [Bool, expr, Bool.true]
        bool-expr (nth args 1)
        bool-true (e/const' (:bool-true omega-names) [])
        bool-type (e/const' (:bool-name omega-names) [])
        ;; Decidable instance: instDecidableEqBool expr true
        dec-inst (e/app* (e/const' (name/from-string "instDecidableEqBool") [])
                         bool-expr bool-true)]
    (e/app* (e/const' (name/from-string "of_decide_eq_true") [])
            prop
            dec-inst
            (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                    bool-type bool-true))))

(defn- prove-false-from-justification
  "Build a proof of False from a Justification proving an impossible constraint.

   Uses: not_sat'_of_isImpossible : isImpossible s → ¬ s.sat' x v
   Which means: isImpossible s → s.sat' x v → False

   We have:
   - sat-proof: proof that s.sat' x v (from Justification tree)
   - impossible-proof: decide proof that isImpossible s = true

   Final term: not_sat'_of_isImpossible s impossible x v sat-proof"
  [env result atoms-expr]
  (let [{:keys [justification constraint coeffs]} (:proof-false result)
        ;; Build the sat' proof from the Justification tree
        ;; Returns {:proof :constraint-cic :coeffs-cic} with CIC expressions matching proof types
        sat-result (extract-proof justification atoms-expr (:assumptions result)
                                   (or (:num-vars result) 0))
        sat-proof (:proof sat-result)
        ;; Use the CIC expressions from the proof type — these must be consistent
        ;; throughout not_sat'_of_isImpossible's arguments
        s-cic (:constraint-cic sat-result)
        x-cic (:coeffs-cic sat-result)
        ;; Build the isImpossible proof using s-cic (the proof's constraint).
        ;; s-cic may be Constraint.combine(Constraint.combo(...)) etc. but all inputs
        ;; are concrete, so isImpossible s-cic reduces to true via the kernel.
        impossible-prop (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                                (e/const' (:bool-name omega-names) [])
                                (e/app (e/const' (:constraint-is-impossible omega-names) []) s-cic)
                                (e/const' (:bool-true omega-names) []))
        impossible-proof (build-decide-proof env impossible-prop)]
    ;; not_sat'_of_isImpossible : {s} → isImpossible s = true → x → v → sat' s x v = true → False
    ;; All uses of s must be the same CIC expression — use s-cic from the proof.
    (e/app* (e/const' (:not-sat-impossible omega-names) [])
            s-cic
            impossible-proof
            x-cic
            atoms-expr
            sat-proof)))

;; ============================================================
;; Public API
;; ============================================================

(defn- tactic-error! [msg data]
  (throw (ex-info (str "omega: " msg) (merge {:kind :tactic-error} data))))

(declare reify-prop reify-prop-forall reify-prop-iff negate-goal negate-goal-forall)

(def ^:private int-zero
  "The Int expression for 0: Int.ofNat 0"
  (e/app (e/const' (name/from-string "Int.ofNat") []) (e/lit-nat 0)))

(defn- mk-nat-to-int-le
  "Convert h : a ≤ b (Nat) to ↑a ≤ ↑b (Int).
   Uses: Iff.mpr {↑a ≤ ↑b} {a ≤ b} (Int.ofNat_le a b) h"
  [a-nat b-nat hyp-proof]
  (let [int-le-prop (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                            int-type (e/const' (:int-inst-le omega-names) [])
                            (nat-to-int a-nat) (nat-to-int b-nat))
        nat-le-prop (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                            (e/const' (:nat-name omega-names) [])
                            (e/const' (:inst-le-nat omega-names) [])
                            a-nat b-nat)]
    (e/app* (e/const' (:iff-mpr omega-names) [])
            int-le-prop nat-le-prop
            (e/app* (e/const' (:int-ofnat-le omega-names) []) a-nat b-nat)
            hyp-proof)))

(defn- mk-le-of-le-of-eq
  "Build le_of_le_of_eq.{0} Int a b c Int.instLEInt h1 h2 : a ≤ c
   given h1 : a ≤ b, h2 : b = c"
  [a b c h1 h2]
  (e/app* (e/const' (:le-of-le-of-eq omega-names) [lvl/zero])
          int-type a b c (e/const' (:int-inst-le omega-names) []) h1 h2))

(defn- mk-ineq-proof-fn
  "Build a proof function for an inequality hypothesis h : a ≤ b.
   Chain: h → ↑a ≤ ↑b → 0 ≤ ↑b - ↑a → 0 ≤ lc.eval atoms.
   diff-prf-fn returns {:proof :lhs :rhs} where proof : lhs = rhs, lhs = lc.eval atoms."
  [hyp-proof a-expr b-expr _diff-lc diff-prf-fn type-name]
  (if (nil? hyp-proof)
    nil
    (fn [atoms-expr]
      (let [a-int (if (= type-name (:nat-name omega-names)) (nat-to-int a-expr) a-expr)
            b-int (if (= type-name (:nat-name omega-names)) (nat-to-int b-expr) b-expr)
            h-int (if (= type-name (:nat-name omega-names))
                    (mk-nat-to-int-le a-expr b-expr hyp-proof)
                    hyp-proof)
            ;; Int.sub_nonneg_of_le : ∀ {a b}, b ≤ a → 0 ≤ a - b
            ;; h-int : a-int ≤ b-int, so pass {b-int} {a-int} h-int → 0 ≤ b-int - a-int
            sub-expr (mk-int-sub b-int a-int)
            h-sub (e/app* (e/const' (:int-sub-nonneg-of-le omega-names) [])
                          b-int a-int h-int)
            ;; Get eval proof: lc.eval atoms = ↑b - ↑a (or similar)
            eval-result (if (fn? diff-prf-fn) (diff-prf-fn atoms-expr) diff-prf-fn)
            eval-lhs (:lhs eval-result)
            eval-rhs (:rhs eval-result)
            ;; Eq.symm: (↑b - ↑a) = lc.eval atoms
            symm-proof (mk-eq-symm eval-lhs eval-rhs (:proof eval-result))]
        ;; le_of_le_of_eq: 0 ≤ (↑b - ↑a) → (↑b - ↑a) = lc.eval → 0 ≤ lc.eval
        (mk-le-of-le-of-eq int-zero sub-expr eval-lhs h-sub symm-proof)))))

(defn- mk-eq-proof-fn
  "Build a proof function for an equality hypothesis h : a = b.
   Chain: h → ↑a = ↑b → ↑a - ↑b = 0 → lc.eval atoms = 0."
  [hyp-proof a-expr b-expr _diff-lc diff-prf-fn type-name]
  (if (nil? hyp-proof)
    nil
    (fn [atoms-expr]
      (let [a-int (if (= type-name (:nat-name omega-names)) (nat-to-int a-expr) a-expr)
            b-int (if (= type-name (:nat-name omega-names)) (nat-to-int b-expr) b-expr)
            ;; Convert Nat = to Int = via congrArg Int.ofNat h
            ;; congrArg.{u,v} : {α} {β} {a1} {a2} (f : α→β) (h : a1=a2) → f a1 = f a2
            h-int (if (= type-name (:nat-name omega-names))
                    (e/app* (e/const' (:congr-arg omega-names) [u1 u1])
                            (e/const' (:nat-name omega-names) []) ;; α = Nat
                            int-type ;; β = Int
                            a-expr b-expr ;; {a1} {a2}
                            (e/const' (:int-ofnat omega-names) []) ;; f = Int.ofNat
                            hyp-proof)
                    hyp-proof)
            ;; Int.sub_eq_zero_of_eq : {a b : Int} → a = b → a - b = 0
            sub-expr (mk-int-sub a-int b-int)
            h-sub (e/app* (e/const' (:int-sub-eq-zero-of-eq omega-names) [])
                          a-int b-int h-int)
            ;; eval proof: lc.eval atoms = (a-int - b-int)
            eval-result (if (fn? diff-prf-fn) (diff-prf-fn atoms-expr) diff-prf-fn)
            eval-lhs (:lhs eval-result)
            eval-rhs (:rhs eval-result)
            ;; Chain: lc.eval = (↑a - ↑b) = 0
            symm-proof (mk-eq-symm eval-lhs eval-rhs (:proof eval-result))]
        ;; Eq.trans ((↑a - ↑b) = lc.eval) ... no wait
        ;; We want: lc.eval atoms = 0
        ;; eval proof: lc.eval = rhs (where rhs ≈ ↑a - ↑b)
        ;; h-sub: ↑a - ↑b = 0
        ;; So: Eq.trans eval_proof h-sub : lc.eval = 0
        ;; But rhs may differ from sub-expr... for now assume they match
        (mk-eq-trans eval-lhs eval-rhs int-zero (:proof eval-result) h-sub)))))

(defn- mk-lt-proof-fn
  "Build a proof function for a strict inequality hypothesis h : a < b.
   Chain: h → ↑a < ↑b → ↑a + 1 ≤ ↑b → 0 ≤ ↑b - (↑a + 1) → 0 ≤ lc.eval atoms."
  [hyp-proof a-expr b-expr _diff-lc diff-prf-fn type-name]
  (if (nil? hyp-proof)
    nil
    (fn [atoms-expr]
      (let [a-int (if (= type-name (:nat-name omega-names)) (nat-to-int a-expr) a-expr)
            b-int (if (= type-name (:nat-name omega-names)) (nat-to-int b-expr) b-expr)
            ;; Convert Nat < to Int <
            ;; Iff.mpr {↑a < ↑b} {a < b} (Int.ofNat_lt a b) h
            h-int (if (= type-name (:nat-name omega-names))
                    (let [int-lt-prop (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                              int-type (e/const' (name/from-string "Int.instLTInt") [])
                                              (nat-to-int a-expr) (nat-to-int b-expr))
                          nat-lt-prop (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                              (e/const' (:nat-name omega-names) [])
                                              (e/const' (:inst-lt-nat omega-names) [])
                                              a-expr b-expr)]
                      (e/app* (e/const' (:iff-mpr omega-names) [])
                              int-lt-prop nat-lt-prop
                              (e/app* (e/const' (:int-ofnat-lt omega-names) []) a-expr b-expr)
                              hyp-proof))
                    hyp-proof)
            ;; Int.add_one_le_of_lt : {a b : Int} → a < b → a + 1 ≤ b
            int-one (e/app (e/const' (name/from-string "Int.ofNat") []) (e/lit-nat 1))
            a-plus-1 (mk-int-add a-int int-one)
            h-le (e/app* (e/const' (:int-add-one-le-of-lt omega-names) [])
                         a-int b-int h-int)
            ;; sub_nonneg_of_le : ∀ {a b}, b ≤ a → 0 ≤ a - b
            ;; h-le : a+1 ≤ b, so pass {b} {a+1} → 0 ≤ b - (a+1)
            sub-expr (mk-int-sub b-int a-plus-1)
            h-sub (e/app* (e/const' (:int-sub-nonneg-of-le omega-names) [])
                          b-int a-plus-1 h-le)
            ;; Eval proof bridge
            eval-result (if (fn? diff-prf-fn) (diff-prf-fn atoms-expr) diff-prf-fn)
            eval-lhs (:lhs eval-result)
            eval-rhs (:rhs eval-result)
            symm-proof (mk-eq-symm eval-lhs eval-rhs (:proof eval-result))]
        (mk-le-of-le-of-eq int-zero sub-expr eval-lhs h-sub symm-proof)))))

(defn- mk-nat-sub-dichotomy
  "Build the Nat.sub dichotomy disjunction.
   For atom = ↑(a - b), generates:
     Nat.le_total b a : b ≤ a ∨ a ≤ b  (note: we want b ≤ a ∨ a < b, but le_total gives b ≤ a ∨ a ≤ b)
   Left branch (b ≤ a):  ↑(a-b) = ↑a - ↑b  via Int.ofNat_sub
   Right branch (a ≤ b): a - b = 0 via Nat.sub_eq_zero_of_le, so ↑(a-b) = 0

   Actually, Nat.le_total gives m ≤ n ∨ n ≤ m. We use Nat.le_total b a : b ≤ a ∨ a ≤ b.
   Left (b ≤ a): ↑(a-b) = ↑a - ↑b  [real subtraction]
   Right (a ≤ b): a-b = 0, so ↑(a-b) = ↑0 = 0  [truncated to zero]

   Returns a disjunction to queue:
   {:or-proof (Nat.le_total b a), :left-type (b ≤ a), :right-type (a ≤ b),
    :left-facts [...], :right-facts [...]}

   But for simplicity, we queue the raw Or and let reify-prop handle each branch."
  [table atom-idx nat-a nat-b]
  (let [nat-type (e/const' (:nat-name omega-names) [])
        le-inst (e/const' (:inst-le-nat omega-names) [])
        ;; b ≤ a
        left-type (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                          nat-type le-inst nat-b nat-a)
        ;; a ≤ b
        right-type (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                           nat-type le-inst nat-a nat-b)
        ;; Nat.le_total b a : b ≤ a ∨ a ≤ b
        or-proof (e/app* (e/const' (:nat-le-total omega-names) [])
                         nat-b nat-a)]
    {:or-proof or-proof
     :left-type left-type
     :right-type right-type
     ;; Metadata for building equality constraints in branches
     :nat-sub-info {:atom-idx atom-idx :nat-a nat-a :nat-b nat-b}}))

(defn- add-nat-sub-dichotomies
  "For each Nat.sub atom in the table, queue a dichotomy disjunction."
  [problem table]
  (reduce (fn [problem [idx {:keys [a b]}]]
            (queue-disjunction problem (mk-nat-sub-dichotomy table idx a b)))
          problem
          (:nat-sub-atoms table)))

(defn- add-nat-sub-equality
  "Add Nat.sub equality constraint for a dichotomy branch.
   For left branch (b ≤ a): add Eq Int ↑(a-b) (↑a - ↑b) via Int.ofNat_sub
   For right branch (a ≤ b): add Eq Int ↑(a-b) ↑0 via congrArg ofNat (Nat.sub_eq_zero_of_le)
   Delegates to reify-prop's Eq handler for proper proof chain construction."
  [st table problem {:keys [atom-idx nat-a nat-b]} branch hyp-proof]
  (let [nat-sub-expr (e/app* (e/const' (:nat-sub omega-names) []) nat-a nat-b)
        nat-sub-int (nat-to-int nat-sub-expr)]
    (case branch
      :left
      ;; b ≤ a, so ↑(a-b) = ↑a - ↑b
      ;; Int.ofNat_sub : (arg0 arg1 : Nat) → arg0 ≤ arg1 → ↑(arg1 - arg0) = ↑arg1 - ↑arg0
      ;; arg0=nat-b, arg1=nat-a, hyp : nat-b ≤ nat-a
      (let [eq-proof (e/app* (e/const' (:int-ofnat-sub omega-names) [])
                             nat-b nat-a hyp-proof)
            ;; eq-proof : @Eq Int ↑(a-b) (↑a - ↑b)
            rhs (mk-int-sub (nat-to-int nat-a) (nat-to-int nat-b))
            eq-type (e/app* (e/const' (:eq-name omega-names) [u1])
                            int-type nat-sub-int rhs)]
        ;; Feed through reify-prop as Eq Int ↑(a-b) (↑a - ↑b)
        (reify-prop st table problem eq-type eq-proof))
      :right
      ;; a ≤ b, so a - b = 0 in Nat, hence ↑(a-b) = ↑0 in Int
      ;; Nat.sub_eq_zero_of_le : {n m : Nat} → n ≤ m → n - m = 0
      ;; n=nat-a, m=nat-b, hyp : nat-a ≤ nat-b
      (let [nat-sub-zero (e/app* (e/const' (:nat-sub-eq-zero-of-le omega-names) [])
                                 nat-a nat-b hyp-proof)
            ;; nat-sub-zero : @Eq Nat (a - b) 0
            ;; congrArg Int.ofNat nat-sub-zero : @Eq Int ↑(a-b) ↑0
            ofnat-fn (e/const' (:int-ofnat omega-names) [])
            nat-zero (e/lit-nat 0)
            congr-proof (e/app* (e/const' (:congr-arg omega-names) [u1 u1])
                                (e/const' (:nat-name omega-names) [])
                                int-type
                                nat-sub-expr nat-zero
                                ofnat-fn
                                nat-sub-zero)
            ;; congr-proof : @Eq Int ↑(a-b) ↑0
            zero-int (nat-to-int nat-zero)
            eq-type (e/app* (e/const' (:eq-name omega-names) [u1])
                            int-type nat-sub-int zero-int)]
        (reify-prop st table problem eq-type congr-proof)))))

(defn- reify-prop
  "Reify a CIC proposition into constraints added to the problem.
   hyp-proof is the CIC proof term for the hypothesis (an fvar or nil for backward compat).
   Returns [atom-table problem]."
  [st table problem prop hyp-proof]
  (let [matched (try-match-head st prop)]
    (if-not matched
      ;; No const head — try forall (implication)
      (reify-prop-forall st table problem prop hyp-proof)
      (let [[head-name head-levels args] matched]
        (cond
          ;; Eq _ a b → a - b = 0
          (and (= head-name (:eq-name omega-names)) (= 3 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                [table' lc-a prf-a] (reify-term st table (nth args 1))
                [table'' lc-b prf-b] (reify-term st table' (nth args 2))
                diff (lc-sub lc-a lc-b)
                diff-prf (mk-sub-eval-proof lc-a lc-b prf-a prf-b)
                proof-fn (mk-eq-proof-fn hyp-proof (nth args 1) (nth args 2)
                                         diff diff-prf type-name)]
            [table'' (add-equality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; LE.le _ _ a b → b - a ≥ 0
          (and (= head-name (:le-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                a-arg (nth args 2) b-arg (nth args 3)
                [table' lc-a prf-a] (reify-term st table a-arg)
                [table'' lc-b prf-b] (reify-term st table' b-arg)
                diff (lc-sub lc-b lc-a)
                diff-prf (mk-sub-eval-proof lc-b lc-a prf-b prf-a)
                proof-fn (mk-ineq-proof-fn hyp-proof a-arg b-arg diff diff-prf type-name)]
            [table'' (add-inequality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; Nat.le a b → b - a ≥ 0
          (and (= head-name (:nat-le omega-names)) (= 2 (count args)))
          (let [[table' lc-a prf-a] (reify-term st table (nth args 0))
                [table'' lc-b prf-b] (reify-term st table' (nth args 1))
                diff (lc-sub lc-b lc-a)
                diff-prf (mk-sub-eval-proof lc-b lc-a prf-b prf-a)
                proof-fn (mk-ineq-proof-fn hyp-proof (nth args 0) (nth args 1)
                                           diff diff-prf (:nat-name omega-names))]
            [table'' (add-inequality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; LT.lt _ _ a b → b - a - 1 ≥ 0
          (and (= head-name (:lt-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                a-arg (nth args 2) b-arg (nth args 3)
                [table' lc-a prf-a] (reify-term st table a-arg)
                [table'' lc-b prf-b] (reify-term st table' b-arg)
                ;; a < b becomes a+1 ≤ b, so diff = b - (a+1)
                one-lc (mk-lc 1)
                lc-a-plus-1 (lc-add lc-a one-lc)
                prf-a-plus-1 (mk-add-eval-proof lc-a one-lc prf-a (mk-eval-rfl-proof one-lc))
                diff (lc-sub lc-b lc-a-plus-1)
                diff-prf (mk-sub-eval-proof lc-b lc-a-plus-1 prf-b prf-a-plus-1)
                proof-fn (mk-lt-proof-fn hyp-proof a-arg b-arg diff diff-prf type-name)]
            [table'' (add-inequality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; GE.ge _ _ a b → a - b ≥ 0
          ;; GE.ge α inst a b means a ≥ b, i.e., b ≤ a, so a - b ≥ 0
          (and (= head-name (:ge-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                ;; GE.ge α inst a b: a=args[2], b=args[3]
                ;; Convert to LE.le b a via ge_iff_le, then treat as b ≤ a
                ge-a (nth args 2) ge-b (nth args 3)
                [table' lc-b prf-b] (reify-term st table ge-b)
                [table'' lc-a prf-a] (reify-term st table' ge-a)
                ;; diff = a - b ≥ 0
                diff (lc-sub lc-a lc-b)
                diff-prf (mk-sub-eval-proof lc-a lc-b prf-a prf-b)
                ;; Build proof: Iff.mp (ge_iff_le α inst a b) hyp : b ≤ a
                ;; Then use mk-ineq-proof-fn with b ≤ a (le-proof for b, a)
                le-inst (nth args 1) ;; LE instance (from GE args)
                ge-iff (when hyp-proof
                         (e/app* (e/const' (:ge-iff-le omega-names) head-levels)
                                 type-arg le-inst ge-a ge-b))
                le-proof (when hyp-proof
                           (e/app* (e/const' (:iff-mp omega-names) [])
                                   (e/app* (e/const' (:ge-name omega-names) [lvl/zero])
                                           type-arg le-inst ge-a ge-b)
                                   (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                                           type-arg le-inst ge-b ge-a)
                                   ge-iff hyp-proof))
                ;; Now le-proof : b ≤ a, use mk-ineq-proof-fn with (b, a)
                proof-fn (mk-ineq-proof-fn le-proof ge-b ge-a diff diff-prf type-name)]
            [table'' (add-inequality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; GT.gt _ _ a b → a - b - 1 ≥ 0
          ;; GT.gt α inst a b means a > b, i.e., b < a
          (and (= head-name (:gt-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                gt-a (nth args 2) gt-b (nth args 3)
                [table' lc-a prf-a] (reify-term st table gt-a)
                [table'' lc-b prf-b] (reify-term st table' gt-b)
                ;; a > b means b < a, i.e., b+1 ≤ a, i.e., a - b - 1 ≥ 0
                one-lc (mk-lc 1)
                lc-b-plus-1 (lc-add lc-b one-lc)
                prf-b-plus-1 (mk-add-eval-proof lc-b one-lc prf-b (mk-eval-rfl-proof one-lc))
                diff (lc-sub lc-a lc-b-plus-1)
                diff-prf (mk-sub-eval-proof lc-a lc-b-plus-1 prf-a prf-b-plus-1)
                ;; Build proof: Iff.mp (gt_iff_lt α lt-inst a b) hyp : b < a
                lt-inst (nth args 1) ;; LT instance
                gt-iff (when hyp-proof
                         (e/app* (e/const' (:gt-iff-lt omega-names) head-levels)
                                 type-arg lt-inst gt-a gt-b))
                lt-proof (when hyp-proof
                           (e/app* (e/const' (:iff-mp omega-names) [])
                                   (e/app* (e/const' (:gt-name omega-names) [lvl/zero])
                                           type-arg lt-inst gt-a gt-b)
                                   (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                           type-arg lt-inst gt-b gt-a)
                                   gt-iff hyp-proof))
                ;; lt-proof : b < a, use mk-lt-proof-fn with (b, a)
                proof-fn (mk-lt-proof-fn lt-proof gt-b gt-a diff diff-prf type-name)]
            [table'' (add-inequality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; And p q
          (and (= head-name (:and-name omega-names)) (= 2 (count args)))
          (let [;; And.left : And P Q → P
                left-proof (when hyp-proof
                             (e/app* (e/const' (name/from-string "And.left") [])
                                     (nth args 0) (nth args 1) hyp-proof))
                ;; And.right : And P Q → Q
                right-proof (when hyp-proof
                              (e/app* (e/const' (name/from-string "And.right") [])
                                      (nth args 0) (nth args 1) hyp-proof))
                [table' problem'] (reify-prop st table problem (nth args 0) left-proof)
                [table'' problem''] (reify-prop st table' problem' (nth args 1) right-proof)]
            [table'' problem''])

          ;; False → direct contradiction (short-circuit the solver)
          (= head-name (:false-name omega-names))
          (if hyp-proof
            ;; hyp-proof directly proves False — store it for short-circuit
            [table (assoc problem :direct-false hyp-proof)]
            ;; No proof available, add trivially unsat constraint
            [table (add-inequality problem -1 [] nil)])

          ;; True → no constraint
          (= head-name (:true-name omega-names))
          [table problem]

          ;; Ne.{u} α a b → same as Not (Eq α a b), i.e., a ≠ b
          (and (= head-name (:ne-name omega-names)) (= 3 (count args)))
          (let [eq-prop (e/app* (e/const' (:eq-name omega-names) head-levels)
                                (nth args 0) (nth args 1) (nth args 2))
                [table' negated] (negate-goal st table problem eq-prop hyp-proof)]
            (if (:disjunction negated)
              ;; Queue the disjunction for later processing
              [table' (queue-disjunction problem (:disjunction negated))]
              [table' negated]))

          ;; Or P Q → queue as disjunction for later case-splitting
          (and (= head-name (:or-name omega-names)) (= 2 (count args)))
          (if hyp-proof
            [table (queue-disjunction problem
                     {:or-proof hyp-proof
                      :left-type (nth args 0)
                      :right-type (nth args 1)})]
            [table problem])

          ;; Not P → negate the inner proposition
          ;; Converts ¬(a ≤ b) → b < a, ¬(a < b) → b ≤ a, etc.
          (and (= head-name (:not-name omega-names)) (= 1 (count args)))
          (let [[table' negated] (negate-goal st table problem (nth args 0) hyp-proof)]
            (if (:disjunction negated)
              ;; Queue the disjunction for later processing
              [table' (queue-disjunction problem (:disjunction negated))]
              [table' negated]))

          ;; Dvd.dvd α inst k x → feed equality through reify-prop
          ;; Nat: Nat.div_mul_cancel h : (x / k) * k = x
          ;; Int: use emod_eq_zero_of_dvd + emod_def to get x - k*(x/k) = 0
          (and (= head-name (:dvd-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                k-arg (nth args 2)
                x-arg (nth args 3)
                k-whnf (#'tc/cached-whnf st k-arg)]
            (if (and (or (= type-name (:nat-name omega-names))
                         (= type-name (:int-name omega-names)))
                     (e/lit-nat? k-whnf)
                     (pos? (e/lit-nat-val k-whnf)))
              (if (= type-name (:nat-name omega-names))
                ;; Nat: Nat.div_mul_cancel {n m} (h : m ∣ n) : (n / m) * m = n
                ;; With n=x, m=k: (x / k) * k = x
                ;; Feed Eq Nat ((x/k)*k) x through reify-prop
                (let [nat-type (e/const' (:nat-name omega-names) [])
                      div-expr (e/app* (e/const' (:hdiv omega-names) [lvl/zero lvl/zero lvl/zero])
                                       nat-type nat-type nat-type
                                       (e/app* (e/const' (name/from-string "instHDiv") [lvl/zero])
                                               nat-type (e/const' (name/from-string "Nat.instDiv") []))
                                       x-arg k-arg)
                      mul-expr (e/app* (e/const' (:hmul omega-names) [lvl/zero lvl/zero lvl/zero])
                                       nat-type nat-type nat-type
                                       (e/app* (e/const' (name/from-string "instHMul") [lvl/zero])
                                               nat-type (e/const' (name/from-string "instMulNat") []))
                                       div-expr k-arg)
                      eq-proof (when hyp-proof
                                 (e/app* (e/const' (name/from-string "Nat.div_mul_cancel") [])
                                         x-arg k-arg hyp-proof))
                      eq-type (e/app* (e/const' (:eq-name omega-names) [u1])
                                      nat-type mul-expr x-arg)]
                  (reify-prop st table problem eq-type eq-proof))
                ;; Int: Eq.trans (Eq.symm (Int.emod_def x k)) (Int.emod_eq_zero_of_dvd k x h)
                ;; gives: x - k * (x / k) = 0
                ;; Feed Eq Int (x - k*(x/k)) 0 through reify-prop
                (let [emod-def-proof (e/app* (e/const' (name/from-string "Int.emod_def") [])
                                             x-arg k-arg)
                      emod-zero-proof (when hyp-proof
                                        (e/app* (e/const' (:int-emod-eq-zero-of-dvd omega-names) [])
                                                k-arg x-arg hyp-proof))
                      ;; emod_def : x % k = x - k * (x / k)
                      ;; emod_eq_zero : x % k = 0
                      ;; Eq.symm (emod_def) : x - k*(x/k) = x % k
                      ;; Eq.trans (Eq.symm emod_def) emod_zero : x - k*(x/k) = 0
                      int-div-expr (e/app* (e/const' (:hdiv omega-names) [lvl/zero lvl/zero lvl/zero])
                                           int-type int-type int-type
                                           (e/app* (e/const' (name/from-string "instHDiv") [lvl/zero])
                                                   int-type (e/const' (name/from-string "Int.instDiv") []))
                                           x-arg k-arg)
                      int-mul-expr (e/app* (e/const' (:hmul omega-names) [lvl/zero lvl/zero lvl/zero])
                                          int-type int-type int-type
                                          (e/app* (e/const' (name/from-string "instHMul") [lvl/zero])
                                                  int-type (e/const' (name/from-string "Int.instMul") []))
                                          k-arg int-div-expr)
                      sub-expr (e/app* (e/const' (:hsub omega-names) [lvl/zero lvl/zero lvl/zero])
                                       int-type int-type int-type
                                       (e/app* (e/const' (name/from-string "instHSub") [lvl/zero])
                                               int-type (e/const' (name/from-string "Int.instSub") []))
                                       x-arg int-mul-expr)
                      zero-int (e/app (e/const' (:int-ofnat omega-names) []) (e/lit-nat 0))
                      ;; Build Eq.trans proof
                      mod-type (e/app* (e/const' (:hmod omega-names) [lvl/zero lvl/zero lvl/zero])
                                       int-type int-type int-type
                                       (e/app* (e/const' (name/from-string "instHMod") [lvl/zero])
                                               int-type (e/const' (name/from-string "Int.instMod") []))
                                       x-arg k-arg)
                      eq-proof (when hyp-proof
                                 (e/app* (e/const' (:eq-trans omega-names) [u1])
                                         int-type sub-expr mod-type zero-int
                                         (e/app* (e/const' (:eq-symm omega-names) [u1])
                                                 int-type mod-type sub-expr
                                                 emod-def-proof)
                                         emod-zero-proof))
                      eq-type (e/app* (e/const' (:eq-name omega-names) [u1])
                                      int-type sub-expr zero-int)]
                  (reify-prop st table problem eq-type eq-proof)))
              [table problem]))

          :else
          ;; Try Iff (positive) and forall (implication) before giving up
          (let [[t p] (reify-prop-iff st table problem prop hyp-proof)]
            (if (not= p problem)
              [t p]
              (reify-prop-forall st table problem prop hyp-proof))))))))

(defn- reify-prop-forall
  "Handle forall-based propositions that try-match-head can't detect:
   - P → Q (implication): convert to ¬P ∨ Q via Decidable.not_or_of_imp
   - P ↔ Q (Iff): convert to (P ∧ Q) ∨ (¬P ∧ ¬Q) via iff_iff_and_or_not_and_not"
  [st table problem prop hyp-proof]
  (let [whnf (#'tc/cached-whnf st prop)]
    (cond
      ;; Iff P Q is an application, handle it here since we need WHNF
      ;; After WHNF, Iff P Q remains as Iff P Q (it's a structure)
      ;; Actually Iff is matched by try-match-head. Check for forall (implication).
      (and (e/forall? whnf) (= :default (e/forall-info whnf)))
      ;; P → Q: convert to ¬P ∨ Q via Decidable.not_or_of_imp
      ;; Decidable.not_or_of_imp {P Q : Prop} [Decidable P] (h : P → Q) : ¬P ∨ Q
      (let [p-type (e/forall-type whnf)
            body-raw (e/forall-body whnf)
            fv-id (long (System/nanoTime))
            q-type (e/instantiate1 body-raw (e/fvar fv-id))
            ;; Check if body uses bvar 0 (dependent forall vs non-dependent arrow)
            is-dependent (pos? (e/bvar-range body-raw))]
        (if is-dependent
          ;; Dependent forall — not an implication, bail
          [table problem]
          ;; Implication: P → Q  →  ¬P ∨ Q
          (let [not-const (e/const' (:not-name omega-names) [])
                not-p (e/app not-const p-type)
                ;; Decidable.not_or_of_imp {P Q} [dec P] (h : P → Q) : ¬P ∨ Q
                or-proof (when hyp-proof
                           (e/app* (e/const' (:not-or-of-imp omega-names) [])
                                   p-type q-type
                                   (e/app (e/const' (:classical-prop-dec omega-names) []) p-type)
                                   hyp-proof))
                ;; Queue as disjunction: ¬P ∨ Q
                left-type not-p
                right-type q-type]
            [table (queue-disjunction problem
                     {:or-proof or-proof
                      :left-type left-type
                      :right-type right-type})])))

      :else [table problem])))

(defn- reify-prop-iff
  "Handle positive Iff: (P ↔ Q) → (P ∧ Q) ∨ (¬P ∧ ¬Q)
   via Iff.mp iff_iff_and_or_not_and_not"
  [st table problem prop hyp-proof]
  (let [matched (try-match-head st prop)
        [head-name _head-levels args] matched]
    (if (and matched (= head-name (:iff-name omega-names)) (= 2 (count args)))
      (let [p-arg (nth args 0) q-arg (nth args 1)
            not-const (e/const' (:not-name omega-names) [])
            not-p (e/app not-const p-arg)
            not-q (e/app not-const q-arg)
            ;; (P ∧ Q) ∨ (¬P ∧ ¬Q)
            left-type (e/app* (e/const' (:and-name omega-names) []) p-arg q-arg)
            right-type (e/app* (e/const' (:and-name omega-names) []) not-p not-q)
            ;; iff_iff_and_or_not_and_not {P Q : Prop} : (P ↔ Q) ↔ ((P∧Q)∨(¬P∧¬Q))
            ;; Takes only 2 implicit args, no Decidable instances
            iff-prop (e/app* (e/const' (:iff-name omega-names) []) p-arg q-arg)
            or-type (e/app* (e/const' (:or-name omega-names) []) left-type right-type)
            or-proof (when hyp-proof
                       (e/app* (e/const' (:iff-mp omega-names) [])
                               iff-prop or-type
                               (e/app* (e/const' (:iff-iff-and-or omega-names) [])
                                       p-arg q-arg)
                               hyp-proof))]
        [table (queue-disjunction problem
                 {:or-proof or-proof
                  :left-type left-type
                  :right-type right-type})])
      [table problem])))

(defn- negate-goal
  "Negate the goal and add constraints to the problem.
   hyp-proof is the proof of ¬P (from by_contra), or nil."
  [st table problem goal-type hyp-proof]
  (let [matched (try-match-head st goal-type)]
    (if-not matched
      ;; No const head — try forall (¬(P → Q))
      (negate-goal-forall st table problem goal-type hyp-proof)
      (let [[head-name head-levels args] matched]
        (cond
          ;; Goal: Eq _ a b → ¬(a = b): split into a < b ∨ b < a
          (and (= head-name (:eq-name omega-names)) (= 3 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                a-arg (nth args 1) b-arg (nth args 2)
                [table' lc-a prf-a] (reify-term st table a-arg)
                [table'' lc-b prf-b] (reify-term st table' b-arg)
                ;; Branch 1: a < b → b - a - 1 ≥ 0
                one-lc (mk-lc 1)
                lc-a-plus-1 (lc-add lc-a one-lc)
                prf-a-plus-1 (mk-add-eval-proof lc-a one-lc prf-a (mk-eval-rfl-proof one-lc))
                diff-ab (lc-sub lc-b lc-a-plus-1)
                diff-prf-ab (mk-sub-eval-proof lc-b lc-a-plus-1 prf-b prf-a-plus-1)
                ;; Branch 2: b < a → a - b - 1 ≥ 0
                lc-b-plus-1 (lc-add lc-b one-lc)
                prf-b-plus-1 (mk-add-eval-proof lc-b one-lc prf-b (mk-eval-rfl-proof one-lc))
                diff-ba (lc-sub lc-a lc-b-plus-1)
                diff-prf-ba (mk-sub-eval-proof lc-a lc-b-plus-1 prf-a prf-b-plus-1)
                ;; Create fresh fvars for Or.elim branches
                left-fvar-id (long (System/nanoTime))
                right-fvar-id (long (+ 1 (System/nanoTime)))
                ;; Left type: a < b (Int) or a < b (Nat)
                left-type (if (= type-name (:nat-name omega-names))
                            (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                    type-arg (e/const' (:inst-lt-nat omega-names) [])
                                    a-arg b-arg)
                            (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                    int-type (e/const' (:int-inst-lt omega-names) [])
                                    a-arg b-arg))
                ;; Right type: b < a (Int) or a > b (Nat) — Nat version uses GT
                right-type (if (= type-name (:nat-name omega-names))
                             (e/app* (e/const' (:gt-name omega-names) [lvl/zero])
                                     type-arg (e/const' (:inst-lt-nat omega-names) [])
                                     a-arg b-arg)
                             (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                     int-type (e/const' (:int-inst-lt omega-names) [])
                                     b-arg a-arg))
                left-hyp (e/fvar left-fvar-id)
                right-hyp (e/fvar right-fvar-id)
                ;; Build proof-fns using the fvar hypotheses
                left-proof-fn (mk-lt-proof-fn left-hyp a-arg b-arg
                                              diff-ab diff-prf-ab type-name)
                ;; For Int right branch: b < a; for Nat: a > b (which is b < a via gt_iff_lt)
                right-proof-fn (if (= type-name (:nat-name omega-names))
                                 ;; Nat: right is GT.gt a b, convert via gt_iff_lt to b < a
                                 ;; GT.gt.{0} for Nat, so gt_iff_lt.{0}
                                 (let [lt-inst (e/const' (:inst-lt-nat omega-names) [])
                                       gt-iff (e/app* (e/const' (:gt-iff-lt omega-names) [lvl/zero])
                                                      type-arg lt-inst a-arg b-arg)
                                       lt-proof (e/app* (e/const' (:iff-mp omega-names) [])
                                                        right-type
                                                        (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                                                type-arg lt-inst b-arg a-arg)
                                                        gt-iff right-hyp)]
                                   (mk-lt-proof-fn lt-proof b-arg a-arg
                                                   diff-ba diff-prf-ba type-name))
                                 (mk-lt-proof-fn right-hyp b-arg a-arg
                                                 diff-ba diff-prf-ba type-name))
                ;; Build the two branch problems
                left-problem (add-inequality problem (:const diff-ab) (:coeffs diff-ab) left-proof-fn)
                right-problem (add-inequality problem (:const diff-ba) (:coeffs diff-ba) right-proof-fn)
                ;; Build the Or proof from hyp-proof (¬(a = b))
                ;; Int: Int.lt_or_gt_of_ne {a} {b} h : a < b ∨ b < a
                ;; Nat: Nat.lt_or_gt_of_ne {a} {b} h : a < b ∨ a > b
                or-proof-name (if (= type-name (:nat-name omega-names))
                                (:nat-lt-or-gt-of-ne omega-names)
                                (:int-lt-or-gt-of-ne omega-names))
                or-proof-fn (when hyp-proof
                              (e/app* (e/const' or-proof-name [])
                                      a-arg b-arg hyp-proof))]
            [table'' {:disjunction
                      {:branches [left-problem right-problem]
                       :left-type left-type :right-type right-type
                       :left-fvar-id left-fvar-id :right-fvar-id right-fvar-id
                       :or-proof or-proof-fn}}])

          ;; Goal: LE.le _ _ a b → ¬(a ≤ b): means b < a, i.e., a - b ≥ 1
          ;; pushNot: Nat.lt_of_not_le h : b < a
          (and (= head-name (:le-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                a-arg (nth args 2) b-arg (nth args 3)
                ;; ¬(a ≤ b) → b < a
                pushed-proof (when hyp-proof
                               (if (= type-name (:nat-name omega-names))
                                 (e/app* (e/const' (:nat-lt-of-not-le omega-names) [])
                                         a-arg b-arg hyp-proof)
                                 ;; Int: Iff.mp (Int.not_le a b) hyp : b < a
                                 (let [not-le-iff (e/app* (e/const' (:int-not-le omega-names) [])
                                                          a-arg b-arg)
                                       not-prop (e/app (e/const' (:not-name omega-names) [])
                                                       (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                                                               int-type (e/const' (:int-inst-le omega-names) [])
                                                               a-arg b-arg))
                                       lt-prop (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                                       int-type (e/const' (:int-inst-lt omega-names) [])
                                                       b-arg a-arg)]
                                   (e/app* (e/const' (:iff-mp omega-names) [])
                                           not-prop lt-prop not-le-iff hyp-proof))))
                [table' lc-a prf-a] (reify-term st table a-arg)
                [table'' lc-b prf-b] (reify-term st table' b-arg)
                ;; b < a means b+1 ≤ a, constraint: a - (b+1) ≥ 0
                one-lc (mk-lc 1)
                lc-b-plus-1 (lc-add lc-b one-lc)
                prf-b-plus-1 (mk-add-eval-proof lc-b one-lc prf-b (mk-eval-rfl-proof one-lc))
                diff (lc-sub lc-a lc-b-plus-1)
                diff-prf (mk-sub-eval-proof lc-a lc-b-plus-1 prf-a prf-b-plus-1)
                proof-fn (mk-lt-proof-fn pushed-proof b-arg a-arg diff diff-prf type-name)]
            [table'' (add-inequality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; Goal: LT.lt _ _ a b → ¬(a < b): means b ≤ a
          ;; pushNot: Nat.le_of_not_lt h : b ≤ a
          (and (= head-name (:lt-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                a-arg (nth args 2) b-arg (nth args 3)
                pushed-proof (when hyp-proof
                               (if (= type-name (:nat-name omega-names))
                                 (e/app* (e/const' (:nat-le-of-not-lt omega-names) [])
                                         a-arg b-arg hyp-proof)
                                 ;; Int: Iff.mp (Int.not_lt a b) hyp : b ≤ a
                                 (let [not-lt-iff (e/app* (e/const' (:int-not-lt omega-names) [])
                                                          a-arg b-arg)
                                       not-prop (e/app (e/const' (:not-name omega-names) [])
                                                       (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                                               int-type (e/const' (:int-inst-lt omega-names) [])
                                                               a-arg b-arg))
                                       le-prop (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                                                       int-type (e/const' (:int-inst-le omega-names) [])
                                                       b-arg a-arg)]
                                   (e/app* (e/const' (:iff-mp omega-names) [])
                                           not-prop le-prop not-lt-iff hyp-proof))))
                [table' lc-a prf-a] (reify-term st table a-arg)
                [table'' lc-b prf-b] (reify-term st table' b-arg)
                ;; b ≤ a gives a - b ≥ 0
                diff (lc-sub lc-a lc-b)
                diff-prf (mk-sub-eval-proof lc-a lc-b prf-a prf-b)
                proof-fn (mk-ineq-proof-fn pushed-proof b-arg a-arg diff diff-prf type-name)]
            [table'' (add-inequality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; Goal: GE.ge α inst a b → ¬(a ≥ b): means b > a, i.e., a < b
          ;; ¬(a ≥ b) → ¬(b ≤ a) → a < b via Int.lt_of_not_le / Nat.lt_of_not_le
          (and (= head-name (:ge-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                ge-a (nth args 2) ge-b (nth args 3)
                ;; ¬(a ≥ b) is definitionally ¬(b ≤ a)
                ;; Nat.lt_of_not_le : ¬(b ≤ a) → a < b
                ;; Int.lt_of_not_le : ¬(a ≤ b) → b < a  (swapped args)
                pushed-proof (when hyp-proof
                               (if (= type-name (:nat-name omega-names))
                                 ;; Nat: ¬(b ≤ a) → a < b (Nat.lt_of_not_le)
                                 (e/app* (e/const' (:nat-lt-of-not-le omega-names) [])
                                         ge-b ge-a hyp-proof)
                                 ;; Int: ¬(b ≤ a) → a < b via Iff.mp (Int.not_le b a)
                                 (let [not-le-iff (e/app* (e/const' (:int-not-le omega-names) [])
                                                          ge-b ge-a)
                                       not-prop (e/app (e/const' (:not-name omega-names) [])
                                                       (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                                                               int-type (e/const' (:int-inst-le omega-names) [])
                                                               ge-b ge-a))
                                       lt-prop (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                                       int-type (e/const' (:int-inst-lt omega-names) [])
                                                       ge-a ge-b)]
                                   (e/app* (e/const' (:iff-mp omega-names) [])
                                           not-prop lt-prop not-le-iff hyp-proof))))
                [table' lc-a prf-a] (reify-term st table ge-a)
                [table'' lc-b prf-b] (reify-term st table' ge-b)
                ;; a < b → b - a - 1 ≥ 0
                one-lc (mk-lc 1)
                lc-a-plus-1 (lc-add lc-a one-lc)
                prf-a-plus-1 (mk-add-eval-proof lc-a one-lc prf-a (mk-eval-rfl-proof one-lc))
                diff (lc-sub lc-b lc-a-plus-1)
                diff-prf (mk-sub-eval-proof lc-b lc-a-plus-1 prf-b prf-a-plus-1)
                proof-fn (mk-lt-proof-fn pushed-proof ge-a ge-b diff diff-prf type-name)]
            [table'' (add-inequality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; Goal: GT.gt α inst a b → ¬(a > b): means a ≤ b
          ;; ¬(a > b) → ¬(b < a) → a ≤ b via Int.le_of_not_lt / Nat.le_of_not_lt
          (and (= head-name (:gt-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                gt-a (nth args 2) gt-b (nth args 3)
                ;; ¬(a > b) is definitionally ¬(b < a)
                ;; Nat.le_of_not_lt : ¬(b < a) → a ≤ b
                ;; Int.le_of_not_lt : ¬(a < b) → b ≤ a  (check arg order)
                pushed-proof (when hyp-proof
                               (if (= type-name (:nat-name omega-names))
                                 (e/app* (e/const' (:nat-le-of-not-lt omega-names) [])
                                         gt-b gt-a hyp-proof)
                                 ;; Int: ¬(b < a) → a ≤ b via Iff.mp (Int.not_lt b a)
                                 (let [not-lt-iff (e/app* (e/const' (:int-not-lt omega-names) [])
                                                          gt-b gt-a)
                                       not-prop (e/app (e/const' (:not-name omega-names) [])
                                                       (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                                               int-type (e/const' (:int-inst-lt omega-names) [])
                                                               gt-b gt-a))
                                       le-prop (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                                                       int-type (e/const' (:int-inst-le omega-names) [])
                                                       gt-a gt-b)]
                                   (e/app* (e/const' (:iff-mp omega-names) [])
                                           not-prop le-prop not-lt-iff hyp-proof))))
                [table' lc-a prf-a] (reify-term st table gt-a)
                [table'' lc-b prf-b] (reify-term st table' gt-b)
                ;; a ≤ b → b - a ≥ 0
                diff (lc-sub lc-b lc-a)
                diff-prf (mk-sub-eval-proof lc-b lc-a prf-b prf-a)
                proof-fn (mk-ineq-proof-fn pushed-proof gt-a gt-b diff diff-prf type-name)]
            [table'' (add-inequality problem (:const diff) (:coeffs diff) proof-fn)])

          ;; Goal: And P Q → ¬(P ∧ Q): split into ¬P ∨ ¬Q via not_and_or
          (and (= head-name (:and-name omega-names)) (= 2 (count args)))
          (let [p-arg (nth args 0) q-arg (nth args 1)
                not-const (e/const' (:not-name omega-names) [])
                ;; ¬P and ¬Q types (using Not constant for consistency with not_and_or)
                not-p (e/app not-const p-arg)
                not-q (e/app not-const q-arg)
                ;; Iff.mp (@not_and_or P Q) hyp-proof : ¬P ∨ ¬Q
                and-pq (e/app* (e/const' (:and-name omega-names) []) p-arg q-arg)
                neg-and (e/app not-const and-pq)
                or-neg (e/app* (e/const' (:or-name omega-names) []) not-p not-q)
                or-proof (when hyp-proof
                           (e/app* (e/const' (:iff-mp omega-names) [])
                                   neg-and or-neg
                                   (e/app* (e/const' (:not-and-or omega-names) [])
                                           p-arg q-arg)
                                   hyp-proof))
                ;; Create fvars for Or.elim branches
                left-fvar-id (long (System/nanoTime))
                right-fvar-id (long (+ 1 (System/nanoTime)))
                left-hyp (e/fvar left-fvar-id)
                right-hyp (e/fvar right-fvar-id)
                ;; Each branch: negate the inner prop with the ¬P / ¬Q proof
                [table' left-result] (negate-goal st table problem p-arg left-hyp)
                [table'' right-result] (negate-goal st table' problem q-arg right-hyp)]
            ;; If either branch produces a nested disjunction, bail out
            (if (or (:disjunction left-result) (:disjunction right-result))
              [table problem]  ;; fall through to decide
              [table'' {:disjunction
                        {:branches [left-result right-result]
                         :left-type not-p :right-type not-q
                         :left-fvar-id left-fvar-id :right-fvar-id right-fvar-id
                         :or-proof or-proof}}]))

          ;; Goal: Or P Q → ¬(P ∨ Q): gives ¬P ∧ ¬Q, then negate both
          (and (= head-name (:or-name omega-names)) (= 2 (count args)))
          (let [p-arg (nth args 0) q-arg (nth args 1)
                not-const (e/const' (:not-name omega-names) [])
                not-p (e/app not-const p-arg)
                not-q (e/app not-const q-arg)
                ;; Iff.mp (@not_or P Q) hyp-proof : And (Not P) (Not Q)
                neg-or (e/app not-const (e/app* (e/const' (:or-name omega-names) []) p-arg q-arg))
                and-neg (e/app* (e/const' (:and-name omega-names) []) not-p not-q)
                and-proof (when hyp-proof
                            (e/app* (e/const' (:iff-mp omega-names) [])
                                    neg-or and-neg
                                    (e/app* (e/const' (:not-or omega-names) [])
                                            p-arg q-arg)
                                    hyp-proof))
                ;; Split into ¬P and ¬Q, then negate each
                left-proof (when and-proof
                             (e/app* (e/const' (:and-left omega-names) [])
                                     not-p not-q and-proof))
                right-proof (when and-proof
                              (e/app* (e/const' (:and-right omega-names) [])
                                      not-p not-q and-proof))
                [table' problem'] (negate-goal st table problem p-arg left-proof)
                [table'' problem''] (negate-goal st table' problem' q-arg right-proof)]
            ;; If either returns a disjunction, bail out
            (if (or (:disjunction problem') (:disjunction problem''))
              [table problem]
              [table'' problem'']))

          ;; Goal: Iff P Q → ¬(P ↔ Q): convert to (¬P ↔ Q) via Decidable.not_iff
          ;; then feed as positive Iff hypothesis
          ;; Decidable.not_iff {Q P} [dec P] : ¬(P ↔ Q) ↔ (¬P ↔ Q)
          (and (= head-name (:iff-name omega-names)) (= 2 (count args)))
          (let [p-arg (nth args 0) q-arg (nth args 1)
                not-const (e/const' (:not-name omega-names) [])
                ;; Build: Iff.mp (Decidable.not_iff Q P [dec P]) hyp : ¬P ↔ Q
                iff-pq (e/app* (e/const' (:iff-name omega-names) []) p-arg q-arg)
                neg-iff (e/app not-const iff-pq)
                not-p (e/app not-const p-arg)
                not-p-iff-q (e/app* (e/const' (:iff-name omega-names) []) not-p q-arg)
                not-p-iff-q-proof (when hyp-proof
                                    (e/app* (e/const' (:iff-mp omega-names) [])
                                            neg-iff not-p-iff-q
                                            (e/app* (e/const' (:dec-not-iff omega-names) [])
                                                    q-arg p-arg
                                                    (e/app (e/const' (:classical-prop-dec omega-names) []) p-arg))
                                            hyp-proof))]
            ;; Feed (¬P ↔ Q) as a positive Iff through reify-prop-iff
            (reify-prop-iff st table problem not-p-iff-q not-p-iff-q-proof))

          ;; Goal: Dvd.dvd α inst k x → ¬(k ∣ x)
          ;; For Nat: Nat.emod_pos_of_not_dvd h : 0 < x % k
          ;; For Int: Int.emod_pos_of_not_dvd h : k = 0 ∨ 0 < x % k
          (and (= head-name (:dvd-name omega-names)) (= 4 (count args)))
          (let [type-arg (nth args 0)
                type-whnf (#'tc/cached-whnf st type-arg)
                type-name (when (e/const? type-whnf) (e/const-name type-whnf))
                k-arg (nth args 2) x-arg (nth args 3)]
            (cond
              (= type-name (:nat-name omega-names))
              ;; Nat.emod_pos_of_not_dvd k x h : 0 < x % k
              ;; This is LT.lt Nat instLTNat 0 (HMod.hMod ... x k)
              (let [pushed-proof (when hyp-proof
                                   (e/app* (e/const' (:nat-emod-pos-of-not-dvd omega-names) [])
                                           k-arg x-arg hyp-proof))]
                ;; Feed as LT hypothesis: 0 < x % k
                (reify-prop st table problem
                            (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                    type-arg (e/const' (:inst-lt-nat omega-names) [])
                                    (e/lit-nat 0)
                                    (e/app* (e/const' (:hmod omega-names) [lvl/zero lvl/zero lvl/zero])
                                            type-arg type-arg type-arg
                                            (e/app* (e/const' (name/from-string "instHMod") [lvl/zero])
                                                    type-arg (e/const' (name/from-string "Nat.instMod") []))
                                            x-arg k-arg))
                            pushed-proof))

              (= type-name (:int-name omega-names))
              ;; Int.emod_pos_of_not_dvd k x h : k = 0 ∨ 0 < x % k (disjunction)
              (let [pushed-proof (when hyp-proof
                                   (e/app* (e/const' (:int-emod-pos-of-not-dvd omega-names) [])
                                           k-arg x-arg hyp-proof))
                    zero-int (e/app (e/const' (:int-ofnat omega-names) []) (e/lit-nat 0))
                    left-type (e/app* (e/const' (:eq-name omega-names) [(lvl/succ lvl/zero)])
                                      int-type k-arg zero-int)
                    mod-expr (e/app* (e/const' (:hmod omega-names) [lvl/zero lvl/zero lvl/zero])
                                     int-type int-type int-type
                                     (e/app* (e/const' (name/from-string "instHMod") [lvl/zero])
                                             int-type (e/const' (name/from-string "Int.instMod") []))
                                     x-arg k-arg)
                    right-type (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                       int-type (e/const' (:int-inst-lt omega-names) [])
                                       zero-int mod-expr)
                    left-fvar-id (long (System/nanoTime))
                    right-fvar-id (long (+ 1 (System/nanoTime)))
                    left-hyp (e/fvar left-fvar-id)
                    right-hyp (e/fvar right-fvar-id)
                    [table' left-problem'] (reify-prop st table problem left-type left-hyp)
                    [table'' right-problem'] (reify-prop st table' problem right-type right-hyp)]
                (if (or (:disjunction left-problem') (:disjunction right-problem'))
                  [table problem]
                  [table'' {:disjunction
                            {:branches [left-problem' right-problem']
                             :left-type left-type :right-type right-type
                             :left-fvar-id left-fvar-id :right-fvar-id right-fvar-id
                             :or-proof pushed-proof}}]))

              :else [table problem]))

          ;; Goal: Not P → assume P (hyp-proof proves ¬(¬P), i.e. P)
          (and (= head-name (:not-name omega-names)) (= 1 (count args)))
          (let [;; ¬(¬P) → P via Decidable.of_not_not
                inner-proof (when hyp-proof
                              (e/app* (e/const' (name/from-string "Decidable.of_not_not") [])
                                      (nth args 0)
                                      (e/app (e/const' (:classical-prop-dec omega-names) [])
                                             (nth args 0))
                                      hyp-proof))]
            (reify-prop st table problem (nth args 0) inner-proof))

          ;; Goal: False → no negation needed
          (= head-name (:false-name omega-names))
          [table problem]

          :else
          ;; Check for forall (¬(P → Q)) — try-match-head won't detect foralls
          (negate-goal-forall st table problem goal-type hyp-proof))))))

(defn- negate-goal-forall
  "Handle negation of forall-based goals that try-match-head can't detect:
   ¬(P → Q) → P ∧ ¬Q via not_imp"
  [st table problem goal-type hyp-proof]
  (let [whnf (#'tc/cached-whnf st goal-type)]
    (if (and (e/forall? whnf) (= :default (e/forall-info whnf)))
      ;; P → Q where P is the domain
      (let [p-type (e/forall-type whnf)
            body-raw (e/forall-body whnf)
            fv-id (long (System/nanoTime))
            q-type (e/instantiate1 body-raw (e/fvar fv-id))
            ;; Check if body uses bvar 0 (dependent forall vs non-dependent arrow)
            ;; A non-dependent arrow P → Q has body with bvar-range = 0 (no loose bvars after
            ;; stripping outer foralls replaced bvars with fvars). Only bvar 0 refers to
            ;; the forall's own bound var.
            is-dependent (pos? (e/bvar-range body-raw))]
        (if is-dependent
          ;; Dependent forall — not an implication, bail
          [table problem]
          ;; ¬(P → Q): gives P ∧ ¬Q via Iff.mp not_imp
          ;; not_imp {P Q : Prop} : ¬(P → Q) ↔ (P ∧ ¬Q) — no Decidable needed
          (let [not-const (e/const' (:not-name omega-names) [])
                not-q (e/app not-const q-type)
                imp-prop (e/forall' "_" p-type (e/abstract1 q-type fv-id) :default)
                neg-imp (e/app not-const imp-prop)
                and-type (e/app* (e/const' (:and-name omega-names) []) p-type not-q)
                ;; Iff.mp (not_imp) hyp : P ∧ ¬Q
                and-proof (when hyp-proof
                            (e/app* (e/const' (:iff-mp omega-names) [])
                                    neg-imp and-type
                                    (e/app* (e/const' (:not-imp omega-names) [])
                                            p-type q-type)
                                    hyp-proof))
                ;; Extract P and ¬Q from the conjunction
                p-proof (when and-proof
                          (e/app* (e/const' (:and-left omega-names) [])
                                  p-type not-q and-proof))
                nq-proof (when and-proof
                           (e/app* (e/const' (:and-right omega-names) [])
                                   p-type not-q and-proof))
                ;; Reify P as positive hypothesis, negate Q
                [table' problem'] (reify-prop st table problem p-type p-proof)
                [table'' problem''] (negate-goal st table' problem' q-type nq-proof)]
            (if (:disjunction problem'')
              [table problem]  ;; bail if nested disjunction
              [table'' problem'']))))
      ;; Not a forall
      [table problem])))

(defn- collect-hypotheses
  "Collect constraints from local context hypotheses.
   Passes the fvar as the hypothesis proof term."
  [st table problem lctx]
  (reduce
   (fn [[table problem] [id decl]]
     (if (= :local (:tag decl))
       (try
         (let [hyp-proof (e/fvar id)]
           (reify-prop st table problem (:type decl) hyp-proof))
         (catch Exception _ [table problem]))
       [table problem]))
   [table problem]
   lctx))

(defn- add-nat-nonnegativity
  "For each Nat-typed atom, add x ≥ 0 constraint.
   Proof: ↑n ≥ 0 for n : Nat. Uses Nat.zero_le n."
  [st table problem]
  (reduce
   (fn [problem [idx expr]]
     (try
       (let [ty (tc/infer-type st expr)
             ty-whnf (#'tc/cached-whnf st ty)]
         (if (and (e/const? ty-whnf) (= (e/const-name ty-whnf) (:nat-name omega-names)))
           (let [coeffs (vec (concat (repeat idx 0) [1]))
                 ;; Nat.zero_le n : 0 ≤ n
                 ;; Then convert: Iff.mpr (Int.ofNat_le 0 n) (Nat.zero_le n) : ↑0 ≤ ↑n
                 ;; Then: Int.sub_nonneg_of_le ... : 0 ≤ ↑n - ↑0 = ↑n
                 ;; For the constraint 0 + dot([0..1..0], atoms) ≥ 0,
                 ;; the proof is just that ↑n ≥ 0.
                 ;; Since the LC has const=0 and coeffs=[..0,1,0..],
                 ;; lc.eval atoms = 0 + ↑n = ↑n (for single-var case)
                 ;; The proof function: 0 ≤ lc.eval atoms follows from 0 ≤ ↑n
                 proof-fn (fn [atoms-expr]
                            ;; Int.natCast_nonneg n : 0 ≤ ↑n
                            ;; → 0 ≤ lc.eval atoms via le_of_le_of_eq + eval proof
                            (let [n-int (nat-to-int expr)
                                  h-nonneg (e/app (e/const' (name/from-string "Int.natCast_nonneg") []) expr)
                                  eval-result ((mk-coordinate-eval-proof idx) atoms-expr)
                                  eval-lhs (:lhs eval-result)
                                  eval-rhs (:rhs eval-result)
                                  symm-proof (mk-eq-symm eval-lhs eval-rhs (:proof eval-result))]
                              (mk-le-of-le-of-eq int-zero n-int eval-lhs h-nonneg symm-proof)))]
             (add-inequality problem 0 coeffs proof-fn))
           problem))
       (catch Exception _ problem)))
   problem
   (:idx->expr table)))

(defn- add-div-bounds
  "For each div atom (x/k with literal k > 0), add bounds:
   Nat: (x/k)*k ≤ x  via Nat.div_mul_le_self
   Int: k*(x/k) ≤ x  via Int.mul_ediv_self_le (needs k ≠ 0)
        x < k*(x/k)+k via Int.lt_mul_ediv_self_add (needs 0 < k)
   Feeds through reify-prop for proper proof construction."
  [st table problem]
  (reduce
   (fn [[table problem] [idx {:keys [a b type-name expr]}]]
     (try
       (let [nat-type (e/const' (:nat-name omega-names) [])
             k-whnf (#'tc/cached-whnf st b)]
         (if (= type-name (:nat-name omega-names))
           ;; Nat: Nat.div_mul_le_self m n : m / n * n ≤ m
           ;; This is LE.le Nat instLENat (HMul ... (HDiv ... a b) b) a
           (let [div-mul (e/app* (e/const' (:hmul omega-names) [lvl/zero lvl/zero lvl/zero])
                                 nat-type nat-type nat-type
                                 (e/app* (e/const' (name/from-string "instHMul") [lvl/zero])
                                         nat-type (e/const' (name/from-string "instMulNat") []))
                                 expr b)
                 le-type (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                                 nat-type (e/const' (:inst-le-nat omega-names) [])
                                 div-mul a)
                 le-proof (e/app* (e/const' (:nat-div-mul-le-self omega-names) []) a b)
                 [table' problem'] (reify-prop st table problem le-type le-proof)
                 ;; Also add upper bound: a % k < k  via Nat.mod_lt a (pos-proof : 0 < k)
                 ;; This gives the constraint: a - k*(a/k) < k, i.e., a - k*q < k
                 k-val (e/lit-nat-val k-whnf)
                 mod-expr (e/app* (e/const' (:hmod omega-names) [lvl/zero lvl/zero lvl/zero])
                                  nat-type nat-type nat-type
                                  (e/app* (e/const' (name/from-string "instHMod") [lvl/zero])
                                          nat-type (e/const' (name/from-string "Nat.instMod") []))
                                  a b)
                 lt-type (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                 nat-type (e/const' (:inst-lt-nat omega-names) [])
                                 mod-expr b)
                 ;; Proof: Nat.mod_lt a (pos : 0 < k)
                 ;; Need to construct 0 < k proof. For ground k, use decide.
                 pos-prop (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                  nat-type (e/const' (:inst-lt-nat omega-names) [])
                                  (e/lit-nat 0) b)
                 pos-dec (e/app (e/const' (:classical-prop-dec omega-names) []) pos-prop)
                 pos-refl (e/app* (e/const' (:eq-refl omega-names) [(lvl/succ lvl/zero)])
                                  (e/const' (:bool-name omega-names) [])
                                  (e/const' (:bool-true omega-names) []))
                 pos-proof (e/app* (e/const' (name/from-string "of_decide_eq_true") [])
                                   pos-prop pos-dec pos-refl)
                 lt-proof (e/app* (e/const' (:nat-mod-lt omega-names) []) a b pos-proof)]
             (reify-prop st table' problem' lt-type lt-proof))
           ;; Int: feed bounds through reify-prop
           ;; Int.mul_ediv_self_le {x k} (h : k ≠ 0) : k*(x/k) ≤ x
           ;; Int.lt_mul_ediv_self_add {x k} (h : 0 < k) : x < k*(x/k)+k
           (let [k-int (e/app (e/const' (:int-ofnat omega-names) []) (e/lit-nat (e/lit-nat-val k-whnf)))
                 ;; For Int, k needs to be Int literal, build ne-proof and pos-proof via decide
                 ne-zero-prop (e/app* (e/const' (:ne-name omega-names) [u1])
                                      int-type k-int
                                      (e/app (e/const' (:int-ofnat omega-names) []) (e/lit-nat 0)))
                 ;; Use of_decide_eq_true for ground propositions
                 ne-dec (e/app (e/const' (:classical-prop-dec omega-names) []) ne-zero-prop)
                 ne-refl (e/app* (e/const' (:eq-refl omega-names) [(lvl/succ lvl/zero)])
                                 (e/const' (:bool-name omega-names) [])
                                 (e/const' (:bool-true omega-names) []))
                 ne-proof (e/app* (e/const' (name/from-string "of_decide_eq_true") [])
                                  ne-zero-prop ne-dec ne-refl)
                 ;; k*(x/k) ≤ x
                 mul-div (e/app* (e/const' (:hmul omega-names) [lvl/zero lvl/zero lvl/zero])
                                 int-type int-type int-type
                                 (e/app* (e/const' (name/from-string "instHMul") [lvl/zero])
                                         int-type (e/const' (name/from-string "Int.instMul") []))
                                 k-int expr)
                 le-type (e/app* (e/const' (:le-name omega-names) [lvl/zero])
                                 int-type (e/const' (:int-inst-le omega-names) [])
                                 mul-div a)
                 le-proof (e/app* (e/const' (:int-mul-ediv-self-le omega-names) [])
                                  a k-int ne-proof)
                 [table' problem'] (reify-prop st table problem le-type le-proof)
                 ;; x < k*(x/k) + k
                 pos-prop (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                  int-type (e/const' (:int-inst-lt omega-names) [])
                                  (e/app (e/const' (:int-ofnat omega-names) []) (e/lit-nat 0)) k-int)
                 pos-dec (e/app (e/const' (:classical-prop-dec omega-names) []) pos-prop)
                 pos-proof (e/app* (e/const' (name/from-string "of_decide_eq_true") [])
                                   pos-prop pos-dec ne-refl)
                 mul-div-plus-k (e/app* (e/const' (:hadd omega-names) [lvl/zero lvl/zero lvl/zero])
                                        int-type int-type int-type
                                        (e/app* (e/const' (name/from-string "instHAdd") [lvl/zero])
                                                int-type (e/const' (name/from-string "Int.instAdd") []))
                                        mul-div k-int)
                 lt-type (e/app* (e/const' (:lt-name omega-names) [lvl/zero])
                                 int-type (e/const' (:int-inst-lt omega-names) [])
                                 a mul-div-plus-k)
                 lt-proof (e/app* (e/const' (:int-lt-mul-ediv-self-add omega-names) [])
                                  a k-int pos-proof)]
             (reify-prop st table' problem' lt-type lt-proof))))
       (catch Exception _ [table problem])))
   [table problem]
   (:div-atoms table)))

(defn- omega-impl
  "Recursive omega implementation: run solver, then process disjunctions.
   Returns result map with :atom-table and optional :disjunctions-proof,
   or nil if unsolvable."
  [st table problem depth]
  (when (> depth 10)
    (throw (ex-info "omega: disjunction depth exceeded" {})))
  ;; Ensure Nat nonnegativity for any atoms added during disjunction branch processing
  (let [problem (add-nat-nonnegativity st table problem)]
  (let [[table result] (run-omega-solver table problem)]
    (when (System/getProperty "omega.trace")
      (println (str "  solver: possible=" (:possible result)
                    " c=" (count (:constraints result))
                    " d=" (count (:disjunctions result)))))
    (if-not (:possible result)
      (assoc result :atom-table table)
      ;; No contradiction — try disjunctions
      (let [disjs (:disjunctions result)]
        (when (seq disjs)
          (let [{:keys [or-proof left-type right-type branches] :as disj} (first disjs)
                remaining-disjs (vec (rest disjs))]
            (if branches
              ;; Old-style: treat as new-style by reifying the hypothesis type
              (let [{:keys [left-fvar-id right-fvar-id]} disj
                    left-hyp (e/fvar left-fvar-id)
                    right-hyp (e/fvar right-fvar-id)
                    left-problem (assoc problem :disjunctions remaining-disjs)
                    [table' left-problem'] (reify-prop st table left-problem left-type left-hyp)
                    left-result (omega-impl st table' left-problem' (inc depth))]
                (when left-result
                  (let [right-problem (assoc problem :disjunctions remaining-disjs)
                        [table'' right-problem'] (reify-prop st table' right-problem right-type right-hyp)
                        right-result (omega-impl st table'' right-problem' (inc depth))]
                    (when right-result
                      (assoc left-result
                             :atom-table (or (:atom-table right-result) table'')
                             :disjunctions-proof
                             [{:left-result left-result
                               :right-result right-result
                               :left-type left-type
                               :right-type right-type
                               :left-fvar-id left-fvar-id
                               :right-fvar-id right-fvar-id
                               :or-proof or-proof}])))))
              ;; New-style: reify hypothesis in each branch
              ;; Use the original problem (before solving) so constraints are fresh
              (let [left-fvar-id (long (System/nanoTime))
                    right-fvar-id (long (+ 1 (System/nanoTime)))
                    left-hyp (e/fvar left-fvar-id)
                    right-hyp (e/fvar right-fvar-id)
                    nat-sub-info (:nat-sub-info disj)
                    left-problem (assoc problem :disjunctions remaining-disjs)
                    [table' left-problem'] (reify-prop st table left-problem left-type left-hyp)
                    ;; Add Nat.sub equality for left branch if applicable
                    ;; left-hyp proves left-type (e.g. b ≤ a), pass as hyp-proof
                    [table' left-problem'] (if nat-sub-info
                                             (add-nat-sub-equality st table' left-problem' nat-sub-info :left left-hyp)
                                             [table' left-problem'])
                    left-result (omega-impl st table' left-problem' (inc depth))]
                (when left-result
                  (let [right-problem (assoc problem :disjunctions remaining-disjs)
                        [table'' right-problem'] (reify-prop st table' right-problem right-type right-hyp)
                        ;; Add Nat.sub equality for right branch if applicable
                        [table'' right-problem'] (if nat-sub-info
                                                   (add-nat-sub-equality st table'' right-problem' nat-sub-info :right right-hyp)
                                                   [table'' right-problem'])
                        right-result (omega-impl st table'' right-problem' (inc depth))]
                    (when right-result
                      (assoc left-result
                             :atom-table (or (:atom-table right-result) table'')
                             :disjunctions-proof
                             [{:left-result left-result
                               :right-result right-result
                               :left-type left-type
                               :right-type right-type
                               :left-fvar-id left-fvar-id
                               :right-fvar-id right-fvar-id
                               :or-proof or-proof}])))))))))))))


(defn- omega-check
  "Run the omega algorithm. Returns the solved problem with :atom-table metadata, or nil.
   neg-hyp-proof is the proof of ¬P for the negated goal (from by_contra), or nil."
  [st goal-type lctx neg-hyp-proof]
  (let [table (mk-atom-table)
        problem (mk-problem)
        ;; Collect from hypotheses
        [table problem] (collect-hypotheses st table problem lctx)
        ;; Check for direct False hypothesis short-circuit
        _ (when (:direct-false problem)
            ;; Found a direct False proof — return immediately
            (throw (ex-info "::direct-false::"
                            {:direct-false (:direct-false problem)
                             :atom-table table})))
        ;; Negate goal
        [table negated] (negate-goal st table problem goal-type neg-hyp-proof)]
    ;; Check for direct False in negated problem
    (when (:direct-false negated)
      (throw (ex-info "::direct-false::"
                      {:direct-false (:direct-false negated)
                       :atom-table table})))
    (let [base-problem (if (:disjunction negated)
                        ;; Goal negation produced a disjunction — queue it on the original problem
                        (queue-disjunction problem (:disjunction negated))
                        ;; No disjunction — negated IS the problem with constraints added
                        negated)
          nn-problem (add-nat-nonnegativity st table base-problem)
          dichotomy-problem (add-nat-sub-dichotomies nn-problem table)
          [table' ready-problem] (add-div-bounds st table dichotomy-problem)]
      (omega-impl st table' ready-problem 0))))

(declare build-false-proof-from-result)

(defn- build-false-proof-from-result
  "Build a proof of False from an omega result, handling nested disjunctions.
   atoms-expr is the CIC expression for the atoms list."
  [env result atoms-expr]
  (if-let [disj-proofs (seq (:disjunctions-proof result))]
    ;; Has disjunction proofs — build Or.elim chain
    (let [{:keys [left-result right-result left-type right-type
                  left-fvar-id right-fvar-id or-proof]} (first disj-proofs)
          false-type (e/const' (:false-name omega-names) [])
          left-false (build-false-proof-from-result env left-result atoms-expr)
          right-false (build-false-proof-from-result env right-result atoms-expr)
          left-lam (e/lam "h_left" left-type
                          (e/abstract1 left-false left-fvar-id) :default)
          right-lam (e/lam "h_right" right-type
                           (e/abstract1 right-false right-fvar-id) :default)]
      (e/app* (e/const' (:or-elim omega-names) [])
              left-type right-type false-type
              or-proof left-lam right-lam))
    ;; No disjunctions — direct proof from justification
    (prove-false-from-justification env result atoms-expr)))

(defn- strip-forall-binders
  "Strip leading forall binders from goal type, introducing fresh fvars.
   Returns [inner-type fvar-infos lctx'] where fvar-infos is a vec of
   {:id fvar-id :name str :type Expr} in introduction order."
  [st goal-type lctx]
  (loop [ty goal-type, lctx lctx, fvar-infos [], st st]
    (let [ty-whnf (#'tc/cached-whnf st ty)]
      (if (e/forall? ty-whnf)
        (let [fv-id (long (System/nanoTime))
              binder-name (or (e/forall-name ty-whnf) "x")
              ;; Use original ty's binder type when possible to preserve structure
              ;; (WHNF may unfold LE.le to Nat.le etc.)
              use-original (e/forall? ty)
              binder-type (if use-original (e/forall-type ty) (e/forall-type ty-whnf))
              body (e/instantiate1 (if use-original (e/forall-body ty) (e/forall-body ty-whnf))
                                   (e/fvar fv-id))
              lctx' (red/lctx-add-local lctx fv-id binder-name binder-type)
              st' (assoc st :lctx lctx')]
          (recur body lctx'
                 (conj fvar-infos {:id fv-id :name binder-name :type binder-type})
                 st'))
        ;; Return the non-WHNF type to preserve LE.le/LT.lt structure
        ;; (WHNF unfolds LE.le to Nat.le which omega doesn't recognize)
        [ty fvar-infos lctx]))))

(defn- wrap-proof-in-lambdas
  "Wrap a proof term in lambdas for the introduced fvars (reverse of strip-forall-binders).
   Abstracts each fvar and wraps in a lambda."
  [proof-term fvar-infos]
  (reduce (fn [term {:keys [id name type]}]
            (e/lam name type (e/abstract1 term id) :default))
          proof-term
          (reverse fvar-infos)))

(defn omega
  "Close the current goal using the omega decision procedure with proof term construction.

   Strategy:
   1. Try decide first (fast path for ground cases)
   2. Try rfl for def-eq equality goals
   3. Run FM solver with Justification tracking
   4. Construct proof term from Justification tree
   5. Fall back to decide if proof construction fails"
  [ps]
  ;; Fast path: try decide
  (try
    (decide-tac/decide ps)
    (catch Exception _
      ;; Try rfl
      (let [goal (proof/current-goal ps)
            _ (when-not goal (tactic-error! "No goals" {}))
            env (:env ps)
            st (tc/mk-tc-state env)
            st (assoc st :lctx (:lctx goal))
            goal-type (:type goal)
            goal-whnf (#'tc/cached-whnf st goal-type)
            [head args] (e/get-app-fn-args goal-whnf)]
        ;; Try rfl
        (if (and (e/const? head)
                 (= (e/const-name head) (:eq-name omega-names))
                 (= 3 (count args))
                 (tc/is-def-eq st (nth args 1) (nth args 2)))
          (let [proof-term (e/app* (e/const' (:eq-refl omega-names) (e/const-levels head))
                                   (nth args 0) (nth args 1))]
            (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof-term})
                (proof/record-tactic :omega [] (:id goal))))
          ;; Strip leading forall binders (auto-intro) then run omega
          (let [[inner-goal fvar-infos lctx-with-intros]
                (strip-forall-binders st goal-whnf (:lctx goal))
                st-intros (assoc st :lctx lctx-with-intros)
                inner-whnf (#'tc/cached-whnf st-intros inner-goal)
                is-false-goal (and (e/const? inner-whnf)
                                   (= (e/const-name inner-whnf) (:false-name omega-names)))]
            ;; Try omega with by_contra structure for non-False inner goals
            (let [neg-hyp-fvar-id (when-not is-false-goal (long (System/nanoTime)))
                  neg-hyp-proof (when neg-hyp-fvar-id (e/fvar neg-hyp-fvar-id))
                  neg-type (when-not is-false-goal
                             (e/arrow inner-goal (e/const' (:false-name omega-names) [])))
                  lctx' (if neg-hyp-fvar-id
                          (red/lctx-add-local lctx-with-intros neg-hyp-fvar-id "h_neg" neg-type)
                          lctx-with-intros)
                  st' (assoc st :lctx lctx')
                  ;; Run omega, handling direct-false short-circuit
                  result (try
                           (omega-check st' inner-goal lctx' neg-hyp-proof)
                           (catch clojure.lang.ExceptionInfo ex
                             (if (= "::direct-false::" (.getMessage ex))
                               {:direct-false (:direct-false (ex-data ex))
                                :atom-table (:atom-table (ex-data ex))}
                               (throw ex))))]
              (if-not result
                (tactic-error! "omega failed — could not derive contradiction"
                               {:goal goal-type})
                ;; Found contradiction. Try to construct proof term.
                (try
                  (let [false-proof
                        (if (:direct-false result)
                          ;; Direct False hypothesis — already have proof of False
                          (:direct-false result)
                          ;; Build proof (handles simple and disjunction cases via omega-impl)
                          (let [atom-table (:atom-table result)
                                atoms-expr (if atom-table
                                             (build-atoms-expr atom-table)
                                             (e/app (e/const' (name/from-string "List.nil") [lvl/zero]) int-type))]
                            (build-false-proof-from-result env result atoms-expr)))
                        inner-proof (if is-false-goal
                                      false-proof
                                      (let [lam-body (e/abstract1 false-proof neg-hyp-fvar-id)
                                            lam-term (e/lam "h_neg" neg-type lam-body :default)]
                                        (e/app* (e/const' (:decidable-by-contra omega-names) [])
                                                inner-goal
                                                (e/app (e/const' (:classical-prop-dec omega-names) [])
                                                       inner-goal)
                                                lam-term)))
                        ;; Wrap in lambdas for the intro'd forall binders
                        proof-term (wrap-proof-in-lambdas inner-proof fvar-infos)]
                    (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof-term})
                        (proof/record-tactic :omega [] (:id goal))))
                  (catch Exception ex
                    ;; Proof construction failed — fall back to decide
                    (try
                      (decide-tac/decide ps)
                      (catch Exception _
                        (tactic-error!
                         (str "omega: found contradiction but cannot certify: " (.getMessage ex))
                         {:goal goal-type})))))))))))))

;; ============================================================
;; SMT solver: delegated to cic.tactic.omega.smt-backend
;; ============================================================

(defn- smt-solve
  "Run zustand SMT solver on the reified omega problem.
   Returns the problem with :possible false and :proof-false set, or nil."
  [problem]
  (smt-backend/solve problem))

(defn- smt-omega-check
  "Run omega with zustand SMT backend instead of internal FM solver.
   Falls back to internal solver if SMT fails."
  [st goal-type lctx neg-hyp-proof]
  (let [table (mk-atom-table)
        problem (mk-problem)
        [table problem] (collect-hypotheses st table problem lctx)
        _ (when (:direct-false problem)
            (throw (ex-info "::direct-false::"
                            {:direct-false (:direct-false problem)
                             :atom-table table})))
        [table negated] (negate-goal st table problem goal-type neg-hyp-proof)]
    (when (:direct-false negated)
      (throw (ex-info "::direct-false::"
                      {:direct-false (:direct-false negated)
                       :atom-table table})))
    (let [base-problem (if (:disjunction negated)
                        (queue-disjunction problem (:disjunction negated))
                        negated)
          nn-problem (add-nat-nonnegativity st table base-problem)
          dichotomy-problem (add-nat-sub-dichotomies nn-problem table)
          [table' ready-problem] (add-div-bounds st table dichotomy-problem)
          ;; Try SMT solver first
          smt-result (smt-solve ready-problem)]
      (if smt-result
        (assoc smt-result :atom-table table')
        ;; Fall back to internal FM solver
        (omega-impl st table' ready-problem 0)))))

(defn smt-omega
  "Close the current goal using SMT-certified omega.

   Like `omega`, but uses zustand SMT solver with Farkas certificates
   for the constraint solving step. The proof term is fully kernel-verified —
   the SMT solver is only an oracle, not trusted.

   Falls back to internal Fourier-Motzkin if zustand fails."
  [ps]
  ;; Fast path: try decide
  (try
    (decide-tac/decide ps)
    (catch Exception _
      (let [goal (proof/current-goal ps)
            _ (when-not goal (tactic-error! "No goals" {}))
            env (:env ps)
            st (tc/mk-tc-state env)
            st (assoc st :lctx (:lctx goal))
            goal-type (:type goal)
            goal-whnf (#'tc/cached-whnf st goal-type)
            [head args] (e/get-app-fn-args goal-whnf)]
        ;; Try rfl
        (if (and (e/const? head)
                 (= (e/const-name head) (:eq-name omega-names))
                 (= 3 (count args))
                 (tc/is-def-eq st (nth args 1) (nth args 2)))
          (let [proof-term (e/app* (e/const' (:eq-refl omega-names) (e/const-levels head))
                                   (nth args 0) (nth args 1))]
            (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof-term})
                (proof/record-tactic :smt-omega [] (:id goal))))
          ;; Strip forall binders, run smt-omega-check
          (let [[inner-goal fvar-infos lctx-with-intros]
                (strip-forall-binders st goal-whnf (:lctx goal))
                st-intros (assoc st :lctx lctx-with-intros)
                inner-whnf (#'tc/cached-whnf st-intros inner-goal)
                is-false-goal (and (e/const? inner-whnf)
                                   (= (e/const-name inner-whnf) (:false-name omega-names)))
                neg-hyp-fvar-id (when-not is-false-goal (long (System/nanoTime)))
                neg-hyp-proof (when neg-hyp-fvar-id (e/fvar neg-hyp-fvar-id))
                neg-type (when-not is-false-goal
                           (e/arrow inner-goal (e/const' (:false-name omega-names) [])))
                lctx' (if neg-hyp-fvar-id
                        (red/lctx-add-local lctx-with-intros neg-hyp-fvar-id "h_neg" neg-type)
                        lctx-with-intros)
                st' (assoc st :lctx lctx')
                result (try
                         (smt-omega-check st' inner-goal lctx' neg-hyp-proof)
                         (catch clojure.lang.ExceptionInfo ex
                           (if (= "::direct-false::" (.getMessage ex))
                             {:direct-false (:direct-false (ex-data ex))
                              :atom-table (:atom-table (ex-data ex))}
                             (throw ex))))]
            (if-not result
              (tactic-error! "smt-omega failed — could not derive contradiction"
                             {:goal goal-type})
              (try
                (let [false-proof
                      (if (:direct-false result)
                        (:direct-false result)
                        (let [atom-table (:atom-table result)
                              atoms-expr (if atom-table
                                           (build-atoms-expr atom-table)
                                           (e/app (e/const' (name/from-string "List.nil") [lvl/zero]) int-type))]
                          (build-false-proof-from-result env result atoms-expr)))
                      inner-proof (if is-false-goal
                                    false-proof
                                    (let [lam-body (e/abstract1 false-proof neg-hyp-fvar-id)
                                          lam-term (e/lam "h_neg" neg-type lam-body :default)]
                                      (e/app* (e/const' (:decidable-by-contra omega-names) [])
                                              inner-goal
                                              (e/app (e/const' (:classical-prop-dec omega-names) [])
                                                     inner-goal)
                                              lam-term)))
                      proof-term (wrap-proof-in-lambdas inner-proof fvar-infos)]
                  (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof-term})
                      (proof/record-tactic :smt-omega [] (:id goal))))
                (catch Exception ex
                  ;; Fall back to regular omega
                  (try
                    (omega ps)
                    (catch Exception _
                      (tactic-error!
                       (str "smt-omega: found contradiction but cannot certify: " (.getMessage ex))
                       {:goal goal-type}))))))))))))

;; ============================================================
;; Interactive cross-level API
;; ============================================================
;;
;; Exposes the omega reification pipeline as separate steps.
;; Users can inspect the constraint system, try different solver
;; strategies, fork state, and navigate between levels.

(defn reify-goal
  "Reify a proof state goal into an omega problem.
   Returns {:st tc-state, :table atom-table, :problem constraint-problem,
            :inner-goal inner-goal-type, :fvar-infos intro-fvars,
            :neg-hyp-fvar-id by-contra-fvar, :neg-hyp-proof by-contra-proof}
   or throws on failure."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "No goals" {}))
        env (:env ps)
        st (tc/mk-tc-state env)
        st (assoc st :lctx (:lctx goal))
        goal-type (:type goal)
        goal-whnf (#'tc/cached-whnf st goal-type)
        [inner-goal fvar-infos lctx-with-intros]
        (strip-forall-binders st goal-whnf (:lctx goal))
        st-intros (assoc st :lctx lctx-with-intros)
        inner-whnf (#'tc/cached-whnf st-intros inner-goal)
        is-false-goal (and (e/const? inner-whnf)
                           (= (e/const-name inner-whnf) (:false-name omega-names)))
        neg-hyp-fvar-id (when-not is-false-goal (long (System/nanoTime)))
        neg-hyp-proof (when neg-hyp-fvar-id (e/fvar neg-hyp-fvar-id))
        neg-type (when-not is-false-goal
                   (e/arrow inner-goal (e/const' (:false-name omega-names) [])))
        lctx' (if neg-hyp-fvar-id
                (red/lctx-add-local lctx-with-intros neg-hyp-fvar-id "h_neg" neg-type)
                lctx-with-intros)
        st' (assoc st :lctx lctx')
        ;; Reify: collect hypotheses, negate goal, add bounds
        table (mk-atom-table)
        problem (mk-problem)
        [table problem] (collect-hypotheses st' table problem lctx')
        [table negated] (negate-goal st' table problem inner-goal neg-hyp-proof)
        base-problem (if (:disjunction negated)
                       (queue-disjunction problem (:disjunction negated))
                       negated)
        nn-problem (add-nat-nonnegativity st' table base-problem)
        dichotomy-problem (add-nat-sub-dichotomies nn-problem table)
        [table ready-problem] (add-div-bounds st' table dichotomy-problem)]
    {:st st'
     :table table
     :problem ready-problem
     :inner-goal inner-goal
     :fvar-infos fvar-infos
     :neg-hyp-fvar-id neg-hyp-fvar-id
     :neg-hyp-proof neg-hyp-proof
     :is-false-goal is-false-goal
     :ps ps}))

(defn- expr->named-string
  "Convert an expression to a human-readable string, resolving fvar IDs to names from lctx."
  ([st expr] (expr->named-string st expr 0))
  ([st expr depth]
   (if (> depth 15)
     "..."
     (let [d (inc depth)
           lctx (:lctx st)]
       (case (e/tag expr)
         :fvar (let [id (e/fvar-id expr)
                     decl (red/lctx-lookup lctx id)]
                 (or (:name decl) (str "?fv" id)))
         :app (let [[head args] (e/get-app-fn-args expr)]
                (if (e/const? head)
                  ;; Simplify well-known Nat ops
                  (let [cn (name/->string (e/const-name head))]
                    (case cn
                      "Nat.add" (if (= 2 (count args))
                                  (str "(" (expr->named-string st (nth args 0) d)
                                       " + " (expr->named-string st (nth args 1) d) ")")
                                  (str "(" cn " " (clojure.string/join " " (map #(expr->named-string st % d) args)) ")"))
                      "Nat.sub" (if (= 2 (count args))
                                  (str "(" (expr->named-string st (nth args 0) d)
                                       " - " (expr->named-string st (nth args 1) d) ")")
                                  (str "(" cn " " (clojure.string/join " " (map #(expr->named-string st % d) args)) ")"))
                      "Nat.mul" (if (= 2 (count args))
                                  (str "(" (expr->named-string st (nth args 0) d)
                                       " * " (expr->named-string st (nth args 1) d) ")")
                                  (str "(" cn " " (clojure.string/join " " (map #(expr->named-string st % d) args)) ")"))
                      "HAdd.hAdd" (if (= 6 (count args))
                                    (str "(" (expr->named-string st (nth args 4) d)
                                         " + " (expr->named-string st (nth args 5) d) ")")
                                    (str "(" cn " ...)"))
                      "HSub.hSub" (if (= 6 (count args))
                                    (str "(" (expr->named-string st (nth args 4) d)
                                         " - " (expr->named-string st (nth args 5) d) ")")
                                    (str "(" cn " ...)"))
                      "HMul.hMul" (if (= 6 (count args))
                                    (str "(" (expr->named-string st (nth args 4) d)
                                         " * " (expr->named-string st (nth args 5) d) ")")
                                    (str "(" cn " ...)"))
                      "LE.le" (if (>= (count args) 4)
                                (str "(" (expr->named-string st (nth args 2) d)
                                     " ≤ " (expr->named-string st (nth args 3) d) ")")
                                (str "(" cn " ...)"))
                      "LT.lt" (if (>= (count args) 4)
                                (str "(" (expr->named-string st (nth args 2) d)
                                     " < " (expr->named-string st (nth args 3) d) ")")
                                (str "(" cn " ...)"))
                      "Eq" (if (= 3 (count args))
                             (str "(" (expr->named-string st (nth args 1) d)
                                  " = " (expr->named-string st (nth args 2) d) ")")
                             (str "(" cn " ...)"))
                      "Not" (if (= 1 (count args))
                              (str "¬" (expr->named-string st (nth args 0) d))
                              (str "(" cn " ...)"))
                      "Nat.succ" (if (= 1 (count args))
                                   (str "(succ " (expr->named-string st (nth args 0) d) ")")
                                   (str "(" cn " ...)"))
                      ;; Default: abbreviated
                      (str "(" cn " " (clojure.string/join " " (map #(expr->named-string st % d) args)) ")")))
                  ;; Non-const head
                  (str "(" (expr->named-string st head d) " "
                       (clojure.string/join " " (map #(expr->named-string st % d) args)) ")")))
         :lit-nat (str (e/lit-nat-val expr))
         :const (name/->string (e/const-name expr))
         :bvar (str "#" (e/bvar-idx expr))
         ;; Fall through for other forms
         (e/->string expr))))))

(defn- fvar-name
  "Get a human-readable name for an expression (fvar name from lctx, or short string)."
  [st expr]
  (expr->named-string st expr))

(defn show-problem
  "Pretty-print the reified omega problem."
  [{:keys [st table problem]}]
  (println "Atoms:")
  (doseq [[idx expr] (sort-by key (:idx->expr table))]
    (let [sub-info (get (:nat-sub-atoms table) idx)
          display (if sub-info
                    (str (fvar-name st (:a sub-info)) " - "
                         (fvar-name st (:b sub-info)))
                    (fvar-name st expr))]
      (println (str "  x" idx " = " display))))
  (println (str "\nConstraints (" (count (:constraints problem)) "):"))
  (doseq [[k fact] (:constraints problem)]
    (let [{:keys [coeffs constraint]} fact
          {:keys [lower upper]} constraint
          terms (keep-indexed
                 (fn [i c]
                   (when-not (zero? c)
                     (str (when (pos? c) "+") c "*x" i)))
                 coeffs)
          lhs (if (empty? terms) "0" (clojure.string/join " " terms))]
      (println (str "  " lhs
                    (cond
                      (and lower upper (= lower upper)) (str " = " lower)
                      (and lower upper) (str " ∈ [" lower ", " upper "]")
                      lower (str " ≥ " lower)
                      upper (str " ≤ " upper)
                      :else " (unconstrained)")))))
  (when (seq (:equalities problem))
    (println (str "\nEqualities: " (count (:equalities problem)))))
  (when (seq (:disjunctions problem))
    (println (str "\nDisjunctions (" (count (:disjunctions problem)) "):")))
  (doseq [[i d] (map-indexed vector (:disjunctions problem))]
    (println (str "  [" i "] " (expr->named-string st (:left-type d))
                  " ∨ " (expr->named-string st (:right-type d))
                  (when (:nat-sub-info d) " (Nat.sub)")))))

(defn solve-fm
  "Run the Fourier-Motzkin solver on a reified problem.
   Returns the result map or nil."
  [{:keys [st table problem] :as reified}]
  (omega-impl st table problem 0))

(defn solve-smt
  "Run the zustand SMT solver on a reified problem.
   Returns the result map or nil."
  [{:keys [problem] :as reified}]
  (smt-backend/solve problem))

(defn certify
  "Reconstruct the full proof term from a solver result.
   Returns the solved proof state."
  [{:keys [st table problem inner-goal fvar-infos
           neg-hyp-fvar-id neg-hyp-proof is-false-goal ps] :as reified}
   result]
  (let [goal (proof/current-goal ps)
        env (:env ps)
        atom-table (:atom-table result)
        atoms-expr (if atom-table
                     (build-atoms-expr atom-table)
                     (e/app (e/const' (name/from-string "List.nil") [lvl/zero]) int-type))
        false-proof (if (:direct-false result)
                      (:direct-false result)
                      (build-false-proof-from-result env result atoms-expr))
        inner-proof (if is-false-goal
                      false-proof
                      (let [lam-body (e/abstract1 false-proof neg-hyp-fvar-id)
                            lam-term (e/lam "h_neg"
                                            (e/arrow inner-goal
                                                     (e/const' (:false-name omega-names) []))
                                            lam-body :default)]
                        (e/app* (e/const' (:decidable-by-contra omega-names) [])
                                inner-goal
                                (e/app (e/const' (:classical-prop-dec omega-names) [])
                                       inner-goal)
                                lam-term)))
        proof-term (wrap-proof-in-lambdas inner-proof fvar-infos)]
    (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof-term})
        (proof/record-tactic :omega-interactive [] (:id goal)))))

