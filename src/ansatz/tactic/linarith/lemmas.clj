;; The lemma roles of Mathlib/Tactic/Linarith/Lemmas.lean (and the root lemmas linarith's
;; preprocessing and verification apply), for each carrier.
(ns ansatz.tactic.linarith.lemmas
  "Proof-term builders for the lemma ROLES linarith uses. Mathlib states each role once,
   generically (`Linarith.mul_neg`, `Linarith.add_nonpos`, `sub_nonpos_of_le`, …). Two
   families implement them here:

   - `int-family`: Lean core's `Int` lemmas, so linarith works in an `Init`-only
     environment (the bundled medium tier) as well as under Mathlib;
   - `generic-family`: Mathlib's own `Mathlib.Tactic.Linarith.*` lemmas and the root order
     lemmas, instantiated at any ordered field (instances synthesized), used when Mathlib
     is loaded.

   A proof is carried as a record `{:proof term :type prop}`."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.tactic.app-builder :as ab]
            [ansatz.tactic.linarith.parsing :as p]))

(defn c [n & [us]] (e/const' (name/from-string n) (or us [])))
(defn- u1 [] (lvl/succ lvl/zero))

(defn rec [proof type] {:proof proof :type type})

(defn- app-rec
  "mk-app on records: explicit arguments are records (their types are known)."
  [st cname args & opts]
  (let [terms (mapv :proof args)
        types (into {} (map (juxt :proof :type)) args)
        r (apply ab/mk-app st cname terms :types types opts)]
    (rec (:term r) (:type r))))

(defn- id-as
  "`@id T p` — `p` re-typed as the definitionally equal `T`."
  [lvl-u T p]
  (rec (e/app* (c "id" [lvl-u]) T p) T))

;; ------------------------------------------------------------------
;; Int terms, spelled as Lean elaborates them
;; ------------------------------------------------------------------

(def Int (c "Int"))
(def Nat (c "Nat"))
(defn int-num [n]
  (e/app* (c "OfNat.ofNat" [lvl/zero]) Int (e/lit-nat n) (e/app (c "instOfNat") (e/lit-nat n))))
(defn- hop [op inst a b]
  (e/app* (c op [lvl/zero lvl/zero lvl/zero]) Int Int Int inst a b))
(defn int-add [a b] (hop "HAdd.hAdd" (e/app* (c "instHAdd" [lvl/zero]) Int (c "Int.instAdd")) a b))
(defn int-sub [a b] (hop "HSub.hSub" (e/app* (c "instHSub" [lvl/zero]) Int (c "Int.instSub")) a b))
(defn int-mul [a b] (hop "HMul.hMul" (e/app* (c "instHMul" [lvl/zero]) Int (c "Int.instMul")) a b))
(defn int-neg [a] (e/app* (c "Neg.neg" [lvl/zero]) Int (c "Int.instNegInt") a))
(defn int-pow [a k]
  (e/app* (c "HPow.hPow" [lvl/zero lvl/zero lvl/zero]) Int Nat Int
          (e/app* (c "instHPow" [lvl/zero lvl/zero]) Int Nat
                  (e/app* (c "instPowNat" [lvl/zero]) Int (c "Int.instNatPow")))
          a k))
(defn int-lt [a b] (e/app* (c "LT.lt" [lvl/zero]) Int (c "Int.instLTInt") a b))
(defn int-le [a b] (e/app* (c "LE.le" [lvl/zero]) Int (c "Int.instLEInt") a b))
(defn int-eq [a b] (e/app* (c "Eq" [(u1)]) Int a b))
(defn int-cast [n] (e/app* (c "Nat.cast" [lvl/zero]) Int (c "instNatCastInt") n))
(def int-zero (int-num 0))

(defn int-rel [iq a b] (case iq :lt (int-lt a b) :le (int-le a b) :eq (int-eq a b)))

(defn- int-pos-proof
  "`0 < n` for a positive numeral: `Int.lt 0 n` unfolds to `Int.NonNeg (n - (0 + 1))`,
   which the kernel computes to `Int.NonNeg (Int.ofNat (n - 1))`."
  [n]
  (rec (e/app (c "Int.NonNeg.mk") (e/lit-nat (dec' n))) (int-lt int-zero (int-num n))))

(defn- int-nonneg-proof [n]
  (rec (e/app (c "Int.NonNeg.mk") (e/lit-nat n)) (int-le int-zero (int-num n))))

(defn- lhs-of [r] (nth (p/ineq? (:type r)) 2))
(defn- rhs-of [r] (nth (p/ineq? (:type r)) 3))

(defn- congr-arg
  "congrArg (fun x => body[x]) h : f a = f b, with f given as a lambda over Int."
  [st f h]
  (app-rec st "congrArg" [(rec f (e/forall' "x" Int Int :default)) h]))

(def int-family
  {:name :int
   :carrier? (fn [_st ty] (= (p/strip-mdata ty) Int))

   ;; compWithZero
   :sub-nonpos-of-le (fn [st h] (app-rec st "Int.sub_nonpos_of_le" [h]))
   :sub-neg-of-lt (fn [st h] (app-rec st "Int.sub_neg_of_lt" [h]))
   :sub-eq-zero-of-eq (fn [st h] (app-rec st "Int.sub_eq_zero_of_eq" [h]))

   ;; filterComparisons: ¬ a ≤ b → b < a, ¬ a < b → b ≤ a
   :not-le (fn [st h]
             (let [[_ _ a b] (p/ineq? (p/not? (:type h)))
                   iff (ab/mk-app st "Int.not_le" [] :explicit {0 a 1 b})]
               (app-rec st "Iff.mp" [(rec (:term iff) (:type iff)) h])))
   :not-lt (fn [st h]
             (let [[_ _ a b] (p/ineq? (p/not? (:type h)))
                   iff (ab/mk-app st "Int.not_lt" [] :explicit {0 a 1 b})]
               (app-rec st "Iff.mp" [(rec (:term iff) (:type iff)) h])))

   ;; strengthenStrictInt: a < b → a + 1 ≤ b (`Int.lt` is defined as this)
   :strengthen-strict (fn [_st h]
                        (let [[_ _ a b] (p/ineq? (:type h))]
                          (id-as lvl/zero (int-le (int-add a (int-num 1)) b) (:proof h))))

   ;; mkSingleCompZeroOf: h : t R 0, c > 0 ↦ c * t R 0
   :mul-const (fn [st n iq h]
                (let [t (lhs-of h)]
                  (case iq
                    :lt (app-rec st "Int.mul_neg_of_pos_of_neg" [(int-pos-proof n) h])
                    :le (app-rec st "Int.mul_nonpos_of_nonneg_of_nonpos" [(int-nonneg-proof n) h])
                    :eq (let [f (e/lam "x" Int (int-mul (int-num n) (e/bvar 0)) :default)
                              r (congr-arg st f h)]
                          (id-as lvl/zero (int-eq (int-mul (int-num n) t) int-zero) (:proof r))))))

   ;; addIneq: t₁ R₁ 0, t₂ R₂ 0 ↦ t₁ + t₂ R 0
   :add (fn [st iq1 h1 iq2 h2]
          (let [a (lhs-of h1) b (lhs-of h2)
                le-of-eq #(app-rec st "Int.le_of_eq" [%])
                res (fn [iq r] [iq (id-as lvl/zero (int-rel iq (int-add a b) int-zero) (:proof r))])]
            (case [iq1 iq2]
              [:eq :eq] (let [f (e/lam "x" Int (e/lam "y" Int (int-add (e/bvar 1) (e/bvar 0)) :default) :default)
                              r1 (app-rec st "congrArg" [(rec f (e/forall' "x" Int (e/forall' "y" Int Int :default) :default)) h1])
                              r (app-rec st "congr" [r1 h2])]
                          (res :eq r))
              [:eq :le] [:le (app-rec st "Int.add_nonpos" [(le-of-eq h1) h2])]
              [:le :eq] [:le (app-rec st "Int.add_nonpos" [h1 (le-of-eq h2)])]
              [:le :le] [:le (app-rec st "Int.add_nonpos" [h1 h2])]
              [:eq :lt] (res :lt (app-rec st "Int.add_lt_add_of_le_of_lt" [(le-of-eq h1) h2]))
              [:le :lt] (res :lt (app-rec st "Int.add_lt_add_of_le_of_lt" [h1 h2]))
              [:lt :eq] (res :lt (app-rec st "Int.add_lt_add_of_lt_of_le" [h1 (le-of-eq h2)]))
              [:lt :le] (res :lt (app-rec st "Int.add_lt_add_of_lt_of_le" [h1 h2]))
              [:lt :lt] [:lt (app-rec st "Int.add_neg" [h1 h2])])))

   :neg-one-lt-zero (fn [st _ty] (app-rec st "Int.neg_neg_of_pos" [(int-pos-proof 1)]))

   :neg-eq-zero (fn [st h]
                  (let [t (lhs-of h)
                        iff (ab/mk-app st "Int.neg_eq_zero" [] :explicit {0 t})]
                    (app-rec st "Iff.mpr" [(rec (:term iff) (:type iff)) h])))

   ;; Linarith.lt_irrefl after rewriting sm < 0 with sm = 0
   :contradiction (fn [st hlt heq]
                    (let [f (e/lam "x" Int (int-lt (e/bvar 0) int-zero) :default)
                          eqp (app-rec st "congrArg" [(rec f (e/forall' "x" Int (e/sort' lvl/zero) :default)) heq])
                          h00 (app-rec st "Eq.mp" [eqp hlt])
                          h00 (id-as lvl/zero (int-lt int-zero int-zero) (:proof h00))]
                      (rec (e/app* (c "Int.lt_irrefl") int-zero (:proof h00)) (c "False"))))

   ;; nlinarith products
   :le-of-lt (fn [st h] (app-rec st "Int.le_of_lt" [h]))
   :mul-nonneg-np (fn [st ha hb] (app-rec st "Int.mul_nonneg_of_nonpos_of_nonpos" [ha hb]))
   :mul-pos-nn (fn [st ha hb] (app-rec st "Int.mul_pos_of_neg_of_neg" [ha hb]))
   :zero-mul-eq (fn [st ha hb]
                  (let [a (lhs-of ha) b (lhs-of hb)
                        f (e/lam "x" Int (int-mul (e/bvar 0) b) :default)
                        r (congr-arg st f ha)
                        ;; 0 * b = 0 is not closed (b is open): use Int.zero_mul
                        z (rec (e/app (c "Int.zero_mul") b) (int-eq (int-mul int-zero b) int-zero))
                        t (app-rec st "Eq.trans" [r z])]
                    (rec (:proof t) (int-eq (int-mul a b) int-zero))))
   :mul-zero-eq (fn [st ha hb]
                  (let [a (lhs-of ha) b (lhs-of hb)
                        f (e/lam "x" Int (int-mul a (e/bvar 0)) :default)
                        r (congr-arg st f hb)
                        ;; a * 0 = 0 is not closed (a is open): use Int.mul_zero
                        z (rec (e/app (c "Int.mul_zero") a) (int-eq (int-mul a int-zero) int-zero))
                        t (app-rec st "Eq.trans" [r z])]
                    (rec (:proof t) (int-eq (int-mul a b) int-zero))))
   :sq-nonneg (fn [_st a] (rec (e/app (c "Int.sq_nonneg") a) (int-le int-zero (int-pow a (e/lit-nat 2)))))
   :mul-self-nonneg
   (fn [st a]
     ;; Or.elim (Int.le_total 0 a) (fun h => Int.mul_nonneg h h)
     ;;   (fun h => Int.mul_nonneg_of_nonpos_of_nonpos h h)
     (let [goal (int-le int-zero (int-mul a a))
           h0 (e/app* (c "Int.le_total") int-zero a)
           pos (e/lam "h" (int-le int-zero a)
                      (e/app* (c "Int.mul_nonneg") a a (e/bvar 0) (e/bvar 0)) :default)
           neg (e/lam "h" (int-le a int-zero)
                      (e/app* (c "Int.mul_nonneg_of_nonpos_of_nonpos") a a (e/bvar 0) (e/bvar 0)) :default)]
       (rec (e/app* (c "Or.elim") (int-le int-zero a) (int-le a int-zero) goal h0 pos neg) goal)))})

(defn family-for
  "The lemma family for comparisons over `ty`, or nil."
  [st ty]
  (some #(when ((:carrier? %) st ty) %) [int-family]))
