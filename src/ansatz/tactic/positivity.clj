;; Port of Mathlib/Tactic/Positivity/Core.lean (Strictness, orElse, core, compareHyp, solve)
;; and the arithmetic extensions of Mathlib/Tactic/Positivity/Basic.lean (evalAdd, evalMul,
;; evalPow, evalNatCast), with numerals as normNumPositivity and Nat canonically nonnegative.
(ns ansatz.tactic.positivity
  "`positivity`: prove goals `0 ≤ e`, `0 < e`, `e ≠ 0` (and `0 ≠ e`) by recursion on `e`.

   Each subterm gets a `Strictness` — positive, nonnegative, nonzero or none — with a proof;
   an extension per head symbol combines the results of its arguments (`a + b`, `a * b`,
   `a ^ n`, `↑n`), numerals are decided, a Nat is canonically nonnegative, and hypotheses
   `lo ≤ e`, `lo < e`, `e = c`, `e ≠ 0` with numeral bounds are compared, as in Mathlib's
   `Positivity.core`. Results are merged with `orElse` (nonnegative and nonzero make
   positive).

   Carriers: Int and Nat with Lean core lemmas (no Mathlib needed). A goal that is not of
   positivity shape but compares two numerals is handed to norm_num."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.app-builder :as ab]
            [ansatz.tactic.linarith.lemmas :as L]
            [ansatz.tactic.linarith.parsing :as p]
            [ansatz.tactic.proof :as proof]))

(defn- tactic-error! [msg data]
  (throw (ex-info (str "positivity: " msg) (merge {:kind :tactic-error} data))))

(defn- rec [pf ty] {:proof pf :type ty})
(defn- app-rec [st cname args & opts]
  (let [r (apply ab/mk-app st cname (mapv #(if (map? %) (:proof %) %) args)
                 :types (into {} (keep (fn [a] (when (map? a) [(:proof a) (:type a)]))) args)
                 opts)]
    (rec (:term r) (:type r))))

;; ------------------------------------------------------------------
;; carriers
;; ------------------------------------------------------------------

(def ^:private Nat L/Nat)
(def ^:private Int L/Int)
(def ^:private u1 (lvl/succ lvl/zero))

(defn- nat-lt [a b] (e/app* (L/c "LT.lt" [lvl/zero]) Nat (L/c "instLTNat") a b))
(defn- nat-le [a b] (e/app* (L/c "LE.le" [lvl/zero]) Nat (L/c "instLENat") a b))
(defn- ne [ty a b] (e/app* (L/c "Ne" [u1]) ty a b))
(defn- carrier-zero [ty] (if (= ty Int) L/int-zero (e/lit-nat 0)))
(defn- lt [ty a b] (if (= ty Int) (L/int-lt a b) (nat-lt a b)))
(defn- le [ty a b] (if (= ty Int) (L/int-le a b) (nat-le a b)))
(defn- ns-of [ty] (if (= ty Int) "Int" "Nat"))

;; ------------------------------------------------------------------
;; Strictness and orElse
;; ------------------------------------------------------------------

(defn- positive [pf] {:kind :positive :proof pf})
(defn- nonnegative [pf] {:kind :nonnegative :proof pf})
(defn- nonzero [pf] {:kind :nonzero :proof pf})
(def ^:private none {:kind :none})

(defn- to-nonneg [st ty r]
  (case (:kind r)
    :positive (app-rec st (str (ns-of ty) ".le_of_lt") [(:proof r)])
    :nonnegative (:proof r)
    nil))

(defn- to-positive [r] (when (= :positive (:kind r)) (:proof r)))

(defn- to-nonzero [st ty r]
  (case (:kind r)
    :positive (app-rec st (str (ns-of ty) ".ne_of_gt") [(:proof r)])
    :nonzero (:proof r)
    nil))

(defn- lt-of-le-of-ne'
  "lt_of_le_of_ne': 0 ≤ a, a ≠ 0 ⊢ 0 < a, through `lt_iff_le_and_ne`."
  [_st ty pnn pnz]
  (let [[_ _ _ a] (p/ineq? (:type pnn))
        z (carrier-zero ty)
        symm (e/app* (L/c "Ne.symm" [u1]) ty a z (:proof pnz))
        conj (e/app* (L/c "And") (le ty z a) (ne ty z a))]
    (rec (e/app* (L/c "Iff.mpr") (lt ty z a) conj
                 (e/app* (L/c (str (ns-of ty) ".lt_iff_le_and_ne")) z a)
                 (e/app* (L/c "And.intro") (le ty z a) (ne ty z a) (:proof pnn) symm))
         (lt ty z a))))

(defn- safe [f] (try (f) (catch clojure.lang.ExceptionInfo _ none)))

(defn- or-else
  "Mathlib's orElse: keep the better result, combining nonnegative and nonzero."
  [st ty r1 t2]
  (case (:kind r1)
    :none (safe t2)
    :positive r1
    :nonnegative (let [r2 (safe t2)]
                   (case (:kind r2)
                     :positive r2
                     :nonzero (positive (lt-of-le-of-ne' st ty (:proof r1) (:proof r2)))
                     r1))
    :nonzero (let [r2 (safe t2)]
               (case (:kind r2)
                 :positive r2
                 :nonnegative (positive (lt-of-le-of-ne' st ty (:proof r2) (:proof r1)))
                 r1))))

;; ------------------------------------------------------------------
;; numerals (normNumPositivity) and canonical nonnegativity
;; ------------------------------------------------------------------

(defn- nat-zero-le [x] (rec (e/app (L/c "Nat.zero_le") x) (nat-le (e/lit-nat 0) x)))

(defn- numeral-value
  "The integer value of a numeral (`n`, `-n`), or nil."
  [x]
  (let [x (p/strip-mdata x)]
    (or (p/numeral? x)
        (when-let [[h args] (p/head-args x)]
          (when (and (= h "Neg.neg") (= 3 (count args)))
            (some-> (p/numeral? (nth args 2)) -'))))))

(defn- int-pos [n x]
  ;; `0 < n` unfolds to `Int.NonNeg (n - (0 + 1))`, computed by the kernel
  (rec (e/app (L/c "Int.NonNeg.mk") (e/lit-nat (dec' n))) (L/int-lt L/int-zero x)))

(defn- norm-num-positivity [_st ty x]
  (if-let [v (numeral-value x)]
    (cond
      (and (pos? v) (= ty Int)) (positive (int-pos v x))
      (and (pos? v) (= ty Nat))
      (let [prop (nat-lt (e/lit-nat 0) x)]
        (positive (rec (e/app* (L/c "of_decide_eq_true") prop (e/app* (L/c "Nat.decLt") (e/lit-nat 0) x)
                               (e/app* (L/c "Eq.refl" [u1]) (L/c "Bool") (L/c "Bool.true")))
                       prop)))
      (zero? v) (nonnegative (if (= ty Int)
                               (rec (e/app (L/c "Int.le_refl") x) (L/int-le L/int-zero x))
                               (nat-zero-le x)))
      (and (neg? v) (= ty Int))
      (let [[_ args] (p/head-args x)
            n (nth args 2)
            neg-lt (rec (e/app* (L/c "Int.neg_neg_of_pos") n (:proof (int-pos (-' v) n)))
                        (L/int-lt x L/int-zero))]
        (nonzero (rec (e/app* (L/c "Int.ne_of_lt") x L/int-zero (:proof neg-lt)) (ne Int x L/int-zero))))
      :else none)
    none))

(defn- positivity-canon [_st ty x]
  (if (= ty Nat) (nonnegative (nat-zero-le x)) none))

;; ------------------------------------------------------------------
;; hypotheses (compareHyp, compareHypNonzero)
;; ------------------------------------------------------------------

(defn- compare-hyp [st ty x [id decl]]
  (let [h (rec (e/fvar id) (:type decl))
        t (p/strip-mdata (:type decl))
        [iq cty lo hi :as ineq] (p/ineq? t)
        n (ns-of ty)
        same? (fn [a b] (= (p/strip-mdata a) (p/strip-mdata b)))]
    (cond
      (and ineq (same? cty ty) (#{:le :lt} iq) (same? hi x))
      (let [r (norm-num-positivity st ty lo)]
        (case iq
          :le (cond
                (p/zero? lo) (nonnegative h)
                (= :positive (:kind r)) (positive (app-rec st (str n ".lt_of_lt_of_le") [(:proof r) h]))
                (= :nonnegative (:kind r)) (nonnegative (app-rec st (str n ".le_trans") [(:proof r) h]))
                :else none)
          :lt (cond
                (p/zero? lo) (positive h)
                (= :positive (:kind r)) (positive (app-rec st (str n ".lt_trans") [(:proof r) h]))
                (= :nonnegative (:kind r)) (positive (app-rec st (str n ".lt_of_le_of_lt") [(:proof r) h]))
                :else none)))

      (and ineq (= iq :eq) (same? cty ty) (or (same? hi x) (same? lo x)))
      (let [[c h] (if (same? hi x)
                    [lo h]
                    [hi (rec (e/app* (L/c "Eq.symm" [u1]) ty lo hi (:proof h))
                             (e/app* (L/c "Eq" [u1]) ty hi lo))])
            le-cx (app-rec st (str n ".le_of_eq") [h])
            r (norm-num-positivity st ty c)]
        (cond
          (p/zero? c) (nonnegative le-cx)
          (= :positive (:kind r)) (positive (app-rec st (str n ".lt_of_lt_of_le") [(:proof r) le-cx]))
          (= :nonnegative (:kind r)) (nonnegative (app-rec st (str n ".le_trans") [(:proof r) le-cx]))
          :else none))

      :else
      (if-let [[nty a b] (p/ne? t)]
        (cond
          (and (same? nty ty) (p/zero? b) (same? a x)) (nonzero h)
          (and (same? nty ty) (p/zero? a) (same? b x))
          (nonzero (rec (e/app* (L/c "Ne.symm" [u1]) ty a b (:proof h)) (ne ty b a)))
          :else none)
        none))))

;; ------------------------------------------------------------------
;; extensions (Positivity/Basic.lean)
;; ------------------------------------------------------------------

(declare core)

(defn- eval-add [st ty x a b]
  (let [ra (core st ty a) rb (core st ty b)]
    (case [(:kind ra) (:kind rb)]
      [:positive :positive] (positive (if (= ty Int)
                                        (app-rec st "Int.add_pos" [(:proof ra) (:proof rb)])
                                        (app-rec st "Nat.add_pos_left" [(:proof ra) b])))
      [:positive :nonnegative]
      (positive (if (= ty Int)
                  (app-rec st "Int.add_pos_of_pos_of_nonneg" [(:proof ra) (:proof rb)])
                  (app-rec st "Nat.add_pos_left" [(:proof ra) b])))
      [:nonnegative :positive]
      (positive (if (= ty Int)
                  (app-rec st "Int.add_pos_of_nonneg_of_pos" [(:proof ra) (:proof rb)])
                  (app-rec st "Nat.add_pos_right" [a (:proof rb)])))
      [:nonnegative :nonnegative]
      (nonnegative (if (= ty Int) (app-rec st "Int.add_nonneg" [(:proof ra) (:proof rb)]) (nat-zero-le x)))
      (tactic-error! "failed to prove positivity of a sum" {:expr x}))))

(defn- eval-mul [st ty x a b]
  (let [ra (core st ty a) rb (core st ty b)
        n (ns-of ty)
        try-pos #(if-let [pa (to-positive ra)]
                   (if-let [pb (to-positive rb)]
                     (positive (app-rec st (str n ".mul_pos") [pa pb]))
                     none)
                   none)
        try-nn #(if-let [pa (to-nonneg st ty ra)]
                  (if-let [pb (to-nonneg st ty rb)]
                    (nonnegative (if (= ty Int) (app-rec st "Int.mul_nonneg" [pa pb]) (nat-zero-le x)))
                    none)
                  none)
        try-nz #(if-let [pa (to-nonzero st ty ra)]
                  (if-let [pb (to-nonzero st ty rb)]
                    (nonzero (app-rec st (str n ".mul_ne_zero") [pa pb]))
                    none)
                  none)]
    (-> none
        (as-> r (or-else st ty r try-pos))
        (as-> r (or-else st ty r try-nn))
        (as-> r (or-else st ty r try-nz)))))

(defn- eval-pow [st ty x a k]
  (let [kv (p/numeral? k)
        ;; an even literal exponent: 0 ≤ a ^ (2m) for every a
        even (when (and (= ty Int) kv (pos? kv) (even? kv))
               (if (= 2 kv)
                 (nonnegative (rec (e/app (L/c "Int.sq_nonneg") a) (L/int-le L/int-zero x)))
                 (let [m (quot kv 2)
                       sq (L/int-pow a (e/lit-nat 2))
                       outer (app-rec st "Int.pow_nonneg"
                                      [(rec (e/app (L/c "Int.sq_nonneg") a) (L/int-le L/int-zero sq))]
                                      :explicit {1 (e/lit-nat m)})
                       ;; Int.pow_mul : a ^ (2 * m) = (a ^ 2) ^ m; `2 * m` computes to k
                       eqp (rec (e/app* (L/c "Int.pow_mul") a (e/lit-nat 2) (e/lit-nat m))
                                (L/int-eq x (L/int-pow sq (e/lit-nat m))))
                       f (e/lam "y" Int (L/int-le L/int-zero (e/bvar 0)) :default)
                       congr (app-rec st "congrArg" [(rec f (e/forall' "y" Int (e/sort' lvl/zero) :default)) eqp])]
                   (nonnegative (rec (:proof (app-rec st "Eq.mpr" [congr outer])) (L/int-le L/int-zero x))))))]
    (or-else st ty (or even none)
             (fn []
               (let [ra (core st ty a) n (ns-of ty)]
                 (case (:kind ra)
                   :positive (positive (app-rec st (str n ".pow_pos") [(:proof ra)] :explicit {1 k}))
                   :nonnegative (nonnegative (if (= ty Int)
                                               (app-rec st "Int.pow_nonneg" [(:proof ra)] :explicit {1 k})
                                               (nat-zero-le x)))
                   :nonzero (if (= ty Int)
                              (nonzero (app-rec st "Int.pow_ne_zero" [(:proof ra)] :explicit {1 k}))
                              none)
                   none))))))

(defn- eval-sub
  "evalSub: `a - b` is positive given a hypothesis `b < a`, nonnegative given `b ≤ a` (Int)."
  [st ty x a b]
  (if (not= ty Int)
    none
    (reduce
     (fn [r [id decl]]
       (or-else st ty r
                (fn []
                  (let [[iq cty lo hi] (p/ineq? (p/strip-mdata (:type decl)))
                        h (rec (e/fvar id) (:type decl))
                        same? (fn [u v] (= (p/strip-mdata u) (p/strip-mdata v)))]
                    (if (and iq (same? cty Int) (same? lo b) (same? hi a))
                      (case iq
                        :lt (positive (app-rec st "Int.sub_pos_of_lt" [h]))
                        :le (nonnegative (app-rec st "Int.sub_nonneg_of_le" [h]))
                        none)
                      none)))))
     none (filter (fn [[_ d]] (= :local (:tag d))) (sort-by key (:lctx st))))))

(defn- eval-nat-cast [st x n]
  (let [r (core st Nat n)]
    (if (= :positive (:kind r))
      (let [iff (ab/mk-app st "Int.natCast_pos" [] :explicit {0 n})]
        (positive (app-rec st "Iff.mpr" [(rec (:term iff) (:type iff)) (:proof r)])))
      (nonnegative (rec (e/app (L/c "Int.natCast_nonneg") n) (L/int-le L/int-zero x))))))

(defn- extensions
  "The extensions whose pattern matches `x` (Positivity's DiscrTree lookup)."
  [st ty x]
  (let [[h args] (p/head-args x)
        n (count args)]
    (cond
      (and (= h "HAdd.hAdd") (= n 6)) [#(eval-add st ty x (nth args 4) (nth args 5))]
      (and (= h "HMul.hMul") (= n 6)) [#(eval-mul st ty x (nth args 4) (nth args 5))]
      (and (= h "HSub.hSub") (= n 6)) [#(eval-sub st ty x (nth args 4) (nth args 5))]
      (and (= h "Int.sub") (= n 2)) [#(eval-sub st ty x (nth args 0) (nth args 1))]
      (and (= h "HPow.hPow") (= n 6)) [#(eval-pow st ty x (nth args 4) (nth args 5))]
      (and (= h "Int.pow") (= n 2)) [#(eval-pow st ty x (nth args 0) (nth args 1))]
      ;; the concrete operations the ansatz surface elaborates Nat/Int arithmetic to
      (and (contains? #{"Nat.add" "Int.add"} h) (= n 2)) [#(eval-add st ty x (nth args 0) (nth args 1))]
      (and (contains? #{"Nat.mul" "Int.mul"} h) (= n 2)) [#(eval-mul st ty x (nth args 0) (nth args 1))]
      (and (= h "Nat.pow") (= n 2)) [#(eval-pow st ty x (nth args 0) (nth args 1))]
      (and (= h "Nat.cast") (= n 3) (= ty Int)) [#(eval-nat-cast st x (nth args 2))]
      :else [])))

(defn core
  "Positivity.core: the best Strictness of `x : ty`; throws when there is none."
  [st ty x]
  (let [x (p/strip-mdata x)
        r (reduce (fn [r ext] (or-else st ty r ext)) none (extensions st ty x))
        r (or-else st ty r #(norm-num-positivity st ty x))
        r (or-else st ty r #(positivity-canon st ty x))
        r (if (= :positive (:kind r))
            r
            (reduce (fn [r d] (or-else st ty r #(compare-hyp st ty x d)))
                    r (filter (fn [[_ d]] (= :local (:tag d))) (sort-by key (:lctx st)))))]
    (when (= :none (:kind r))
      (tactic-error! "failed to prove positivity/nonnegativity/nonzeroness" {:expr x}))
    r))

;; ------------------------------------------------------------------
;; solve
;; ------------------------------------------------------------------

(defn solve
  "A proof term of `t`: `0 ≤ e`, `0 < e`, `e ≠ 0` or `0 ≠ e`."
  [st t]
  (let [t (p/strip-mdata t)
        [iq ity lo hi] (p/ineq? t)
        [rel ty e] (if (and (#{:le :lt} iq) (p/zero? lo))
                     [iq ity hi]
                     (when-let [[nty a b] (p/ne? t)]
                       (cond (p/zero? b) [:ne nty a]
                             (p/zero? a) [:ne' nty b])))
        ty (some-> ty p/strip-mdata)]
    (when-not (and rel (contains? #{Int Nat} ty))
      (tactic-error! "not a positivity goal" {:goal t}))
    (let [r (core st ty e)
          z (carrier-zero ty)
          fail #(tactic-error! (str "failed to prove " (name rel) ", but it would be possible to prove "
                                    (name (:kind r)))
                               {:goal t})]
      (:proof
       (case rel
         :lt (if (= :positive (:kind r)) (:proof r) (fail))
         :le (or (to-nonneg st ty r) (fail))
         :ne (or (to-nonzero st ty r) (fail))
         :ne' (if-let [nz (to-nonzero st ty r)]
                (rec (e/app* (L/c "Ne.symm" [u1]) ty e z (:proof nz)) (ne ty z e))
                (fail)))))))

(defn positivity
  "Mathlib's `positivity`."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (tactic-error! "no goals" {}))
        st (tc/attach-lctx (tc/mk-tc-state (:env ps)) (:lctx goal))
        target (:type goal)
        term (try (solve st target)
                  (catch clojure.lang.ExceptionInfo ex
                    ;; a numeral comparison that is not a positivity goal (`1 ≤ 2`): norm_num
                    (if-let [ps' (try ((requiring-resolve 'ansatz.tactic.norm-num/numeral-order) st ps target)
                                      (catch Exception _ nil))]
                      (reduced ps')
                      (throw ex))))]
    (if (reduced? term)
      @term
      (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term term})
          (proof/record-tactic :positivity [] (:id goal))))))
