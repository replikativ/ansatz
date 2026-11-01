;; Port of Mathlib/Tactic/Linarith/Preprocessing.lean.
(ns ansatz.tactic.linarith.preprocessing
  "linarith's preprocessing chain over proof records `{:proof :type}`, in Mathlib's order:
   splitConjunctions, filterComparisons, natToInt, strengthenStrictInt, compWithZero
   (cancelDenoms is a no-op for the carriers handled here), and for nlinarith the
   nlinarithExtras products and squares. removeNe is the optional `splitNe` branching."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.tactic.linarith.lemmas :as L]
            [ansatz.tactic.linarith.parsing :as p]))

(defn- carrier [r] (some-> (p/ineq-or-not-ineq? (:type r)) (nth 2)))

(defn- nat? [ty] (= (p/strip-mdata ty) L/Nat))

;; ------------------------------------------------------------------
;; splitConjunctions
;; ------------------------------------------------------------------

(defn split-conjunctions [_st hs]
  (letfn [(aux [r]
            (let [[h args] (p/head-args (:type r))]
              (if (and (= h "And") (= 2 (count args)))
                (let [[a b] args]
                  (concat (aux (L/rec (e/app* (L/c "And.left") a b (:proof r)) a))
                          (aux (L/rec (e/app* (L/c "And.right") a b (:proof r)) b))))
                [r])))]
    (vec (mapcat aux hs))))

;; ------------------------------------------------------------------
;; filterComparisons
;; ------------------------------------------------------------------

(def nat-family
  "Nat versions of the negation lemmas (Nat comparisons are moved to Int afterwards)."
  {:not-le (fn [_st h]
             (let [[_ _ a b] (p/ineq? (p/not? (:type h)))
                   concl (e/app* (L/c "LT.lt" [lvl/zero]) L/Nat (L/c "instLTNat") b a)]
               (L/rec (e/app* (L/c "Iff.mp") (:type h) concl
                              (e/app* (L/c "Nat.not_le") a b) (:proof h))
                      concl)))
   :not-lt (fn [_st h]
             (let [[_ _ a b] (p/ineq? (p/not? (:type h)))
                   concl (e/app* (L/c "LE.le" [lvl/zero]) L/Nat (L/c "instLENat") b a)]
               (L/rec (e/app* (L/c "Iff.mp") (:type h) concl
                              (e/app* (L/c "Nat.not_lt") a b) (:proof h))
                      concl)))})

(defn- negation-family [st fam-for ty]
  (if (nat? ty) nat-family (fam-for st ty)))

(defn filter-comparisons
  "Keep comparisons; push a negated `≤`/`<` into the opposite strict/weak comparison; drop
   negated equalities and anything else."
  [st fam-for hs]
  (vec (mapcat (fn [r]
                 (if-let [[pos? iq ty] (p/ineq-or-not-ineq? (:type r))]
                   (if pos?
                     [r]
                     (if-let [fam (negation-family st fam-for ty)]
                       (case iq
                         :le [((:not-le fam) st (L/rec (:proof r) (p/strip-mdata (:type r))))]
                         :lt [((:not-lt fam) st (L/rec (:proof r) (p/strip-mdata (:type r))))]
                         :eq [])
                       []))
                   []))
               hs)))

;; ------------------------------------------------------------------
;; natToInt
;; ------------------------------------------------------------------

(defn push-cast
  "The Int expression `((x : Nat) : Int)` with the cast pushed through `+`, `*`, numeral
   powers and numerals, as `push_cast` does. Every step is definitional (Int.natCast_add,
   natCast_mul, natCast_pow, natCast_ofNat are `rfl`), so the result is used as a type
   ascription. Truncated subtraction, division and everything else stay atoms `↑x`."
  [x]
  (let [x (p/strip-mdata x)]
    (if-let [n (p/numeral? x)]
      (L/int-num n)
      (let [[h args] (p/head-args x)
            n (count args)]
        (cond
          (and (= h "HAdd.hAdd") (= n 6)) (L/int-add (push-cast (nth args 4)) (push-cast (nth args 5)))
          (and (= h "HMul.hMul") (= n 6)) (L/int-mul (push-cast (nth args 4)) (push-cast (nth args 5)))
          (and (= h "Nat.add") (= n 2)) (L/int-add (push-cast (nth args 0)) (push-cast (nth args 1)))
          (and (= h "Nat.mul") (= n 2)) (L/int-mul (push-cast (nth args 0)) (push-cast (nth args 1)))
          (and (= h "Nat.succ") (= n 1)) (L/int-add (push-cast (nth args 0)) (L/int-num 1))
          (and (= h "HPow.hPow") (= n 6) (p/numeral? (nth args 5)))
          (L/int-pow (push-cast (nth args 4)) (e/lit-nat (p/numeral? (nth args 5))))
          (and (= h "Nat.pow") (= n 2) (p/numeral? (nth args 1)))
          (L/int-pow (push-cast (nth args 0)) (e/lit-nat (p/numeral? (nth args 1))))
          :else (L/int-cast x))))))

(defn- nat-cast-atoms
  "getNatComparisons: the maximal `((t : ℕ) : ℤ)` subterms reachable through + * - neg."
  [x]
  (let [x (p/strip-mdata x)
        [h args] (p/head-args x)
        n (count args)]
    (cond
      (and (= h "Nat.cast") (= n 3)) [(nth args 2)]
      (and (contains? #{"HAdd.hAdd" "HMul.hMul" "HSub.hSub"} h) (= n 6))
      (concat (nat-cast-atoms (nth args 4)) (nat-cast-atoms (nth args 5)))
      (and (= h "Neg.neg") (= n 3)) (nat-cast-atoms (nth args 2))
      :else [])))

(defn nat-to-int
  "Move Nat comparisons to Int (`Int.ofNat_le`/`ofNat_lt`/`ofNat_inj`, casts pushed), and add
   `0 ≤ ↑t` for every cast atom of every comparison."
  [_st hs]
  (let [hs (mapv (fn [r]
                   (let [[iq ty a b] (p/ineq? (:type r))]
                     (if (and iq (nat? ty))
                       (let [lemma (case iq :le "Int.ofNat_le" :lt "Int.ofNat_lt" :eq "Int.ofNat_inj")
                             cast-ty (L/int-rel iq (L/int-cast a) (L/int-cast b))
                             pushed (L/int-rel iq (push-cast a) (push-cast b))
                             pr (e/app* (L/c "Iff.mpr") cast-ty (:type r)
                                        (e/app* (L/c lemma) a b) (:proof r))]
                         (L/rec (e/app* (L/c "id" [lvl/zero]) pushed pr) pushed))
                       r)))
                 hs)
        atoms (distinct (mapcat (fn [r]
                                  (when-let [[_ _ a b] (p/ineq? (:type r))]
                                    (concat (nat-cast-atoms a) (nat-cast-atoms b))))
                                hs))
        nonneg (mapv (fn [t] (L/rec (e/app (L/c "Int.natCast_nonneg") t)
                                    (L/int-le L/int-zero (L/int-cast t))))
                     atoms)]
    (into nonneg hs)))

;; ------------------------------------------------------------------
;; strengthenStrictInt, compWithZero
;; ------------------------------------------------------------------

(defn strengthen-strict-int [st fam-for hs]
  (mapv (fn [r]
          (let [[iq ty] (p/ineq? (:type r))]
            (if (and (= iq :lt) (= (p/strip-mdata ty) L/Int))
              ((:strengthen-strict (fam-for st ty)) st r)
              r)))
        hs))

(defn rearrange-comparison
  "`a R b` → `a - b R 0`."
  [st fam r]
  (case (first (p/ineq? (:type r)))
    :le ((:sub-nonpos-of-le fam) st r)
    :lt ((:sub-neg-of-lt fam) st r)
    :eq ((:sub-eq-zero-of-eq fam) st r)))

(defn comp-with-zero [st fam-for hs]
  (vec (keep (fn [r]
               (let [[_ ty] (p/ineq? (:type r))]
                 (when-let [fam (fam-for st ty)]
                   (try (rearrange-comparison st fam r)
                        (catch clojure.lang.ExceptionInfo _ nil)))))
             hs)))

;; ------------------------------------------------------------------
;; nlinarithExtras
;; ------------------------------------------------------------------

(defn- find-squares
  "findSquares: (atom, true) for `a ^ 2`, (atom, false) for `a * a`; atoms numbered in
   first-seen order (AtomM)."
  [acc x]
  (let [x (p/strip-mdata x)]
    (if (e/has-loose-bvars? x)
      acc
      (let [[h args] (p/head-args x)
            n (count args)
            atom! (fn [acc a]
                    (let [a (p/strip-mdata a)
                          i (or (get-in acc [:index a]) (count (:index acc)))]
                      [(assoc-in acc [:index a] i) i]))
            children (fn [acc] (reduce find-squares acc (if (e/app? x) [(e/app-fn x) (e/app-arg x)] [])))
            sq (fn [base] (let [acc (find-squares acc base)
                                [acc i] (atom! acc base)]
                            (update acc :found conj [i true base])))]
        (cond
          (and (= h "HPow.hPow") (= n 6) (= 2 (p/numeral? (nth args 5)))) (sq (nth args 4))
          (and (= h "Int.pow") (= n 2) (= 2 (p/numeral? (nth args 1)))) (sq (nth args 0))
          (and (contains? #{"HMul.hMul" "Int.mul"} h) (contains? #{6 2} n)
               (let [[a b] (if (= n 6) [(nth args 4) (nth args 5)] args)]
                 (= (p/strip-mdata a) (p/strip-mdata b))))
          (let [a (if (= n 6) (nth args 4) (nth args 0))
                acc (find-squares acc a)
                [acc i] (atom! acc a)]
            (update acc :found conj [i false (p/strip-mdata a)]))
          :else (children acc))))))

(defn- square-proofs [st fam fam-for ls]
  (let [acc (reduce (fn [acc r] (find-squares acc (:type r))) {:index {} :found #{}} (reverse ls))
        found (sort-by (fn [[i sq? _]] [i (if sq? 1 0)]) (:found acc))
        new-es (keep (fn [[_ sq? a]]
                       (try ((if sq? (:sq-nonneg fam) (:mul-self-nonneg fam)) st a)
                            (catch clojure.lang.ExceptionInfo _ nil)))
                     found)]
    (comp-with-zero st fam-for new-es)))

(defn- product-proofs [st fam fam-for ls]
  (let [with-comps (mapv (fn [r] [(or (first (p/parse-comp-and-expr (:type r))) :lt) r]) ls)
        n (count with-comps)
        products
        (for [i (range n) j (range i n)
              :let [[ia a] (nth with-comps i) [ib b] (nth with-comps j)
                    r (try
                        (cond
                          (= ia :eq) ((:zero-mul-eq fam) st a b)
                          (= ib :eq) ((:mul-zero-eq fam) st a b)
                          (and (= ia :lt) (= ib :lt)) ((:mul-pos-nn fam) st a b)
                          (and (= ia :lt) (= ib :le)) ((:mul-nonneg-np fam) st ((:le-of-lt fam) st a) b)
                          (and (= ia :le) (= ib :lt)) ((:mul-nonneg-np fam) st a ((:le-of-lt fam) st b))
                          :else ((:mul-nonneg-np fam) st a b))
                        (catch clojure.lang.ExceptionInfo _ nil))]
              :when r]
          r)]
    (comp-with-zero st fam-for (vec products))))

(defn nlinarith-extras
  "For every `t` with `t^2` or `t*t` in a hypothesis, `t^2 ≥ 0` / `t*t ≥ 0`; for every pair of
   comparisons `t₁ R₁ 0`, `t₂ R₂ 0` (the diagonal included), the product `t₁*t₂ R 0`."
  [st fam-for ls]
  (let [by-type (group-by (fn [r] (nth (p/ineq? (:type r)) 1)) ls)]
    (vec (mapcat (fn [[ty ls]]
                   (if-let [fam (fam-for st ty)]
                     (let [new-es (square-proofs st fam fam-for ls)
                           products (product-proofs st fam fam-for (into (vec new-es) ls))]
                       (concat new-es ls products))
                     ls))
                 by-type))))

;; ------------------------------------------------------------------
;; the chain
;; ------------------------------------------------------------------

(defn preprocess
  "Run the default preprocessors (and nlinarith's when `nonlinear?`) over `hs`."
  [st fam-for hs {:keys [nonlinear? split-hypotheses?] :or {split-hypotheses? true}}]
  (cond-> hs
    split-hypotheses? (->> (split-conjunctions st))
    true (->> (filter-comparisons st fam-for))
    true (->> (nat-to-int st))
    true (->> (strengthen-strict-int st fam-for))
    true (->> (comp-with-zero st fam-for))
    nonlinear? (->> (nlinarith-extras st fam-for))))
