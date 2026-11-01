;; Port of Mathlib/Tactic/Linarith/Verification.lean (proveFalseByLinarith and helpers).
(ns ansatz.tactic.linarith.verification
  "Turn an oracle certificate into a proof of `False`.

   With comparisons `tᵢ Rᵢ 0` and certificate coefficients `cᵢ`, the proof is Mathlib's:
   `Σ cᵢ tᵢ < 0` by folding the scaled comparisons with the addIneq lemmas, `Σ cᵢ tᵢ = 0`
   by the ring discharger, and the contradiction `0 < 0`. The certificate is untrusted;
   the kernel checks the resulting term."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.linarith.lemmas :as L]
            [ansatz.tactic.linarith.parsing :as p]
            [ansatz.tactic.linarith.simplex :as simplex]))

(defn- error! [msg data]
  (throw (ex-info (str "linarith: " msg) (assoc data :kind :tactic-error))))

(def ^:dynamic *trace* nil)
(defn- trace! [k v] (when *trace* (swap! *trace* conj [k v])))

(defn- iq-of [r] (first (p/parse-comp-and-expr (:type r))))

(defn mk-single-comp-zero-of
  "h : t R 0 ↦ [R' (c * t R' 0)]; c = 1 leaves h untouched."
  [st fam c h]
  (let [iq (iq-of h)]
    (cond
      (= c 1) [iq h]
      :else [iq ((:mul-const fam) st c iq h)])))

(defn mk-lt-zero-proof
  "(proof, coeff) pairs ↦ a proof of `Σ cᵢ tᵢ R 0`, R as strong as possible."
  [st fam pairs]
  (when (empty? pairs) (error! "no linear hypotheses found" {}))
  (let [[[h c] & more] pairs
        [iq pf] (mk-single-comp-zero-of st fam c h)]
    (second
     (reduce (fn [[iq pf] [h c]]
               (let [[iq' h'] (mk-single-comp-zero-of st fam c h)]
                 ((:add fam) st iq pf iq' h')))
             [iq pf] more))))

(defn- add-neg-eq-proofs
  "For each `t = 0`, also `-t = 0` (same original index)."
  [st fam indexed]
  (vec (mapcat (fn [[r i]]
                 (if (= :eq (iq-of r))
                   [[r i] [((:neg-eq-zero fam) st r) i]]
                   [[r i]]))
               indexed)))

(defn prove-false-by-linarith
  "`hyps`: proof records of `tᵢ Rᵢ 0`, all over one carrier with family `fam`.
   `discharger`: (fn [eq-type] proof-term) proving `Σ = 0`. Returns [False-proof used-idxs]."
  [st fam discharger hyps]
  (when (empty? hyps) (error! "no args to linarith" {}))
  (let [carrier (nth (p/ineq? (:type (first hyps))) 1)
        l' (add-neg-eq-proofs st fam (map vector hyps (range)))
        inputs (into [[((:neg-one-lt-zero fam) st carrier) nil]] (reverse l'))
        [comps max-var] (p/linear-forms-and-max-var (mapv (comp :type first) inputs))
        _ (trace! :comps comps)
        cert (or (simplex/produce-certificate comps max-var)
                 (error! "linarith failed to find a contradiction"
                         {:comparisons (count comps) :variables (inc max-var)}))
        _ (trace! :certificate cert)
        used (keep-indexed (fn [n [r orig]] (when-let [k (get cert n)] [r k orig])) inputs)
        pairs (mapv (fn [[r k _]] [r k]) used)
        idxs (distinct (keep (fn [[_ _ o]] o) used))
        sm-lt-zero (mk-lt-zero-proof st fam pairs)
        [_ _ sm zero] (p/ineq? (:type sm-lt-zero))
        sort (tc/infer-type st carrier)
        eq-type (e/app* (e/const' (name/from-string "Eq") [(if (e/sort? sort) (e/sort-level sort)
                                                                (lvl/succ lvl/zero))])
                        carrier sm zero)
        sm-eq-zero (L/rec (discharger eq-type) eq-type)]
    [(:proof ((:contradiction fam) st sm-lt-zero sm-eq-zero)) idxs]))
