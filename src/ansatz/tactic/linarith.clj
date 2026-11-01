;; Port of Mathlib/Tactic/Linarith/Frontend.lean: linarith and nlinarith.
;; Oracle: linarith/simplex.clj (Oracle/SimplexAlgorithm), parsing: linarith/parsing.clj
;; (Parsing.lean, Datatypes.lean), preprocessing: linarith/preprocessing.clj
;; (Preprocessing.lean), certificate checking: linarith/verification.clj
;; (Verification.lean), lemma roles: linarith/lemmas.clj (Lemmas.lean).
(ns ansatz.tactic.linarith
  "`linarith`: prove a goal that follows linearly from the comparisons in the context.

   As in Mathlib: an inequality goal is negated into a hypothesis (an equality goal is
   split into `≤` both ways, any other goal is closed by `exfalso`); the hypotheses are
   preprocessed into the form `t R 0` (R ∈ {<, ≤, =}), Nat comparisons moved to Int;
   they are partitioned by carrier, the goal's carrier first; the simplex oracle searches
   for a nonnegative combination `Σ cᵢ tᵢ` that is identically zero yet `< 0`; the
   certificate becomes a proof of `False` whose `Σ cᵢ tᵢ = 0` step is discharged by `ring`.

   `nlinarith` runs the same with the nlinarith preprocessing: squares of atoms and pairwise
   products of all hypotheses (and the negated goal) are added before the oracle runs, so
   the certificate may use products — a Positivstellensatz certificate of degree 2.

   Carriers: Int (Lean core lemmas, works in an Init-only environment) and Nat (moved to
   Int). Every proof is checked by the kernel."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.app-builder :as ab]
            [ansatz.tactic.linarith.lemmas :as L]
            [ansatz.tactic.linarith.parsing :as p]
            [ansatz.tactic.linarith.preprocessing :as pre]
            [ansatz.tactic.linarith.verification :as ver]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.ring :as ring]))

(defn- error! [msg data]
  (throw (ex-info (str "linarith: " msg) (merge {:kind :tactic-error} data))))

(defn- fam-for [st ty] (L/family-for st ty))

(defn- carrier-of [r] (nth (p/ineq? (:type r)) 1))

(defn- partition-by-type
  "partitionByTypeIdx: [[carrier [[record original-index] …]] …] in first-seen order."
  [rs]
  (reduce (fn [acc [r i]]
            (let [ty (p/strip-mdata (carrier-of r))
                  k (first (keep-indexed (fn [j [t _]] (when (= t ty) j)) acc))]
              (if k (update-in acc [k 1] conj [r i]) (conj acc [ty [[r i]]]))))
          [] (map vector rs (range))))

(defn- discharger [env lctx]
  (fn [eq-type] (ring/prove-eq env lctx eq-type)))

(defn- run-linarith
  "Preprocess `hyps` and find a contradiction among them. Returns a proof of False."
  [st pref-type hyps opts]
  (let [rs (pre/preprocess st fam-for hyps opts)
        groups (partition-by-type rs)
        pref (some-> pref-type p/strip-mdata)
        groups (if pref
                 (concat (filter #(= (first %) pref) groups) (remove #(= (first %) pref) groups))
                 groups)
        disch (discharger (:env st) (:lctx st))
        errors (atom [])]
    (or (some (fn [[ty grp]]
                (when-let [fam (fam-for st ty)]
                  (try (first (ver/prove-false-by-linarith st fam disch (mapv first grp)))
                       (catch clojure.lang.ExceptionInfo ex
                         (swap! errors conj (.getMessage ex))
                         nil))))
              groups)
        (error! "linarith failed to find a contradiction"
                {:carriers (mapv first groups) :errors @errors}))))

;; ------------------------------------------------------------------
;; goals
;; ------------------------------------------------------------------

(defn- fresh-hyp
  "A fresh local `h : ty` in st; returns [st' fvar]."
  [st ty]
  (let [id (max (inc (reduce max -1 (keys (:lctx st)))) @(:next-id st))]
    (swap! (:next-id st) (fn [v] (max v (inc id))))
    [(assoc st :lctx (red/lctx-add-local (:lctx st) id "h" ty)) (e/fvar id)]))

(defn- under-hyp
  "Prove False with an extra hypothesis of type `ty`; returns `fun h : ty => proof`."
  [st ty hyps opts]
  (let [[st' fv] (fresh-hyp st ty)
        [_ carrier] (p/ineq? ty)
        pf (run-linarith st' carrier (into [(L/rec fv ty)] hyps) opts)]
    (e/lam "h" ty (e/abstract1 pf (e/fvar-id fv)) :default)))

(defn- lt-ty [ty a b]
  (if (= (p/strip-mdata ty) L/Int)
    (L/int-lt a b)
    (e/app* (L/c "LT.lt" [lvl/zero]) L/Nat (L/c "instLTNat") a b)))

(defn- le-ty [ty a b]
  (if (= (p/strip-mdata ty) L/Int)
    (L/int-le a b)
    (e/app* (L/c "LE.le" [lvl/zero]) L/Nat (L/c "instLENat") a b)))

(defn- ns-of [ty] (if (= (p/strip-mdata ty) L/Int) "Int" "Nat"))

(defn- prove-goal
  "The proof term for `target` from the comparisons `hyps` (records)."
  [st target hyps opts]
  (let [target (p/strip-mdata target)
        ineq (p/ineq? target)
        [iq ty a b] ineq
        supported? (and ty (contains? #{L/Int L/Nat} (p/strip-mdata ty)))]
    (cond
      (= target (L/c "False")) (run-linarith st nil hyps opts)

      ;; a < b: assume b ≤ a (lt_of_not_ge)
      (and supported? (= :lt iq))
      (e/app* (L/c (str (ns-of ty) ".lt_of_not_ge")) b a (under-hyp st (le-ty ty b a) hyps opts))

      ;; a ≤ b: assume b < a (le_of_not_gt)
      (and supported? (= :le iq))
      ;; Int.le_of_not_gt {a b} : ¬a > b → a ≤ b; Nat.le_of_not_gt {a b} : ¬b > a → b ≤ a
      (let [[x y] (if (= "Int" (ns-of ty)) [a b] [b a])]
        (e/app* (L/c (str (ns-of ty) ".le_of_not_gt")) x y (under-hyp st (lt-ty ty b a) hyps opts)))

      ;; a = b: both ≤ (eq_of_not_lt_of_not_gt)
      (and supported? (= :eq iq))
      (let [n (ns-of ty)
            not-lt (fn [x y] ; ¬ x < y → y ≤ x
                     (e/app* (L/c "Iff.mp")
                             (e/app (L/c "Not") (lt-ty ty x y)) (le-ty ty y x)
                             (e/app* (L/c (str n ".not_lt")) x y)
                             (under-hyp st (lt-ty ty x y) hyps opts)))]
        (e/app* (L/c (str n ".le_antisymm")) a b (not-lt b a) (not-lt a b)))

      ;; any other ordered field (Mathlib): getContrLemma's lt_of_not_ge / le_of_not_gt /
      ;; eq_of_not_lt_of_not_gt, the hypothesis read off the lemma's binder
      (and ty (#{:lt :le :eq} iq) (not supported?) (L/family-for st ty))
      (let [contr (fn [r]
                    ;; r : ¬ P → goal; returns (r (fun h : P => False-proof))
                    (let [[_ binder-ty] [nil (e/forall-type (:type r))]
                          P (p/not? binder-ty)]
                      (e/app (:term r) (under-hyp st P hyps opts))))]
        (case iq
          :lt (contr (ab/mk-app st "lt_of_not_ge" [] :expected target))
          :le (contr (ab/mk-app st "le_of_not_gt" [] :expected target))
          :eq (let [r (ab/mk-app st "Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt" [a b])
                    t1 (e/forall-type (:type r))
                    p1 (p/not? t1)
                    t2 (e/forall-type (e/forall-body (:type r)))
                    p2 (p/not? t2)]
                (e/app* (:term r) (under-hyp st p1 hyps opts) (under-hyp st p2 hyps opts)))))

      ;; ¬ p for a comparison p: assume p
      (and (p/not? target) (p/ineq? (p/not? target)))
      (under-hyp st (p/not? target) hyps opts)

      ;; anything else: exfalso
      :else
      (let [sort (tc/infer-type st target)
            u (if (e/sort? sort) (e/sort-level sort) lvl/zero)]
        (e/app* (L/c "False.elim" [u]) target (run-linarith st nil hyps opts))))))

(defn- local-hyps [lctx]
  (vec (keep (fn [[id decl]]
               (when (= :local (:tag decl)) (L/rec (e/fvar id) (:type decl))))
             (sort-by key lctx))))

(defn linarith*
  "Close the main goal. Options:
   - `:only?`       use only `:extra` (and the negated goal), not the local context
   - `:extra`       additional proof terms
   - `:nonlinear?`  run the nlinarith preprocessing"
  [ps & {:keys [only? extra nonlinear?]}]
  (let [goal (proof/current-goal ps)
        _ (when-not goal (error! "no goals" {}))
        st (tc/attach-lctx (tc/mk-tc-state (:env ps)) (:lctx goal))
        extra (mapv (fn [t] (L/rec t (tc/infer-type st t))) extra)
        hyps (if only? extra (into (local-hyps (:lctx goal)) extra))
        term (prove-goal st (:type goal) hyps {:nonlinear? nonlinear?})]
    (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term term})
        (proof/record-tactic (if nonlinear? :nlinarith :linarith) [] (:id goal)))))

(defn linarith
  "Mathlib's `linarith`."
  [ps & opts]
  (apply linarith* ps opts))

(defn nlinarith
  "Mathlib's `nlinarith`: linarith with the products-and-squares preprocessing."
  [ps & {:as opts}]
  (apply linarith* ps (mapcat identity (assoc opts :nonlinear? true))))
