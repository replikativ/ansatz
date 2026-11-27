(ns ansatz.meta.constructions.indpred-below
  "Lean v4.36.0 Meta/IndPredBelow.lean mkBelow for a recursive inductive predicate: `I.below` is
   itself an inductive predicate (one constructor per constructor of `I`, carrying the motive
   proofs and the nested below proofs of its recursive arguments), and `I.brecOn` is a theorem.
   A proof cannot be eliminated into a Prop that contains nested proofs, so the data `below`
   (built by recursion) does not apply."
  (:require [ansatz.meta.constructions.util :as u]
            [ansatz.meta.constructions.cases-on :as cases-on]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]))

(defn- ih-index
  "isIH: the index of the motive at the head of `type`'s forall body, or nil."
  [ctx motives type]
  (let [[_ body] (u/forall-telescope ctx type)
        h (e/get-app-fn body)]
    (first (keep-indexed (fn [i m] (when (= m h) i)) motives))))

(defn- below-app [below-names lps params motives i]
  (u/app (u/const' (nth below-names i) (mapv lvl/param lps)) (concat params motives)))

(defn- ih->below
  "ihTypeToBelowType: `(ys) → motive_j args` ↦ `(ys) → I_j.below params motives args`."
  [ctx below-names lps params motives type]
  (let [[ys body] (u/forall-telescope ctx type)
        j (first (keep-indexed (fn [i m] (when (= m (e/get-app-fn body)) i)) motives))]
    (u/mk-forall-fvars ctx ys (u/app (below-app below-names lps params motives j) (e/get-app-args body)))))

(defn- to-implicit
  "toImplicit: every binder but the last implicit."
  [t]
  (if (and (e/forall? t) (e/forall? (e/forall-body t)))
    (e/forall' (e/forall-name t) (e/forall-type t) (to-implicit (e/forall-body t)) :implicit)
    t))

(defn mk-below
  "`env` with `I.below` (an inductive predicate) and `I.brecOn` (a theorem) for every type of
   `n`'s block when `n` is a safe, recursive inductive predicate; otherwise `env`."
  [env n]
  (let [ind (env/lookup! env (name/from-string (str n)))
        ctx0 (u/context env)]
    (if (or (.isUnsafe ind) (not (.isRec ind)) (not (u/prop-former? ctx0 (.type ind)))
            (env/lookup env (name/from-string (str n ".below"))))
      env
      (let [lps (vec (.levelParams ind))
            rec (env/lookup! env (name/from-string (str n ".rec")))
            large? (> (count (.levelParams rec)) (count lps))
            rec-type (if large?
                       (e/instantiate-level-params (.type rec) {(first (.levelParams rec)) lvl/zero})
                       (.type rec))
            np (.numParams rec) nm (.numMotives rec) nn (.numMinors rec)
            all (mapv str (.all ind))
            names (fn [suffix] (into (mapv #(str % suffix) all)
                                     (map #(str (first all) suffix "_" %) (range 1 (inc (.numNested ind))))))
            below-names (names ".below") brecon-names (names ".brecOn")
            rec-names (names ".rec")
            ctx (u/context env)
            [xs _] (u/forall-telescope ctx rec-type (+ np nm nn))
            params (subvec xs 0 np) motives (subvec xs np (+ np nm)) minors (subvec xs (+ np nm))
            ;; the recursor's parameters and motives are implicit binders
            _ (u/implicit! ctx (into params motives))
            ;; mkBelowInductives: one inductive predicate per motive, in one declaration
            types
            (mapv (fn [i motive]
                    (let [ctors (filter #(= i (ih-index ctx motives (u/infer-type ctx %))) minors)]
                      [(nth below-names i)
                       (u/mk-forall-fvars ctx (into params motives) (to-implicit (u/infer-type ctx motive)))
                       (mapv (fn [minor]
                               (let [[args body] (u/forall-telescope ctx (u/infer-type ctx minor))
                                     vars (reduce (fn [vars a]
                                                    (let [t (u/infer-type ctx a)]
                                                      (if (ih-index ctx motives t)
                                                        (conj vars (u/local-decl ctx "ih" (ih->below ctx below-names lps params motives t)) a)
                                                        (conj vars a))))
                                                  [] args)]
                                 [(str (nth below-names i) "." (:name (u/decl ctx minor)))
                                  (u/mk-forall-fvars ctx (into (into params motives) vars)
                                                     (ih->below ctx below-names lps params motives body))]))
                             ctors)]))
                  (range nm) motives)
            env (env/add-inductive env (env/mk-inductive-decl lps (+ np nm) false types))
            env (reduce (fn [env b] (cases-on/mk-cases-on env b)) env below-names)
            _ (u/set-env! ctx env)
            _ (u/implicit! ctx (into params motives))
            ;; mkBRecOn: F_i : ∀ is x, I_i.below … is x → motive_i is x
            fs (mapv (fn [i motive]
                       (let [[majors _] (u/forall-telescope ctx (u/infer-type ctx motive))]
                         (u/local-decl ctx (str "F_" (inc i))
                                       (u/mk-forall-fvars ctx majors
                                                          (u/mk-arrow ctx (u/app (below-app below-names lps params motives i) majors)
                                                                      (u/app motive majors))))))
                     (range nm) motives)
            rec-motives (mapv #(below-app below-names lps params motives %) (range nm))
            rec-minors
            (mapv (fn [minor]
                    (let [[args body] (u/forall-telescope ctx (u/infer-type ctx minor))
                          i (ih-index ctx motives (u/infer-type ctx minor))
                          [vars cargs]
                          (reduce (fn [[vars cargs] a]
                                    (let [t (u/infer-type ctx a)]
                                      (if-let [j (ih-index ctx motives t)]
                                        (let [new-ih (u/local-decl ctx "ih" (ih->below ctx below-names lps params motives t))
                                              [ys tb] (u/forall-telescope ctx t)
                                              proof (u/mk-lambda-fvars ctx ys (u/app (nth fs j) (conj (vec (e/get-app-args tb))
                                                                                                      (u/app new-ih ys))))]
                                          [(conj vars new-ih) (conj cargs new-ih proof)])
                                        [(conj vars a) (conj cargs a)])))
                                  [[] []] args)
                          ctor (u/const' (str (nth below-names i) "." (:name (u/decl ctx minor))) (mapv lvl/param lps))]
                      (u/mk-lambda-fvars ctx vars (u/app ctor (concat params motives cargs)))))
                  minors)
            rec-levels (cond->> (mapv lvl/param lps) large? (into [lvl/zero]))]
        (reduce
         (fn [env i]
           (let [motive (nth motives i)
                 [majors _] (u/forall-telescope ctx (u/infer-type ctx motive))
                 _ (u/implicit! ctx (pop majors))
                 rec-app (u/app (u/const' (nth rec-names i) rec-levels)
                                (concat params rec-motives rec-minors majors))
                 proof (u/app (nth fs i) (conj majors rec-app))
                 vars (vec (concat params motives majors fs))]
             (env/check-constant env (env/mk-thm (name/from-string (nth brecon-names i)) lps
                                                 (u/mk-forall-fvars ctx vars (u/app motive majors))
                                                 (u/mk-lambda-fvars ctx vars proof)))))
         env (range nm))))))
