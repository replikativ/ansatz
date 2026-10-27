(ns ansatz.tactic.grind.normalize
  "Lean Grind/Propagate.lean (ite, Bool, decide) and Proj.lean reductions, v4.33.1.
   Includes the narrow adapter for the executable surface Bool.rec encoding."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.grind.egraph :as eg]
            [ansatz.tactic.grind.proof :as gp]
            [ansatz.tactic.grind.theorem :as theorem]))

(defn bool-rec? [expr]
  (let [[h args] (e/get-app-fn-args expr)]
    (and (e/const? h) (= "Bool.rec" (name/->string (e/const-name h))) (= 4 (count args)))))

(defn bool-value [gs cond]
  (some (fn [nm]
          (let [value (e/const' (name/from-string nm) [])]
            (when (eg/is-eqv gs cond value) value))) ["Bool.false" "Bool.true"]))

(defn- projection-app? [gs expr]
  (let [[h _] (e/get-app-fn-args expr)]
    (when (e/const? h)
      (when-let [ci (env/lookup (:env gs) (e/const-name h))]
        (when (= :def (env/ci-tag ci))
          (loop [value (.value ci)]
            (if (e/lam? value) (recur (e/lam-body value)) (e/proj? value))))))))

(defn- reducible-bool-app? [st expr]
  ;; Grind.Simp.preprocessImpl unfolds reducible definitions. In the surface,
  ;; Bool combinators and Bool-valued definitions expose Bool.rec, handled below.
  ;; Keep comparison heads for their Init bridge theorems and the solver.
  (let [[h _] (e/get-app-fn-args expr)]
    (and (e/app? expr) (e/const? h)
         (not (contains? #{"Bool.rec" "Nat.blt" "Nat.ble" "Nat.beq"}
                         (name/->string (e/const-name h))))
         (= (tc/infer-type st expr) (e/const' (name/from-string "Bool") [])))))

(defn- reduce-eq [gs st expr gen]
  (let [result (#'tc/cached-whnf st expr)]
    (if (= result expr) gs
        (-> gs (eg/internalize result gen)
            (eg/assert-eq expr result (gp/mk-eq-refl st result))))))

(defn propagate [gs st]
  ;; The executable surface uses Bool.rec, with false before true. Never coerce
  ;; Bool to Prop, and never treat arbitrary recursors as conditionals.
  (reduce
   (fn [gs [expr node]]
     (cond
       ;; Grind.Simp's Nat reduction exposes successor constructors before
       ;; E-matching. Nat.add recurses on its second argument; reducing a known
       ;; numeral here is definitional, even when its first argument is open.
       (let [[h args] (e/get-app-fn-args expr)]
         (and (e/const? h) (= "Nat.add" (name/->string (e/const-name h)))
              (= 2 (count args)) (e/lit-nat? (second args))))
       (let [[_ [a b]] (e/get-app-fn-args expr)
             n (e/lit-nat-val b)
             ;; Select the defining Nat.add equation without unfolding the
             ;; exported implementation's course-of-values recursor.
             result (if (zero? n) a
                        (e/app (e/const' (name/from-string "Nat.succ") [])
                               (e/app* (e/const' (name/from-string "Nat.add") [])
                                       a (e/lit-nat (dec n)))))]
         (-> gs (eg/internalize result (:gen node))
             (eg/assert-eq expr result (gp/mk-eq-refl st result))))

       (e/proj? expr)
       (if-let [ctor (some #(when (:ctor (eg/get-enode gs %)) %)
                           (eg/collect-eqc gs (e/proj-struct expr)))]
         (let [new-expr (e/proj (e/proj-type-name expr) (e/proj-idx expr) ctor)]
           (-> gs (eg/internalize new-expr (:gen node))
               (reduce-eq st new-expr (:gen node)))) gs)

       (and (e/app? expr) (e/lam? (e/get-app-fn expr)))
       ;; Beta only: WHNF would unfold a comparison in the selected branch
       ;; into its implementation recursor, hiding the solver's indexed symbol.
       (let [[head args] (e/get-app-fn-args expr)
             result (reduce e/app (e/instantiate1 (e/lam-body head) (first args)) (rest args))]
         (-> gs (eg/internalize result (:gen node))
             (eg/assert-eq expr result (gp/mk-eq-refl st result))))

       (and (e/app? expr) (projection-app? gs expr))
       (reduce-eq gs st expr (:gen node))

       (reducible-bool-app? st expr)
       (reduce-eq gs st expr (:gen node))

       (bool-rec? expr)
       (let [[h args] (e/get-app-fn-args expr) cond (last args)]
         (if-let [value (bool-value gs cond)]
           (let [reduced-app (reduce e/app h (assoc (vec args) 3 value))
                 ;; Propagate.lean's ite rule selects the branch itself. WHNF
                 ;; here would also unfold a recursive call in that branch,
                 ;; disconnecting the equation/IH terms from their graph nodes.
                 result (nth args (if (= value (e/const' (name/from-string "Bool.false") [])) 1 2))
                 gs (-> gs (eg/internalize reduced-app (:gen node))
                        (eg/internalize result (:gen node)))]
             ;; Congruence connects expr to reduced-app using cond=value; the
             ;; iota step is definitional and its equality is checked by the kernel.
             (eg/assert-eq gs reduced-app result (gp/mk-eq-refl st result))) gs))
       :else gs))
   gs (:enodes gs)))

(defn- decide-args [expr]
  (let [[h args] (e/get-app-fn-args expr)]
    (when (and (e/const? h) (= "Decidable.decide" (name/->string (e/const-name h)))
               (= 2 (count args)))
      args)))

(defn propagate-decide-up [branch truth]
  ;; Propagate.lean:propagateDecideUp. Init's decide_eq_true/false take a
  ;; proposition proof directly, instead of Grind's convenience p = True/False.
  (reduce
    (fn [branch [expr node]]
      (if-let [[p inst] (decide-args expr)]
        (let [{:keys [yes no]} (truth branch p)
              value (e/const' (name/from-string (if yes "Bool.true" "Bool.false")) [])]
          (if (and (or yes no) (not (eg/is-eqv (:graph branch) expr value)))
            (let [proof (e/app* (e/const' (name/from-string (if yes "decide_eq_true" "decide_eq_false")) [])
                                p inst (or yes no))]
              (update branch :graph #(-> % (eg/internalize value (:gen node))
                                           (eg/assert-eq expr value proof)))) branch)) branch))
    branch (get-in branch [:graph :enodes])))

(defn propagate-decide-down [branch truth]
  ;; Propagate.lean:propagateDecideDown. Assert p/Not p using the checked Init
  ;; of_decide lemmas; assert-fact then supplies the propositional equality edge.
  (reduce
    (fn [branch [expr node]]
      (if-let [[p inst] (decide-args expr)]
        (if-let [value (bool-value (:graph branch) expr)]
          (let [positive? (= value (e/const' (name/from-string "Bool.true") []))
                known (truth branch p)]
            (if (get known (if positive? :yes :no)) branch
                (let [proof (e/app* (e/const' (name/from-string
                                               (if positive? "of_decide_eq_true" "of_decide_eq_false")) [])
                                    p inst (gp/mk-eq-proof (:graph branch) (:tc branch) expr value))
                      prop (if positive? p (e/app (e/const' (name/from-string "Not") []) p))]
                  (update branch :raw-facts conj {:prop prop :proof proof :gen (:gen node)})))) branch)
        branch))
    branch (get-in branch [:graph :enodes])))

(defn activate-comparison-theorems [branch]
  ;; Propagate.lean propagateBEqUp/Down normalize lawful Boolean comparisons.
  ;; Surface Nat.beq/Nat.ble/Nat.blt bypass BEq/decide, so use their checked Init bridges.
  ;; Activation follows Internalize.activateTheorems' symbol indices, not the goal.
  (reduce (fn [branch [symbol lemma]]
            (if (and (seq (get-in branch [:graph :app-map (name/from-string symbol)]))
                     (not (contains? (:comparison-theorems-active branch) symbol)))
              (-> branch (update :comparison-theorems-active (fnil conj #{}) symbol)
                  (update :theorems into (theorem/for-hint (:tc branch) lemma))) branch))
          branch [["Nat.beq" "Nat.beq_eq"] ["Nat.ble" "Nat.ble_eq"] ["Nat.blt" "Nat.blt_eq"]]))

(defn- apply-congr-fun [st lhs rhs proof args]
  ;; Grind/Propagate.lean applyCongrFun: carry the conditional equality through
  ;; every argument beyond the conditional prefix, including dependent binders.
  (reduce (fn [[lhs rhs proof] arg]
            (let [type (#'tc/cached-whnf st (tc/infer-type st lhs))
                  alpha (e/forall-type type)
                  beta (e/lam (e/forall-name type) alpha (e/forall-body type) (e/forall-info type))]
              [(e/app lhs arg) (e/app rhs arg)
               (gp/mk-congr-fun st alpha beta lhs rhs proof arg)]))
          [lhs rhs proof] args))

(defn propagate-ite [branch truth]
  ;; Propagate.lean propagateIte/propagateDIte: select a branch using a
  ;; checked condition proof. Init's if_pos/neg and dif_pos/neg are equivalent
  ;; to the Grind convenience lemmas used by Lean.
  (reduce
   (fn [branch [expr node]]
     (let [[h args] (e/get-app-fn-args expr)
           nm (when (e/const? h) (name/->string (e/const-name h)))]
       (if (and (contains? #{"ite" "dite"} nm) (<= 5 (count args)))
         (let [[alpha p inst yes no] args
               value (truth branch p)
               hp (or (:yes value) (:no value))]
           (if hp
             (let [positive? (boolean (:yes value))
                   selected (if positive? yes no)
                   result (if (= nm "dite") (e/app selected hp) selected)
                   lemma (str (if (= nm "dite") "dif_" "if_") (if positive? "pos" "neg"))
                   proof (e/app* (e/const' (name/from-string lemma) (e/const-levels h))
                                 p inst hp alpha yes no)
                   prefix (reduce e/app h (take 5 args))
                   [_ result proof] (apply-congr-fun (:tc branch) prefix result proof (drop 5 args))]
               (update branch :graph #(-> % (eg/internalize result (:gen node))
                                          (eg/assert-eq expr result proof)))) branch)) branch)))
   branch (get-in branch [:graph :enodes])))
