(ns ansatz.tactic.grind.simp
  "Lean/Meta/Tactic/Grind/Simp.lean simpCore/preprocessImpl, checkout v4.33.1.
   Elementary Nat normalization through simp's public proof-producing expression API."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.instance :as instance]
            [ansatz.tactic.grind.action :as action]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.grind.theorem :as theorem]
            [ansatz.tactic.grind.egraph :as eg]
            [ansatz.tactic.grind.proof :as proof]))

(def ^:dynamic *max-rec-depth* 1000) ; Lean's default maxRecDepth.

(defn- check-rec-depth! [expr]
  (loop [todo [[expr 0]]]
    (when-let [[expr depth] (peek todo)]
      (when (>= depth *max-rec-depth*)
        (action/fail! (str "maximum recursion depth exceeded (" *max-rec-depth* ")")
                      {:limit :maxRecDepth :value *max-rec-depth*}))
      (let [children (case (e/tag expr)
                       :app [(e/app-fn expr) (e/app-arg expr)]
                       :lam [(e/lam-type expr) (e/lam-body expr)]
                       :forall [(e/forall-type expr) (e/forall-body expr)]
                       :let [(e/let-type expr) (e/let-value expr) (e/let-body expr)]
                       :proj [(e/proj-struct expr)]
                       :mdata [(e/mdata-expr expr)] [])]
        (recur (into (pop todo) (map #(vector % (inc depth)) children)))))))

(defn- unfold-reducible [expr]
  ;; Grind.Simp.preprocessImpl / Sym.unfoldReducible: imported Init lemmas use
  ;; HAdd/LE notation while the executable surface uses Nat.add/Nat.le directly.
  ;; Only fold the standard Nat instances; these steps are definitionally equal.
  (if (e/app? expr)
    (let [[head args] (e/get-app-fn-args expr)
          args (mapv unfold-reducible args)
          nm (when (e/const? head) (name/->string (e/const-name head)))
          nat (e/const' (name/from-string "Nat") [])
          hadd (e/app* (e/const' (name/from-string "instHAdd") [lvl/zero])
                       nat (e/const' (name/from-string "instAddNat") []))]
      (cond
        (and (= nm "HAdd.hAdd") (= 6 (count args)) (= [nat nat nat hadd] (subvec args 0 4)))
        (e/app* (e/const' (name/from-string "Nat.add") []) (nth args 4) (nth args 5))
        (and (= nm "LE.le") (= 4 (count args)) (= nat (first args))
             (= (second args) (e/const' (name/from-string "instLENat") [])))
        (e/app* (e/const' (name/from-string "Nat.le") []) (nth args 2) (nth args 3))
        :else (reduce e/app head args))) expr))

(defn mk-context [st]
  ;; No local hypothesis rewrites or contextual discharger. Normalize the public
  ;; lemma entries before indexing, retaining their original checked proof names.
  (let [lemmas (simp/make-simp-lemmas (:env st)
                                       ["Nat.add_zero" "Nat.zero_add" "Nat.add_succ" "Nat.succ_add"
                                        "Nat.add_assoc" "Nat.add_comm" "Nat.add_left_comm"
                                        "Nat.zero_le" "Nat.le_refl"])
        lemmas (mapv (fn [lemma]
                       (let [lhs (unfold-reducible (:lhs-pattern lemma))
                             [head args] (e/get-app-fn-args lhs)]
                         (assoc lemma :lhs-pattern lhs :rhs (unfold-reducible (:rhs lemma))
                                :head-name (e/const-name head) :lhs-nargs (count args)))) lemmas)]
    (simp/build-lemma-index (tc/mk-tc-state (:env st)) (:env st) lemmas)))

(defn- numeral-view [expr]
  ;; Lean reduces Nat literal patterns to constructors for matching. Expose one
  ;; constructor at addition operands so add_succ/succ_add can match literal 1.
  (let [expr (unfold-reducible expr) [head args] (e/get-app-fn-args expr)]
    (if (and (e/const? head) (= "Nat.add" (name/->string (e/const-name head))) (= 2 (count args)))
      (reduce e/app head (map (fn [arg]
                               (if (and (e/lit-nat? arg) (pos? (e/lit-nat-val arg)))
                                 (e/app (e/const' (name/from-string "Nat.succ") [])
                                        (e/lit-nat (dec (e/lit-nat-val arg)))) arg)) args)) expr)))

(defn- nat-candidate? [expr]
  (let [[head args] (e/get-app-fn-args expr)
        nm (when (e/const? head) (name/->string (e/const-name head)))]
    (or (contains? #{"Nat.add" "Nat.succ" "Nat.le"} nm)
        (and (= nm "LE.le") (seq args) (e/const? (first args))
             (= "Nat" (name/->string (e/const-name (first args))))))))

(defn- c [n] (e/const' (name/from-string n) []))

(defn- ground-result [st expr]
  ;; Grind.Simp.simpCore's ground simprocs. Init omits simp's convenience
  ;; eq_true/false_of_decide lemmas; use the underlying checked decide lemmas
  ;; and propext instead. Missing/stuck instances are normal non-applicability.
  (when (and (not (e/has-fvar-flag expr)) (not (e/has-loose-bvars? expr)))
    (let [type (tc/infer-type st expr)]
      (if (= type (e/sort' lvl/zero))
        (when-let [inst (instance/synthesize* st (:env st) (instance/index-for (:env st))
                                             (e/app (c "Decidable") expr) 0)]
          (let [value (#'tc/cached-whnf st (e/app* (c "Decidable.decide") expr inst))
                yes? (= value (c "Bool.true"))
                no? (= value (c "Bool.false"))]
            (when (or yes? no?)
              (let [result (c (if yes? "True" "False"))
                    hp (e/app* (c (if yes? "of_decide_eq_true" "of_decide_eq_false"))
                               expr inst (proof/mk-eq-refl st value))
                    forward (e/lam "h" expr
                                   (if yes? (c "True.intro") (e/app hp (e/bvar 0))) :default)
                    backward (e/lam "h" result
                                    (if yes? hp
                                        (e/app* (e/const' (name/from-string "False.elim") [lvl/zero])
                                                expr (e/bvar 0))) :default)]
                {:expr result :proof? (e/app* (c "propext") expr result
                                             (e/app* (c "Iff.intro") expr result forward backward))}))))
        ;; WHNF evaluates closed applications of computable definitions, including
        ;; surface definitions without registered equation theorems.
        (when (contains? #{(c "Nat") (c "Int") (c "Bool")} type)
          {:expr (#'tc/cached-whnf st expr)})))))

(defn preprocess [gs st]
  (let [index (:simp-context gs)]
    (reduce
     (fn [gs [expr node]]
       (if (or (nat-candidate? expr)
               (and (e/app? expr) (not (e/has-fvar-flag expr))
                    (not (e/has-loose-bvars? expr))))
         ;; Grind.Simp.simpCore/preprocessImpl simplify the whole well-typed
         ;; term. Independent root substitution breaks dependent arguments.
         (let [key expr]
           (if (contains? (:simp-done gs) key) gs
             (let [candidate expr
                   _ (check-rec-depth! candidate)
                   result (simp/simp-expr-result st (:env st) index (numeral-view candidate) (inc *max-rec-depth*))
                   ;; Reuse simp's literal simprocs first. Ground evaluation
                   ;; supplies the Init-only decision path and definitions that
                   ;; have no equation theorem registered with simp.
                   result (if (= candidate (:expr result))
                            (or (ground-result st candidate) result) result)
                   _ (check-rec-depth! (:expr result))
                   gs (-> gs (update :simp-done (fnil conj #{}) key)
                          (eg/internalize candidate (:gen node))
                          (eg/internalize (:expr result) (:gen node)))]
               (eg/assert-eq gs candidate (:expr result)
                             (or (:proof? result) (proof/mk-eq-refl st (:expr result))))))) gs))
     gs (:enodes gs))))


(defn normalization-theorems [st]
  ;; The stage-2 Nat length normalization requirement uses checked Init lemmas,
  ;; before the arithmetic solver port. As with Internalize.activateTheorems,
  ;; activate these only when their Nat.le index occurs. Match conclusions to
  ;; avoid inventing an unbounded chain of successor upper bounds.
  (into (mapv (fn [n]
          (let [nm (name/from-string n)
                ci (env/lookup (:env st) nm)
                body (loop [t (.type ci)]
                       (if (e/forall? t) (recur (e/forall-body t)) t))]
            (assoc (theorem/compile-theorem st nm
                                             (e/const' nm (mapv lvl/param (.levelParams ci)))
                                             (.type ci) (vec (.levelParams ci)) [(unfold-reducible body)])
                   :kind :bwd)))
        ["Nat.succ_le_succ" "Nat.le_succ_of_le"])
        ;; The surface compiles ordered conditionals to Nat.ble. Its false
        ;; branch needs the checked total-order complement, as Lean's Nat
        ;; normalization/order integration provides. This remains an E-match
        ;; theorem, without a target-dependent tactic or arithmetic fallback.
        (let [thm (theorem/named st "Nat.le_total")
              patterns (mapv unfold-reducible (:patterns thm))]
          [(assoc thm :patterns patterns :symbols (mapv theorem/head-index patterns))])))
