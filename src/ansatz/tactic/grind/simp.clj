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
            [ansatz.tactic.grind.proof :as proof])
  (:import [ansatz.kernel ExprMap LeanExprKey]))

(defn mk-state []
  {:num-steps (atom 0) :contexts (java.util.IdentityHashMap.)
   :unfold-cache (java.util.IdentityHashMap.) :numeral-cache (java.util.IdentityHashMap.)})

(def ^:dynamic *state* nil)

(defn- transform-children [expr]
  (case (e/tag expr)
    :app (let [[head args] (e/get-app-fn-args expr)] (into [head] args))
    :lam [(e/lam-type expr) (e/lam-body expr)]
    :forall [(e/forall-type expr) (e/forall-body expr)]
    :let [(e/let-type expr) (e/let-value expr) (e/let-body expr)]
    :proj [(e/proj-struct expr)]
    :mdata [(e/mdata-expr expr)] []))

(defn- transform-with-cache [expr ^java.util.IdentityHashMap cache post]
  ;; Meta/Transform.lean transformWithCache: cache before descending, iterate
  ;; application spines, and guard actual recursion. The explicit stack also
  ;; makes the named limit independent of the JVM's stack size.
  (loop [todo [[expr 1 false]]]
    (if-let [[node depth finish?] (peek todo)]
      (let [todo (pop todo)]
        (cond
          (.containsKey cache node) (recur todo)
          finish?
          (let [children (transform-children node)
                changed (mapv #(.get cache %) children)
                [a b c] changed
                result (if (every? true? (map identical? children changed)) node
                           (case (e/tag node)
                             :app (reduce e/app a (rest changed))
                             :lam (e/lam (e/lam-name node) a b (e/lam-info node))
                             :forall (e/forall' (e/forall-name node) a b (e/forall-info node))
                             :let (e/let' (e/let-name node) a b c)
                             :proj (e/proj (e/proj-type-name node) (e/proj-idx node) a)
                             :mdata (e/mdata (e/mdata-data node) a) node))]
            (.put cache node (post result))
            (recur todo))
          :else
          (do (action/check-rec-depth! depth)
              (recur (reduce (fn [todo child] (conj todo [child (inc depth) false]))
                             (conj todo [node depth true]) (reverse (transform-children node)))))))
      (.get cache expr))))

(defn- unfold-reducible-step [expr]
  ;; Grind.Simp.preprocessImpl / Sym.unfoldReducible: imported Init lemmas use
  ;; HAdd/LE notation while the executable surface uses Nat.add/Nat.le directly.
  (if (e/app? expr)
    (let [[head args] (e/get-app-fn-args expr)
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
        :else expr)) expr))

(defn- unfold-reducible [expr]
  (transform-with-cache expr (or (:unfold-cache *state*) (java.util.IdentityHashMap.))
                        unfold-reducible-step))

(defn mk-context [st]
  ;; Init/Grind/Norm.lean leaves associativity/commutativity to arithmetic
  ;; solvers; ordered rewriting here would expand shared sums.
  ;; No local hypothesis rewrites or contextual discharger. Normalize the public
  ;; lemma entries before indexing, retaining their original checked proof names.
  (let [lemmas (simp/make-simp-lemmas (:env st)
                                       ["Nat.add_zero" "Nat.zero_add" "Nat.add_succ" "Nat.succ_add"
                                        "Nat.zero_le" "Nat.le_refl"])
        lemmas (mapv (fn [lemma]
                       (let [lhs (unfold-reducible (:lhs-pattern lemma))
                             [head args] (e/get-app-fn-args lhs)]
                         (assoc lemma :lhs-pattern lhs :rhs (unfold-reducible (:rhs lemma))
                                :head-name (e/const-name head) :lhs-nargs (count args)))) lemmas)]
    (simp/build-lemma-index (tc/mk-tc-state (:env st)) (:env st) lemmas)))

(defn- numeral-view-step [expr]
  ;; Lean reduces Nat literal patterns to constructors for matching. Expose one
  ;; constructor at addition operands so add_succ/succ_add can match literal 1.
  (let [expr (unfold-reducible expr) [head args] (e/get-app-fn-args expr)]
    (if (and (e/const? head) (= "Nat.add" (name/->string (e/const-name head))) (= 2 (count args)))
      (let [changed (mapv (fn [arg]
                                (if (and (e/lit-nat? arg) (pos? (e/lit-nat-val arg)))
                                  (e/app (e/const' (name/from-string "Nat.succ") [])
                                         (e/lit-nat (dec (e/lit-nat-val arg)))) arg)) args)]
        (if (every? true? (map identical? args changed)) expr (reduce e/app head changed))) expr)))

(defn- numeral-view [expr state]
  (let [^java.util.IdentityHashMap cache (:numeral-cache state)]
    (or (.get cache expr)
        (let [result (numeral-view-step expr)] (.put cache expr result) result))))

(defn- simp-state [state st]
  ;; Proof-producing simp caches are scoped to the TC context because surface
  ;; tactics may rebind local IDs; numSteps is shared across the whole grind call.
  (let [^java.util.IdentityHashMap contexts (:contexts state)]
    (or (.get contexts st)
        (let [config {:cache (ExprMap. 64)
                      :on-step (fn []
                                 (when (> @(:num-steps state) (:max-steps action/*config*))
                                   (action/budget! action/*config* :max-steps @(:num-steps state)))
                                 (swap! (:num-steps state) inc))}]
          (.put contexts st config)
          config))))

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
  (let [index (:simp-context gs)
        state (or *state* (mk-state))
        config (simp-state state st)]
    (binding [*state* state simp/*max-rec-depth* (:max-rec-depth action/*config*)]
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
                     result (simp/simp-expr-result st (:env st) index (numeral-view candidate state)
                                                   (:max-rec-depth action/*config*) config)
                   ;; Reuse simp's literal simprocs first. Ground evaluation
                   ;; supplies the Init-only decision path and definitions that
                   ;; have no equation theorem registered with simp.
                     result (if (.equals (LeanExprKey. candidate) (LeanExprKey. (:expr result)))
                              (assoc result :expr candidate) result)
                     result (if (identical? candidate (:expr result))
                              (or (ground-result st candidate) result) result)
                     gs (-> gs (update :simp-done (fnil conj #{}) key)
                            (eg/internalize candidate (:gen node))
                            (eg/internalize (:expr result) (:gen node)))]
                 (eg/assert-eq gs candidate (:expr result)
                               (or (:proof? result) (proof/mk-eq-refl st (:expr result))))))) gs))
     gs (:enodes gs)))))

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
