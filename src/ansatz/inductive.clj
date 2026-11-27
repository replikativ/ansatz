;; Inductive type definitions compatible with Lean 4's kernel.
;;
;; The surface elaborates the header and constructors into Lean's `inductive_decl`; the kernel's
;; add_inductive (ansatz.kernel.AddInductive, a port of Lean's src/kernel/inductive.cpp) generates
;; and checks the inductive, constructors and recursors. The auxiliary constructions — casesOn,
;; recOn, below/brecOn, noConfusionType, noConfusion — are built above the kernel, as in Lean.
;;
;; Usage:
;;   (define-inductive env "Color" [] [['red []] ['green []] ['blue []]])
;;   (define-inductive env "MyList" '[α Type] [['nil []] ['cons [['head 'α] ['tail '(MyList α)]]]])

(ns ansatz.inductive
  "Define inductive types compatible with Lean 4's kernel."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.elab.inductive :as elab]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.meta.constructions.cases-on :as cases-on]
            [ansatz.meta.constructions.rec-on :as rec-on]
            [ansatz.meta.constructions.brec-on :as brec-on]
            [ansatz.meta.constructions.ctor-idx :as ctor-idx]
            [ansatz.meta.constructions.ctor-elim :as ctor-elim]
            [ansatz.meta.constructions.no-confusion :as no-confusion]
            [ansatz.meta.constructions.util :as u])
  (:import [ansatz.kernel ConstantInfo]))

(def ^:private kernel-fuel
  "Fuel for admitting one declaration (the kernel's default per-declaration budget)."
  5000000)

(defn occurs-in?
  "Check if the inductive name occurs in an expression."
  [expr induct-name]
  (cond
    (e/const? expr) (= (e/const-name expr) induct-name)
    (e/app? expr) (or (occurs-in? (e/app-fn expr) induct-name)
                      (occurs-in? (e/app-arg expr) induct-name))
    (e/forall? expr) (or (occurs-in? (e/forall-type expr) induct-name)
                         (occurs-in? (e/forall-body expr) induct-name))
    (e/lam? expr) (or (occurs-in? (e/lam-type expr) induct-name)
                      (occurs-in? (e/lam-body expr) induct-name))
    :else false))

;; ============================================================
;; Phase 1: Core declarations
;; ============================================================

(defn- build-inductive-type
  "Build: ∀ (p1:T1) ... (pn:Tn) (i1:I1) ... (ik:Ik) → Sort result_level
   indices is a vec of {:name :compiled-type} (empty for non-indexed types)."
  [params indices result-level]
  (let [body (e/sort' result-level)
        ;; Wrap index foralls (innermost first)
        body (loop [i (dec (count indices)) body body]
               (if (< i 0) body
                   (recur (dec i) (e/forall' (:name (nth indices i))
                                             (:compiled-type (nth indices i))
                                             body :default))))]
    ;; Lean Elab/MutualInductive.lean elabHeadersAux preserves the header binders.
    ;; Explicit family parameters become implicit only in constructor types.
    (loop [i (dec (count params)) body body]
      (if (< i 0) body
          (recur (dec i) (e/forall' (:name (nth params i)) (:compiled-type (nth params i))
                                    body :default))))))

(defn- build-constructor-type
  "Build: ∀ (p1:T1) ... (pn:Tn) (f1:F1) ... (fm:Fm) → I p1...pn idx1...idxk
   field-types must be compiled at depth = n_params + field_index.
   return-indices are compiled Expr for the constructor's specific index values,
   at depth n-params + n-fields (in scope of params + fields)."
  [params fields ind-name ind-lvls return-indices]
  (let [n-params (count params)
        n-fields (count fields)
        n-total (+ n-params n-fields)
        ;; Return type: I p1...pn idx1...idxk at depth n-total
        return-type (reduce (fn [acc i]
                              (e/app acc (e/bvar (- n-total i 1))))
                            (e/const' ind-name ind-lvls)
                            (range n-params))
        ;; Apply index expressions
        return-type (reduce (fn [acc idx-expr] (e/app acc idx-expr))
                            return-type return-indices)]
    ;; Wrap fields (inner binders), right-to-left
    (loop [i (dec n-fields) body return-type]
      (if (< i 0)
        ;; Wrap params (outer binders) — implicit like Lean 4
        (loop [i (dec n-params) body body]
          (if (< i 0) body
              (recur (dec i) (e/forall' (:name (nth params i))
                                        (:compiled-type (nth params i))
                                        body :implicit))))
        (recur (dec i) (e/forall' (:name (nth fields i))
                                  (:type (nth fields i))
                                  body :default))))))

(defn- type-level-param [form]
  (when (and (sequential? form) (= 'Type (first form)) (= 2 (count form)))
    (name/from-string (str (second form)))))

(defn- explicit-result-level
  "The level of an explicit result sort `:in`: Prop, Type, (Type u), (Sort u) (u a name or a
   natural number)."
  [form]
  (let [lv (fn [x] (if (integer? x) (lvl/from-nat x) (lvl/param (name/from-string (str x)))))]
    (cond
      (= 'Prop form) lvl/zero
      (= 'Type form) (lvl/succ lvl/zero)
      (and (seq? form) (= 'Type (first form))) (lvl/succ (lv (second form)))
      (and (seq? form) (= 'Sort (first form))) (lv (second form))
      :else (throw (ex-info (str "unsupported result sort " (pr-str form)) {:in form})))))

(defn- level-params-of
  "The universe parameters occurring in `x`, in order of first occurrence."
  [x]
  (let [out (volatile! [])
        add (fn add [l]
              (cond
                (lvl/param? l) (when-not (some #{(lvl/param-name l)} @out) (vswap! out conj (lvl/param-name l)))
                (lvl/succ? l) (add (lvl/succ-pred l))
                (lvl/max? l) (do (add (lvl/max-lhs l)) (add (lvl/max-rhs l)))
                (lvl/imax? l) (do (add (lvl/imax-lhs l)) (add (lvl/imax-rhs l)))))]
    (letfn [(walk [x]
              (case (e/tag x)
                :sort (add (e/sort-level x))
                :const (run! add (e/const-levels x))
                :app (do (walk (e/app-fn x)) (walk (e/app-arg x)))
                :lam (do (walk (e/lam-type x)) (walk (e/lam-body x)))
                :forall (do (walk (e/forall-type x)) (walk (e/forall-body x)))
                :let (do (walk (e/let-type x)) (walk (e/let-value x)) (walk (e/let-body x)))
                :mdata (walk (e/mdata-expr x))
                :proj (walk (e/proj-struct x))
                nil))]
      (walk x))
    @out))

(defn- with-family-levels
  "`x` with every occurrence of the family constant at the declaration's universe parameters."
  [x ind-name levels]
  (letfn [(walk [x]
            (case (e/tag x)
              :const (if (= (e/const-name x) ind-name) (e/const' ind-name levels) x)
              :app (e/app (walk (e/app-fn x)) (walk (e/app-arg x)))
              :lam (e/lam (e/lam-name x) (walk (e/lam-type x)) (walk (e/lam-body x)) (e/lam-info x))
              :forall (e/forall' (e/forall-name x) (walk (e/forall-type x)) (walk (e/forall-body x)) (e/forall-info x))
              :let (e/let' (e/let-name x) (walk (e/let-type x)) (walk (e/let-value x)) (walk (e/let-body x)))
              :mdata (e/mdata (e/mdata-data x) (walk (e/mdata-expr x)))
              :proj (e/proj (e/proj-type-name x) (e/proj-idx x) (walk (e/proj-struct x)))
              x))]
    (walk x)))

(defn- level-pred
  "`l - 1` for a level that is a successor in every branch (`max (u+1) 1` → `max u 0`), else nil."
  [l]
  (cond
    (lvl/succ? l) (lvl/succ-pred l)
    (lvl/max? l) (let [a (level-pred (lvl/max-lhs l)) b (level-pred (lvl/max-rhs l))]
                   (when (and a b) (lvl/simplify (lvl/level-max a b))))
    :else nil))

(defn- infer-result-level
  "Lean Elab/MutualInductive.lean inferResultingUniverse for one type: `Prop` when the type is a
   Prop candidate (isPropCandidate: one constructor, at least one field, every field a proof not
   mentioning the type), otherwise the least level above 1 and every field's sort level (the
   result level itself, met by a recursive field, imposes nothing)."
  [env ind-name ind-levels header-type ctor-types n-params provisional]
  (let [;; the family as a provisional constant, only to read off the fields' sorts
        env (env/add-constant env (env/mk-axiom ind-name (vec ind-levels) header-type))
        ctx (u/context env)
        fields (mapv (fn [t] (let [[xs _] (u/forall-telescope ctx t)] (subvec xs n-params))) ctor-types)
        occurs? (fn [x] (some #{ind-name} (u/fold-constants conj [] x)))
        field-level (fn [f] (u/get-level ctx (u/infer-type ctx f)))
        prop-candidate? (and (= 1 (count ctor-types)) (seq (first fields))
                             (every? (fn [f] (and (lvl/level-zero? (lvl/simplify (field-level f)))
                                                  (not (occurs? (u/infer-type ctx f)))))
                                     (first fields)))]
    (if prop-candidate?
      lvl/zero
      (lvl/simplify
       (reduce (fn [acc f]
                 (lvl/level-max acc (lvl/instantiate (field-level f) {provisional lvl/zero})))
               (lvl/succ lvl/zero) (apply concat fields))))))

(defn define-inductive
  "Define an inductive type, adding kernel declarations to env.

   Args:
     env          - kernel Env
     ind-name-str - name, e.g. \"MyList\"
     params-spec  - flat vector [α Type β (Type u) ...]
                    Type forms: Type (fixed), (Type u) (polymorphic), Prop
     ctors-spec   - list of [ctor-name fields] or [ctor-name fields return-indices] entries
                    fields: flat vector [field-name field-type ...]
                    return-indices: vector of index expressions for this ctor's return type
     opts:
       :in              - result universe: 'Prop or 'Type (default: auto from params)
       :indices         - flat vector [idx-name idx-type ...] for indexed families
       :no-confusion?   - emit T.noConfusionType and T.noConfusion. Default true.
                          Set false to omit these auxiliaries explicitly.

   Adds: inductive, constructors, recursor, casesOn, recOn, optionally
   below/brecOn (for recursive types), noConfusionType and noConfusion. Returns env.
   A declaration the kernel rejects (positivity, universes, nesting, ...) throws ex-info
   {:inductive name} carrying the kernel's message, which names the constructor and argument."
  [env ind-name-str params-spec ctors-spec & {:keys [in indices no-confusion?]
                                              :or {no-confusion? true}}]
  (let [ind-name (name/from-string ind-name-str)

        ;; Parse parameters, extracting universe level params
        param-pairs (vec (partition 2 params-spec))
        n-params (count param-pairs)

        ;; Extract level params from (Type u) forms
        ;; E.g., [α (Type u) β (Type v)] → level params [u, v]
        level-param-names (vec (distinct
                                (keep (fn [[_ ptype-form]]
                                        (type-level-param ptype-form))
                                      param-pairs)))
        ;; Level param Level objects for const references
        ind-levels level-param-names
        ind-level-levels (mapv lvl/param level-param-names)

        ;; The result sort: explicit (`:in`), or inferred after the constructors are elaborated
        ;; (Lean Elab/MutualInductive.lean inferResultingUniverse), meanwhile a provisional
        ;; level parameter standing for Lean's result-level metavariable.
        explicit-level (when in (explicit-result-level in))
        provisional (name/from-string "_ansatz.result")
        ;; `Type ?r` while elaborating, so that nested occurrences (`List T`) unify, as Lean's
        ;; result-level metavariable does
        header-level (or explicit-level (lvl/succ (lvl/param provisional)))

        self-const (e/const' ind-name ind-level-levels)

        ;; Lean Elab/MutualInductive.lean elabHeaders/withInductiveLocalDecls,
        ;; then Elab/Inductive.lean elabCtors: no provisional constant in elaboration.
        {:keys [params indices ctors]}
        (elab/elab-inductive env ind-name-str param-pairs
                             (vec (partition 2 (or indices []))) ctors-spec
                             header-level self-const)
        ctor-types (mapv (fn [ctor]
                           (build-constructor-type params (:fields ctor) ind-name ind-level-levels
                                                   (:compiled-return-indices ctor)))
                         ctors)
        result-level (or explicit-level
                         (infer-result-level env ind-name ind-levels
                                             (build-inductive-type params indices header-level)
                                             ctor-types n-params provisional))
        ;; the provisional level, instantiated in nested occurrences (`List.{?r} T`): result - 1
        ctor-types (if explicit-level ctor-types
                       (let [r-1 (level-pred result-level)]
                         (mapv (fn [t]
                                 (if (some #{provisional} (level-params-of t))
                                   (if r-1
                                     (e/instantiate-level-params t {provisional r-1})
                                     (throw (ex-info (str "inductive " ind-name-str ": cannot infer the result universe; give it with :in")
                                                     {:inductive ind-name-str})))
                                   t))
                               ctor-types)))
        ;; universe parameters of constructor fields generalize too (after the header's)
        ind-levels (vec (remove #{provisional}
                                (distinct (concat ind-levels
                                                  (level-params-of (build-inductive-type params indices result-level))
                                                  (mapcat level-params-of ctor-types)))))
        ind-level-levels (mapv lvl/param ind-levels)
        ctor-types (mapv #(with-family-levels % ind-name ind-level-levels) ctor-types)
        ;; Lean's inductive_decl: the header and the constructor types. The kernel derives
        ;; everything else — metadata, positivity, nesting, the recursor and its rules.
        decl (env/mk-inductive-decl
              ind-levels n-params false
              [[ind-name (build-inductive-type params indices result-level)
                (mapv (fn [ctor t] [(name/from-string (:full-name ctor)) t]) ctors ctor-types)]])]

    (let [env (try (env/add-inductive env decl kernel-fuel)
                   (catch RuntimeException ex
                     (throw (ex-info (str "inductive " ind-name-str " rejected by the kernel: " (.getMessage ex))
                                     {:inductive ind-name-str} ex))))
          num-nested (.numNested ^ConstantInfo (env/lookup env ind-name))
          ;; Lean/Elab/MutualInductive.lean mkAuxConstructions (55f80e10).
          ;; Consume the checked recursor, including the kernel's nested motives.
          has? (fn [n] (some? (env/lookup env (name/from-string n))))
          ;; Lean 4.36: `mkRecOn` reuses `casesOn` where it can, so build that first
          env (if (has? "PUnit") (cases-on/mk-cases-on env ind-name-str) env)
          env (rec-on/mk-rec-on env ind-name-str)
          env (if (has? "Nat") (ctor-idx/mk-ctor-idx env ind-name-str) env)
          env (if (has? "Nat") (ctor-elim/mk-ctor-elim env ind-name-str) env)
          env (if (and no-confusion? (has? "PUnit") (has? "Eq") (has? "HEq"))
                (no-confusion/mk-no-confusion env ind-name-str) env)
          env (if (and (has? "PUnit") (has? "Prod"))
                (-> env (brec-on/mk-below ind-name-str) (brec-on/mk-brec-on ind-name-str)) env)]
      ;; Update global env atom with the new env
      (reset! @(requiring-resolve 'ansatz.core/ansatz-env) env)

      (println "✓ inductive" ind-name-str "defined:"
               (count ctors) "constructors, recursor"
               (if (pos? num-nested) (str "(nested, num-nested=" num-nested ")") ", auxiliaries"))
      env)))
