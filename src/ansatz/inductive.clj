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

(defn binder-info
  "The binder kind a DSL binder symbol carries as metadata: ^:implicit `{x}`, ^:inst `[x]`,
   ^:strict `⦃x⦄`; otherwise explicit."
  [sym]
  (let [m (meta sym)]
    (cond (:inst m) :inst-implicit
          (:implicit m) :implicit
          (:strict m) :strict-implicit
          :else :default)))

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
                                             body (binder-info (:sym (nth indices i)))))))]
    ;; Lean Elab/MutualInductive.lean elabHeadersAux preserves the header binders.
    ;; Explicit family parameters become implicit only in constructor types.
    (loop [i (dec (count params)) body body]
      (if (< i 0) body
          (recur (dec i) (e/forall' (:name (nth params i)) (:compiled-type (nth params i))
                                    body (binder-info (:sym (nth params i)))))))))

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
        ;; Wrap params (outer binders): Elab/Inductive.lean withExplicitToImplicit — an explicit
        ;; parameter is implicit in the constructor, an instance or strict-implicit one stays
        (loop [i (dec n-params) body body]
          (if (< i 0) body
              (recur (dec i) (e/forall' (:name (nth params i))
                                        (:compiled-type (nth params i))
                                        body (let [b (binder-info (:sym (nth params i)))]
                                               (if (= b :default) :implicit b))))))
        (recur (dec i) (e/forall' (:name (nth fields i))
                                  (:type (nth fields i))
                                  body (binder-info (:sym (nth fields i)))))))))

(defn- type-level-param [form]
  (when (and (sequential? form) (= 'Type (first form)) (= 2 (count form)) (symbol? (second form)))
    (name/from-string (str (second form)))))

(defonce ^:private provisional-counter (atom 0))

(defn- default-result-level
  "The header's own universe: Type, or above the `(Type u)` universes of its parameters."
  [level-param-names]
  (if (empty? level-param-names)
    (lvl/succ lvl/zero)
    (reduce lvl/level-max (map #(lvl/succ (lvl/param %)) level-param-names))))

(defn- level-of-form
  "A universe level written in a DSL sort: a name or a natural number."
  [x]
  (cond (and (integer? x) (>= x 0)) (lvl/from-nat x)
        (and (symbol? x) (nil? (namespace x))) (lvl/param (name/from-string (str x)))
        :else (throw (ex-info (str "unsupported universe level " (pr-str x)) {:level x}))))

(defn- explicit-result-level
  "The level of an explicit result sort `:in`: Prop, Type, (Type u), (Sort u) with u a name or a
   natural number."
  [form]
  (cond
    (= 'Prop form) lvl/zero
    (= 'Type form) (lvl/succ lvl/zero)
    (and (seq? form) (= 2 (count form)) (= 'Type (first form))) (lvl/succ (level-of-form (second form)))
    (and (seq? form) (= 2 (count form)) (= 'Sort (first form))) (level-of-form (second form))
    :else (throw (ex-info (str "unsupported result sort " (pr-str form)) {:in form}))))

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

(defn- level-atoms
  "Lean accLevel's traversal of a normalized level: its `base + k` atoms, through max and imax
   (both operands of an imax count, as Lean visits them)."
  [l]
  (letfn [(go [l k]
              (cond
                (lvl/succ? l) (go (lvl/succ-pred l) (inc k))
                (lvl/max? l) (concat (go (lvl/max-lhs l) k) (go (lvl/max-rhs l) k))
                (lvl/imax? l) (concat (go (lvl/imax-lhs l) k) (go (lvl/imax-rhs l) k))
                :else [[l k]]))]
    (go (lvl/simplify l) 0)))

(defn- add-offset [l k] (reduce (fn [l _] (lvl/succ l)) l (range k)))

(defn- infer-result-level
  "Lean Elab/MutualInductive.lean inferResultingUniverse for one type. `Prop` when the type is a
   Prop candidate (isPropCandidate: one constructor, at least one field, every field a proof not
   mentioning the type). Otherwise every field level's atom `b + k` is a constraint on the result
   (accLevel; the result level itself, met by a recursive field, imposes nothing): with the
   result `Type ?r` forced by a nested occurrence (`nested?`), `?r ≥ b + k - 1` (and `?r ≥ b` when
   `k = 0`, Lean's universe bump) and the result is `?r + 1`; otherwise the result is the least
   level above 1 and every atom. Returns {:level :r-1}."
  [env ind-name ind-levels header-type ctor-types n-params provisional nested?]
  (let [;; the family as a provisional constant, only to read off the fields' sorts
        env (env/add-constant env (env/mk-axiom ind-name (vec ind-levels) header-type))
        ctx (u/context env)
        fields (mapv (fn [t] (let [[xs _] (u/forall-telescope ctx t)] (subvec xs n-params))) ctor-types)
        occurs? (fn [x] (some #{ind-name} (u/fold-constants conj [] x)))
        field-level (fn [f] (u/get-level ctx (u/infer-type ctx f)))
        prop-candidate? (and (= 1 (count ctor-types)) (seq (first fields))
                             (every? (fn [f] (and (lvl/level-zero? (lvl/simplify (field-level f)))
                                                  (not (occurs? (u/infer-type ctx f)))))
                                     (first fields)))
        atoms (->> (apply concat fields)
                   (mapcat #(level-atoms (field-level %)))
                   (remove (fn [[b _]] (and (lvl/param? b) (= provisional (lvl/param-name b))))))]
    (cond
      prop-candidate? {:level lvl/zero}
      nested? (let [r (lvl/simplify (reduce (fn [acc [b k]] (lvl/level-max acc (add-offset b (max 0 (dec k)))))
                                            lvl/zero atoms))]
                {:level (lvl/succ r) :r-1 r})
      :else {:level (lvl/simplify (reduce (fn [acc [b k]] (lvl/level-max acc (add-offset b k)))
                                          (lvl/succ lvl/zero) atoms))})))

(defn- fixed-index-prefix
  "Lean Elab/MutualInductive.lean computeFixedIndexBitMask / fixedIndicesToParams for one type:
   how many leading indices are fixed — in every constructor the binder at that position is the
   index of its result, and every occurrence of the family in a field passes that same index."
  [env ind-name ind-levels ind-type ctor-types n-params n-indices]
  (if (zero? n-indices)
    0
    (let [env (env/add-constant env (env/mk-axiom ind-name (vec ind-levels) ind-type))
          ctx (u/context env)
          arity (+ n-params n-indices)
          mask (reduce
                (fn [mask t]
                  (let [[xs result] (u/forall-telescope ctx t)
                        rargs (vec (e/get-app-args result))
                        mask (reduce (fn [mask i]
                                       (if (and (< i (count xs)) (= (nth xs i) (nth rargs i))) mask (assoc mask i false)))
                                     mask (range n-params arity))
                        ;; Lean forEachWhere: at a family application inspect its argument
                        ;; vector and stop; elsewhere visit every child
                        occurrences (fn occ [x]
                                      (let [[h as] (e/get-app-fn-args x)]
                                        (if (and (e/const? h) (= (e/const-name h) ind-name))
                                          [(vec as)]
                                          (case (e/tag x)
                                            :app (concat (occ (e/app-fn x)) (occ (e/app-arg x)))
                                            :forall (concat (occ (e/forall-type x)) (occ (e/forall-body x)))
                                            :lam (concat (occ (e/lam-type x)) (occ (e/lam-body x)))
                                            :let (concat (occ (e/let-type x)) (occ (e/let-value x)) (occ (e/let-body x)))
                                            :mdata (occ (e/mdata-expr x))
                                            :proj (occ (e/proj-struct x))
                                            nil))))]
                    (reduce (fn [mask as]
                              (reduce (fn [mask i]
                                        (if (and (< i (count as)) (= (nth as i) (nth rargs i))) mask (assoc mask i false)))
                                      mask (range n-params arity)))
                            mask (mapcat #(occurrences (u/infer-type ctx %)) (subvec xs n-params)))))
                (vec (repeat arity true)) ctor-types)]
      (count (take-while #(nth mask %) (range n-params arity))))))

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
       :in              - explicit result sort: Prop, Type, (Type u), (Sort u) with u a name or a
                          natural number. Default: inferred from the constructor fields (Lean
                          inferResultingUniverse; a type with one constructor whose fields are
                          all proofs is a Prop, empty and fieldless types are Type)
       :indices         - flat vector [idx-name idx-type ...] for indexed families
       :promote-indices? - promote a fixed prefix of the indices to parameters (Lean's
                          inductive.autoPromoteIndices). Default true; a/inductive takes it
                          after :indices, e.g. `:indices [n Nat] :promote-indices? false`.
       Binder kinds: a parameter, index or field symbol with ^:implicit, ^:inst or ^:strict.
       :no-confusion?   - emit T.noConfusionType and T.noConfusion. Default true.
                          Set false to omit these auxiliaries explicitly.

   Adds: inductive, constructors, recursor, casesOn, recOn, optionally
   below/brecOn (for recursive types), noConfusionType and noConfusion. Returns env.
   A declaration the kernel rejects (positivity, universes, nesting, ...) throws ex-info
   {:inductive name} carrying the kernel's message, which names the constructor and argument."
  [env ind-name-str params-spec ctors-spec & {:keys [in indices no-confusion? promote-indices?]
                                              :or {no-confusion? true promote-indices? true}}]
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

        _ (when (env/lookup env ind-name)
            (throw (ex-info (str "inductive " ind-name-str ": already declared") {:inductive ind-name-str})))
        ;; The result sort: explicit (`:in`), or inferred after the constructors are elaborated
        ;; (Lean Elab/MutualInductive.lean inferResultingUniverse), meanwhile `Type ?r` with a
        ;; provisional level parameter standing for Lean's result-level metavariable (so nested
        ;; occurrences such as `List T` unify).
        explicit-level (when in (explicit-result-level in))
        ;; a numeric name component: no DSL symbol spells it
        provisional (name/mk-num (name/from-string "_ansatz_result") (swap! provisional-counter inc))
        elaborate (fn [header-level]
                    (let [{:keys [params indices ctors] :as r}
                          (elab/elab-inductive env ind-name-str param-pairs
                                               (vec (partition 2 (or indices []))) ctors-spec
                                               header-level (e/const' ind-name ind-level-levels))]
                      (let [ctor-types (mapv (fn [ctor]
                                               (build-constructor-type params (:fields ctor) ind-name ind-level-levels
                                                                       (:compiled-return-indices ctor)))
                                             ctors)]
                        (assoc r :ctor-types ctor-types
                               ;; Lean fixedIndicesToParams, before universe inference
                               ;; (MutualInductive.lean): a fixed prefix of the indices becomes
                               ;; parameters, so its binders are no fields
                               :promoted (if promote-indices?
                                           (fixed-index-prefix env ind-name ind-levels
                                                               (build-inductive-type params indices header-level)
                                                               ctor-types n-params (count indices))
                                           0)))))
        ;; A nested occurrence in a container of a fixed universe (`Wrap : Type → Type`) cannot
        ;; unify with the rigid provisional level, where Lean assigns its metavariable: then the
        ;; header's default universe (Type, or above the parameters' universes) is the result.
        [{:keys [params indices ctors ctor-types promoted]} result-level]
        (if explicit-level
          [(elaborate explicit-level) explicit-level]
          (let [attempt (try (elaborate (lvl/succ (lvl/param provisional)))
                             (catch clojure.lang.ExceptionInfo ex ex))]
            (if (instance? Exception attempt)
              (let [l0 (default-result-level level-param-names)]
                [(try (elaborate l0) (catch Exception _ (throw attempt))) l0])
              (let [nested? (some #(some #{provisional} (level-params-of %)) (:ctor-types attempt))
                    {:keys [level r-1]} (infer-result-level env ind-name ind-levels
                                                            (build-inductive-type (:params attempt) (:indices attempt)
                                                                                  (lvl/succ (lvl/param provisional)))
                                                            (:ctor-types attempt) (+ n-params (:promoted attempt))
                                                            provisional nested?)]
                [(cond-> attempt
                   nested? (update :ctor-types (fn [ts] (mapv #(e/instantiate-level-params % {provisional r-1}) ts))))
                 level]))))
        ;; Lean sortDeclLevelParams: the header's universes in order of occurrence, then the
        ;; remaining ones (from constructor fields) ordered by name
        ;; (an explicit result sort is part of the header, as Lean captures it there)
        header-levels (vec (remove #{provisional} (level-params-of (build-inductive-type params indices (or explicit-level lvl/zero)))))
        ind-levels (into header-levels
                         (sort-by str (remove (set (cons provisional header-levels))
                                              (distinct (concat (level-params-of (build-inductive-type params indices result-level))
                                                                (mapcat level-params-of ctor-types))))))
        ind-level-levels (mapv lvl/param ind-levels)
        ctor-types (mapv #(with-family-levels % ind-name ind-level-levels) ctor-types)
        ;; Lean's inductive_decl: the header and the constructor types. The kernel derives
        ;; everything else — metadata, positivity, nesting, the recursor and its rules.
        n-params (+ n-params promoted)
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
