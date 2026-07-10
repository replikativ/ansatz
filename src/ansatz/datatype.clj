(ns ansatz.datatype
  "Prototype Shen-style datatype judgments over core.logic.

   This namespace is deliberately outside the kernel. A datatype is an untrusted,
   searchable rule table. `solve` can return candidate answers and, optionally, a
   derivation tree; later layers can reconstruct/check CIC proof terms from that
   derivation.

   `sequent-datatype` is a small Shen-style layer over the same rule engine. It
   compiles rules with assumptions, premises, and conclusions to explicit
   context-passing relations."
  (:require [clojure.core.logic :as l]
            [clojure.string :as str]))

(defn logic-var-symbol?
  "True for data-level logic variables such as `?env` or `?type`."
  [x]
  (and (symbol? x) (str/starts-with? (name x) "?")))

(defn- lvar-name [sym]
  (let [n (subs (name sym) 1)]
    (if (seq n) (symbol n) sym)))

(defn- lvar-for! [env sym]
  (or (get @env sym)
      (let [v (l/lvar (lvar-name sym))]
        (vswap! env assoc sym v)
        v)))

(defn- term->logic! [env term]
  (cond
    (logic-var-symbol? term) (lvar-for! env term)
    (vector? term) (mapv #(term->logic! env %) term)
    (map? term) (into (empty term)
                      (map (fn [[k v]]
                             [(term->logic! env k) (term->logic! env v)]))
                      term)
    (set? term) (into #{} (map #(term->logic! env %)) term)
    (seq? term) (doall (map #(term->logic! env %) term))
    :else term))

(def ^:private default-predicates
  {:integero integer?
   :keywordo keyword?
   :numbero number?
   :stringo string?
   :symbolo symbol?})

(defn- op-key [op]
  (cond
    (keyword? op) op
    (symbol? op) (keyword (name op))
    :else op))

(defn- relation-call? [dt form]
  (and (sequential? form)
       (contains? (:relations dt) (first form))))

(declare compile-goal)

(defn- builtin-goal [dt env [op & args :as form]]
  (let [k (op-key op)
        arg (fn [i]
              (when-not (< i (count args))
                (throw (ex-info "Datatype builtin called with too few arguments"
                                {:goal form :index i})))
              (term->logic! env (nth args i)))]
    (case k
      :== (l/== (arg 0) (arg 1))
      :!= (l/!= (arg 0) (arg 1))
      :conso (l/conso (arg 0) (arg 1) (arg 2))
      :emptyo (l/emptyo (arg 0))
      :membero (l/membero (arg 0) (arg 1))
      :rembero (l/rembero (arg 0) (arg 1) (arg 2))
      :appendo (l/appendo (arg 0) (arg 1) (arg 2))
      :fail l/fail
      :succeed l/succeed
      (if-let [pred (get (:predicates dt) k)]
        (l/predc (arg 0) pred (symbol (name k)))
        (throw (ex-info "Unknown datatype goal"
                        {:goal form
                         :known-relations (:relations dt)
                         :known-builtins (into #{:== :!= :conso :emptyo
                                                :membero :rembero :appendo
                                                :fail :succeed}
                                               (keys (:predicates dt)))}))))))

(defn- compile-body-goal [dt env proof? form]
  (if (relation-call? dt form)
    (let [p (when proof? (l/lvar 'premise))
          g (compile-goal dt env form p)]
      {:goal g :proof p})
    {:goal (compile-goal dt env form nil)}))

(defn- rule-goal [dt rule rel args proof]
  (let [env (volatile! {})
        head (:head rule)]
    (when-not (= rel (first head))
      (throw (ex-info "Rule stored under the wrong relation"
                      {:relation rel :rule rule})))
    (let [head-args (mapv #(term->logic! env %) (rest head))
          body (mapv #(compile-body-goal dt env (some? proof) %) (:body rule))
          body-goals (mapv :goal body)
          body-proofs (->> body (keep :proof) vec)
          reified-head (into [rel] head-args)
          proof-goal (when proof
                       (l/== proof (into [:rule (:name rule) reified-head] body-proofs)))]
      (l/and* (cond-> [(l/== (vec args) head-args)]
                (seq body-goals) (into body-goals)
                proof-goal (conj proof-goal))))))

(defn- relation-goal [dt rel args proof]
  (fn [state]
    (if-let [rules (seq (get (:rules-by-relation dt) rel))]
      ((l/or* (mapv #(rule-goal dt % rel args proof) rules)) state)
      (l/fail state))))

(defn- compile-goal
  "Compile a data goal to a core.logic goal. If `proof` is non-nil and the goal is
   a judgment call, unify it with a reified derivation tree."
  [dt env form proof]
  (when-not (sequential? form)
    (throw (ex-info "Datatype goals must be sequential forms" {:goal form})))
  (let [rel (first form)]
    (if (relation-call? dt form)
      (relation-goal dt rel (mapv #(term->logic! env %) (rest form)) proof)
      (do
        (when proof
          (throw (ex-info "Proof trees are only available for datatype relations"
                          {:goal form})))
        (builtin-goal dt env form)))))

(defn- validate-rule! [rule]
  (when-not (and (map? rule) (:name rule) (sequential? (:head rule)))
    (throw (ex-info "Datatype rules need :name and sequential :head" {:rule rule})))
  (let [head (:head rule)]
    (when (empty? head)
      (throw (ex-info "Datatype rule head cannot be empty" {:rule rule}))))
  (update rule :body #(vec (or % []))))

(defn datatype
  "Build a searchable datatype from a rule spec.

   Spec shape:

     {:name :stlc
      :predicates {:customo custom?}
      :rules [{:name :var
               :head [!- ?env ?x ?type]
               :body [[symbolo ?x] [lookup ?env ?x ?type]]}]}

   Logic variables are symbols whose names start with `?`. Relation names are
   inferred from rule heads. Builtins are `==`, `!=`, `conso`, `emptyo`,
   `membero`, `rembero`, `appendo`, `succeed`, `fail`, and the predicate goals
   in `:predicates` plus the default `symbolo`, `integero`, `numbero`,
   `stringo`, and `keywordo`."
  [spec]
  (let [rules (mapv validate-rule! (:rules spec))
        relations (set (map (comp first :head) rules))]
    (assoc spec
           :predicates (merge default-predicates (:predicates spec))
           :relations relations
           :rules rules
           :rules-by-name (into {} (map (juxt :name identity)) rules)
           :rules-by-relation (group-by (comp first :head) rules))))

(defmacro defdatatype
  "Define a datatype value from a quoted-looking rule spec."
  [name spec]
  `(def ~name (datatype (assoc '~spec :name ~(keyword name)))))

(defn- sequent-ctx-var
  [rule-name tag idx]
  (symbol (str "?" (name rule-name) "__" tag "__ctx" idx)))

(defn- extend-context
  [rule-name ctx assumptions tag]
  (loop [ctx ctx
         assumptions (seq assumptions)
         idx 0
         body []]
    (if-not assumptions
      {:ctx ctx :body body}
      (let [ctx' (sequent-ctx-var rule-name tag idx)]
        (recur ctx'
               (next assumptions)
               (inc idx)
               (conj body ['conso (first assumptions) ctx ctx']))))))

(defn- consume-context
  [rule-name ctx assumptions]
  (loop [ctx ctx
         assumptions (seq assumptions)
         idx 0
         body []]
    (if-not assumptions
      {:ctx ctx :body body}
      (let [ctx' (sequent-ctx-var rule-name "consume" idx)]
        (recur ctx'
               (next assumptions)
               (inc idx)
               (conj body ['rembero (first assumptions) ctx ctx']))))))

(defn- premise-spec [premise]
  (if (map? premise)
    premise
    {:conclusion premise}))

(defn- compile-sequent-premise
  [relation rule-name base-ctx idx premise]
  (let [{:keys [assumptions conclusion]} (premise-spec premise)]
    (when-not (contains? (premise-spec premise) :conclusion)
      (throw (ex-info "Sequent premise needs a conclusion" {:premise premise})))
    (let [{premise-ctx :ctx body :body} (extend-context rule-name base-ctx assumptions
                                                        (str "prem" idx))]
      (conj body [relation premise-ctx conclusion]))))

(defn- compile-sequent-rule
  [relation rule]
  (let [rule-name (:name rule)
        ctx (or (:context rule) '?ctx)]
    (when-not (and (map? rule) rule-name (contains? rule :conclusion))
      (throw (ex-info "Sequent rules need :name and :conclusion" {:rule rule})))
    (let [{base-ctx :ctx consumed :body} (consume-context rule-name ctx (:assumptions rule))
          premises (map-indexed #(compile-sequent-premise relation rule-name base-ctx %1 %2)
                                (:premises rule))]
      {:name rule-name
       :head [relation ctx (:conclusion rule)]
       :body (vec (concat consumed
                          (:where rule)
                          (:body rule)
                          (mapcat identity premises)))})))

(defn- sequent-assumption-rule
  [relation name]
  {:name name
   :head [relation '?ctx '?prop]
   :body [['membero '?prop '?ctx]]})

(defn sequent-datatype
  "Build a Shen-style sequent datatype over the relation engine.

   Spec shape:

     {:relation t*
      :rules [{:name :lam
               :conclusion [:of [:lam ?x ?body] [:-> ?a ?b]]
               :premises [{:assumptions [[:of ?x ?a]]
                           :conclusion [:of ?body ?b]}]}]}

   Each compiled relation has shape `[relation context proposition]`. Rule
   `:assumptions` are consumed from the incoming context with `rembero`; premise
   assumptions are pushed onto the premise context with `conso`. By default an
   assumption rule is added so goals can be discharged from the current context."
  [spec]
  (let [relation (or (:relation spec) 't*)
        assumption-rule? (not= false (:assumption-rule? spec))
        assumption-name (or (:assumption-rule-name spec) :by-assumption)
        rules (cond-> []
                assumption-rule? (conj (sequent-assumption-rule relation assumption-name))
                true (into (mapv #(compile-sequent-rule relation %) (:rules spec))))]
    (datatype (assoc spec
                     :relation relation
                     :rules rules
                     :sequent? true))))

(defmacro defsequentdatatype
  "Define a Shen-style sequent datatype value from a quoted-looking spec."
  [name spec]
  `(def ~name (sequent-datatype (assoc '~spec :name ~(keyword name)))))

(defn derivation?
  "True for derivation trees emitted by `solve` with `{:proof? true}`."
  [x]
  (and (vector? x) (= :rule (first x)) (<= 3 (count x))))

(defn derivation-rule [proof]
  (when-not (derivation? proof)
    (throw (ex-info "Expected datatype derivation" {:proof proof})))
  (second proof))

(defn derivation-head [proof]
  (when-not (derivation? proof)
    (throw (ex-info "Expected datatype derivation" {:proof proof})))
  (nth proof 2))

(defn derivation-premises [proof]
  (when-not (derivation? proof)
    (throw (ex-info "Expected datatype derivation" {:proof proof})))
  (subvec proof 3))

(defn reconstruct
  "Fold a derivation tree into a proof artifact.

   `handlers` maps rule names to `(fn [head premise-artifacts] artifact)`.
   The artifact can be an Ansatz surface term, a kernel expression, a trace, or
   any other certificate representation. Unknown rules raise."
  [handlers proof]
  (let [rule (derivation-rule proof)
        head (derivation-head proof)
        premises (mapv #(reconstruct handlers %) (derivation-premises proof))]
    (if-let [f (get handlers rule)]
      (f head premises)
      (throw (ex-info "No datatype reconstruction handler"
                      {:rule rule :head head :known-rules (keys handlers)})))))

(def ^:private unbound ::unbound)

(defn- binding-value [bindings term]
  (if (logic-var-symbol? term)
    (get bindings term unbound)
    term))

(defn- resolved-binding-value [bindings term]
  (cond
    (logic-var-symbol? term) (get bindings term unbound)

    (vector? term)
    (let [values (mapv #(resolved-binding-value bindings %) term)]
      (if (some #{unbound} values) unbound values))

    (seq? term)
    (let [values (doall (map #(resolved-binding-value bindings %) term))]
      (if (some #{unbound} values) unbound values))

    (map? term)
    (reduce-kv (fn [m k v]
                 (let [k' (resolved-binding-value bindings k)
                       v' (resolved-binding-value bindings v)]
                   (if (or (= k' unbound) (= v' unbound))
                     (reduced unbound)
                     (assoc m k' v'))))
               (empty term)
               term)

    :else term))

(defn- bind-var [bindings sym value]
  (let [old (get bindings sym unbound)]
    (cond
      (= old unbound) (assoc bindings sym value)
      (= old value) bindings
      :else (throw (ex-info "Datatype derivation binding mismatch"
                            {:var sym :expected old :actual value})))))

(declare bind-pattern)

(defn- try-bind-pattern
  [bindings pattern value]
  (try
    (bind-pattern bindings pattern value)
    (catch clojure.lang.ExceptionInfo _
      unbound)))

(defn bind-pattern
  "Bind data-level logic variables in `pattern` to `value`.

   Returns an updated bindings map keyed by symbols such as `?env`. Constants
   must match exactly. Sequential patterns are matched structurally."
  ([pattern value]
   (bind-pattern {} pattern value))
  ([bindings pattern value]
   (cond
     (logic-var-symbol? pattern)
     (bind-var bindings pattern value)

     (and (sequential? pattern) (sequential? value) (= (count pattern) (count value)))
     (reduce (fn [b [p v]] (bind-pattern b p v))
             bindings
             (map vector pattern value))

     (and (map? pattern) (map? value) (= (set (keys pattern)) (set (keys value))))
     (reduce (fn [b k] (bind-pattern b (get pattern k) (get value k)))
             bindings
             (keys pattern))

     (= pattern value)
     bindings

     :else
     (throw (ex-info "Datatype derivation pattern mismatch"
                     {:pattern pattern :value value :bindings bindings})))))

(defn- resolve-term [bindings term]
  (let [v (binding-value bindings term)]
    (if (= v unbound)
      (throw (ex-info "Datatype proof template references unbound variable"
                      {:var term :bindings bindings}))
      v)))

(defn- bind-builtin-pattern [bindings dt [op & args :as form]]
  (case (op-key op)
    :conso
    (let [[head tail whole] args
          whole-value (binding-value bindings whole)
          head-value (resolved-binding-value bindings head)
          tail-value (resolved-binding-value bindings tail)]
      (cond
        (not= whole-value unbound)
        (let [s (seq whole-value)]
          (when-not s
            (throw (ex-info "Datatype conso proof pattern expected a non-empty sequence"
                            {:goal form :whole whole-value})))
          (-> bindings
              (bind-pattern head (first s))
              (bind-pattern tail (rest s))))

        (and (not= head-value unbound) (not= tail-value unbound))
        (bind-pattern bindings whole (cons head-value tail-value))

        :else
        (throw (ex-info "Datatype conso proof pattern is underconstrained"
                        {:goal form :bindings bindings}))))

    :==
    (let [[lhs rhs] args
          lhs-value (resolved-binding-value bindings lhs)
          rhs-value (resolved-binding-value bindings rhs)]
      (cond
        (not= lhs-value unbound) (bind-pattern bindings rhs lhs-value)
        (not= rhs-value unbound) (bind-pattern bindings lhs rhs-value)
        :else (throw (ex-info "Datatype == proof pattern is underconstrained"
                              {:goal form :bindings bindings}))))

    :emptyo
    (bind-pattern bindings (first args) '())

    :membero
    (let [[item coll] args
          coll-value (resolved-binding-value bindings coll)]
      (if (= coll-value unbound)
        bindings
        (or (some #(let [b (try-bind-pattern bindings item %)]
                     (when-not (= b unbound) b))
                  coll-value)
            (throw (ex-info "Datatype membero proof pattern did not match"
                            {:goal form :collection coll-value :bindings bindings})))))

    :rembero
    (let [[item coll out] args
          coll-value (resolved-binding-value bindings coll)
          out-value (resolved-binding-value bindings out)]
      (if (= coll-value unbound)
        bindings
        (let [xs (vec coll-value)]
          (or (some (fn [idx]
                      (let [removed (concat (subvec xs 0 idx) (subvec xs (inc idx)))]
                        (when (or (= out-value unbound) (= out-value removed))
                          (let [b (try-bind-pattern bindings item (nth xs idx))]
                            (when-not (= b unbound)
                              (if (= out-value unbound)
                                (bind-pattern b out removed)
                                b))))))
                    (range (count xs)))
              (throw (ex-info "Datatype rembero proof pattern did not match"
                              {:goal form
                               :collection coll-value
                               :out out-value
                               :bindings bindings}))))))

    :appendo
    (let [[prefix suffix whole] args
          prefix-value (resolved-binding-value bindings prefix)
          suffix-value (resolved-binding-value bindings suffix)
          whole-value (resolved-binding-value bindings whole)]
      (cond
        (and (not= prefix-value unbound) (not= suffix-value unbound))
        (bind-pattern bindings whole (concat prefix-value suffix-value))

        (and (not= prefix-value unbound) (not= whole-value unbound))
        (let [n (count prefix-value)]
          (when-not (= (seq prefix-value) (seq (take n whole-value)))
            (throw (ex-info "Datatype appendo prefix did not match"
                            {:goal form :prefix prefix-value :whole whole-value})))
          (bind-pattern bindings suffix (drop n whole-value)))

        :else bindings))

    (:!= :fail :succeed) bindings

    (if (contains? (:predicates dt) (op-key op))
      bindings
      (throw (ex-info "Unsupported datatype builtin in proof binding"
                      {:goal form :bindings bindings})))))

(defn rule-context
  "Return reconstruction context for `proof`.

   The context binds rule variables using the rule head, relation premises, and
   the simple builtin forms that can determine data (`conso`, `==`, `emptyo`)."
  ([dt proof premise-artifacts]
   (let [rule-name (derivation-rule proof)
         rule (or (get (:rules-by-name dt) rule-name)
                  (throw (ex-info "Unknown datatype rule in derivation"
                                  {:rule rule-name :known-rules (keys (:rules-by-name dt))})))
         premise-proofs (derivation-premises proof)
         binding-state (volatile! (bind-pattern (:head rule) (derivation-head proof)))
         relation-idx (volatile! 0)]
     (doseq [body-form (:body rule)]
       (if (relation-call? dt body-form)
         (let [idx @relation-idx
               premise-proof (nth premise-proofs idx nil)]
           (when-not premise-proof
             (throw (ex-info "Datatype derivation is missing a relation premise"
                             {:rule rule-name :body body-form :index idx})))
           (vswap! binding-state bind-pattern body-form (derivation-head premise-proof))
           (vswap! relation-idx inc))
         (vswap! binding-state bind-builtin-pattern dt body-form)))
     (when-not (= @relation-idx (count premise-proofs))
       (throw (ex-info "Datatype derivation has extra relation premises"
                       {:rule rule-name
                        :expected @relation-idx
                        :actual (count premise-proofs)})))
     {:rule rule
      :rule-name rule-name
      :head (derivation-head proof)
      :proof proof
      :bindings @binding-state
      :premises premise-artifacts
      :premise-proofs premise-proofs})))

(defn instantiate-template
  "Instantiate a proof template against a reconstruction context.

   Template operators:
     `[:call \"Ctor.name\" ...]` builds a surface application list.
     `[:encode :kind arg ...]` calls `(:encoders ctx)`.
     `[:premise n]` or `[:premise n :term]` reads a premise artifact.
     `[:side :kind arg ...]` calls `(:side ctx)` for domain-specific proofs."
  [ctx template]
  (letfn [(inst [x]
            (cond
              (logic-var-symbol? x) (resolve-term (:bindings ctx) x)
              (vector? x)
              (case (first x)
                :call (apply list (symbol (second x)) (map inst (drop 2 x)))
                :encode (let [[_ k & args] x
                              f (or (get-in ctx [:encoders k])
                                    (throw (ex-info "Unknown datatype proof encoder"
                                                    {:encoder k :known-encoders (keys (:encoders ctx))})))]
                          (apply f (map inst args)))
                :premise (let [[_ idx k] x
                               artifact (nth (:premises ctx) idx)]
                           (if k (get artifact k) artifact))
                :side (let [[_ k & args] x
                            f (or (get-in ctx [:side k])
                                  (throw (ex-info "Unknown datatype proof side builder"
                                                  {:side k :known-side-builders (keys (:side ctx))})))]
                        (apply f ctx (map inst args)))
                (mapv inst x))
              (seq? x) (doall (map inst x))
              :else x))]
    (inst template)))

(defn template-handlers
  "Compile a rule certificate spec into reconstruction handlers.

   `spec` accepts `:encoders`, `:side`, and `:rules`. Each rule entry is either
   a handler function `(fn [ctx] artifact)` or a map with `:term` template."
  [dt spec]
  (let [encoders (:encoders spec)
        side (:side spec)]
    (into {}
          (map (fn [[rule-name rule-spec]]
                 [rule-name
                  (fn [ctx]
                    (let [ctx (assoc ctx :encoders encoders :side side)]
                      (if (fn? rule-spec)
                        (rule-spec ctx)
                        {:rule (:rule-name ctx)
                         :head (:head ctx)
                         :term (instantiate-template ctx (:term rule-spec))})))]))
          (:rules spec))))

(defn reconstruct-with-rules
  "Like `reconstruct`, but handlers receive a rule-aware context with bindings."
  [dt handlers proof]
  (let [premises (mapv #(reconstruct-with-rules dt handlers %) (derivation-premises proof))
        ctx (rule-context dt proof premises)]
    (if-let [f (get handlers (:rule-name ctx))]
      (f ctx)
      (throw (ex-info "No datatype reconstruction handler"
                      {:rule (:rule-name ctx)
                       :head (:head ctx)
                       :known-rules (keys handlers)})))))

(defn certifier
  "Build a derivation certifier from a datatype and template spec."
  [dt spec]
  (let [handlers (template-handlers dt spec)]
    (fn [proof]
      (reconstruct-with-rules dt handlers proof))))

(defn- split-reified-answer [result]
  (if (and (sequential? result) (= ':- (second result)))
    {:answer (first result) :constraints (vec (drop 2 result))}
    {:answer result :constraints []}))

(defn- result-map [qvars proof? item-count result]
  (let [{:keys [answer constraints]} (split-reified-answer result)
        values (cond
                 (zero? item-count) []
                 (= 1 item-count) [answer]
                 :else (vec answer))
        qcount (count qvars)
        qmap (zipmap qvars (subvec values 0 qcount))]
    (cond-> qmap
      proof? (assoc :proof (nth values qcount))
      (seq constraints) (assoc :constraints constraints))))

(defn solve
  "Run `goal` against datatype `dt`.

   `qvars` is a vector of data-level logic variable symbols to reify. `n` is a
   maximum result count; pass nil for all answers. With `{:proof? true}`, the
   result maps include `:proof`, a tree of
   `[:rule rule-name reified-head ...premises]`. Answers come from core.logic's
   interleaving search, not Prolog-style DFS."
  ([dt qvars goal]
   (solve dt nil qvars goal nil))
  ([dt n qvars goal]
   (solve dt n qvars goal nil))
  ([dt n qvars goal opts]
   (let [env (volatile! {})
         qterms (mapv #(term->logic! env %) qvars)
         proof? (:proof? opts)
         proof (when proof? (l/lvar 'proof))
         compiled-goal (compile-goal dt env goal proof)
         answer-items (cond-> qterms proof? (conj proof))
         item-count (count answer-items)
         answer-term (if (= 1 item-count) (first answer-items) answer-items)
         answers (l/solutions (l/tabled-s true {:reify-vars true}) answer-term compiled-goal)
         limited (if (some? n) (take n answers) answers)]
     (map #(result-map qvars proof? item-count %) limited))))
