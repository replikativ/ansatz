;; Verified reducer/transducer experiments for Clojure-facing pipelines.
;;
;; This namespace intentionally does not modify the core Ansatz compiler.  It
;; gives us a small, explicit reducer calculus that can later be connected to
;; kernel-checked definitions and proofs.

(ns ansatz.reducers
  (:refer-clojure :exclude [cat eduction empty filter frequencies group-by into map mapcat reduce remove transduce])
  (:require [clojure.core :as core]
            [clojure.core.reducers :as reducers]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel Env Expr TypeChecker]))

;; ============================================================
;; Pipeline AST
;; ============================================================

(declare compile-xform* optimize-steps empty)

(defrecord Pipeline [steps optimized-steps optimizations compiled-xform])

(def ^:private certification-key ::certified-fn)

(defn certified-fn
  "Wrap a runtime function with kernel-side certification metadata.

   The returned value remains an ordinary callable Clojure function. The
   metadata is intentionally separate from kernel validation: use
   `validate-certified-fn` before treating the kernel side as checked."
  [{:keys [name type kernel-term runtime metadata]}]
  (when-not (fn? runtime)
    (throw (ex-info "certified-fn requires a callable :runtime"
                    {:name name
                     :runtime runtime})))
  (when-not (or name kernel-term)
    (throw (ex-info "certified-fn requires :name or :kernel-term"
                    {:metadata metadata})))
  (with-meta
    (fn
      ([] (runtime))
      ([x] (runtime x))
      ([x y] (runtime x y))
      ([x y z] (runtime x y z))
      ([x y z & more] (apply runtime x y z more)))
    {certification-key {:name name
                        :type type
                        :kernel-term kernel-term
                        :runtime runtime
                        :metadata metadata}}))

(defn certification
  "Return certification metadata attached by `certified-fn`, if present."
  [f]
  (get (meta f) certification-key))

(defn certified-fn?
  "True when `f` carries Ansatz reducer certification metadata."
  [f]
  (boolean (certification f)))

(defn- derived-certification [kind components]
  {:name (symbol (str "ansatz.reducers.derived/" (name kind)))
   :derived? true
   :kind kind
   :components (vec components)})

(defn- attach-certification [step cert]
  (if cert
    (assoc step :certification cert)
    step))

(defn- certification-checked? [cert]
  (true? (get-in cert [:metadata :kernel :checked?])))

(defn- step-certified? [step]
  (case (:op step)
    :cat true
    (:map :filter :remove :mapcat) (certification-checked? (:certification step))
    false))

(defn- mk-pipeline [steps]
  (let [steps (vec steps)
        optimized (optimize-steps steps)
        optimized-steps (:steps optimized)
        optimizations (:optimizations optimized)]
    (->Pipeline steps optimized-steps optimizations (delay (compile-xform* optimized-steps)))))

(defn pipeline?
  "True when `x` is an Ansatz reducer pipeline."
  [x]
  (instance? Pipeline x))

(defn- ensure-pipeline [x]
  (cond
    (nil? x) empty
    (pipeline? x) x
    :else (throw (ex-info "Expected ansatz.reducers/Pipeline" {:value x}))))

(defn- append-step [pipeline step]
  (mk-pipeline (conj (:steps (ensure-pipeline pipeline)) step)))

(defn map
  "Append a stateless map transform, or create a one-step pipeline."
  ([f] (map empty f))
  ([pipeline f]
   (append-step pipeline (attach-certification {:op :map :f f :fold-safe? true}
                                               (certification f)))))

(defn filter
  "Append a stateless filter transform, or create a one-step pipeline."
  ([pred] (filter empty pred))
  ([pipeline pred]
   (append-step pipeline (attach-certification {:op :filter :pred pred :fold-safe? true}
                                               (certification pred)))))

(defn remove
  "Append a stateless remove transform, or create a one-step pipeline."
  ([pred] (remove empty pred))
  ([pipeline pred]
   (append-step pipeline (attach-certification {:op :remove :pred pred :fold-safe? true}
                                               (certification pred)))))

(defn cat
  "Append Clojure's `cat` transducer, or create a one-step pipeline."
  ([] (cat empty))
  ([pipeline]
   (append-step pipeline {:op :cat :fold-safe? true})))

(defn mapcat
  "Append a stateless mapcat transform, or create a one-step pipeline."
  ([f] (mapcat empty f))
  ([pipeline f]
   (append-step pipeline (attach-certification {:op :mapcat :f f :fold-safe? true}
                                               (certification f)))))

(def flat-map
  "Alias for `mapcat`; closer to lean-reducers naming."
  mapcat)

(defn compose
  "Compose pipelines left-to-right, matching normal threading order."
  [& pipelines]
  (mk-pipeline (core/mapcat (comp :steps ensure-pipeline) pipelines)))

(defn- unsupported-pipeline-form [form]
  (throw (ex-info "Unsupported reducer pipeline form"
                  {:form form
                   :supported '(map filter remove cat mapcat flat-map)})))

(defn- pipeline-step-form [acc form]
  (let [head (if (seq? form) (first form) form)
        op (when (symbol? head) (symbol (name head)))
        args (when (seq? form) (rest form))]
    (case op
      map (if (= 1 (count args))
            `(map ~acc ~(first args))
            (unsupported-pipeline-form form))
      filter (if (= 1 (count args))
               `(filter ~acc ~(first args))
               (unsupported-pipeline-form form))
      remove (if (= 1 (count args))
               `(remove ~acc ~(first args))
               (unsupported-pipeline-form form))
      cat (if (empty? args)
            `(cat ~acc)
            (unsupported-pipeline-form form))
      mapcat (if (= 1 (count args))
               `(mapcat ~acc ~(first args))
               (unsupported-pipeline-form form))
      flat-map (if (= 1 (count args))
                 `(flat-map ~acc ~(first args))
                 (unsupported-pipeline-form form))
      (unsupported-pipeline-form form))))

(defmacro pipeline
  "Create a Pipeline using Clojure-transducer-like forms.

   Example:
     (pipeline
       (map inc)
       (filter even?)
       (mapcat range))

   The forms are not ordinary Clojure transducers; they are compiled to an
   explicit Ansatz reducer pipeline so later terminals can require proofs before
   using parallel regrouping."
  [& forms]
  (core/reduce pipeline-step-form `empty forms))

(defmacro defpipeline
  "Define a named reducer pipeline."
  [pipeline-name & forms]
  `(def ~pipeline-name (pipeline ~@forms)))

(defn fold-safe?
  "Whether a pipeline can be applied inside `reducers/fold` chunks.

   This prototype only exposes stateless transforms, so every built-in step is
   fold-safe. Stateful/early-terminating transforms should set this false until
   their completion and `reduced` semantics are modeled explicitly."
  [pipeline]
  (every? :fold-safe? (:steps (ensure-pipeline pipeline))))

;; ============================================================
;; Pipeline Optimizer
;; ============================================================

(def ^:private optimization-laws
  "Reducer rewrite law catalog.

   These entries are semantic law names for the optimizer trace. The current
   implementation applies only evaluation-order-preserving rewrites; the next
   step is to back these law names with kernel declarations over a reducer DSL."
  {:remove->filter {:law 'ansatz.reducers.law/remove->filter
                    :kernel-checked? false}
   :map-map {:law 'ansatz.reducers.law/map-map
             :kernel-checked? false}
   :filter-filter {:law 'ansatz.reducers.law/filter-filter
                   :kernel-checked? false}})

(defn- certification-summary [cert]
  (when cert
    (cond-> {:name (:name cert)}
      (:derived? cert) (assoc :derived? true)
      (get-in cert [:metadata :kernel :checked?]) (assoc :kernel-checked? true))))

(defn- step-summary [step]
  (let [cert (:certification step)]
    (cond-> (select-keys step [:op :fold-safe?])
      cert (assoc :certification (certification-summary cert)
                  :function-kernel-checked? (certification-checked? cert)))))

(defn- map-step [f]
  (attach-certification {:op :map :f f :fold-safe? true}
                        (certification f)))

(defn- filter-step [pred]
  (attach-certification {:op :filter :pred pred :fold-safe? true}
                        (certification pred)))

(defn- optimization [rule from to]
  (assoc (get optimization-laws rule)
         :rule rule
         :functions-certified? (every? step-certified? from)
         :from (mapv step-summary from)
         :to (mapv step-summary to)))

(defn- normalize-step [step]
  (case (:op step)
    :remove
    (let [pred (:pred step)
          cert (:certification step)
          normalized (attach-certification (filter-step (fn [x] (not (pred x))))
                                           (when cert
                                             (derived-certification :not [cert])))]
      [normalized [(optimization :remove->filter [step] [normalized])]])
    [step []]))

(defn- try-fuse-steps [left right]
  (case [(:op left) (:op right)]
    [:map :map]
    (let [f (:f left)
          g (:f right)
          left-cert (:certification left)
          right-cert (:certification right)
          fused (attach-certification (map-step (fn [x] (g (f x))))
                                      (when (and left-cert right-cert)
                                        (derived-certification :compose [left-cert right-cert])))]
      [fused (optimization :map-map [left right] [fused])])

    [:filter :filter]
    (let [p (:pred left)
          q (:pred right)
          left-cert (:certification left)
          right-cert (:certification right)
          fused (attach-certification (filter-step (fn [x] (and (p x) (q x))))
                                      (when (and left-cert right-cert)
                                        (derived-certification :and [left-cert right-cert])))]
      [fused (optimization :filter-filter [left right] [fused])])

    nil))

(defn- optimize-steps
  "Normalize and fuse pipeline steps.

   Rewrites preserve Clojure evaluation order. The returned optimization trace is
   intentionally explicit so callers can inspect which law justified each
   transformation."
  [steps]
  (loop [remaining (seq steps)
         stack []
         optimizations []]
    (if-not remaining
      {:steps (vec stack)
       :optimizations (vec optimizations)}
      (let [[step normalize-opts] (normalize-step (first remaining))
            optimizations (core/into optimizations normalize-opts)]
        (if-let [[fused fuse-opt] (when-let [left (peek stack)]
                                   (try-fuse-steps left step))]
          (recur (next remaining)
                 (conj (pop stack) fused)
                 (conj optimizations fuse-opt))
          (recur (next remaining)
                 (conj stack step)
                 optimizations))))))

(def empty
  "The identity reducer pipeline."
  (mk-pipeline []))

(defn- step->xform [{:keys [op f pred]}]
  (case op
    :map (core/map f)
    :filter (core/filter pred)
    :remove (core/remove pred)
    :cat core/cat
    :mapcat (core/mapcat f)))

(defn- compile-xform* [steps]
  (if (seq steps)
    (apply comp (core/map step->xform steps))
    identity))

(defn xform
  "Compile a pipeline to an ordinary Clojure transducer.

   The optimized compiled transducer is cached on the immutable Pipeline value."
  [pipeline]
  (force (:compiled-xform (ensure-pipeline pipeline))))

(defn explain
  "Return a small data summary of the pipeline."
  [pipeline]
  (let [pipeline (ensure-pipeline pipeline)]
    (cond-> {:steps (mapv step-summary (:steps pipeline))
             :optimized-steps (mapv step-summary (:optimized-steps pipeline))
             :optimizations (mapv #(select-keys % [:rule :law :kernel-checked?
                                                   :rule-kernel-checked? :functions-certified?
                                                   :from :to])
                                  (:optimizations pipeline))
             :fold-safe? (fold-safe? pipeline)}
      (:reducer-law-checks pipeline)
      (assoc :reducer-law-checks (:reducer-law-checks pipeline)))))

;; ============================================================
;; Kernel-checked reducer law and function certificates
;; ============================================================

(defrecord ReducerLawSpec [rule theorem expected-type metadata])

(defn- declaration-name-str [decl-name]
  (cond
    (symbol? decl-name) (str decl-name)
    (string? decl-name) decl-name
    :else nil))

(defn reducer-law-spec
  "Create a reducer optimizer law descriptor.

   `expected-type` is the kernel expression for the theorem type that must be
   definitionally equal to the referenced declaration's type. This validates the
   rewrite schema, not any arbitrary Clojure function captured by a pipeline."
  [{:keys [rule theorem expected-type metadata]}]
  (when-not rule
    (throw (ex-info "ReducerLawSpec requires :rule" {:theorem theorem})))
  (when-not (declaration-name-str theorem)
    (throw (ex-info "ReducerLawSpec requires theorem symbol or string"
                    {:rule rule
                     :theorem theorem})))
  (when-not (instance? Expr expected-type)
    (throw (ex-info "ReducerLawSpec requires kernel Expr :expected-type"
                    {:rule rule
                     :theorem theorem
                     :expected-type expected-type})))
  (->ReducerLawSpec rule theorem expected-type metadata))

(defn reducer-law-checked?
  "True when a reducer law spec has been checked against a kernel declaration."
  [spec]
  (true? (get-in spec [:metadata :kernel :checked?])))

(defn validate-reducer-law-spec
  "Kernel-check a reducer optimizer law theorem type."
  ([^Env kernel-env spec]
   (validate-reducer-law-spec kernel-env spec {}))
  ([^Env kernel-env spec {:keys [fuel] :or {fuel 50000000}}]
   (let [spec (if (instance? ReducerLawSpec spec)
                spec
                (reducer-law-spec spec))
         theorem-name (declaration-name-str (:theorem spec))
         ci (env/lookup kernel-env (name/from-string theorem-name))]
     (when-not ci
       (throw (ex-info "Reducer law declaration not found"
                       {:rule (:rule spec)
                        :theorem theorem-name})))
     (let [tc (doto (TypeChecker. kernel-env)
                (.setFuel (long fuel)))
           expected (:expected-type spec)
           actual (.type ci)
           ok? (.isDefEq tc actual expected)]
       (when-not ok?
         (throw (ex-info "Reducer law type does not match"
                         {:rule (:rule spec)
                          :theorem theorem-name
                          :expected (e/->string expected)
                          :actual (e/->string actual)})))
       (assoc spec :metadata
              (-> (:metadata spec)
                  (assoc-in [:kernel :checked?] true)
                  (assoc-in [:kernel :checked-at] (str (java.time.Instant/now)))
                  (assoc-in [:kernel :theorem] theorem-name)
                  (assoc-in [:kernel :type-checked?] true)))))))

(defn validate-reducer-law-specs
  "Kernel-check a collection or map of reducer law specs."
  ([^Env kernel-env law-specs]
   (validate-reducer-law-specs kernel-env law-specs {}))
  ([^Env kernel-env law-specs opts]
   (let [specs (cond
                 (nil? law-specs) []
                 (map? law-specs) (vals law-specs)
                 (sequential? law-specs) law-specs
                 :else [law-specs])]
     (core/into {}
                (for [spec specs
                      :let [checked (validate-reducer-law-spec kernel-env spec opts)]]
                  [(:rule checked) checked])))))

(defn validate-certified-fn
  "Check the kernel-side type attached to a `certified-fn`.

   This validates the kernel declaration or expression. It still records a
   runtime trust boundary: Ansatz must know why the Clojure runtime function
   corresponds to the checked kernel term before stronger optimizer claims can
   be made."
  ([^Env kernel-env f]
   (validate-certified-fn kernel-env f {}))
  ([^Env kernel-env f {:keys [fuel] :or {fuel 50000000}}]
   (let [cert (certification f)]
     (when-not cert
       (throw (ex-info "Expected function created by certified-fn" {:value f})))
     (let [tc (doto (TypeChecker. kernel-env)
                (.setFuel (long fuel)))
           term (:kernel-term cert)
           decl-name (or (declaration-name-str term)
                         (declaration-name-str (:name cert)))
           actual (cond
                    (instance? Expr term) (.inferType tc term)
                    decl-name (let [ci (env/lookup kernel-env (name/from-string decl-name))]
                                (when-not ci
                                  (throw (ex-info "Certified function declaration not found"
                                                  {:name decl-name})))
                                (.type ci))
                    :else (throw (ex-info "Certified function needs :kernel-term or :name"
                                          {:certification cert})))
           expected (:type cert)]
       (when (and expected (not (instance? Expr expected)))
         (throw (ex-info "Certified function :type must be a kernel Expr when validating"
                         {:name (:name cert)
                          :type expected})))
       (when (and expected (not (.isDefEq tc actual expected)))
         (throw (ex-info "Certified function type does not match"
                         {:name (:name cert)
                          :expected (e/->string expected)
                          :actual (e/->string actual)})))
       (with-meta f
         {certification-key
          (assoc cert :metadata
                 (-> (:metadata cert)
                     (assoc-in [:kernel :checked?] true)
                     (assoc-in [:kernel :checked-at] (str (java.time.Instant/now)))
                     (assoc-in [:kernel :type] actual)
                     (assoc-in [:runtime :trusted?] (true? (get-in cert [:metadata :runtime :trusted?])))))})))))

(defn- reducer-law-check-summary [spec]
  {:rule (:rule spec)
   :theorem (get-in spec [:metadata :kernel :theorem])
   :kernel-checked? (reducer-law-checked? spec)})

(defn- mark-optimization-checked [checked-laws opt]
  (let [law (get checked-laws (:rule opt))
        rule-checked? (boolean (and law (reducer-law-checked? law)))
        functions-certified? (boolean (:functions-certified? opt))
        checked? (and rule-checked? functions-certified?)]
    (cond-> opt
      law (assoc :law (or (get-in law [:metadata :kernel :theorem])
                          (:theorem law))
                 :rule-kernel-checked? rule-checked?)
      checked? (assoc :kernel-checked? true))))

(defn check-pipeline
  "Attach kernel-checked reducer law information to a pipeline.

   The optimized transducer is unchanged. This marks an optimization as
   `:kernel-checked? true` only when the rewrite theorem type was checked and
   all functions involved in that rewrite carry kernel-validated certification
   metadata."
  ([^Env kernel-env pipeline law-specs]
   (check-pipeline kernel-env pipeline law-specs {}))
  ([^Env kernel-env pipeline law-specs opts]
   (let [pipeline (ensure-pipeline pipeline)
         checked-laws (validate-reducer-law-specs kernel-env law-specs opts)
         checked-opts (mapv #(mark-optimization-checked checked-laws %)
                            (:optimizations pipeline))]
     (assoc pipeline
            :optimizations checked-opts
            :reducer-law-checks (mapv reducer-law-check-summary
                                      (vals checked-laws))))))

;; ============================================================
;; Sequential terminals
;; ============================================================

(defn transduce
  "Run a pipeline with Clojure's `transduce`."
  ([pipeline rf coll]
   (core/transduce (xform pipeline) rf coll))
  ([pipeline rf init coll]
   (core/transduce (xform pipeline) rf init coll)))

(defn reduce
  "Run a pipeline with a plain two-arity reducing function."
  [pipeline rf init coll]
  (transduce pipeline (core/completing rf) init coll))

(defn into
  "Collect a pipeline into `to`, using Clojure's transducer-aware `into`."
  [to pipeline coll]
  (core/into to (xform pipeline) coll))

(defn eduction
  "Return a reducible/iterable eduction for a pipeline."
  [pipeline coll]
  (core/eduction (xform pipeline) coll))

;; ============================================================
;; Law-carrying monoids
;; ============================================================

(def required-laws
  #{:assoc :left-identity :right-identity})

(defrecord MonoidSpec [name unit-fn combine laws metadata])

(defn monoid-spec
  "Create a law-carrying monoid descriptor.

   `unit-fn` is a zero-arity function because Clojure reducers call the
   combining function with zero arguments to obtain a fresh identity value.
   `laws` is a map containing at least `:assoc`, `:left-identity`, and
   `:right-identity`.  Today these are carried as certificates/theorem refs;
   the next step is to validate them against Ansatz kernel declarations."
  [{:keys [name unit-fn combine laws metadata]}]
  (when-not (fn? unit-fn)
    (throw (ex-info "MonoidSpec requires :unit-fn" {:name name})))
  (when-not (fn? combine)
    (throw (ex-info "MonoidSpec requires :combine" {:name name})))
  (->MonoidSpec name unit-fn combine (or laws {}) metadata))

(defn lawful?
  "True when a MonoidSpec carries all laws needed by parallel fold."
  [spec]
  (and (instance? MonoidSpec spec)
       (every? #(contains? (:laws spec) %) required-laws)))

(defn kernel-lawful?
  "True when a MonoidSpec has been checked against kernel theorem types."
  [spec]
  (true? (get-in spec [:metadata :kernel :checked?])))

(defn- assert-lawful! [spec]
  (when-not (lawful? spec)
    (throw (ex-info "Parallel fold requires a lawful MonoidSpec"
                    {:name (:name spec)
                     :required required-laws
                     :present (set (keys (:laws spec)))})))
  spec)

(defn unit
  "Produce the monoid identity value."
  [spec]
  ((:unit-fn (assert-lawful! spec))))

(defn combine
  "Combine two monoid values."
  [spec left right]
  ((:combine (assert-lawful! spec)) left right))

(defn combinef
  "Compile a MonoidSpec to Clojure reducers' 0/2-arity combine function."
  [spec]
  (let [{:keys [unit-fn combine]} (assert-lawful! spec)]
    (fn
      ([] (unit-fn))
      ([left right] (combine left right)))))

(defn- c [s]
  (e/const' (name/from-string s) []))

(defn- hadd-combine [type-expr add-inst-name]
  (let [inst-hadd (e/app* (e/const' (name/from-string "instHAdd") [lvl/zero])
                          type-expr
                          (c add-inst-name))]
    (fn [left right]
      (e/app* (e/const' (name/from-string "HAdd.hAdd")
                        [lvl/zero lvl/zero lvl/zero])
              type-expr type-expr type-expr inst-hadd left right))))

(defn- nat-zero-expr []
  (let [nat (c "Nat")]
    (e/app* (e/const' (name/from-string "OfNat.ofNat") [lvl/zero])
            nat
            (e/lit-nat 0)
            (e/app (c "instOfNatNat") (e/lit-nat 0)))))

(defn- int-zero-expr []
  (let [int-type (c "Int")]
    (e/app* (e/const' (name/from-string "OfNat.ofNat") [lvl/zero])
            int-type
            (e/lit-nat 0)
            (e/app (c "instOfNat") (e/lit-nat 0)))))

(defn- monoid-kernel
  [type-expr unit-expr combine-expr]
  {:type type-expr
   :unit unit-expr
   :combine-expr combine-expr})

(defn- eq-expr [type-expr lhs rhs]
  (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
          type-expr lhs rhs))

(defn- assoc-type [{:keys [type combine-expr]}]
  (let [a (e/bvar 2)
        b (e/bvar 1)
        c (e/bvar 0)
        lhs (combine-expr (combine-expr a b) c)
        rhs (combine-expr a (combine-expr b c))]
    (e/forall' "_" type
               (e/forall' "_" type
                          (e/forall' "_" type
                                     (eq-expr type lhs rhs)
                                     :default)
                          :default)
               :default)))

(defn- left-identity-type [{:keys [type unit combine-expr]}]
  (let [a (e/bvar 0)]
    (e/forall' "_" type
               (eq-expr type (combine-expr unit a) a)
               :default)))

(defn- right-identity-type [{:keys [type unit combine-expr]}]
  (let [a (e/bvar 0)]
    (e/forall' "_" type
               (eq-expr type (combine-expr a unit) a)
               :default)))

(defn- expected-law-type [kernel law]
  (case law
    :assoc (assoc-type kernel)
    :left-identity (left-identity-type kernel)
    :right-identity (right-identity-type kernel)))

(defn- law-name-str [law-name]
  (cond
    (symbol? law-name) (str law-name)
    (string? law-name) law-name
    :else nil))

(defn- assert-kernel-metadata! [spec]
  (let [kernel (get-in spec [:metadata :kernel])]
    (when-not (and (:type kernel) (:unit kernel) (:combine-expr kernel))
      (throw (ex-info "MonoidSpec needs :metadata :kernel with :type, :unit, and :combine-expr"
                      {:name (:name spec)
                       :metadata (:metadata spec)})))
    kernel))

(defn validate-monoid-spec
  "Kernel-check a MonoidSpec's law certificates.

   This validates theorem *types*: each law reference must resolve to a
   declaration whose type is definitionally equal to the generated monoid-law
   type for the spec's kernel type/unit/combine terms. The returned spec is
   marked kernel-checked.

   This still leaves a runtime backend trust boundary: for the built-in Nat/Int
   specs, the runtime functions are the same primitives used by Ansatz's Clojure
   compiler for those kernel operations."
  ([^Env kernel-env spec]
   (validate-monoid-spec kernel-env spec {}))
  ([^Env kernel-env spec {:keys [fuel] :or {fuel 50000000}}]
   (assert-lawful! spec)
   (let [kernel (assert-kernel-metadata! spec)
         tc (doto (TypeChecker. kernel-env)
              (.setFuel (long fuel)))
         checks
         (core/into {}
                    (for [law required-laws
                          :let [law-ref (get (:laws spec) law)
                                law-name (law-name-str law-ref)
                                _ (when-not law-name
                                    (throw (ex-info "Kernel law reference must be a symbol or string"
                                                    {:name (:name spec)
                                                     :law law
                                                     :law-ref law-ref})))
                                ci (env/lookup kernel-env (name/from-string law-name))
                                _ (when-not ci
                                    (throw (ex-info "Kernel law declaration not found"
                                                    {:name (:name spec)
                                                     :law law
                                                     :law-name law-name})))
                                expected (expected-law-type kernel law)
                                actual (.type ci)
                                ok? (.isDefEq tc actual expected)]
                          :when true]
                      (do
                        (when-not ok?
                          (throw (ex-info "Kernel law type does not match MonoidSpec"
                                          {:name (:name spec)
                                           :law law
                                           :law-name law-name
                                           :expected (e/->string expected)
                                           :actual (e/->string actual)})))
                        [law {:theorem law-name
                              :type-checked? true}])))
         checked-at (java.time.Instant/now)]
     (assoc spec :metadata
            (-> (:metadata spec)
                (assoc-in [:kernel :checked?] true)
                (assoc-in [:kernel :checked-at] (str checked-at))
                (assoc-in [:kernel :law-checks] checks))))))

(defn checked
  "Convenience wrapper for `validate-monoid-spec`."
  ([kernel-env spec]
   (validate-monoid-spec kernel-env spec))
  ([kernel-env spec opts]
   (validate-monoid-spec kernel-env spec opts)))

(defn- assert-kernel-lawful! [spec]
  (when-not (kernel-lawful? spec)
    (throw (ex-info "Kernel-checked fold requires validate-monoid-spec"
                    {:name (:name spec)
                     :kernel-checked? (kernel-lawful? spec)})))
  (assert-lawful! spec))

(def nat-add
  "Law certificate for exact non-negative integer addition.

   The law refs name Lean/Ansatz theorem declarations. This prototype carries
   them; it does not yet check that the runtime function is the compiled form of
   the referenced CIC operation."
  (monoid-spec
   {:name :nat/add
    :unit-fn (constantly 0)
    :combine (fn [left right] (+ left right))
    :laws {:assoc 'Nat.add_assoc
           :left-identity 'Nat.zero_add
           :right-identity 'Nat.add_zero}
    :metadata {:ansatz/type 'Nat
               :ansatz/op 'Nat.add
               :kernel (monoid-kernel (c "Nat")
                                      (nat-zero-expr)
                                      (hadd-combine (c "Nat") "instAddNat"))
               :runtime {:trusted-primitive :clojure.lang.Numbers/add}}}))

(def int-add
  "Law certificate for exact integer addition."
  (monoid-spec
   {:name :int/add
    :unit-fn (constantly 0)
    :combine (fn [left right] (+ left right))
    :laws {:assoc 'Int.add_assoc
           :left-identity 'Int.zero_add
           :right-identity 'Int.add_zero}
    :metadata {:ansatz/type 'Int
               :ansatz/op 'Int.add
               :kernel (monoid-kernel (c "Int")
                                      (int-zero-expr)
                                      (hadd-combine (c "Int") "Int.instAdd"))
               :runtime {:trusted-primitive :clojure.lang.Numbers/add}}}))

;; ============================================================
;; Parallel terminals
;; ============================================================

(defn- assert-fold-safe! [pipeline]
  (when-not (fold-safe? pipeline)
    (throw (ex-info "Pipeline contains transforms that are not fold-safe"
                    (explain pipeline))))
  pipeline)

(defn fold-map
  "Lawful parallel map-then-fold.

   This is the safe parallel primitive: every element is mapped to a monoid
   value, chunk results are combined with the same monoid, and Clojure's
   `reducers/fold` handles the chunk tree. Arbitrary `step` folds are excluded
   from the safe API because they additionally need a homomorphism law."
  ([pipeline spec f coll]
   (fold-map pipeline spec f coll {}))
  ([pipeline spec f coll {:keys [grain] :or {grain 512}}]
   (let [pipeline (assert-fold-safe! (ensure-pipeline pipeline))
         {:keys [combine]} (assert-lawful! spec)
         xf (xform pipeline)
         reducef (xf (fn [acc x] (combine acc (f x))))]
     (reducers/fold grain (combinef spec) reducef coll))))

(defn fold-map-checked
  "Kernel-checked variant of `fold-map`.

   Call `validate-monoid-spec` first. This is the API to use when the caller
   wants the fold laws backed by checked Ansatz/Lean declarations rather than
   just structurally present certificate names."
  ([pipeline spec f coll]
   (fold-map-checked pipeline spec f coll {}))
  ([pipeline spec f coll opts]
   (assert-kernel-lawful! spec)
   (fold-map pipeline spec f coll opts)))

(defn fold-map-seq
  "Sequential map-then-fold using Clojure's `transduce`.

   This is the low-overhead path for ordinary Clojure workloads. It still uses a
   lawful monoid descriptor so callers can share the same terminal spec with the
   parallel path, but it does not rely on regrouping."
  [pipeline spec f coll]
  (let [pipeline (ensure-pipeline pipeline)
        {:keys [unit-fn combine]} (assert-lawful! spec)
        rf (fn
             ([] (unit-fn))
             ([acc] acc)
             ([acc x] (combine acc (f x))))]
    (core/transduce (xform pipeline) rf (unit-fn) coll)))

(defn fold-map-seq-checked
  "Kernel-checked variant of `fold-map-seq`."
  [pipeline spec f coll]
  (assert-kernel-lawful! spec)
  (fold-map-seq pipeline spec f coll))

(defn sum-by
  "Lawful parallel sum after mapping each input to a monoid value."
  ([pipeline spec f coll]
   (sum-by pipeline spec f coll {}))
  ([pipeline spec f coll opts]
   (fold-map pipeline spec f coll opts)))

(defn sum
  "Lawful parallel sum using identity as the value function."
  ([pipeline spec coll]
   (sum pipeline spec coll {}))
  ([pipeline spec coll opts]
   (sum-by pipeline spec identity coll opts)))

(defn sum-by-seq
  "Sequential sum after mapping each input to a monoid value."
  [pipeline spec f coll]
  (fold-map-seq pipeline spec f coll))

(defn sum-seq
  "Sequential sum using identity as the value function."
  [pipeline spec coll]
  (sum-by-seq pipeline spec identity coll))

(defn sum-by-checked
  "Kernel-checked variant of `sum-by`."
  ([pipeline spec f coll]
   (sum-by-checked pipeline spec f coll {}))
  ([pipeline spec f coll opts]
   (fold-map-checked pipeline spec f coll opts)))

(defn sum-checked
  "Kernel-checked variant of `sum`."
  ([pipeline spec coll]
   (sum-checked pipeline spec coll {}))
  ([pipeline spec coll opts]
   (sum-by-checked pipeline spec identity coll opts)))

(defn sum-by-seq-checked
  "Kernel-checked variant of `sum-by-seq`."
  [pipeline spec f coll]
  (fold-map-seq-checked pipeline spec f coll))

(defn sum-seq-checked
  "Kernel-checked variant of `sum-seq`."
  [pipeline spec coll]
  (sum-by-seq-checked pipeline spec identity coll))

(defn unchecked-fold-map
  "Parallel map-then-fold without law checking.

   This mirrors lean-reducers' explicit unchecked path. Use only when the caller
   accepts Clojure reducers' regrouping semantics."
  ([pipeline unit-fn combine f coll]
   (unchecked-fold-map pipeline unit-fn combine f coll {}))
  ([pipeline unit-fn combine f coll {:keys [grain] :or {grain 512}}]
   (let [pipeline (assert-fold-safe! (ensure-pipeline pipeline))
         xf (xform pipeline)
         reducef (xf (fn [acc x] (combine acc (f x))))
         combinef (fn
                    ([] (unit-fn))
                    ([left right] (combine left right)))]
     (reducers/fold grain combinef reducef coll))))

(def ^:private missing-value
  (Object.))

(defn- merge-groups [value-spec left right]
  (let [value-combine (:combine (assert-lawful! value-spec))]
    (core/reduce-kv
     (fn [groups k rv]
       (let [lv (get groups k missing-value)]
         (assoc groups k (if (identical? lv missing-value)
                           rv
                           (value-combine lv rv)))))
     left
     right)))

(defn- group-monoid [value-spec]
  (assert-lawful! value-spec)
  (monoid-spec
   {:name [:group-by (:name value-spec)]
    :unit-fn hash-map
    :combine (partial merge-groups value-spec)
    :laws {:assoc {:derived :pointwise-map-assoc
                   :from (:name value-spec)}
           :left-identity {:derived :empty-map-left-identity
                           :from (:name value-spec)}
           :right-identity {:derived :empty-map-right-identity
                            :from (:name value-spec)}}
    :metadata {:derived-from value-spec}}))

(defn group-by
  "Lawful parallel grouping.

   `value-f` maps each input to a contribution for its key. Values with the same
   key are merged using `value-spec`."
  ([pipeline value-spec key-f value-f coll]
   (group-by pipeline value-spec key-f value-f coll {}))
  ([pipeline value-spec key-f value-f coll opts]
   (fold-map pipeline
             (group-monoid value-spec)
             (fn [x] {(key-f x) (value-f x)})
             coll
             opts)))

(defn group-by-seq
  "Sequential grouping using a transient map accumulator."
  [pipeline value-spec key-f value-f coll]
  (let [pipeline (ensure-pipeline pipeline)
        value-combine (:combine (assert-lawful! value-spec))]
    (persistent!
     (core/transduce
      (xform pipeline)
      (fn
        ([] (transient {}))
        ([groups] groups)
        ([groups x]
         (let [k (key-f x)
               rv (value-f x)
               lv (get groups k missing-value)]
           (assoc! groups k (if (identical? lv missing-value)
                              rv
                              (value-combine lv rv))))))
      (transient {})
      coll))))

(defn frequencies
  "Lawful parallel frequency map.

   `count-spec` is usually `nat-add` or a kernel-checked version of it."
  ([pipeline count-spec key-f coll]
   (frequencies pipeline count-spec key-f coll {}))
  ([pipeline count-spec key-f coll opts]
   (group-by pipeline count-spec key-f (constantly 1) coll opts)))

(defn frequencies-seq
  "Sequential frequency map using a transient map accumulator."
  [pipeline count-spec key-f coll]
  (group-by-seq pipeline count-spec key-f (constantly 1) coll))

(defn group-by-checked
  "Kernel-checked variant of `group-by` for the value monoid.

   The map-level group monoid laws are derived pointwise from the checked value
   monoid; this function requires the value monoid itself to be kernel-checked."
  ([pipeline value-spec key-f value-f coll]
   (group-by-checked pipeline value-spec key-f value-f coll {}))
  ([pipeline value-spec key-f value-f coll opts]
   (assert-kernel-lawful! value-spec)
   (group-by pipeline value-spec key-f value-f coll opts)))

(defn group-by-seq-checked
  "Kernel-checked variant of `group-by-seq`."
  [pipeline value-spec key-f value-f coll]
  (assert-kernel-lawful! value-spec)
  (group-by-seq pipeline value-spec key-f value-f coll))

(defn frequencies-checked
  "Kernel-checked variant of `frequencies`."
  ([pipeline count-spec key-f coll]
   (frequencies-checked pipeline count-spec key-f coll {}))
  ([pipeline count-spec key-f coll opts]
   (group-by-checked pipeline count-spec key-f (constantly 1) coll opts)))

(defn frequencies-seq-checked
  "Kernel-checked variant of `frequencies-seq`."
  [pipeline count-spec key-f coll]
  (group-by-seq-checked pipeline count-spec key-f (constantly 1) coll))
