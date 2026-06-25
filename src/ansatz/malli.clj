(ns ansatz.malli
  "The gradual dependently-typed surface for Clojurians: malli schemas as a/defn signatures.

   Loads ONLY when metosin/malli is on the classpath (ansatz core does not depend on it;
   the a/defn macro and the elaborator probe via requiring-resolve — the optionality seam).

   The porting story is a one-token diff. Given ordinary instrumented Clojure:

     (defn add2 [x y] (+ x y))
     (m/=> add2 [:=> [:cat :int :int] :int])

   change `defn` to `a/defn` and the SAME schema becomes the kernel signature.

   Pipeline: `signature-for` (macro time) returns param/ret as PURE-DATA marker forms
   `(:malli/schema <form>)`; the elaborator translates the marker via `schema->type-expr`
   (kernel Exprs built here, no env needed — unknown constants surface honestly at
   elaboration). The translator is ported from wandler's ansatz.malli (the comprehensive
   prior art) onto this contract.

   Registry: domain types register once with `register-type!`; schemas referencing them
   ([:ref :user/id] or bare :user/id) resolve and recurse — pipelines over registered
   types just work."
  (:require [malli.core :as m]
            [malli.generator :as mg]
            [clojure.string :as str]
            [ansatz.inductive :as inductive]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]))

(defn- nm [s] (name/from-string s))
(defn- kconst [s] (e/const' (nm s) []))
(def ^:private u1 (lvl/succ lvl/zero))

;; ── domain-type registry (schema keyword → schema form) ─────────────────────────────────
(defonce ^{:doc "Domain types: keyword → malli schema form. Registered once, referenced anywhere."}
  type-registry (atom {}))

(defn register-type!
  "Register a named domain schema, e.g. (register-type! :user/age [:int {:min 0 :max 150}])."
  [k schema-form]
  (swap! type-registry assoc k schema-form))

(defn- deref-registry [f]
  (or (get @type-registry f)
      (when (and (vector? f) (= :ref (first f))) (get @type-registry (second f)))))

;; ── kernel-type constructors ─────────────────────────────────────────────────────────────
(defn- klist [a] (e/app (e/const' (nm "List") [lvl/zero]) a))
(defn- koption [a] (e/app (e/const' (nm "Option") [lvl/zero]) a))
(defn- kprod [a b] (e/app* (e/const' (nm "Prod") [lvl/zero lvl/zero]) a b))
(defn- record-type-name
  "Deterministic structure name for [:map …] entries [[field-name type-Expr] …]: field
   names for readability + a short hash of the field types for collision safety, so the
   same schema always names the same kernel type (idempotent synthesis)."
  [entries]
  (str "MalliRec_" (str/join "_" (map first entries))
       "_" (format "%x" (bit-and (hash (mapv (fn [[f t]] [f (e/->string t)]) entries))
                                 0xffffff))))

(defn ensure-record!
  "Synthesize (idempotently) a named single-constructor structure for [:map …] entries
   into the global env — inductive + mk + per-field projections — and register it in the
   structure registry with :map? true: the runtime representation is a PLAIN Clojure map
   (what the [:map] schema validates), keyword access elaborates to kernel projections.
   Runs eagerly at signature-for (macro) time so the env snapshot taken by define-verified
   already contains the record. Returns the type's const Expr."
  [entries]
  (let [tname (record-type-name entries)
        kname (nm tname)
        env0 ((requiring-resolve 'ansatz.core/env))]
    (when-not (env/lookup env0 kname)
      (let [flat (vec (mapcat (fn [[f t]] [(symbol f) t]) entries))
            env1 (inductive/define-inductive env0 tname [] [['mk flat]])
            ind (kconst tname)
            env2 (reduce (fn [acc-env [idx [f _]]]
                           (let [proj-name (nm (str tname "." f))
                                 pv (e/lam "self" ind (e/proj kname idx (e/bvar 0)) :default)
                                 pt (tc/infer-type (tc/mk-tc-state acc-env) pv)]
                             (env/check-constant acc-env
                                                 (env/mk-def proj-name [] pt pv :hints :abbrev))))
                         env1 (map-indexed vector entries))]
        (reset! (deref (requiring-resolve 'ansatz.core/ansatz-env)) env2)
        (swap! (deref (requiring-resolve 'ansatz.core/structure-registry))
               assoc tname {:fields (mapv first entries) :map? true})))
    (kconst tname)))

(defn ensure-opaque!
  "Idempotently install the OPAQUE carrier into the global env: `Opaque : Type` — an abstract type
   inhabited only by runtime boundary values (keywords, uuids, symbols, dates, any value a schema does not
   model precisely) — plus `instDecidableEqOpaque : DecidableEq Opaque`. An opaque field is CARRIED
   (projected) and group-by/join KEY on it (the dec lowers to Clojure `=`, erased at runtime); the type
   has NO other operations, so the type system prevents misuse (no arithmetic/string ops on a date). This
   is the gradual `?` of the typed lane: native where the schema is sharp, `Opaque` where it is not — so a
   record mixes precise fields (full optimizer algebra) with opaque ones (carry + key). Returns the
   `Opaque` const Expr. (For wholesale dynamic EDN with conformance + dynamic ops, the separate Value lane
   `ansatz.surface.schema/schema->value-type` is the other pole.)"
  []
  (let [env0 ((requiring-resolve 'ansatz.core/env))]
    (when-not (env/lookup env0 (nm "Opaque"))
      (let [env1 (env/add-constant env0 (env/mk-axiom (nm "Opaque") [] (e/sort' u1)))
            env2 (env/add-constant env1 (env/mk-axiom (nm "instDecidableEqOpaque") []
                                                      (e/app (e/const' (nm "DecidableEq") [u1]) (kconst "Opaque"))))]
        (reset! (deref (requiring-resolve 'ansatz.core/ansatz-env)) env2))))
  (kconst "Opaque"))

(defn- kprods
  "Right-nested Prod over component types (records/tuples as anonymous products)."
  [ts]
  (let [ts (vec ts)]
    (case (count ts)
      0 (kconst "Unit")
      1 (first ts)
      (reduce (fn [acc t] (kprod t acc)) (peek ts) (rseq (pop ts))))))

(defn- nat-le [a b] (e/app* (e/const' (nm "LE.le") [lvl/zero]) (kconst "Nat")
                            (kconst "instLENat") a b))
(defn- nat-lt [a b] (e/app* (e/const' (nm "LT.lt") [lvl/zero]) (kconst "Nat")
                            (kconst "instLTNat") a b))
(defn- kand [a b] (e/app* (kconst "And") a b))

(defn- bound-prop
  "Prop body over (bvar 0 : Nat): ge ≤ v [∧ v < lt], or nil when unbounded."
  [ge lt]
  (let [lo (when ge (nat-le (e/lit-nat ge) (e/bvar 0)))
        hi (when lt (nat-lt (e/bvar 0) (e/lit-nat lt)))]
    (cond (and lo hi) (kand lo hi) lo lo hi hi :else nil)))

(defn- ksubtype-nat
  "`Subtype Nat (fun v => bounds)` — the refinement type for bounded ints; nil if unbounded."
  [ge lt]
  (when-let [body (bound-prop ge lt)]
    (e/app* (e/const' (nm "Subtype") [u1]) (kconst "Nat")
            (e/lam "v" (kconst "Nat") body :default))))

(defn- ksubtype-string
  "`Subtype String (fun s => min ≤ s.length [∧ s.length ≤ max])`; nil if no length bound.
   The refinement is carried in the TYPE and erased at runtime (a plain String value)."
  [mn mx]
  (let [len (e/app (e/const' (nm "String.length") []) (e/bvar 0))
        lo (when mn (nat-le (e/lit-nat mn) len))
        hi (when mx (nat-le len (e/lit-nat mx)))
        body (cond (and lo hi) (kand lo hi) lo lo hi hi :else nil)]
    (when body
      (e/app* (e/const' (nm "Subtype") [u1]) (kconst "String")
              (e/lam "s" (kconst "String") body :default)))))

;; ── schema → kernel type (ported from wandler, comprehensive) ────────────────────────────
(defn- ksubtype-nodup
  "`Subtype (List X) (fun l => List.Nodup X l)` — the refinement carrier for a malli `:set` (a list
   with no duplicate elements). The `Nodup` proof rides the value (`Subtype.property`); the optimizer's
   certified DISTINCT-removal (`nodup_eraseDups`) consumes it to drop a redundant `distinct`."
  [X]
  (let [listX (klist X)
        P (e/lam "l" listX (e/app* (e/const' (nm "List.Nodup") [lvl/zero]) X (e/bvar 0)) :default)]
    (e/app* (e/const' (nm "Subtype") [u1]) listX P)))

(defn schema->type-expr
  "Convert a malli schema FORM to a kernel type Expr. Unknown constants (Option, Float, …)
   surface honestly at elaboration if the env lacks them; unsupported schema SHAPES throw
   here with the offending form."
  [schema]
  (let [f (if (m/schema? schema) (m/form schema) schema)]
    (cond
      (keyword? f)
      (case f
        ;; v1 maps :int to Nat — this branch's embedding (arithmetic default, WF measures,
        ;; sizeOf) is Nat-centric; negative ints are caught by malli's own runtime checks.
        ;; Promote to Int when the int=long faithfulness story lands here (wandler has it).
        :int (kconst "Nat")
        (:nat-int :nat) (kconst "Nat")
        :boolean (kconst "Bool")
        :string (kconst "String")
        :double (kconst "Float")
        :nil (kconst "Unit")
        ;; opaque scalars (keyword/uuid/symbol/any) — no sharp native rep; the gradual `Opaque` carrier
        ;; (carry + group-by/join key via `=`, no other ops). Registered schemas still take precedence.
        (:keyword :symbol :uuid :any :some :qualified-keyword :qualified-symbol)
        (ensure-opaque!)
        (if-let [r (deref-registry f)]
          (schema->type-expr r)
          (throw (ex-info (str "ansatz.malli: unsupported scalar schema " f) {:form f}))))

      (symbol? f)
      (case f
        (int? integer?) (kconst "Nat")   ;; see :int note above
        (nat-int? pos-int?) (kconst "Nat")
        boolean? (kconst "Bool")
        string? (kconst "String")
        (keyword? symbol? uuid? any? some? ident? simple-keyword? qualified-keyword?)
        (ensure-opaque!)
        (throw (ex-info (str "ansatz.malli: unsupported predicate schema " f) {:form f})))

      (vector? f)
      (let [[tag & more] f
            [props more] (if (map? (first more)) [(first more) (rest more)] [nil more])]
        (case tag
          (:sequential :vector) (klist (schema->type-expr (first more)))
          ;; a `:set` is a List with a declared no-duplicates invariant → the Nodup refinement carrier,
          ;; which licenses certified DISTINCT-removal downstream.
          :set (ksubtype-nodup (schema->type-expr (first more)))
          :maybe (koption (schema->type-expr (first more)))
          :tuple (kprods (map schema->type-expr more))
          ;; [:map [:k T] …] → a synthesized named-field structure: keyword access in
          ;; bodies elaborates to kernel projections, runtime values are plain maps.
          ;; (:optional entry props are accepted; the field type is the entry schema —
          ;; optionality is not yet modeled as Option.)
          :map (ensure-record!
                (mapv (fn [entry]
                        [(name (first entry))
                         (schema->type-expr (if (= 3 (count entry)) (nth entry 2) (nth entry 1)))])
                      more))
          ;; [:int {:min n :max m}] — {:min 0} is definitionally Nat; positive lower /
          ;; any upper bound becomes a Subtype refinement (max m ⇒ v < m+1)
          :int (let [mn (:min props) mx (:max props)
                     ge (when (and mn (pos? mn)) mn)
                     lt (when mx (inc mx))]
                 (cond (or ge lt) (ksubtype-nat ge lt)
                       :else (kconst "Nat")))   ;; see :int note above
          ;; [:and :int [:>= k] [:< m]] — the predicate-combinator spelling of bounds
          :and (let [base (first more)
                     ge (some (fn [s] (when (and (vector? s) (= :>= (first s))) (second s))) more)
                     lt (some (fn [s] (when (and (vector? s) (= :< (first s))) (second s))) more)
                     ge* (when (and ge (pos? ge)) ge)]
                 (cond
                   (and (= :int base) (or ge* lt)) (ksubtype-nat ge* lt)
                   (and (= :int base) ge (zero? ge)) (kconst "Nat")
                   :else (schema->type-expr base)))
          :string (or (ksubtype-string (:min props) (:max props)) (kconst "String"))
          :double (kconst "Float")
          ;; [:enum v…] → the members' scalar type (string→String, int→Nat, bool→Bool); a
          ;; keyword/heterogeneous enum carries as the gradual Opaque (carry + key, no literal compare).
          :enum (let [v (first more)]
                  (cond (string? v) (kconst "String")
                        (int? v)     (kconst "Nat")
                        (boolean? v) (kconst "Bool")
                        :else        (ensure-opaque!)))
          :ref (if-let [r (deref-registry f)]
                 (schema->type-expr r)
                 (throw (ex-info "ansatz.malli: unregistered [:ref …]" {:form f})))
          (if-let [r (deref-registry f)]
            (schema->type-expr r)
            (throw (ex-info (str "ansatz.malli: unsupported schema " tag) {:form f})))))

      :else (throw (ex-info "ansatz.malli: unsupported schema form" {:form f})))))

;; ── a/defn integration (macro-time lookup → pure-data marker forms) ─────────────────────
(defn- marker [schema-form] (list :malli/schema schema-form))

(defn fn-schema->signature
  "[:=> [:cat A B …] R] → {:param-types [(:malli/schema A) …] :ret-type (:malli/schema R)}.
   Marker forms are pure data (embeddable in macroexpansion); the elaborator translates
   them via schema->type-expr."
  [schema]
  (let [f (if (m/schema? schema) (m/form schema) schema)]
    (when (and (vector? f) (= :=> (first f)) (vector? (second f)) (= :cat (first (second f))))
      {:param-types (mapv marker (rest (second f)))
       :ret-type (marker (nth f 2))})))

(defn signature-for
  "Look up the malli function schema for `fn-name` in `ns-sym` (the m/=> registry, then
   :malli/schema metadata on the name symbol). nil = no schema (caller falls through);
   THROW = schema present but untranslatable (honest error)."
  [ns-sym fn-name arity]
  (let [schema (or (:malli/schema (meta fn-name))
                   (get-in (m/function-schemas) [ns-sym (symbol (name fn-name)) :schema]))]
    (when schema
      (let [sig (fn-schema->signature schema)]
        (when-not sig
          (throw (ex-info "ansatz.malli: only [:=> [:cat …] ret] function schemas are supported"
                          {:fn fn-name :schema (if (m/schema? schema) (m/form schema) schema)})))
        (when (not= arity (count (:param-types sig)))
          (throw (ex-info "ansatz.malli: schema arity does not match the parameter vector"
                          {:fn fn-name :schema-arity (count (:param-types sig)) :arity arity})))
        ;; Eagerly translate every marker NOW (macro time): untranslatable schemas throw
        ;; here with the schema in hand, and [:map] record synthesis lands in the global
        ;; env BEFORE define-verified snapshots it.
        (run! (fn [marker] (schema->type-expr (second marker)))
              (conj (:param-types sig) (:ret-type sig)))
        sig))))

;; ── The generative differential lane ─────────────────────────────────────────────────────
;; The kernel checks TYPE-correctness, not source-faithfulness: a well-typed elaboration bug
;; ships a wrong program with a valid certificate (three such bugs were found during the
;; 2026-06 work, all invisible to closed-value testing). The guard is differential: generate
;; inputs from the schema, run the COMPILED runtime and the KERNEL evaluator, compare.

(defn- gen-schema
  "Clamp a schema for generation under the v1 Nat-centric mapping (small non-negative ints,
   short lists) so kernel whnf stays cheap and values stay in Nat."
  [f]
  (let [f (if (m/schema? f) (m/form f) f)]
    (cond
      (contains? #{:int 'int? 'integer? :nat-int 'nat-int?} f) [:int {:min 0 :max 25}]
      (contains? #{:boolean 'boolean?} f) :boolean
      (vector? f)
      (let [[tag & more] f
            [props more] (if (map? (first more)) [(first more) (rest more)] [nil more])]
        (case tag
          (:sequential :vector) [:sequential {:max 6} (gen-schema (first more))]
          :int [:int {:min (max 0 (or (:min props) 0)) :max (min 25 (or (:max props) 25))}]
          (throw (ex-info "differential lane: unsupported generator schema (v1: ints/bools/lists)"
                          {:form f}))))
      :else (throw (ex-info "differential lane: unsupported generator schema" {:form f})))))

(defn- encode-val
  "Clojure value → kernel Expr (v1: Nat / Bool / List Nat)."
  [v]
  (cond
    (integer? v) (e/lit-nat (long v))
    (boolean? v) (kconst (if v "Bool.true" "Bool.false"))
    (or (nil? v) (sequential? v))
    (reduce (fn [acc x] (e/app* (e/const' (nm "List.cons") [lvl/zero]) (kconst "Nat")
                                (encode-val x) acc))
            (e/app (e/const' (nm "List.nil") [lvl/zero]) (kconst "Nat"))
            (reverse v))
    :else (throw (ex-info "differential lane: unencodable value" {:value v}))))

(defn- decode-val
  "whnf'd kernel Expr → Clojure value (v1: Nat literals / Bool / List)."
  [x]
  (let [[h as] (e/get-app-fn-args x)]
    (cond
      (e/lit-nat? x) (e/lit-nat-val x)
      (and (e/const? h) (= "Bool.true" (name/->string (e/const-name h)))) true
      (and (e/const? h) (= "Bool.false" (name/->string (e/const-name h)))) false
      (and (e/const? h) (= "List.nil" (name/->string (e/const-name h)))) ()
      (and (e/const? h) (= "List.cons" (name/->string (e/const-name h))) (= 3 (count as)))
      (cons (decode-val (nth as 1)) (decode-val (nth as 2)))
      :else (throw (ex-info "differential lane: undecodable kernel value"
                            {:value (e/->string x)})))))

(defn check-verified!
  "The differential check for an a/defn'd function with a malli schema: generate `runs`
   inputs from the (clamped) schema, run the compiled runtime and the kernel evaluator,
   compare. Returns {:runs n :ok n} or throws on the first divergence — a divergence means
   an ELABORATION bug (well-typed but source-unfaithful), the exact class the kernel cannot
   see. v1 scope: Nat / Bool / (List Nat) arguments and results."
  [ns-sym fn-sym & {:keys [runs] :or {runs 25}}]
  (let [schema (get-in (m/function-schemas) [ns-sym fn-sym :schema])
        _ (when-not schema (throw (ex-info "check-verified!: no m/=> schema registered"
                                           {:ns ns-sym :fn fn-sym})))
        f (if (m/schema? schema) (m/form schema) schema)
        arg-schemas (mapv gen-schema (rest (second f)))
        the-fn @(ns-resolve ns-sym fn-sym)
        env ((requiring-resolve 'ansatz.core/env))
        cname (name/from-string (name fn-sym))
        tc (doto (ansatz.kernel.TypeChecker. env) (.setFuel 200000000))
        red (.getReducer tc)]
    (dotimes [_ runs]
      (let [args (mapv mg/generate arg-schemas)
            rt-val (apply the-fn args)
            k-app (reduce e/app (e/const' cname []) (mapv encode-val args))
            k-val (decode-val (.whnf red k-app))]
        (when (not= (long k-val) (long rt-val))
          (throw (ex-info "DIFFERENTIAL DIVERGENCE: compiled runtime ≠ kernel evaluation"
                          {:fn fn-sym :args args :runtime rt-val :kernel k-val})))))
    {:runs runs :ok runs}))
