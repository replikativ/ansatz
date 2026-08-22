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
(declare schema->type-expr)

(defn- map-entry-schema
  "The value schema of a [:map …] entry, which is [k T] or [k props T]."
  [entry]
  (if (= 3 (count entry)) (nth entry 2) (nth entry 1)))

(defn- record-entries
  "[:map …] entries as `ensure-record!` wants them: [[field-name field-type-Expr] …].

   One definition: the type layer synthesizes the record from this, and the differential
   codec names its constructor from this, so the two cannot disagree about field order."
  [more]
  (mapv (fn [entry] [(name (first entry)) (schema->type-expr (map-entry-schema entry))]) more))

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

(defn- enum-members
  "An [:enum …] form's members, with a leading property map dropped."
  [more]
  (vec (if (map? (first more)) (rest more) more)))

(defn- enum-type-name
  "Deterministic kernel type name for keyword enum `members`: sanitized member names for
   readability + a short hash of the member vector, so the same enum always names the same
   type (idempotent synthesis) and a reordering names a different one."
  [members]
  (str "MalliEnum_"
       (str/join "_" (map (fn [k] (str/replace (subs (str k) 1) #"[^A-Za-z0-9]" "_")) members))
       "_" (format "%x" (bit-and (hash (vec members)) 0xffffff))))

(defn ensure-enum!
  "Synthesize (idempotently) a closed inductive for a KEYWORD [:enum …]'s `members` into the
   global env — one nullary constructor `c<i>` per member, in DECLARED order — plus a
   `DecidableEq` instance so members compare. Registers a codegen lowering per constructor,
   so the compiled runtime yields the keyword the schema declares. Returns the type's const
   Expr.

   One definition: the type layer synthesizes the inductive from `enum-type-name`, and the
   differential codec names its constructors from the same fn, so the two cannot disagree
   about which constructor is which member."
  [members]
  (let [members (vec members)
        tname   (enum-type-name members)
        env0    ((requiring-resolve 'ansatz.core/env))]
    (when-not (env/lookup env0 (nm tname))
      (let [ctors (mapv (fn [i] [(symbol (str "c" i)) []]) (range (count members)))
            env1  (inductive/define-inductive env0 tname [] ctors)
            env2  (env/add-constant env1
                                    (env/mk-axiom (nm (str "instDecidableEq" tname)) []
                                                  (e/app (e/const' (nm "DecidableEq") [u1])
                                                         (kconst tname))))]
        (reset! (deref (requiring-resolve 'ansatz.core/ansatz-env)) env2)
        (swap! (deref (requiring-resolve 'ansatz.core/codegen-registry))
               into (map-indexed (fn [i mbr] [(str tname ".c" i) (fn [_ _ _] mbr)]) members))))
    (kconst tname)))

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
        ;; a fieldless map declares no accessible fields → the gradual Opaque carrier
        ;; (a [:map [:k T] …] WITH fields synthesizes a record instead, in the vector case).
        :map (ensure-opaque!)
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
        (keyword? symbol? uuid? any? some? ident? simple-keyword? qualified-keyword? map?)
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
          ;; regex-sequence element schemas: :* / :+ collect into a List (the :+ non-empty
          ;; invariant is not carried), :? is an Option — the natural type of a variadic tail.
          (:* :+) (klist (schema->type-expr (first more)))
          :? (koption (schema->type-expr (first more)))
          ;; [:map-of K V] → an association List of key/value Prods; keys and values keep
          ;; their sharp element types (the kernel has no native finite-map).
          :map-of (klist (kprod (schema->type-expr (first more))
                                (schema->type-expr (second more))))
          :tuple (kprods (map schema->type-expr more))
          ;; [:map [:k T] …] → a synthesized named-field structure: keyword access in
          ;; bodies elaborates to kernel projections, runtime values are plain maps.
          ;; (:optional entry props are accepted; the field type is the entry schema —
          ;; optionality is not yet modeled as Option.) A fieldless [:map] carries as Opaque.
          :map (if (seq more)
                 (ensure-record! (record-entries more))
                 (ensure-opaque!))
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
          :enum (let [ms (enum-members more)
                      v  (first ms)]
                  (cond (string? v)  (kconst "String")
                        (int? v)     (kconst "Nat")
                        (boolean? v) (kconst "Bool")
                        (every? keyword? ms) (ensure-enum! ms)
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
  "Clamp a schema for generation so kernel whnf stays cheap: small non-negative ints,
   short lists, short strings and small maps.

   Covers exactly the shapes `encode-val`/`decode-val` can carry across the boundary.
   A shape the codec cannot round-trip must throw HERE rather than generate a value the
   kernel will reject later, where the failure reads as a divergence rather than a gap."
  [f]
  (let [f (if (m/schema? f) (m/form f) f)]
    (cond
      (contains? #{:int 'int? 'integer? :nat-int 'nat-int?} f) [:int {:min 0 :max 25}]
      (contains? #{:boolean 'boolean?} f) :boolean
      (contains? #{:string 'string?} f) [:string {:max 6}]
      ;; a bare :keyword is an OPEN set, so it has no closed kernel carrier — it types as
      ;; Opaque, which is an axiom with no constructors and therefore no value to encode.
      (contains? #{:keyword 'keyword? :symbol 'symbol? :uuid 'uuid? :any 'any?} f)
      (throw (ex-info "differential lane: an open scalar carries as Opaque, which has no closed values"
                      {:form f}))
      (vector? f)
      (let [[tag & more] f
            [props more] (if (map? (first more)) [(first more) (rest more)] [nil more])]
        (case tag
          (:sequential :vector) [:sequential {:max 6} (gen-schema (first more))]
          :int [:int {:min (max 0 (or (:min props) 0)) :max (min 25 (or (:max props) 25))}]
          :string [:string {:min (or (:min props) 0) :max (min 6 (or (:max props) 6))}]
          :maybe [:maybe (gen-schema (first more))]
          ;; [:tuple A B …] rides a right-nested Prod; each component clamps on its own.
          :tuple (into [:tuple] (map gen-schema) more)
          ;; [:map-of K V] rides a List of Prod pairs — kept short for the same reason lists are.
          :map-of [:map-of {:max 4} (gen-schema (first more)) (gen-schema (second more))]
          ;; a homogeneous string/int/bool enum generates its own members unchanged —
          ;; they are already literals the codec carries. A homogeneous KEYWORD enum is a
          ;; closed set, so it rides the inductive `ensure-enum!` synthesizes.
          :enum (if (or (every? (some-fn string? int? boolean?) more)
                        (every? keyword? more))
                  (into [:enum] more)
                  (throw (ex-info "differential lane: only homogeneous string/int/bool/keyword enum members carry"
                                  {:form f})))
          ;; [:map [:k T] …] rides the synthesized record; a FIELDLESS map is the Opaque
          ;; carrier, which has no values to generate.
          :map (if (seq more)
                 (into [:map] (map (fn [entry]
                                     [(first entry) (gen-schema (map-entry-schema entry))]))
                       more)
                 (throw (ex-info "differential lane: a fieldless [:map] carries as Opaque"
                                 {:form f})))
          (throw (ex-info "differential lane: unsupported generator schema" {:form f}))))
      :else (throw (ex-info "differential lane: unsupported generator schema" {:form f})))))

(defn- unprop
  "A schema form's children with a leading property map dropped."
  [more]
  (if (map? (first more)) (rest more) more))

(defn- encode-val
  "Clojure value → kernel Expr, directed by the SCHEMA the value belongs to.

   The schema is required, not a convenience: a List's element type is an explicit kernel
   argument, and a record's fields have a declared order its constructor expects. Encoding
   from the value alone can only guess the element type, and the guess was always `Nat` —
   so a list of anything else produced an ill-typed term."
  [schema v]
  (let [f (if (m/schema? schema) (m/form schema) schema)]
    (cond
      (contains? #{:int 'int? 'integer? :nat-int 'nat-int?} f) (e/lit-nat (long v))
      (contains? #{:boolean 'boolean?} f) (kconst (if v "Bool.true" "Bool.false"))
      (contains? #{:string 'string?} f) (e/lit-str v)

      (vector? f)
      (let [[tag & more] f
            more (unprop more)]
        (case tag
          :int (e/lit-nat (long v))
          :string (e/lit-str v)
          :boolean (kconst (if v "Bool.true" "Bool.false"))

          (:sequential :vector)
          (let [el (first more)
                elt (schema->type-expr el)]
            (reduce (fn [acc x]
                      (e/app* (e/const' (nm "List.cons") [lvl/zero]) elt (encode-val el x) acc))
                    (e/app (e/const' (nm "List.nil") [lvl/zero]) elt)
                    (reverse v)))

          :maybe
          (let [el (first more)
                elt (schema->type-expr el)]
            (if (nil? v)
              (e/app (e/const' (nm "Option.none") [lvl/zero]) elt)
              (e/app* (e/const' (nm "Option.some") [lvl/zero]) elt (encode-val el v))))

          ;; [:tuple A B …] → right-nested Prod.mk, matching the type layer's `kprods`.
          ;; A 1-tuple IS its component; a 0-tuple is Unit.
          :tuple
          (let [enc (fn enc [ss xs]
                      (case (count ss)
                        0 (kconst "Unit.unit")
                        1 (encode-val (first ss) (first xs))
                        (e/app* (e/const' (nm "Prod.mk") [lvl/zero lvl/zero])
                                (schema->type-expr (first ss))
                                (kprods (map schema->type-expr (rest ss)))
                                (encode-val (first ss) (first xs))
                                (enc (rest ss) (rest xs)))))]
            (enc (vec more) (vec v)))

          ;; [:map-of K V] → a List of Prod pairs. Entries are emitted in a deterministic
          ;; order so the same map always encodes to the same term.
          :map-of
          (let [[k-s v-s] (vec more)
                kt (schema->type-expr k-s)
                vt (schema->type-expr v-s)
                pt (kprod kt vt)]
            (reduce (fn [acc [k x]]
                      (e/app* (e/const' (nm "List.cons") [lvl/zero]) pt
                              (e/app* (e/const' (nm "Prod.mk") [lvl/zero lvl/zero]) kt vt
                                      (encode-val k-s k) (encode-val v-s x))
                              acc))
                    (e/app (e/const' (nm "List.nil") [lvl/zero]) pt)
                    (reverse (sort-by (comp pr-str first) v))))

          ;; a string/int/bool enum's members ARE literals of their scalar type, which is
          ;; what schema->type-expr already gives the enum. A keyword member is a
          ;; constructor of the inductive ensure-enum! synthesizes, named by its position.
          :enum (cond (string? v)  (e/lit-str v)
                      (boolean? v) (kconst (if v "Bool.true" "Bool.false"))
                      (integer? v) (e/lit-nat (long v))
                      (keyword? v)
                      (let [ms (enum-members more)
                            i  (.indexOf ^java.util.List ms v)]
                        (when (neg? i)
                          (throw (ex-info "differential lane: value is not a member of the enum"
                                          {:form f :value v})))
                        (ensure-enum! ms)
                        (kconst (str (enum-type-name ms) ".c" i)))
                      :else (throw (ex-info "differential lane: unencodable enum member"
                                            {:form f :value v})))

          ;; [:map [:k T] …] → the synthesized record's constructor, fields applied in
          ;; DECLARED order. ensure-record! is idempotent, so this is also what makes the
          ;; type available when the record was not reached through a signature.
          :map
          (let [entries (record-entries more)
                tname   (record-type-name entries)]
            (ensure-record! entries)
            (reduce (fn [acc entry]
                      (e/app acc (encode-val (map-entry-schema entry) (get v (first entry)))))
                    (kconst (str tname ".mk"))
                    more))

          (throw (ex-info "differential lane: unencodable schema" {:form f :value v}))))

      :else (throw (ex-info "differential lane: unencodable schema" {:form f :value v})))))

(defn- decode-val
  "whnf'd kernel Expr → Clojure value, directed by the schema it should inhabit.

   `whnf` is applied at EVERY descent, not only at the top: whnf is WEAK head normal form,
   so a constructor application's arguments come back unreduced. Without this a function
   that BUILDS a compound result from computed parts is undecodable.

   The schema supplies what the term cannot: a record's field NAMES (the constructor
   carries positions only), the element schema to decode a list's tail against, and which
   of the several shapes that share a kernel representation this one is — a `[:tuple A B]`
   and a two-field record are both Prod-shaped, and a `[:map-of K V]` and a
   `[:sequential [:tuple K V]]` are the same List of pairs."
  [whnf schema x]
  (let [x      (whnf x)
        f      (if (m/schema? schema) (m/form schema) schema)
        [h as] (e/get-app-fn-args x)
        hname  (when (e/const? h) (name/->string (e/const-name h)))
        child  (fn [] (first (unprop (rest f))))
        tag    (when (vector? f) (first f))
        undecodable (fn [t] (throw (ex-info "differential lane: undecodable kernel value"
                                            {:form f :value (e/->string t)})))]
    (cond
      ;; ── schema-decided shapes, checked before the term-directed cases ───────────────
      ;; [:tuple A B …] rides a right-nested Prod.mk; a 1-tuple IS its component.
      (= :tuple tag)
      (let [ss (vec (unprop (rest f)))]
        (case (count ss)
          0 []
          1 [(decode-val whnf (first ss) x)]
          (if (and (= "Prod.mk" hname) (= 4 (count as)))
            (into [(decode-val whnf (first ss) (nth as 2))]
                  (decode-val whnf (into [:tuple] (rest ss)) (nth as 3)))
            (undecodable x))))

      ;; [:map-of K V] rides a List of Prod pairs. Duplicate keys would collapse silently
      ;; into one entry, hiding a kernel result a Clojure map cannot represent, so they
      ;; throw rather than decode.
      (= :map-of tag)
      (let [[k-s v-s] (vec (unprop (rest f)))
            pairs (loop [t x acc []]
                    (let [t (whnf t)
                          [th tas] (e/get-app-fn-args t)
                          tn (when (e/const? th) (name/->string (e/const-name th)))]
                      (cond
                        (= "List.nil" tn) acc
                        (and (= "List.cons" tn) (= 3 (count tas)))
                        (let [pair (whnf (nth tas 1))
                              [ph pas] (e/get-app-fn-args pair)
                              pn (when (e/const? ph) (name/->string (e/const-name ph)))]
                          (when-not (and (= "Prod.mk" pn) (= 4 (count pas)))
                            (undecodable pair))
                          (recur (nth tas 2)
                                 (conj acc [(decode-val whnf k-s (nth pas 2))
                                            (decode-val whnf v-s (nth pas 3))])))
                        :else (undecodable t))))]
        (when-not (= (count pairs) (count (set (map first pairs))))
          (throw (ex-info "differential lane: duplicate keys in a [:map-of …] kernel result"
                          {:form f :keys (mapv first pairs)})))
        (into {} pairs))

      ;; a keyword [:enum …] rides the inductive ensure-enum! synthesized: the constructor
      ;; suffix is the member's DECLARED position, which is the only thing the term carries.
      (and (= :enum tag) (every? keyword? (enum-members (rest f))))
      (let [ms  (enum-members (rest f))
            dot (when hname (str/last-index-of hname "."))
            idx (when dot (parse-long (subs hname (inc (inc dot)))))]
        (if (and idx (< -1 idx (count ms))
                 (= hname (str (enum-type-name ms) ".c" idx)))
          (nth ms idx)
          (undecodable x)))

      ;; ── term-directed cases ────────────────────────────────────────────────────────
      (e/lit-nat? x) (e/lit-nat-val x)
      (e/lit-str? x) (e/lit-str-val x)
      (= "Bool.true" hname) true
      (= "Bool.false" hname) false
      (= "List.nil" hname) ()
      (and (= "List.cons" hname) (= 3 (count as)))
      (cons (decode-val whnf (child) (nth as 1)) (decode-val whnf f (nth as 2)))
      (= "Option.none" hname) nil
      (and (= "Option.some" hname) (= 2 (count as)))
      (decode-val whnf (child) (nth as 1))
      ;; <MalliRec_…>.mk applied to its fields, in the schema's declared order
      (and hname (str/ends-with? hname ".mk") (vector? f) (= :map (first f)))
      (let [entries (unprop (rest f))]
        (into {} (map-indexed (fn [i entry]
                                [(first entry)
                                 (decode-val whnf (map-entry-schema entry) (nth as i))])
                              entries)))
      :else (undecodable x))))

(defn check-verified!
  "The differential check for an a/defn'd function with a malli schema: generate `runs`
   inputs from the (clamped) schema, run the compiled runtime and the kernel evaluator,
   compare. Returns {:runs n :ok n} or throws on the first divergence — a divergence means
   an ELABORATION bug (well-typed but source-unfaithful), the exact class the kernel cannot
   see. Scope: whatever `gen-schema` will clamp and the codec will carry — Nat, Bool,
   String, Option, homogeneous lists of those, named-field [:map] records, [:tuple …],
   [:map-of K V] and homogeneous keyword [:enum …]."
  [ns-sym fn-sym & {:keys [runs] :or {runs 25}}]
  (let [schema (get-in (m/function-schemas) [ns-sym fn-sym :schema])
        _ (when-not schema (throw (ex-info "check-verified!: no m/=> schema registered"
                                           {:ns ns-sym :fn fn-sym})))
        f (if (m/schema? schema) (m/form schema) schema)
        ;; the DECLARED argument schemas type the kernel term; the clamped ones only
        ;; bound generation. They are not interchangeable: [:int {:min 0 :max 25}]
        ;; elaborates to a Subtype, while the function's signature was built from :int.
        arg-forms (vec (rest (second f)))
        out-form (nth f 2)
        arg-schemas (mapv gen-schema arg-forms)
        the-fn @(ns-resolve ns-sym fn-sym)
        env ((requiring-resolve 'ansatz.core/env))
        cname (name/from-string (name fn-sym))
        tc (doto (ansatz.kernel.TypeChecker. env) (.setFuel 200000000))
        red (.getReducer tc)
        whnf (fn [t] (.whnf red t))]
    (dotimes [_ runs]
      (let [args (mapv mg/generate arg-schemas)
            rt-val (apply the-fn args)
            k-app (reduce e/app (e/const' cname [])
                          (mapv encode-val arg-forms args))
            k-val (decode-val whnf out-form k-app)]
        ;; structural =, not (long …): the lane now carries strings, options, lists and
        ;; records, and coercing those to long throws where it should compare.
        (when-not (= k-val rt-val)
          (throw (ex-info "DIFFERENTIAL DIVERGENCE: compiled runtime ≠ kernel evaluation"
                          {:fn fn-sym :args args :runtime rt-val :kernel k-val})))))
    {:runs runs :ok runs}))
