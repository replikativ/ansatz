;; A native formalization of the EDN / Clojure value universe in Ansatz.
;;
;; Clojure's data is essentially EDN: nil, booleans, numbers, strings, keywords,
;; symbols, lists/vectors, maps, sets. We model the whole universe as a single
;; inductive `Value` (cons-cell style, since Ansatz's `a/inductive` supports
;; direct recursion but not nesting under `List`). Every Clojure value is a
;; `Value`; every core operation is a total function over `Value`s.
;;
;; This is the foundation for verified optimization of real Clojure data
;; pipelines: the runtime↔kernel bridge is just an ENCODING (the kernel `Value`
;; IS the EDN AST), the tightest possible link.
;;
;; Map representation: an entry-chain (`ventry k v rest` … `vnil`) tagged by
;; `vmap`. `vassoc` prepends (shadowing); `vget1` reads the head. Canonical
;; (sorted, deduped) maps with scanning `get`/`dissoc` and decidable key equality
;; are the next layer.
;;
;; Requires the env seeded with Lean `Init` (Nat, Bool, Int, String). Call
;; `install-core!` after `(a/init! …)` or after replaying an Init export.

(ns ansatz.surface.schema
  "The SCHEMA leg of ansatz's Clojure↔kernel bridge: the malli→kernel bridge over the Value universe
   (ansatz.surface.data). For a malli schema it compiles the verified conformance predicate γ:Value→Bool
   (compile-schema / schema->conforms-forms) and the #8 universal functor F(schema) = Subtype Value γ
   (schema->value-type). Untagged unions/enums are disjunctive conformance predicates (semantic
   subtyping), not tagged Sums. The PRECISE lane (schema→Nat/List/record/Subtype, for a/defn
   signatures) lives in ansatz.malli. `:re` regex schemas resolve wandler.regex/re-conforms-leaf via a
   soft seam (nil when wandler.regex isn't loaded)."
  (:require [ansatz.core :as a]
            [ansatz.surface.api :as api]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]))

;; ── malli schema → Value conformance predicate ────────────────────────────────
;; A malli schema becomes a REFINEMENT over the Value universe: a kernel-verifiable
;; `Value → Bool` conformance predicate. The compiler is recursive over the schema —
;; scalars reuse the hand-written value-predicates / key-checkers, while nested maps,
;; homogeneous vectors, and optional fields generate fresh helper predicates (each a
;; fuel-recursive `a/defn` over Value that BOTH kernel-verifies and runs, post-#59).

(def ^:private scalar-pred
  "Malli scalar KEYWORD schema → the kernel value-predicate name (Value → Bool)."
  {:int 'vint? :string 'vstr? :boolean 'vbool? :keyword 'vkw? :nil 'vnil?
   :any 'vany? :some 'vsome? :map 'vmap? :double 'vfloat? :float 'vfloat?})

(def ^:private predicate-pred
  "Malli predicate-SYMBOL schema → kernel value-predicate name. Note `:int`/`int?`/`integer?`
   all map to `vint?`: `Value.vint` models an EDN integer *value* (arbitrary precision), so the
   host numeric-tower distinction (Long vs BigInt) is erased by design — faithful on the EDN
   value domain, which is what `Value` models. `double?`/`float?` → `vfloat?` (EDN double)."
  {'int? 'vint? 'integer? 'vint? 'string? 'vstr? 'boolean? 'vbool? 'keyword? 'vkw? 'nil? 'vnil?
   'any? 'vany? 'some? 'vsome? 'map? 'vmap? 'vector? 'vvec? 'set? 'vset?
   'double? 'vfloat? 'float? 'vfloat?})

(def ^:private predicate-range
  "Predicate symbols that mean `:int` + an integer range."
  {'pos-int? {:min 1} 'neg-int? {:max -1} 'nat-int? {:min 0}})

(def ^:private fn->sym
  "Known clojure.core predicate FUNCTIONS → their schema symbol, so an UNQUOTED predicate in a
   malli schema written as data (e.g. `[:tuple pos-int? …]`, where `pos-int?` evals to the fn
   object) is resolved like the symbol form. Unknown fns fall through to a trusted `:fn` leaf."
  {int? 'int? integer? 'integer? string? 'string? boolean? 'boolean? keyword? 'keyword?
   nil? 'nil? any? 'any? some? 'some? map? 'map? vector? 'vector? set? 'set?
   double? 'double? float? 'float? pos-int? 'pos-int? nat-int? 'nat-int? neg-int? 'neg-int?})

(def ^:private scalar-key-checker
  "Malli scalar schema → the hand-written `key-<T>?` checker (keeps flat output identical)."
  {:int 'key-int? :string 'key-str? :boolean 'key-bool?})

(defn- kw-str [k] (subs (str k) 1))   ;; full keyword incl. namespace, matching edn->value

(defn- flit
  "Surface Float literal expr for `x`. The frontend has no negative Float literal, so emit
   negatives as `(sub Float 0.0 |x|)`."
  [x]
  (if (and (number? x) (neg? x)) (list 'sub 'Float 0.0 (double (- x))) x))

(defn- edn->value-form
  "Compile-time Clojure literal → a SURFACE `Value` constructor expr (for :enum / := literals).
   Mirrors `edn->value` but emits `(Value.vint 3)`-style forms instead of the runtime rep."
  [x]
  (cond
    (nil? x)        '(Value.vnil)
    (boolean? x)    (list 'Value.vbool x)
    (integer? x)    (list 'Value.vint x)
    (string? x)     (list 'Value.vstr x)
    (keyword? x)    (list 'Value.vkw (kw-str x))
    (double? x)     (list 'Value.vfloat (flit x))
    (map? x)        (list 'Value.vmap (reduce (fn [acc [k v]]
                                                (list 'Value.ventry (edn->value-form k)
                                                      (edn->value-form v) acc))
                                              '(Value.vnil) (reverse (seq x))))
    (set? x)        (list 'Value.vset (reduce (fn [acc e] (list 'Value.vcons (edn->value-form e) acc))
                                              '(Value.vnil) (reverse (seq x))))
    (sequential? x) (list 'Value.vvec (reduce (fn [acc e] (list 'Value.vcons (edn->value-form e) acc))
                                              '(Value.vnil) (reverse (seq x))))
    :else (throw (ex-info "edn->value-form: unsupported literal" {:x x}))))

(defn- parse-schema
  "Malli node → {:type :props :args}. `[type ?props & children]`, bare keyword/symbol, or a
   raw value (treated as a `:=` literal — malli allows literal schemas)."
  [node]
  (cond
    (keyword? node) {:type node :props nil :args []}
    (symbol? node)  {:type node :props nil :args []}
    (fn? node)      (if-let [s (fn->sym node)] {:type s :props nil :args []}
                            {:type :fn :props nil :args [node]})   ;; unknown fn → trusted leaf
    (and (vector? node) (or (keyword? (first node)) (symbol? (first node))))
    (let [[props args] (if (map? (second node)) [(second node) (drop 2 node)] [nil (rest node)])]
      {:type (first node) :props props :args (vec args)})
    :else {:type := :props nil :args [node]}))   ;; literal value schema

(def ^:private value-ctors
  [['vnil 0] ['vbool 1] ['vint 1] ['vstr 1] ['vkw 1] ['vcons 2] ['vvec 1] ['vmap 1] ['ventry 3]
   ['vfloat 1] ['vset 1]])

(defn- vmatch
  "A `(match disc Value Bool …)` returning `dflt` for every ctor except those in `overrides`
   (ctor-sym → tail: `(body)` for nullary, `([binders] body)` otherwise)."
  [disc dflt overrides]
  (list* 'match disc 'Value 'Bool
         (map (fn [[c ar]]
                (cons c (or (get overrides c)
                            (if (zero? ar) (list dflt)
                                (list (vec (repeatedly ar #(gensym "_g"))) dflt)))))
              value-ctors)))

(defn- and-chain [calls] (if (empty? calls) true  (reduce (fn [a c] (list 'Bool.and a c)) (first calls) (rest calls))))
(defn- or-chain  [calls] (if (empty? calls) false (reduce (fn [a c] (list 'Bool.or  a c)) (first calls) (rest calls))))

(defn- closed-checker-form
  "A fuel-recursive checker `nm : (c : Value) → Bool` — every entry key of chain `c` equals one
   of `key-forms` (the declared `(Value.vkw …)` keys). Empty key-forms → only vnil passes."
  [nm key-forms]
  (list 'ansatz.core/defn nm ['c :- 'Value] 'Bool
        :termination-by 'c
        (vmatch 'c false
                {'vnil   (list true)
                 'ventry (list ['k 'v 'rest]
                               (list 'Bool.and (or-chain (map (fn [ke] (list 'veq 'k ke)) key-forms))
                                     (list nm 'rest)))})))

(defn- tuple-chain
  "Nested fixed-depth match over the cons-chain `disc`: position i must satisfy `(nth preds i)`
   and the chain must end (vnil) exactly after the last. Empty preds → require vnil."
  [preds disc]
  (if (empty? preds)
    (vmatch disc false {'vnil (list true)})
    (let [h (gensym "h__") t (gensym "t__")]
      (vmatch disc false
              {'vcons (list [h t] (list 'Bool.and (list (first preds) h)
                                        (tuple-chain (rest preds) t)))}))))

(defn- mapof-checker-form
  "A fuel-recursive checker `nm : (c : Value) → Bool` — every entry of chain `c` has key ⊢
   kpred and value ⊢ vpred (vnil terminator → true)."
  [nm kpred vpred]
  (list 'ansatz.core/defn nm ['c :- 'Value] 'Bool
        :termination-by 'c
        (vmatch 'c false
                {'vnil   (list true)
                 'ventry (list ['k 'v 'rest]
                               (list 'Bool.and (list kpred 'k)
                                     (list 'Bool.and (list vpred 'v) (list nm 'rest))))})))

(defn- key-checker-form
  "A fuel-recursive checker `nm : (k m : Value) → Bool` — walk map `m`'s entry-chain; at the
   entry whose key = k, return `(sub-pred ev)`. `absent?` true → key may be absent (optional)."
  [nm sub-pred optional?]
  (let [d (if optional? true false)]
    (list 'ansatz.core/defn nm ['k :- 'Value 'm :- 'Value] 'Bool
          :termination-by 'm
          (vmatch 'm d {'vmap   (list ['en] (list nm 'k 'en))
                        'ventry (list ['ek 'ev 'rest]
                                      (list 'if (list 'vkeq 'k 'ek)
                                            (list sub-pred 'ev) (list nm 'k 'rest)))}))))

(defn- all-checker-form
  "A fuel-recursive checker `nm : (c : Value) → Bool` — every element of the cons-chain `c`
   satisfies `sub-pred` (vnil terminator → true)."
  [nm sub-pred]
  (list 'ansatz.core/defn nm ['c :- 'Value] 'Bool
        :termination-by 'c
        (vmatch 'c false {'vnil  (list true)
                          'vcons (list ['h 't] (list 'Bool.and (list sub-pred 'h) (list nm 't)))})))

(defn- vec-checker-form
  "A (non-recursive) checker `nm : (v : Value) → Bool` — v is a `vvec` whose elements all
   satisfy the cons-chain checker `all-name`."
  [nm all-name]
  (list 'ansatz.core/defn nm ['v :- 'Value] 'Bool
        (vmatch 'v false {'vvec (list ['it] (list all-name 'it))})))

(defn- set-checker-form
  "A (non-recursive) checker `nm : (v : Value) → Bool` — v is a `vset` whose elements all
   satisfy the cons-chain checker `all-name`."
  [nm all-name]
  (list 'ansatz.core/defn nm ['v :- 'Value] 'Bool
        (vmatch 'v false {'vset (list ['it] (list all-name 'it))})))

(declare compile-schema)

(defn- compile-field
  "[check forms] for one map field `[k (opts?) t]`. `check` is the boolean expr over `v`;
   `forms` are helper a/defns that must be defined first."
  [[k & more]]
  (let [opts      (when (map? (first more)) (first more))
        t         (if opts (second more) (first more))
        optional? (boolean (:optional opts))
        kexpr     (list 'Value.vkw (kw-str k))]
    (if (and (not optional?) (scalar-key-checker t))
      ;; required scalar field → reuse the hand-written key-<T>? (flat output stays identical)
      [(list (scalar-key-checker t) kexpr 'v) []]
      ;; otherwise compile the sub-schema's predicate and wrap it in a key-checker
      (let [[sub sub-forms] (compile-schema t)
            kc (gensym (if optional? "key_opt__" "key_req__"))]
        [(list kc kexpr 'v)
         (conj (vec sub-forms) (key-checker-form kc sub optional?))]))))

(defn- def-pred
  "A `[nm [form]]` pair defining `nm : Value → Bool` with `body` (over the param `v`),
   appended after `dep-forms`."
  [nm dep-forms body]
  [nm (conj (vec dep-forms) (list 'ansatz.core/defn nm ['v :- 'Value] 'Bool body))])

;; The verified `:re` leaf (#63). When the regex matcher is installed in the CURRENT env (ansatz.
;; regex/install! added `reMatchStr`), `[:re p]` compiles to `(and (vstr? target) <p matches>)`
;; via the kernel Brzozowski matcher — PRECISE (agrees with malli's `:re`). Otherwise it stays the
;; trusted-string leaf (`vstr?`, over-approximating). Gated on the ENV (not a global), so it is
;; properly test-isolated: a test that resets the env without installing regex gets `vstr?`.
(defn- re-leaf-fn []
  (when (env/lookup (a/env) (name/from-string "reMatchStr"))
    (resolve 'wandler.regex/re-conforms-leaf)))

;; ── inline (recursion) compiler ───────────────────────────────────────────────
;; For a SELF-recursive schema we cannot route refs through separate predicates (the kernel's
;; `:termination-by` is single-function), so we INLINE the schema body into one recursive
;; `Value → Bool` over `v`, where `[:ref ::self]` becomes `(fname subterm)` — and every such
;; call is on a MATCH-BOUND strict subterm, so `:termination-by v` (structural) accepts it.
;; The inlined target is always a bound variable (we descend only through match bindings), so
;; ranges/tuples can re-match it safely. Refs nested inside :vector/:map/:map-of need mutual
;; recursion (a follow-up) and are rejected here.
(defn- range-body
  "AND-chain of `{:min :max}` bounds applied to the scalar accessor expr `acc` (e.g. `i` or
   `(String.length s)`); `true` if unconstrained. A bound may be a literal or a surface expr."
  [props acc]
  (let [g (cond-> []
            (contains? props :min) (conj (list '<= (:min props) acc))
            (contains? props :max) (conj (list '<= acc (:max props))))]
    (if (seq g) (and-chain g) true)))

(defn- float-props
  "Float `{:min :max}` with negative bounds rewritten to surface exprs (no negative Float lit)."
  [props]
  (cond-> props (contains? props :min) (update :min flit) (contains? props :max) (update :max flit)))

(declare parse-schema)

(defn- compile-recursive
  "Compile a malli `:schema` recursive node — a local `registry` plus a top `[:ref ::name]` —
   into one `fname : Value → Bool` predicate. The kernel's `:termination-by` is single-function,
   so the WHOLE reference graph becomes one `rcheck : (mode : Nat) (v : Value) → Bool`: every
   registry entry and every collection/field iteration context gets an integer MODE; refs and
   iteration steps are `(rcheck m subterm)` (always a match-bound strict subterm of `v`, so
   structural `:termination-by v` accepts them). Non-iterating constructs are inlined on the
   current target. Supports (mutually) recursive maps/vectors/tuples/map-of/multi — trees, JSON."
  [registry top-ref fname]
  (let [rcheck     (gensym "rcheck__")
        modes      (atom [])                 ;; index = mode number, value = body expr over `v`
        name->mode (atom {})
        alloc!     (fn [] (let [m (count @modes)] (swap! modes conj nil) m))
        call       (fn [m target] (list rcheck m target))]
    (letfn [(gen-tuple [child-schemas disc]
              (if (empty? child-schemas)
                (vmatch disc false {'vnil (list true)})
                (let [h (gensym "h__") t (gensym "t__")]
                  (vmatch disc false
                          {'vcons (list [h t] (list 'Bool.and (gen (first child-schemas) h)
                                                    (gen-tuple (rest child-schemas) t)))}))))
            (gen [schema target]
              (let [{:keys [type props args]} (parse-schema schema)
                    leaf (when (and (empty? args) (nil? props)) (or (scalar-pred type) (predicate-pred type)))]
                (cond
                  (= type :ref)
                  (call (or (@name->mode (first args))
                            (throw (ex-info "recursion: unknown :ref" {:ref (first args)}))) target)
                  leaf                     (list leaf target)
                  (predicate-range type)   (vmatch target false {'vint (list ['i] (range-body (predicate-range type) 'i))})
                  (= type :int)            (vmatch target false {'vint (list ['i] (range-body props 'i))})
                  (and (= type :string) props) (vmatch target false {'vstr (list ['s] (range-body props (list 'String.length 's)))})
                  (and (#{:double :float} type) props) (vmatch target false {'vfloat (list ['f] (range-body (float-props props) 'f))})
                  (#{:and :or} type)       ((if (= type :and) and-chain or-chain) (map #(gen % target) args))
                  (= type :not)            (list 'Bool.not (gen (first args) target))
                  (= type :maybe)          (list 'Bool.or (list 'vnil? target) (gen (first args) target))
                  (= type :enum)           (or-chain (map (fn [lit] (list 'veq target (edn->value-form lit))) args))
                  (= type :=)              (list 'veq target (edn->value-form (first args)))
                  (= type :not=)           (list 'Bool.not (list 'veq target (edn->value-form (first args))))
                  (= type :fn)             (list 'vany? target)   ;; trusted leaf (gradual Any)
                  (= type :re)             (if-let [f (re-leaf-fn)]   ;; precise once regex installed
                                             (f (first args) target)
                                             (list 'vstr? target))    ;; else string verified, pattern trusted
                  (= type :tuple)          (vmatch target false {'vvec (list ['it] (gen-tuple args 'it))})

                  ;; iterating constructs — allocate a subterm-recursing mode
                  (#{:vector :sequential :set} type)
                  (let [h (alloc!) e (gensym "h__") t (gensym "t__")
                        gate (if (= type :set) 'vset 'vvec)]
                    (swap! modes assoc h
                           (vmatch 'v false {'vnil  (list true)
                                             'vcons (list [e t] (list 'Bool.and (gen (first args) e) (call h t)))}))
                    (vmatch target false {gate (list ['it] (call h 'it))}))

                  (= type :map-of)
                  (let [m (alloc!) k (gensym "k__") val (gensym "v__") r (gensym "r__")]
                    (swap! modes assoc m
                           (vmatch 'v false {'vnil   (list true)
                                             'ventry (list [k val r] (list 'Bool.and (gen (first args) k)
                                                                           (list 'Bool.and (gen (second args) val) (call m r))))}))
                    (vmatch target false {'vmap (list ['ee] (call m 'ee))}))

                  (= type :map)
                  (let [fmodes (mapv (fn [[fk & more]]
                                       (let [opts (when (map? (first more)) (first more))
                                             fs (if opts (second more) (first more))
                                             optional? (boolean (:optional opts))
                                             fm (alloc!) k (gensym "k__") val (gensym "v__") r (gensym "r__")]
                                         (swap! modes assoc fm
                                                (vmatch 'v (if optional? true false)
                                                        {'ventry (list [k val r]
                                                                       (list 'if (list 'veq k (list 'Value.vkw (kw-str fk)))
                                                                             (gen fs val) (call fm r)))}))
                                         fm))
                                     args)
                        cm (when (:closed props)
                             (let [c (alloc!) k (gensym "k__") val (gensym "v__") r (gensym "r__")
                                   keyfs (map (fn [e] (list 'Value.vkw (kw-str (first e)))) args)]
                               (swap! modes assoc c
                                      (vmatch 'v false {'vnil   (list true)
                                                        'ventry (list [k val r] (list 'Bool.and (or-chain (map (fn [ke] (list 'veq k ke)) keyfs)) (call c r)))}))
                               c))
                        e (gensym "e__")
                        checks (cond-> (mapv #(call % e) fmodes) cm (conj (call cm e)))]
                    (vmatch target false {'vmap (list [e] (and-chain checks))}))

                  (= type :multi)
                  (let [dispatch (:dispatch props)
                        _ (when-not (keyword? dispatch)
                            (throw (ex-info "multi: only keyword :dispatch supported" {:dispatch dispatch})))
                        dexpr (list 'vget (list 'Value.vkw (kw-str dispatch)) target)
                        parsed (map (fn [[dval & more]] {:dval dval :bs (if (map? (first more)) (second more) (first more))}) args)
                        default (some #(when (= :malli.core/default (:dval %)) %) parsed)
                        regular (remove #(= :malli.core/default (:dval %)) parsed)
                        els (if default (gen (:bs default) target) false)]
                    (reduce (fn [e {:keys [dval bs]}]
                              (list 'if (list 'veq dexpr (edn->value-form dval)) (gen bs target) e))
                            els (reverse regular)))

                  :else (throw (ex-info "recursion: unsupported schema" {:schema schema :type type})))))]
      ;; pre-assign a mode to each registry entry, then generate their bodies (which allocate
      ;; further helper modes), then build the if-chain dispatch.
      (doseq [[rn _] registry] (swap! name->mode assoc rn (alloc!)))
      (doseq [[rn rs] registry] (swap! modes assoc (@name->mode rn) (gen rs 'v)))
      (let [topmode (or (@name->mode (second top-ref))
                        (throw (ex-info "recursion: top ref names no registry entry" {:top top-ref})))
            dispatch (reduce (fn [els i] (list 'if (list '== 'mode i) (nth @modes i) els))
                             false (reverse (range (count @modes))))]
        [fname [(list 'ansatz.core/defn rcheck ['mode :- 'Nat 'v :- 'Value] 'Bool
                      :termination-by 'v dispatch)
                (list 'ansatz.core/defn fname ['v :- 'Value] 'Bool (list rcheck topmode 'v))]]))))

(defn- compile-schema
  "[pred-sym forms] : a kernel `Value → Bool` predicate for malli `schema`, plus helper a/defn
   forms in dependency order. `top-name` (optional) names the outermost generated predicate.
   Covers: scalar keyword/predicate-symbol schemas; `:and`/`:or`/`:not`/`:maybe`; `:enum`/`:=`/
   `:not=` (via structural `veq`); `:int`/`:string` ranges (`{:min :max}`); `:map` (nested,
   optional fields); `:vector`/`:sequential`. Unsupported nodes throw."
  ([schema] (compile-schema schema nil))
  ([schema top-name]
   (let [{:keys [type props args]} (parse-schema schema)
         nm! (fn [p] (or top-name (gensym p)))
         leaf (when (and (empty? args) (nil? props))
                (or (scalar-pred type) (predicate-pred type)))]
     (cond
       ;; scalar keyword / predicate-symbol leaf → reuse a built-in (caller aliases if top)
       leaf [leaf []]

       ;; predicate symbols that imply an int range (pos-int? / nat-int? / neg-int?)
       (predicate-range type)
       (def-pred (nm! "rng__") [] (vmatch 'v false {'vint (list ['i] (range-body (predicate-range type) 'i))}))

       ;; :int (with range props) — bare :int handled by `leaf`
       (= :int type)
       (def-pred (nm! "rng__") [] (vmatch 'v false {'vint (list ['i] (range-body props 'i))}))

       ;; :string with length props — bare :string handled by `leaf`
       (and (= :string type) props)
       (def-pred (nm! "slen__") [] (vmatch 'v false {'vstr (list ['s] (range-body props (list 'String.length 's)))}))

       ;; :double/:float with range props — bare handled by `leaf`
       (and (#{:double :float} type) props)
       (def-pred (nm! "frng__") [] (vmatch 'v false {'vfloat (list ['f] (range-body (float-props props) 'f))}))

       (#{:and :or} type)
       (let [compiled (mapv compile-schema args)
             calls    (map (fn [[p _]] (list p 'v)) compiled)
             op       (if (= :and type) 'and 'or)]
         (def-pred (nm! (str (name type) "__")) (mapcat second compiled)
           (reduce (fn [a c] (list op a c)) (first calls) (rest calls))))

       (= :not type)
       (let [[p f] (compile-schema (first args))]
         (def-pred (nm! "not__") f (list 'Bool.not (list p 'v))))

       (= :maybe type)
       (let [[p f] (compile-schema (first args))]
         (def-pred (nm! "maybe__") f (list 'Bool.or (list 'vnil? 'v) (list p 'v))))

       (= :enum type)
       (def-pred (nm! "enum__") []
         (let [calls (map (fn [lit] (list 'veq 'v (edn->value-form lit))) args)]
           (reduce (fn [a c] (list 'Bool.or a c)) (first calls) (rest calls))))

       (= := type)    (def-pred (nm! "eq__")  [] (list 'veq 'v (edn->value-form (first args))))
       (= :not= type) (def-pred (nm! "neq__") [] (list 'Bool.not (list 'veq 'v (edn->value-form (first args)))))

       ;; :fn — an arbitrary host predicate can't be reflected into the kernel. Compile to a
       ;; TRUSTED leaf (gradual-typing `Any`): always-true, UNVERIFIED at this node, so conforms
       ;; OVER-approximates malli here (accepts ⊇). Use sparingly; the structural part stays proven.
       (= :fn type)   ['vany? []]
       ;; :re — PRECISE once wandler.regex/install! has run (the kernel Brzozowski matcher checks the
       ;; pattern); otherwise the trusted-string leaf (`vstr?`, over-approximating). See *re-leaf-fn*.
       (= :re type)   (if-let [f (re-leaf-fn)]
                        (def-pred (nm! "re__") [] (f (first args) 'v))
                        ['vstr? []])

       (= :map type)
       (let [per     (mapv compile-field args)
             forms   (vec (mapcat second per))
             nm      (nm! "conforms__")
             base    (reduce (fn [acc [check _]] (list 'Bool.and acc check)) (list 'vmap? 'v) per)
             closed? (:closed props)
             only-go (when closed? (gensym "onlykeys_go__"))
             keyfs   (when closed? (map (fn [e] (list 'Value.vkw (kw-str (first e)))) args))
             forms   (if closed? (conj forms (closed-checker-form only-go keyfs)) forms)
             body    (if closed?
                       (list 'Bool.and base (vmatch 'v false {'vmap (list ['e] (list only-go 'e))}))
                       base)]
         [nm (conj forms (list 'ansatz.core/defn nm ['v :- 'Value] 'Bool body))])

       ;; tagged union: dispatch a KEYWORD key, route to the matching branch schema
       (= :multi type)
       (let [dispatch (:dispatch props)
             _ (when-not (keyword? dispatch)
                 (throw (ex-info "multi: only keyword :dispatch supported" {:dispatch dispatch})))
             dexpr (list 'vget (list 'Value.vkw (kw-str dispatch)) 'v)
             parsed (mapv (fn [[dval & more]]
                            (let [bschema (if (map? (first more)) (second more) (first more))
                                  [bp bf] (compile-schema bschema)]
                              {:dval dval :pred bp :forms bf}))
                          args)
             default (some #(when (= :malli.core/default (:dval %)) %) parsed)
             regular (remove #(= :malli.core/default (:dval %)) parsed)
             else    (if default (list (:pred default) 'v) false)
             body    (reduce (fn [e {:keys [dval pred]}]
                               (list 'if (list 'veq dexpr (edn->value-form dval)) (list pred 'v) e))
                             else (reverse regular))]
         (def-pred (nm! "multi__") (mapcat :forms parsed) body))

       (#{:vector :sequential :set} type)
       (let [[sub sub-forms] (compile-schema (first args))
             allf (gensym "all__")
             gatef (nm! (if (= :set type) "set__" "vec__"))
             gate-form (if (= :set type) set-checker-form vec-checker-form)]
         [gatef (into (vec sub-forms) [(all-checker-form allf sub) (gate-form gatef allf)])])

       ;; fixed-length positional vector
       (= :tuple type)
       (let [compiled (mapv compile-schema args)]
         (def-pred (nm! "tuple__") (mapcat second compiled)
           (vmatch 'v false {'vvec (list ['it] (tuple-chain (mapv first compiled) 'it))})))

       ;; homogeneous map: every key ⊢ k-schema, every value ⊢ v-schema
       (= :map-of type)
       (let [[kp kf] (compile-schema (first args))
             [vp vf] (compile-schema (second args))
             go (gensym "mapof_go__")
             nm (nm! "mapof__")]
         [nm (into (vec (concat kf vf))
                   [(mapof-checker-form go kp vp)
                    (list 'ansatz.core/defn nm ['v :- 'Value] 'Bool
                          (vmatch 'v false {'vmap (list ['e] (list go 'e))}))])])

       ;; recursive schema: a local registry + a top `[:ref ::name]`. Compiled by mode
       ;; defunctionalization (handles (mutually) recursive maps/vectors/tuples/map-of — JSON/trees).
       (= :schema type)
       (let [registry (:registry props)
             top      (first args)]
         (when-not (map? registry)
           (throw (ex-info "recursion: :schema needs a :registry" {:props props})))
         (when-not (and (vector? top) (= :ref (first top)))
           (throw (ex-info "recursion: top must be [:ref ::name]" {:top top})))
         (compile-recursive registry top (nm! "rconf__")))

       :else (throw (ex-info "unsupported schema (compile-schema)" {:schema schema :type type}))))))

(defn schema->conforms-forms
  "Compile any supported malli `schema` into the ordered vector of `a/defn` forms defining
   `fn-name : Value → Bool` (the last form) plus any helpers. Each form kernel-verifies AND
   runs on `edn->value`-encoded data. A schema that compiles to a bare built-in predicate
   (e.g. `:int`) gets a thin `fn-name` alias so the public name always exists."
  [fn-name schema]
  (let [[pred forms] (compile-schema schema fn-name)]
    (if (= pred fn-name)
      forms
      (conj (vec forms)
            (list 'ansatz.core/defn fn-name ['v :- 'Value] 'Bool (list pred 'v))))))

(defn schema->conforms-form
  "Compile a FLAT scalar-field `:map` schema to the single `a/defn` form for `fn-name`
   (`λ v. (vmap? v) ∧ ⋀ (key-<T>? :k v)`). Errors if the schema needs helpers — use
   `schema->conforms-forms` for nested/vector/optional schemas."
  [fn-name schema]
  (let [forms (schema->conforms-forms fn-name schema)]
    (assert (= 1 (count forms))
            "schema->conforms-form: schema needs helpers; use schema->conforms-forms")
    (first forms)))

(defn install-conforms!
  "Define `fn-name : Value → Bool` (and any helpers) for malli `schema` on the current env.
   Returns `fn-name`. The predicate is kernel-verified by `a/defn` and runnable on Values."
  [fn-name schema]
  (binding [a/*verbose* false]
    (doseq [form (schema->conforms-forms fn-name schema)]
      (eval form)))
  fn-name)

(def ^:private u1 (lvl/succ lvl/zero))

(defn schema->value-type
  "Framing B — the TOTAL malli→type functor: F(schema) = `Subtype Value (λ v. conforms v = true)`,
   the refinement of the universal `Value` universe carved by the schema's conformance predicate.
   Installs the conformance fn γ:Value→Bool under `conforms-name` (install-conforms!), then returns
   the kernel TYPE as an Expr. Total over EVERY malli schema form — including :or/:enum/recursive that
   the precise lane (ansatz.malli/schema->type-expr) cannot type. This is the one functor that unifies
   records/refine/edn/conforms: an untagged malli union is set-union over the value universe (semantic
   subtyping), modelled faithfully as a disjunctive conformance predicate — NOT a tagged Sum."
  [conforms-name schema]
  (install-conforms! conforms-name schema)
  (let [val   (e/const' (name/from-string "Value") [])
        bool  (e/const' (name/from-string "Bool") [])
        btrue (e/const' (name/from-string "Bool.true") [])
        conf  (e/const' (name/from-string (str conforms-name)) [])
        ;; under binder v (bvar 0):  Eq Bool (conforms v) Bool.true  : Prop
        body  (e/app* (e/const' (name/from-string "Eq") [u1]) bool
                      (e/app conf (e/bvar 0)) btrue)
        pred  (e/lam "v" val body :default)]
    (e/app* (e/const' (name/from-string "Subtype") [u1]) val pred)))

