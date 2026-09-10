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

(ns ansatz.surface.data
  "The DATA leg of ansatz's Clojure↔kernel bridge (sibling of the code leg in ansatz.surface.*): the
   universal `Value`/EDN universe — one inductive carrying every Clojure value (nil/bool/int/str/kw/
   list/vec/map/set/float) + structural ops + the edn->value/value->edn runtime boundary + the
   native-Clojure-over-Value surface (`:k`/`get`/`int?`/`==`/`count`/`assoc` over dynamic data). The
   schema leg (malli→type/conformance) is ansatz.surface.schema. Opt-in: install-core! (Value type/ops)
   + install-surface! (the native verbs), against an Init env."
  (:require [ansatz.core :as a]
            [clojure.java.io :as io]
            [ansatz.surface.api :as api]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as env]))

(defn- head-name
  "Head constant name of a kernel type/term expr (\"Int\" for `Int`, \"List\" for `(List Nat)`), or nil."
  [t]
  (let [[h _] (when t (e/get-app-fn-args t))]
    (when (and h (e/const? h)) (name/->string (e/const-name h)))))

(defn- kw-str [k] (subs (str k) 1))   ;; full keyword incl. namespace, matching edn->value

(def ^:private core-forms
  ;; Read from a resource, not written as a literal here: a quoted literal this size compiles
  ;; (under AOT) into a class initializer over the JVM's 64 KB method limit. Same forms, same
  ;; order; the file is data, so `*read-eval*` is off.
  (binding [*read-eval* false]
    (read-string (slurp (io/resource "ansatz/surface/core-forms.edn")))))

(defn install-core!
  "Define the `Value` type and core ops/laws on the current `ansatz.core` env.
   Requires the env to already contain Lean `Init`. Returns the updated env."
  []
  (binding [a/*verbose* false]
    (doseq [form core-forms]
      (eval form)))
  (a/env))

;; ── runtime EDN ↔ Value boundary (#59) ────────────────────────────────────────
;; The runtime representation of `Value` is the general TAGGED inductive rep produced by
;; ansatz.core's codegen: `[cidx field…]`, ctor index first. These mirror that encoding so
;; the kernel-verified conformance predicates / `vget` / `vassoc` RUN on real Clojure data —
;; and can be differential-tested against malli (`m/validate`) and Clojure `get`.
;;
;;   0 vnil · 1 vbool b · 2 vint i · 3 vstr s · 4 vkw s
;;   5 vcons h t · 6 vvec items · 7 vmap entries · 8 ventry k v rest
;;
;; Maps/vectors are entry/cons chains terminated by vnil; map keys keep insertion order, and
;; first occurrence shadows (matching `vassoc` prepend semantics).

(defn edn->value
  "Encode a Clojure EDN value into the runtime `Value` tagged rep."
  [x]
  (cond
    (nil? x)        [0]
    (boolean? x)    [1 x]
    (integer? x)    [2 (long x)]
    (string? x)     [3 x]
    ;; keep the FULL keyword (namespace included): (subs (str :a/b) 1) = "a/b". `value->edn`
    ;; round-trips via (keyword "a/b") = :a/b; (name :a/b) would drop the namespace.
    (keyword? x)    [4 (subs (str x) 1)]
    (double? x)     [9 x]
    (map? x)        [7 (reduce (fn [acc [k v]] [8 (edn->value k) (edn->value v) acc])
                               [0] (reverse (seq x)))]
    (set? x)        [10 (reduce (fn [acc e] [5 (edn->value e) acc])
                                [0] (reverse (seq x)))]
    (sequential? x) [6 (reduce (fn [acc e] [5 (edn->value e) acc])
                               [0] (reverse (seq x)))]
    :else (throw (ex-info "edn->value: unsupported EDN" {:x x :class (class x)}))))

(declare value->edn)

(defn- vchain->seq [c]
  (loop [c c, acc []]
    (case (long (nth c 0))
      0 acc
      5 (recur (nth c 2) (conj acc (value->edn (nth c 1))))
      (throw (ex-info "value->edn: malformed cons chain" {:c c})))))

(defn- ventries->map [c]
  (loop [c c, acc {}]
    (case (long (nth c 0))
      0 acc
      8 (let [k (value->edn (nth c 1)), v (value->edn (nth c 2))]
          ;; head shadows: keep the first occurrence of a key
          (recur (nth c 3) (if (contains? acc k) acc (assoc acc k v))))
      (throw (ex-info "value->edn: malformed entry chain" {:c c})))))

(defn value->edn
  "Decode a runtime `Value` tagged rep back into a Clojure EDN value (inverse of edn->value
   on the canonical encoding; map keys keep first-occurrence/shadowing semantics)."
  [v]
  (case (long (nth v 0))
    0 nil
    1 (nth v 1)
    2 (nth v 1)
    3 (nth v 1)
    4 (keyword (nth v 1))
    5 (vchain->seq v)
    6 (vchain->seq (nth v 1))
    7 (ventries->map (nth v 1))
    8 (throw (ex-info "value->edn: bare ventry has no EDN form" {:v v}))
    9 (nth v 1)
    10 (set (vchain->seq (nth v 1)))))

;; ── typed bridge: dynamic Value ↔ typed record (#62) ──────────────────────────
;; Commit to a malli schema → a `def-record` typed structure (O(1) field projection at
;; runtime, vs vget's O(chain) walk) + the richer relational algebra. `conforms` (#57) is the
;; OPTIONAL boundary that upgrades a dynamic Value to the typed record (gradual: the caller
;; chooses whether to check; not forced). These are the runtime coercions across that boundary.

(defn value->record
  "Upgrade a conforming EDN `Value` (a vmap) to a typed defrecord via its `map->X` factory. After
   this, field access is an O(1) struct projection (not vget's chain walk) and the typed
   relational laws apply. The boundary conforms-check is the caller's choice — see [[malli-value-refinement]]."
  [map->factory v]
  (map->factory (value->edn v)))

(defn record->value
  "Demote a typed defrecord back to a dynamic EDN `Value` (for serialization / the dynamic path)."
  [r]
  (edn->value (into {} r)))

;; ── native-Clojure-over-Value surface (#60) ───────────────────────────────────
;; So existing Clojure code is portable onto dynamic EDN `Value`: native ops lower onto the
;; `v*` primitives when the operand is a `Value`. Keyword access `(:k v)` is handled in
;; ansatz.core; the symbol-headed ops below register elaborators (no core change).

(defn- value-typed? [est ex] (= "Value" (head-name (api/arg-type est ex))))

(defn- const0 [s] (e/const' (name/from-string s) []))

(defn- vkey-expr
  "Surface key as a `Value`: a keyword literal → `(Value.vkw \"k\")`; else assume it already
   elaborates to a Value."
  [est kform]
  (if (keyword? kform)
    (e/app (const0 "Value.vkw") (e/lit-str (kw-str kform)))
    (api/elab est kform)))

(def ^:private surface-preds
  "Clojure predicate symbol → the kernel Value predicate it lowers to (when the operand is a Value)."
  {'int? "vint?" 'integer? "vint?" 'string? "vstr?" 'boolean? "vbool?" 'keyword? "vkw?"
   'nil? "vnil?" 'map? "vmap?" 'vector? "vvec?" 'set? "vset?" 'double? "vfloat?" 'float? "vfloat?"
   'some? "vsome?" 'any? "vany?"})

;; For a NON-Value operand, fall back to core's normal handling (so e.g. `(some? opt)` over an
;; Option still becomes Option.isSome, and unknown predicates error exactly as before). This is
;; what keeps these global registrations side-effect-free for non-EDN code.
(defn- vpred-elaborator [sym vpred]
  (fn [est args]
    (let [v (api/elab est (first args))]
      (if (value-typed? est v)
        (e/app (const0 vpred) v)
        (throw (ex-info (str "`" sym "` is only supported over a dynamic EDN Value in a "
                             "verified body (operand type is not Value)") {:pred sym}))))))

(declare to-value-operand)

(defn- get-elaborator
  "`(get v k)` over a Value → `(vget (Value.vkw k) v)`; `(get v k default)` → `(vgetD … d)`
   (the default returned when the key is absent — nil = vnil over the Value universe).
   Other receivers fall back to core's keyword-projection sugar (get r :k ≡ (:k r))."
  [est args]
  (let [v (api/elab est (first args))]
    (if (value-typed? est v)
      (if (= 3 (count args))
        (e/app* (const0 "vgetD") (vkey-expr est (second args)) v
                (to-value-operand est (api/elab est (nth args 2))))
        (e/app* (const0 "vget") (vkey-expr est (second args)) v))
      (api/elab est (list (second args) (first args))))))

(defn- to-int-operand
  "Coerce a comparison operand to `Int`: a Value via vint-val (0 off-int), a Nat via
   Int.ofNat, an Int as-is; default assumes Value."
  [est x]
  (case (head-name (api/arg-type est x))
    "Nat"   (e/app (const0 "Int.ofNat") x)
    "Int"   x
    (e/app (const0 "vint-val") x)))

(defn- to-value-operand
  "Coerce a comparison operand to `Value` (for structural veq): a literal wraps in its
   Value ctor, a Value stays."
  [est x]
  (case (head-name (api/arg-type est x))
    "Value"  x
    "String" (e/app (const0 "Value.vstr") x)
    "Nat"    (e/app (const0 "Value.vint") (e/app (const0 "Int.ofNat") x))
    "Int"    (e/app (const0 "Value.vint") x)
    "Bool"   (e/app (const0 "Value.vbool") x)
    x))

(defn- value-cmp-handler
  "Type-directed comparison over a dynamic-EDN Value (registered via the comparison seam):
   `<`/`<=` compare the int payloads (Int via vint-val), `==` is structural veq with the
   other operand coerced to a Value."
  [est rel a0 b0]
  (case rel
    (:lt :le) (let [ai (to-int-operand est a0) bi (to-int-operand est b0)
                    propc (if (= rel :lt) "Int.lt" "Int.le")
                    decc  (if (= rel :lt) "Int.decLt" "Int.decLe")]
                (e/app* (const0 "Decidable.decide")
                        (e/app* (const0 propc) ai bi)
                        (e/app* (const0 decc) ai bi)))
    :eq (e/app* (const0 "veq") (to-value-operand est a0) (to-value-operand est b0))))

(defn install-surface!
  "Register native-Clojure-over-Value surface elaborators (get / int?/map?/string?/… +
   keyword access `(:k v)` via the type-directed keyword-access seam). Idempotent;
   safe to call after `install-core!`."
  []
  (a/register-term-elaborator! 'get get-elaborator)
  ;; (:k v) over a Value receiver → (vget (Value.vkw "k") v) — full keyword incl. namespace,
  ;; matching edn->value's key encoding. Registered structures keep native projection;
  ;; this only fires for Value-typed receivers (the seam dispatches on the type head).
  (api/register-keyword-access! "Value"
                                (fn [_est kw v-expr]
                                  (e/app* (const0 "vget") (e/app (const0 "Value.vkw") (e/lit-str (kw-str kw))) v-expr)))
  (api/register-comparison! "Value" value-cmp-handler)
  ;; (when c x) over a Value body → (if c x (Value.vnil)) — nil = vnil. Intercepted as a
  ;; term elaborator (before macroexpansion to a 3-elem if) so the absence is typed vnil.
  (a/register-term-elaborator! 'when
                               (fn [est args]
                                 (let [x (api/elab est (second args))]
                                   (if (value-typed? est x)
                                     (api/elab est (list 'if (first args) (second args) '(Value.vnil)))
                                     (throw (ex-info "when in a verified body is supported over a dynamic EDN Value body (nil = vnil)"
                                                     {:kind :when-nonvalue}))))))
  ;; (keep f xs) over Value elements → map then drop vnil: (filterv vsome? (mapv f xs)).
  (a/register-term-elaborator! 'keep
                               (fn [est args]
                                 (api/elab est (list 'filterv '(fn [v] (vsome? v)) (list 'mapv (first args) (second args))))))
  ;; map verbs over a dynamic EDN Value: contains?/keys/vals/dissoc/merge lower to the v* ops;
  ;; update/get-in compose existing ops at the surface (no new kernel op).
  (letfn [(value-verb! [sym f]
            (a/register-term-elaborator! sym
                                         (fn [est args]
                                           (let [m (api/elab est (first args))]
                                             (if (value-typed? est m)
                                               (f est m args)
                                               (throw (ex-info (str "`" sym "` in a verified body is supported over a dynamic EDN Value")
                                                               {:verb sym})))))))]
    (value-verb! 'contains? (fn [est m args] (e/app* (const0 "vcontains?") (vkey-expr est (second args)) m)))
    (value-verb! 'keys      (fn [_est m _args] (e/app (const0 "vkeys") m)))
    (value-verb! 'vals      (fn [_est m _args] (e/app (const0 "vvals") m)))
    (value-verb! 'dissoc    (fn [est m args] (e/app* (const0 "vdissoc") (vkey-expr est (second args)) m)))
    (value-verb! 'merge     (fn [est m args] (e/app* (const0 "vmerge") m (api/elab est (second args)))))
    ;; (update m k f) → (vput m k (f (vget k m)))
    (value-verb! 'update    (fn [est m args]
                              (let [kexpr (vkey-expr est (second args))]
                                (e/app* (const0 "vput") m kexpr
                                        (e/app (api/elab est (nth args 2)) (e/app* (const0 "vget") kexpr m))))))
    ;; (get-in m [k1 k2 …]) → nested vget over a literal key path
    (value-verb! 'get-in    (fn [est m args]
                              (let [path (second args)]
                                (if (vector? path)
                                  (reduce (fn [acc k] (e/app* (const0 "vget") (vkey-expr est k) acc)) m path)
                                  (throw (ex-info "get-in needs a literal key vector over a Value" {:verb 'get-in})))))))
  (doseq [[sym vpred] surface-preds]
    (a/register-term-elaborator! sym (vpred-elaborator sym vpred)))
  :installed)
