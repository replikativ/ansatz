(ns ansatz.codegen.native
  "Native runtime representations of Lean's Init types and the `@[extern]` lowerings over them.

   Lean's compiler represents some Init structures natively (Compiler/LCNF/MonoTypes.lean
   hasTrivialStructure?, plus the runtime builtin types) and implements their primitive
   operations in C. Generic codegen builds structures as vectors and reads fields with `nth`,
   which is wrong for a native value: it must never look inside one. Every constructor,
   projection and recursor field of a native type therefore goes through `native-structures`,
   the representation boundary. The implementations live in ansatz.codegen.lean-runtime.

   `extern-lowerings` are the native fast paths. Each entry follows Lean's calling convention:
   `erased` leading type arguments, then `arity` runtime arguments (proof arguments are passed
   as nil and ignored). An extern absent from this table compiles from its Lean body, which then
   reaches native values only through the boundary."
  (:require [ansatz.codegen.lean-runtime]
            [ansatz.codegen.types :as types]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.surface.ingest :refer [structure-registry codegen-registry]])
  (:import [ansatz.kernel ConstantInfo]))

(def ^:private rt "ansatz.codegen.lean-runtime")
(defn- rt-sym [n] (symbol rt (name n)))

(defn- identity-structure
  "A structure represented by its single relevant field (Lean hasTrivialStructure?):
   `relevant` is that field's index; the others are proofs, represented by nil."
  [relevant]
  {:ctor (fn [fields] (nth fields relevant))
   :field (fn [i x] (when (= i relevant) x))})

(def native-structures
  "Lean's runtime builtin types (Compiler/LCNF/Util.lean builtinRuntimeTypes) that are
   structures: inductive name → {:ctor (fn [field-forms] form) :field (fn [index form] form)}.
   Other structures follow `trivial-structure-field`."
  (merge
   {"ByteArray" (identity-structure 0)
    "String" {:ctor (fn [[bytes _]] (list (rt-sym 'utf8->string) bytes))
              :field (fn [i x] (when (zero? i) (list (rt-sym 'string->utf8) x)))}
    "Array" {:ctor (fn [[xs]] (list (rt-sym 'array-of-list) xs))
             :field (fn [_ x] (list (rt-sym 'array-to-list) x))}}
   (into {} (for [t ["UInt8" "UInt16" "UInt32" "UInt64" "USize"]]
              [t (identity-structure 0)]))))

;; ConstantInfo of the constructor → field index or ::none. Keyed by the ConstantInfo itself:
;; a name may be redefined in a different environment.
(def ^:private trivial-cache (java.util.Collections/synchronizedMap (java.util.WeakHashMap.)))

(defn- compute-trivial-field [env ^ConstantInfo ind]
  ;; Lean Compiler/LCNF/Irrelevant.lean computeHasTrivialStructure? (v4.33.1): not unsafe,
  ;; not recursive, one constructor, exactly one field that is neither a proof nor a type
  ;; (getRelevantCtorFields? with isProp ∨ isTypeFormerType).
  (when (and (not (.isUnsafe ind)) (not (.isRec ind)) (= 1 (alength (.ctors ind)))
             ;; a proposition's values are erased already (Lean: ctorType.isErased)
             (not (let [r (loop [t (.type ind)] (if (e/forall? t) (recur (e/forall-body t)) t))]
                    (and (e/sort? r) (ansatz.kernel.Level/isZero (e/sort-level r))))))
    (let [^ConstantInfo ctor (env/lookup env (aget (.ctors ind) 0))
          relevant (loop [t (.type ctor) i 0 ctx [] acc []]
                     (if (e/forall? t)
                       (recur (e/forall-body t) (inc i)
                              (types/bind-type ctx (str "x" i) (e/forall-type t))
                              (if (< i (.numParams ctor))
                                acc
                                (conj acc (not (types/irrelevant-type? env (e/forall-type t) ctx)))))
                       acc))]
      (when (= 1 (count (filter true? relevant)))
        (first (keep-indexed (fn [i r] (when r i)) relevant))))))

(defn trivial-structure-field
  "Lean hasTrivialStructure?: the index of the only relevant field of a one-constructor,
   non-recursive inductive, which is then represented by that field alone. Excludes types
   whose representation was chosen explicitly: registered records (`a/structure`, malli
   `[:map …]`) and constructors with a codegen-registry lowering."
  [env ^String ind-name]
  (when-not (or (contains? native-structures ind-name) (contains? @structure-registry ind-name))
    (when-let [^ConstantInfo ind (env/lookup env (name/from-string ind-name))]
      (when (and (.isInduct ind) (= 1 (alength (.ctors ind)))
                 (not (contains? @codegen-registry (name/->string (aget (.ctors ind) 0)))))
        (let [ctor (env/lookup env (aget (.ctors ind) 0))
              hit (.get trivial-cache ctor)
              v (if (some? hit) hit
                    (let [v (or (compute-trivial-field env ind) ::none)]
                      (.put trivial-cache ctor v)
                      v))]
          (when-not (= ::none v) v))))))

(defn native-structure
  "The representation of a structure-like type when it is not a vector: a runtime builtin
   type, or a trivial structure (its one relevant field). nil for the generic representation."
  ([type-name] (get native-structures type-name))
  ([env type-name]
   (or (get native-structures type-name)
       (when-let [i (trivial-structure-field env type-name)]
         (identity-structure i)))))

;; ── extern table ──────────────────────────────────────────────────────────────────────────────

(defn- entry [erased arity emit] {:erased erased :arity arity :emit emit})
(defn- call [f & fixed] (fn [& args] (apply list (rt-sym f) (concat fixed args))))
(defn- decision [op] (fn [a b] (list (rt-sym 'decide) (list op a b))))

(def ^:private uint-widths
  {"UInt8" 8 "UInt16" 16 "UInt32" 32 "UInt64" 64 "USize" 64})

(defn- uint-entries [t bits]
  (let [binop (fn [f] (entry 0 2 (call f bits)))]
    (merge
     {(str t ".ofNat") (entry 0 1 (call 'uint-of-nat bits))
      (str t ".ofNatLT") (entry 0 2 (fn [n _] n))
      (str t ".ofBitVec") (entry 0 1 identity)
      (str t ".toBitVec") (entry 0 1 identity)
      (str t ".toNat") (entry 0 1 identity)
      (str t ".add") (binop 'uint-add)
      (str t ".sub") (binop 'uint-sub)
      (str t ".mul") (binop 'uint-mul)
      (str t ".div") (binop 'uint-div)
      (str t ".mod") (binop 'uint-mod)
      (str t ".land") (binop 'uint-land)
      (str t ".lor") (binop 'uint-lor)
      (str t ".xor") (binop 'uint-xor)
      (str t ".shiftLeft") (binop 'uint-shift-left)
      (str t ".shiftRight") (binop 'uint-shift-right)
      (str t ".neg") (entry 0 1 (call 'uint-neg bits))
      (str t ".complement") (entry 0 1 (call 'uint-complement bits))
      (str t ".decEq") (entry 0 2 (decision 'clojure.core/==))
      (str t ".decLt") (entry 0 2 (decision 'clojure.core/<))
      (str t ".decLe") (entry 0 2 (decision 'clojure.core/<=))}
     ;; Widening is the identity on values; narrowing truncates (lean_uintN_to_uintM).
     (into {} (for [[t2 bits2] uint-widths
                    :when (not= t t2)
                    :let [suffix (if (= t2 "USize") "USize" t2)]]
                [(str t ".to" suffix)
                 (entry 0 1 (if (>= bits2 bits) identity (call 'uint-of-nat bits2)))])))))

(def extern-lowerings
  "Lean extern name → {:erased :arity :emit (fn [& runtime-arg-forms] form)}."
  (merge
   {"Nat.land" (entry 0 2 (call 'nat-land))
    "Nat.lor" (entry 0 2 (call 'nat-lor))
    "Nat.xor" (entry 0 2 (call 'nat-xor))
    "Nat.shiftLeft" (entry 0 2 (call 'nat-shift-left))
    "Nat.shiftRight" (entry 0 2 (call 'nat-shift-right))
    "Nat.gcd" (entry 0 2 (call 'nat-gcd))
    "Nat.pred" (entry 0 1 (call 'nat-pred))
    "Nat.modCore" (entry 0 2 (fn [a b] (list 'ansatz.codegen.numeric/tmod a b)))
    "Int.decNonneg" (entry 0 1 (fn [m] (list (rt-sym 'decide) (list 'clojure.core/>= m 0))))
    "System.Platform.getNumBits" (entry 0 1 (fn [_] 64))
    "mixHash" (entry 0 2 (call 'mix-hash))

    "Char.ofNatAux" (entry 0 2 (fn [n _] n))

    "String.ofList" (entry 0 1 (call 'string-of-list))
    "String.toList" (entry 0 1 (call 'string-to-list))
    "String.toByteArray" (entry 0 1 (call 'string->utf8))
    "String.ofByteArray" (entry 0 2 (fn [bs _] (list (rt-sym 'utf8->string) bs)))
    "String.append" (entry 0 2 (call 'string-append))
    "String.Internal.append" (entry 0 2 (call 'string-append))
    "String.length" (entry 0 1 (call 'string-length))
    "String.Internal.length" (entry 0 1 (call 'string-length))
    "String.utf8ByteSize" (entry 0 1 (call 'utf8-byte-size))
    "String.decidableLT" (entry 0 2 (fn [a b] (list (rt-sym 'decide) (list (rt-sym 'string-lt) a b))))
    "String.hash" (entry 0 1 (call 'string-hash))
    "USize.repr" (entry 0 1 (fn [n] (list 'clojure.core/str n)))

    "Array.mk" (entry 1 1 (call 'array-of-list))
    "Array.toList" (entry 1 1 (call 'array-to-list))
    "Array.size" (entry 1 1 (fn [a] (list 'clojure.core/count a)))
    "Array.push" (entry 1 2 (call 'array-push))
    "Array.pop" (entry 1 1 (call 'array-pop))
    "Array.getInternal" (entry 1 3 (fn [a i _] (list (rt-sym 'array-get) a i)))
    "Array.uget" (entry 1 3 (fn [a i _] (list (rt-sym 'array-get) a i)))
    "Array.emptyWithCapacity" (entry 1 1 (fn [_] []))
    "Array.mkEmpty" (entry 1 1 (fn [_] []))
    "Array.set" (entry 1 4 (fn [a i v _] (list 'clojure.core/assoc (list 'clojure.core/vec a) i v)))
    "Array.set!" (entry 1 3 (call 'array-set!))

    "ByteArray.mk" (entry 0 1 identity)
    "ByteArray.data" (entry 0 1 identity)
    "ByteArray.size" (entry 0 1 (fn [a] (list 'clojure.core/count a)))
    "ByteArray.push" (entry 0 2 (call 'array-push))
    "ByteArray.get" (entry 0 3 (fn [a i _] (list (rt-sym 'array-get) a i)))
    "ByteArray.uget" (entry 0 3 (fn [a i _] (list (rt-sym 'array-get) a i)))
    "ByteArray.emptyWithCapacity" (entry 0 1 (fn [_] []))
    "ByteArray.copySlice" (entry 0 6 (call 'byte-array-copy-slice))}
   (into {} (mapcat (fn [[t bits]] (uint-entries t bits)) uint-widths))))

(defn- curried [params body] (reduce (fn [b p] (list 'fn [p] b)) body (rseq (vec params))))

(defn app-form
  "Lower an application with compiled args `ca` (erased slots included, as nil)."
  [{:keys [erased arity emit]} ca]
  (let [as (vec (drop (min erased (count ca)) ca))]
    (if (>= (count as) arity)
      (reduce (fn [f a] (list f a)) (apply emit (take arity as)) (drop arity as))
      (let [ss (vec (repeatedly (count as) #(gensym "a")))
            ps (vec (repeatedly (- arity (count as)) #(gensym "p")))
            body (curried ps (apply emit (concat ss ps)))]
        (curried (repeatedly (- erased (min erased (count ca))) #(gensym "_"))
                 (if (seq ss) (list 'let (vec (interleave ss as)) body) body))))))

(defn value-form
  "The extern as a value: curried over its erased and runtime parameters; a binary operation
   with nothing erased also accepts both operands at once (a fold step)."
  [{:keys [erased arity emit] :as e}]
  (if (and (zero? erased) (= 2 arity))
    (let [a (gensym "a") b (gensym "b")]
      (list 'fn (list [a] (list 'fn [b] (emit a b))) (list [a b] (emit a b))))
    (app-form e [])))
