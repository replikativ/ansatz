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
  (:require [ansatz.codegen.lean-runtime]))

(def ^:private rt "ansatz.codegen.lean-runtime")
(defn- rt-sym [n] (symbol rt (name n)))

(defn- identity-structure
  "A structure represented by its single relevant field (Lean hasTrivialStructure?):
   `relevant` is that field's index; the others are proofs, represented by nil."
  [relevant]
  {:ctor (fn [fields] (nth fields relevant))
   :field (fn [i x] (when (= i relevant) x))})

(def native-structures
  "Inductive name → {:ctor (fn [field-forms] form) :field (fn [index form] form)}."
  (merge
   {"Fin" (identity-structure 0)
    "BitVec" (identity-structure 0)
    "Char" (identity-structure 0)
    "String.Pos.Raw" (identity-structure 0)
    "ByteArray" (identity-structure 0)
    "String" {:ctor (fn [[bytes _]] (list (rt-sym 'utf8->string) bytes))
              :field (fn [i x] (when (zero? i) (list (rt-sym 'string->utf8) x)))}
    "Array" {:ctor (fn [[xs]] (list (rt-sym 'array-of-list) xs))
             :field (fn [_ x] (list (rt-sym 'array-to-list) x))}}
   (into {} (for [t ["UInt8" "UInt16" "UInt32" "UInt64" "USize"
                     "Int8" "Int16" "Int32" "Int64" "ISize"]]
              [t (identity-structure 0)]))))

(defn native-structure [type-name] (get native-structures type-name))

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
