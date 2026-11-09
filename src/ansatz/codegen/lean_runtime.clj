(ns ansatz.codegen.lean-runtime
  "Runtime implementations of Lean's `@[extern]` primitives for the Clojure backend.

   Lean's compiler gives a few Init types a native runtime representation and implements the
   operations that cross it in C (Lean v4.33.1 src/include/lean/lean.h, src/runtime/object.cpp,
   src/runtime/hash.cpp). This namespace is the Clojure counterpart. Representations:

     Nat, Int                  long, promoting to BigInt (as before)
     Fin n, BitVec w           the Nat value (Lean: trivial structures over Nat)
     UInt8/16/32/64, USize     the Nat value in [0, 2^w) — never a signed long bit pattern
     Int8/16/32/64, ISize      the underlying UIntN value (its two's-complement bits)
     Char                      the code point as a Nat (Lean: a trivial structure over UInt32)
     String                    java.lang.String (Lean semantics: a sequence of code points)
     String.Pos.Raw            the UTF-8 byte offset as a Nat
     Array α                   a Clojure persistent vector
     ByteArray                 a persistent vector of byte values (its `data : Array UInt8`)

   The functions that convert between a native representation and its Lean structure view
   (`string->utf8`, `utf8->string`, …) are the trusted boundary. Every other extern either has a
   fast path here, tested against its compiled Lean body, or is compiled from that body."
  (:import [java.nio.charset StandardCharsets]))

(set! *warn-on-reflection* true)

;; ── fixed-width unsigned integers (lean.h lean_uintN_*) ──────────────────────────────────────

(def ^:private two64 (.shiftLeft BigInteger/ONE 64))

(defn modulus [bits] (if (= bits 64) two64 (bit-shift-left 1 bits)))

(defn- wrap64 [x]
  ;; Values are Nats: a UInt64 above Long/MAX_VALUE is a BigInt, never a negative long.
  (let [b (.mod (biginteger x) ^BigInteger two64)]
    (if (< (.bitLength b) 63) (.longValue b) (bigint b))))

(defn uint-of-nat
  "lean_uintN_of_nat: n mod 2^bits."
  [bits n]
  (if (= bits 64) (wrap64 n) (mod n (bit-shift-left 1 bits))))

(defn uint-add [bits a b] (uint-of-nat bits (+' a b)))
(defn uint-sub [bits a b] (uint-of-nat bits (-' (+' a (modulus bits)) b)))
(defn uint-mul [bits a b] (uint-of-nat bits (*' a b)))
(defn uint-div [_bits a b] (if (zero? b) 0 (quot a b)))
(defn uint-mod [_bits a b] (if (zero? b) a (rem a b)))
(defn uint-neg [bits a] (uint-of-nat bits (-' (modulus bits) a)))
(declare nat-land nat-lor nat-xor)
(defn uint-land [_bits a b] (nat-land a b))
(defn uint-lor [_bits a b] (nat-lor a b))
(defn uint-xor [_bits a b] (nat-xor a b))
(defn uint-complement [bits a] (uint-of-nat bits (-' (dec' (modulus bits)) a)))
(defn uint-shift-left
  "lean_uintN_shift_left: a << (b mod bits), truncated."
  [bits a b]
  (uint-of-nat bits (bigint (.shiftLeft (biginteger a) (int (mod b bits))))))
(defn uint-shift-right
  "lean_uintN_shift_right: a >> (b mod bits)."
  [bits a b]
  (let [r (.shiftRight (biginteger a) (int (mod b bits)))]
    (if (< (.bitLength r) 63) (.longValue r) (bigint r))))

;; ── Nat bit operations (lean.h lean_nat_land/lor/shiftl/shiftr, Nat.gcd) ──────────────────────

(defn- nat-out [^BigInteger b] (if (< (.bitLength b) 63) (.longValue b) (bigint b)))
(defmacro ^:private bitwise [long-op big-op a b]
  `(let [a# ~a b# ~b]
     (if (and (instance? Long a#) (instance? Long b#))
       (~long-op (long a#) (long b#))
       (nat-out (~big-op ^BigInteger (biginteger a#) ^BigInteger (biginteger b#))))))
(defn nat-land [a b] (bitwise bit-and .and a b))
(defn nat-lor [a b] (bitwise bit-or .or a b))
(defn nat-xor [a b] (bitwise bit-xor .xor a b))
(defn nat-shift-left [a b]
  (when-not (< b Integer/MAX_VALUE)
    (throw (ArithmeticException. "Nat.shiftLeft: shift exceeds the runtime's range")))
  (nat-out (.shiftLeft (biginteger a) (int b))))
(defn nat-shift-right [a b]
  (if (>= b Integer/MAX_VALUE) 0 (nat-out (.shiftRight (biginteger a) (int b)))))
(defn nat-gcd [a b] (nat-out (.gcd (biginteger a) (biginteger b))))
(defn nat-pred [n] (if (zero? n) 0 (dec' n)))

;; ── Decidable results: constructor index plus erased proof (as Nat.decEq) ─────────────────────

(defmacro decide [c] `(if ~c [1 nil] [0 nil]))

;; ── Char / String ─────────────────────────────────────────────────────────────────────────────

(defn string-of-list
  "lean_string_mk (String.ofList): the string of a list of code points."
  [cs]
  (let [sb (StringBuilder.)]
    (doseq [c cs] (.appendCodePoint sb (int c)))
    (.toString sb)))

(defn string-to-list
  "lean_string_data (String.toList): the code points, as a List Char (nil when empty)."
  [^String s]
  (seq (mapv long (iterator-seq (.iterator (.codePoints s))))))

(defn string-length
  "lean_string_length: the number of code points."
  [^String s]
  (long (.codePointCount s 0 (.length s))))

(defn utf8-bytes ^"[B" [^String s] (.getBytes s StandardCharsets/UTF_8))

(defn utf8-byte-size [^String s] (long (alength (utf8-bytes s))))

(defn string->utf8
  "Boundary: lean_string_to_utf8 (String.toByteArray). Bytes as Nat values 0..255."
  [^String s]
  (mapv #(bit-and (long %) 0xff) (utf8-bytes s)))

(defn utf8->string
  "Boundary: lean_string_from_utf8_unchecked (String.ofByteArray). Its argument carries a proof
   of valid UTF-8, so decoding never substitutes."
  [bs]
  (String. (byte-array (map unchecked-byte bs)) StandardCharsets/UTF_8))

(defn string-append [^String s ^String t] (.concat s t))

(defn string-lt
  "lean_string_lt: memcmp of the UTF-8 encodings, i.e. code-point lexicographic order
   (String.compareTo would compare UTF-16 units and misorder supplementary characters)."
  [^String a ^String b]
  (let [la (.length a) lb (.length b)]
    (loop [i 0 j 0]
      (cond
        (>= j lb) false
        (>= i la) true
        :else (let [ca (.codePointAt a i) cb (.codePointAt b j)]
                (cond (< ca cb) true
                      (> ca cb) false
                      :else (recur (+ i (Character/charCount ca)) (+ j (Character/charCount cb)))))))))

(def ^:private murmur-m (unchecked-long 0xc6a4a7935bd1e995))

(defn- u64 [^long x] (if (neg? x) (bigint (.add (BigInteger/valueOf x) ^BigInteger two64)) x))

(defn murmur64a
  "src/runtime/hash.cpp MurmurHash64A (little-endian 8-byte blocks)."
  ^long [^"[B" data ^long seed]
  (let [m (long murmur-m) r 47 len (alength data) nblocks (quot len 8)
        h (loop [i 0 h (bit-xor seed (unchecked-multiply len m))]
            (if (< i nblocks)
              (let [k (loop [b 7 k 0]
                        (if (neg? b) k
                            (recur (dec b) (bit-or (bit-shift-left k 8)
                                                   (bit-and (long (aget data (+ (* i 8) b))) 0xff)))))
                    k (unchecked-multiply k m)
                    k (bit-xor k (unsigned-bit-shift-right k r))
                    k (unchecked-multiply k m)]
                (recur (inc i) (unchecked-multiply (bit-xor h k) m)))
              h))
        tail (* nblocks 8)
        rem (bit-and len 7)
        h (if (pos? rem)
            (unchecked-multiply
             (loop [b (dec rem) h h]
               (if (neg? b) h
                   (recur (dec b) (bit-xor h (bit-shift-left (bit-and (long (aget data (+ tail b))) 0xff)
                                                             (* 8 b))))))
             m)
            h)
        h (bit-xor h (unsigned-bit-shift-right h r))
        h (unchecked-multiply h m)]
    (bit-xor h (unsigned-bit-shift-right h r))))

(defn string-hash
  "lean_string_hash: MurmurHash64A of the UTF-8 bytes with seed 11, as a UInt64."
  [^String s]
  (u64 (murmur64a (utf8-bytes s) 11)))

(defn mix-hash
  "lean_uint64_mix_hash (lean.h)."
  [h k]
  (let [m (long murmur-m)
        k (unchecked-multiply (unchecked-long k) m)
        k (bit-xor k (unsigned-bit-shift-right k 47))
        k (bit-xor k m)
        h (bit-xor (unchecked-long h) k)]
    (u64 (unchecked-multiply h m))))

;; ── Array / ByteArray ─────────────────────────────────────────────────────────────────────────

(defn array-of-list [xs] (vec xs))
(defn array-to-list [a] (seq a))
(defn array-push [a v] (conj (vec a) v))
(defn array-pop [a] (let [a (vec a)] (if (empty? a) a (pop a))))
(defn array-get [a i] (nth a i))
(declare panic!)
(defn array-set!
  "lean_array_set: out of bounds panics (lean_array_set_panic) and returns the array unchanged."
  [a i v]
  (let [a (vec a)]
    (if (and (integer? i) (< -1 i (count a))) (assoc a i v) (panic! "index out of bounds" a))))

(defn panic!
  "lean_panic_fn: report the message and continue with the default value."
  [msg default]
  (binding [*out* *err*] (println (str "PANIC: " msg)))
  default)

(defn executed-sorry!
  "lean_sorry (runtime/object.cpp): `lean_internal_panic(\"executed 'sorry'\")`, which
   does not return. On the JVM it throws."
  []
  (throw (ex-info "executed 'sorry'" {:kind :executed-sorry})))

(defn array-get!
  "lean_array_get / lean_array_get_panic: out of bounds panics and returns the default."
  [default a i]
  (if (and (integer? i) (< -1 i (count a)))
    (nth a i)
    (panic! "index out of bounds" default)))

(defn- extract
  "Array.extract: the elements in [start, min stop size)."
  [v start stop]
  (let [v (vec v) stop (min stop (count v))]
    (if (< start stop) (subvec v start stop) [])))

(defn byte-array-copy-slice
  "ByteArray.copySlice (Init/Data/ByteArray/Basic.lean): the bytes of dest before destOff, then
   src[srcOff, srcOff+len), then the rest of dest after the overwritten range."
  [src src-off dest dest-off len _exact]
  (let [src (vec src) dest (vec dest)]
    (-> (extract dest 0 dest-off)
        (into (extract src src-off (+' src-off len)))
        (into (extract dest (+' dest-off (min len (max 0 (- (count src) src-off)))) (count dest))))))
