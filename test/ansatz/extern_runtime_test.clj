(ns ansatz.extern-runtime-test
  "Lean @[extern] primitives on the Clojure backend (ansatz.codegen.native / lean-runtime).

   Three checks:
   - the values Lean 4.33.1 computes natively (test/lean/extern_runtime.lean, checked there by
     native_decide) are what the compiled Clojure computes;
   - every native fast path agrees with the extern's own Lean body, compiled through the
     representation boundary (the body is the extern's specification);
   - every extern in the bundled Init is accounted for: native, compiled from its body, or
     listed below with a reason."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.codegen :as cg]
            [ansatz.codegen.lean-runtime :as rt]
            [ansatz.codegen.storedef :as sd]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as level]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel ConstantInfo]))

(use-fixtures :once
  (fn [f]
    (let [saved-env @a/ansatz-env
          saved-arity @a/arity-registry
          saved-codegen @a/codegen-registry
          saved-structures @a/structure-registry
          saved-instances @a/ansatz-instance-index]
      (try
        (binding [*ns* (the-ns 'ansatz.extern-runtime-test) a/*verbose* false]
          (a/load-init!)
          (f))
        (finally
          (reset! a/ansatz-env saved-env)
          (reset! a/arity-registry saved-arity)
          (reset! a/codegen-registry saved-codegen)
          (reset! a/structure-registry saved-structures)
          (reset! a/ansatz-instance-index saved-instances))))))

;; ── kernel terms ──────────────────────────────────────────────────────────────────────────────

(defn- ci [n] (env/lookup (a/env) (name/from-string n)))
(defn- c [n] (e/const' (name/from-string n) (repeat (alength (.levelParams ^ConstantInfo (ci n))) level/zero)))
(defn- nat [n] (e/lit-nat (biginteger n)))
(defn- app [f & args] (apply e/app* (c f) args))
(defn- proof [] (c "True.intro"))
(defn- ch [cp] (app "Char.ofNat" (nat cp)))
(defn- str-lit [s] (e/lit-str s))
(defn- nat-list [xs] (reduce (fn [l x] (app "List.cons" (c "Nat") (nat x) l)) (app "List.nil" (c "Nat")) (reverse xs)))
(defn- char-list [cps] (reduce (fn [l x] (app "List.cons" (c "Char") (ch x) l)) (app "List.nil" (c "Char")) (reverse cps)))
(defn- nat-array [xs] (app "Array.mk" (c "Nat") (nat-list xs)))
(defn- byte-array [xs]
  (app "ByteArray.mk"
       (app "Array.mk" (c "UInt8")
            (reduce (fn [l x] (app "List.cons" (c "UInt8") (app "UInt8.ofNat" (nat x)) l))
                    (app "List.nil" (c "UInt8")) (reverse xs)))))

(defn- run [term] (eval (cg/ansatz->clj (a/env) term [])))

(defn- body-of
  "The extern's Lean definition, applied to `args` (its specification)."
  [n args]
  (let [^ConstantInfo k (ci n)
        v (e/instantiate-level-params (.getValue k) (zipmap (.levelParams k) (repeat level/zero)))]
    (apply e/app* v args)))

;; ── Lean 4.33.1 values (test/lean/extern_runtime.lean) ────────────────────────────────────────

(deftest strings-are-code-point-sequences
  (is (= "a😀b" (run (app "String.append" (str-lit "a😀") (str-lit "b")))))
  (is (= [104 128512 233] (run (app "String.toList" (str-lit "h😀é")))))
  (is (= "h😀é" (run (app "String.ofList" (char-list [104 128512 233])))))
  (is (= 3 (run (app "String.Internal.length" (str-lit "h😀é")))))
  (is (= 7 (run (app "String.utf8ByteSize" (str-lit "h😀é")))))
  (is (= [104 240 159 152 128 195 169] (run (app "String.toByteArray" (str-lit "h😀é")))))
  (is (nil? (run (app "String.toList" (str-lit "")))))
  (testing "String < is code-point order (memcmp of UTF-8), not UTF-16 order"
    (let [lt? (fn [x y] (= [1 nil] (run (app "String.decidableLT" (str-lit x) (str-lit y)))))]
      (is (lt? "￿" "😀"))
      (is (lt? "abc" "abd"))
      (is (lt? "ab" "abc"))
      (is (not (lt? "abc" "ab")))
      (is (not (lt? "abc" "abc")))))
  (testing "String.hash is MurmurHash64A with seed 11; mixHash is lean_uint64_mix_hash"
    (is (= 9821865621596011261 (run (app "String.hash" (str-lit "hello")))))
    (is (= 9877294847684254529 (run (app "String.hash" (str-lit "")))))
    (is (= 9139638103461449745 (run (app "String.hash" (str-lit "h😀é longer than eight bytes")))))
    (let [u64 #(app "UInt64.ofNatLT" (nat %) (proof))]
      (is (= 6417489475506850606 (run (app "mixHash" (u64 12345) (u64 67890)))))
      (is (= 5887013808463828774 (run (app "mixHash" (u64 18446744073709551615N) (u64 3))))))))

(deftest chars-are-scalar-values
  (is (= 128512 (run (app "Char.toNat" (ch 128512)))))
  (is (= 0 (run (app "Char.toNat" (ch 55296)))) "a surrogate is not a Char: Char.ofNat gives '\\0'")
  (is (= 0 (run (app "Char.toNat" (ch 1114112)))))
  (is (= 57344 (run (app "Char.toNat" (ch 57344))))))

(deftest unsigned-integers-wrap
  (let [u8 #(app "UInt8.ofNat" (nat %)) u32 #(app "UInt32.ofNat" (nat %)) usz #(app "USize.ofNat" (nat %))]
    (is (= 44 (run (app "UInt8.toNat" (u8 300)))))
    (is (= 44 (run (app "UInt8.add" (u8 200) (u8 100)))))
    (is (= 255 (run (app "UInt8.neg" (u8 1)))))
    (is (= 0x30 (run (app "UInt8.land" (u8 0xF0) (u8 0x3C)))))
    (is (= 255 (run (app "UInt8.lor" (u8 0xF0) (u8 0x0F)))))
    (is (= 2 (run (app "UInt32.shiftLeft" (u32 1) (u32 33)))))
    (is (= 1 (run (app "UInt32.shiftRight" (u32 8) (u32 35)))))
    (is (= 7 (run (app "UInt32.mod" (u32 7) (u32 0)))))
    (is (= 44 (run (app "UInt32.toUInt8" (u32 300)))))
    (is (= 5 (run (app "USize.toNat" (usz (+' 18446744073709551616N 5))))))
    (is (= 18446744073709551615N (run (app "USize.sub" (usz 0) (usz 1)))))
    (is (= 1 (run (app "USize.add" (usz 18446744073709551615N) (usz 2)))))
    (is (= "42" (run (app "USize.repr" (usz 42)))))
    (testing "a UInt64 above Long/MAX_VALUE is its Nat value, not a negative long"
      (is (= 9223372036854775809N (run (app "UInt64.ofNatLT" (nat 9223372036854775809N) (proof))))))))

(deftest nat-bit-operations-are-unbounded
  (let [p70 (.shiftLeft BigInteger/ONE 70)]
    (is (= (+' p70 1) (run (app "Nat.land" (nat (+' p70 5)) (nat (+' p70 3))))))
    (is (= (+' p70 6) (run (app "Nat.lor" (nat p70) (nat 6)))))
    (is (= (*' 3 p70) (run (app "Nat.shiftLeft" (nat 3) (nat 70)))))
    (is (= (+' (.shiftLeft BigInteger/ONE 67) 1) (run (app "Nat.shiftRight" (nat (+' p70 8)) (nat 3)))))
    (is (= (*' 3 (.shiftLeft BigInteger/ONE 65))
           (run (app "Nat.gcd" (nat (*' p70 3)) (nat (*' (.shiftLeft BigInteger/ONE 65) 9))))))
    (is (= 0 (run (app "Nat.pred" (nat 0)))))))

(deftest arrays-and-byte-arrays
  (is (= 4 (run (app "Array.size" (c "Nat") (app "Array.push" (c "Nat") (nat-array [1 2 3]) (nat 4))))))
  (is (= [] (run (app "Array.pop" (c "Nat") (nat-array [])))))
  (is (= [1 2] (run (app "Array.pop" (c "Nat") (nat-array [1 2 3])))))
  ;; Array.set! is outside the bundled Init; its fast path is checked directly.
  (is (= [1 9 3] (rt/array-set! [1 2 3] 1 9)))
  (testing "out of bounds, set! and get! panic (stderr) and continue as Lean does"
    (let [err (java.io.StringWriter.)]
      (binding [*err* err]
        (is (= [1 2 3] (rt/array-set! [1 2 3] 7 9)))
        (is (= 0 (run (app "Array.get!Internal" (c "Nat") (c "instInhabitedNat") (nat-array [1 2]) (nat 5))))))
      (is (re-find #"PANIC: index out of bounds" (str err)))))
  (is (= [9 2 3 4 5] (run (app "ByteArray.copySlice" (byte-array [1 2 3 4 5]) (nat 1) (byte-array [9 9 9])
                               (nat 1) (nat 10) (c "Bool.true")))))
  (is (= [9 9 1 9] (run (app "ByteArray.copySlice" (byte-array [1 2 3 4 5]) (nat 0) (byte-array [9 9 9 9])
                             (nat 2) (nat 1) (c "Bool.true"))))))

(deftest panic-core-returns-the-default
  (let [err (java.io.StringWriter.)]
    (binding [*err* err]
      (is (= 0 (run (app "panicCore" (c "Nat") (c "instInhabitedNat") (str-lit "boom"))))))
    (is (re-find #"PANIC: boom" (str err)))))

;; ── native fast paths agree with the Lean bodies ─────────────────────────────────────────────

(defn- spec-cases
  "Extern → argument lists. Each is evaluated natively and through the extern's Lean body.
   (A function: kernel terms need the loaded Init.)"
  []
  (let [u8 #(app "UInt8.ofNat" (nat %)) u32 #(app "UInt32.ofNat" (nat %)) usz #(app "USize.ofNat" (nat %))]
    {"Nat.land" [[(nat 12) (nat 10)] [(nat 0) (nat 7)] [(nat 255) (nat 256)]]
     "Nat.lor" [[(nat 12) (nat 10)] [(nat 0) (nat 7)] [(nat 255) (nat 256)]]
     "Nat.shiftLeft" [[(nat 3) (nat 5)] [(nat 0) (nat 9)]]
     "Nat.shiftRight" [[(nat 100) (nat 3)] [(nat 1) (nat 9)]]
     "Nat.pred" [[(nat 0)] [(nat 5)]]
     ;; Nat.gcd is absent: its stored value is the well-founded kernel encoding (through
     ;; Nat.gcd._unary), not a runnable definition; the Lean values above cover it.
     "Int.decNonneg" [[(app "Int.ofNat" (nat 3))] [(app "Int.negSucc" (nat 0))]]
     "Char.ofNatAux" [[(nat 97) (proof)]]
     "UInt8.add" [[(u8 200) (u8 100)] [(u8 1) (u8 2)]]
     "UInt8.neg" [[(u8 0)] [(u8 1)] [(u8 200)]]
     "UInt8.land" [[(u8 0xF0) (u8 0x3C)]]
     "UInt8.lor" [[(u8 0xF0) (u8 0x0F)]]
     "UInt8.ofNat" [[(nat 300)] [(nat 7)]]
     "UInt8.toUInt32" [[(u8 200)]]
     "UInt8.decEq" [[(u8 3) (u8 3)] [(u8 3) (u8 4)]]
     "UInt32.ofNat" [[(nat 4294967301)] [(nat 9)]]
     "UInt32.mod" [[(u32 7) (u32 0)] [(u32 17) (u32 5)]]
     "UInt32.land" [[(u32 0xF0F0) (u32 0xFF00)]]
     "UInt32.lor" [[(u32 0xF0F0) (u32 0xFF00)]]
     "UInt32.shiftLeft" [[(u32 1) (u32 33)] [(u32 3) (u32 4)] [(u32 4294967295) (u32 1)]]
     "UInt32.shiftRight" [[(u32 8) (u32 35)] [(u32 4294967295) (u32 4)]]
     "UInt32.toUInt8" [[(u32 300)]]
     "UInt32.decLt" [[(u32 3) (u32 4)] [(u32 4) (u32 3)]]
     "UInt32.decLe" [[(u32 3) (u32 3)] [(u32 4) (u32 3)]]
     "UInt32.decEq" [[(u32 3) (u32 3)] [(u32 4) (u32 3)]]
     "USize.ofNat" [[(nat 18446744073709551621N)]]
     "USize.add" [[(usz 18446744073709551615N) (usz 2)]]
     "USize.sub" [[(usz 0) (usz 1)] [(usz 9) (usz 4)]]
     "USize.decEq" [[(usz 3) (usz 3)] [(usz 3) (usz 4)]]
     "USize.repr" [[(usz 0)] [(usz 42)]]
     "String.append" [[(str-lit "a😀") (str-lit "b")] [(str-lit "") (str-lit "")]]
     "String.toList" [[(str-lit "h😀é")] [(str-lit "")]]
     "String.ofList" [[(char-list [104 128512 233])] [(char-list [])]]
     "String.utf8ByteSize" [[(str-lit "h😀é")]]
     "String.toByteArray" [[(str-lit "h😀é")]]
     "String.decEq" [[(str-lit "a😀") (str-lit "a😀")] [(str-lit "a") (str-lit "b")]]
     "Array.push" [[(c "Nat") (nat-array [1 2]) (nat 3)]]
     "Array.pop" [[(c "Nat") (nat-array [1 2])] [(c "Nat") (nat-array [])]]
     "Array.size" [[(c "Nat") (nat-array [1 2 3])]]
     "Array.toList" [[(c "Nat") (nat-array [1 2 3])] [(c "Nat") (nat-array [])]]
     "Array.getInternal" [[(c "Nat") (nat-array [5 6 7]) (nat 1) (proof)]]
     "Array.uget" [[(c "Nat") (nat-array [5 6 7]) (usz 2) (proof)]]
     "Array.get!Internal" [[(c "Nat") (c "instInhabitedNat") (nat-array [5 6 7]) (nat 1)]]
     "Array.emptyWithCapacity" [[(c "Nat") (nat 4)]]
     "ByteArray.push" [[(byte-array [1 2]) (app "UInt8.ofNat" (nat 3))]]
     "ByteArray.size" [[(byte-array [1 2 3])]]
     "ByteArray.get" [[(byte-array [5 6 7]) (nat 2) (proof)]]
     "ByteArray.data" [[(byte-array [5 6 7])]]}))

(deftest native-fast-paths-agree-with-lean-bodies
  (doseq [[n cases] (spec-cases)
          args cases]
    (testing n
      (is (cg/native-extern? n))
      (is (= (run (apply app n args)) (run (body-of n args)))))))

;; ── coverage of the bundled Init ─────────────────────────────────────────────────────────────

(def ^:private unsupported
  "Bundled-Init externs with neither a native lowering nor a compilable body, and why."
  {"Nat.gcd._unary" "well-founded recursion's internal unary encoding; Nat.gcd runs natively"})

(deftest every-bundled-init-extern-is-accounted-for
  (doseq [n (sort (env/get-extension (a/env) :extern #{}))]
    (testing n
      (is (or (cg/native-extern? n)
              (some? (sd/try-compile-store-def! (a/env) n))
              (contains? unsupported n))
          (str n ": no native lowering, its body does not compile ("
               (:reason (sd/failure-reason n)) "), and it is not listed as unsupported")))))

(deftest compiled-definitions-use-strings-and-chars
  (testing "the definitions the λK model needed: String append/toList/ofList, Char"
    (a/defn ext-greet [x :- String] String (String.append "hi " x))
    (a/defn ext-codes [x :- String] (List Char) (String.toList x))
    (a/defn ext-of [x :- (List Char)] String (String.ofList x))
    (a/defn ext-char [n :- Nat] Nat (Char.toNat (Char.ofNat n)))
    (is (= "hi 😀" ((deref (resolve 'ext-greet)) "😀")))
    (is (= [104 128512] ((deref (resolve 'ext-codes)) "h😀")))
    (is (= "h😀" ((deref (resolve 'ext-of)) [104 128512])))
    (is (= [97 0] (map (deref (resolve 'ext-char)) [97 55296])))))
