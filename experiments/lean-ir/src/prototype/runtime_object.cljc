(ns prototype.runtime-object
  "Lean Name equality and ByteArray primitives for the pinned 64-bit profile.
   Names use ctor1(str)/ctor2(num), fields[parent,payload], cached UInt64 at
   scalar offset16 (lean.h lean_name_hash_ptr; Init/Prelude.lean Name.hash).
   ByteArray uses LeanScalarArray tag248, immutable :bytes and no owned fields.
   Ownership follows lean.h byte-array getters and runtime/object.cpp mk/push.
   Bounds/preconditions fail explicitly; native capacity/address identity is
   outside this prototype. Equality is iterative, including very deep Names."
  (:require [prototype.scalar :as scalar]
            [prototype.native-scalar :as native]
            [prototype.runtime-string :as string]))

(def supported-symbols
  {"lean_name_eq" {:arity 2}
   "lean_mk_empty_byte_array" {:arity 1}
   "lean_byte_array_mk" {:arity 1}
   "lean_byte_array_fget" {:arity 3}
   "lean_byte_array_uget" {:arity 3}
   "lean_byte_array_get" {:arity 2}
   "lean_byte_array_set" {:arity 3}
   "lean_byte_array_fset" {:arity 4}
   "lean_byte_array_uset" {:arity 4}
   "lean_byte_array_push" {:arity 2}
   "lean_byte_array_size" {:arity 1}})

(defn- fail [message data] (throw (ex-info message data)))
(defn- nat! [ops world value]
  (let [x (native/nat-value ops world value)]
    (when-not (and (integer? x) (<= 0 x) #?(:clj true :cljs (js/Number.isSafeInteger x)))
      (fail "Expected exact guest Nat" {:value x})) x))
(defn- node! [ops world value kind]
  (when-not ((:ref? ops) value) (fail "Expected guest object reference" {:value value :kind kind}))
  (let [node ((:node ops) world value)]
    (when-not (= kind (:kind node)) (fail "Incorrect guest runtime object kind" {:kind kind :node node}))
    node))
(defn- anonymous? [value]
  (or (= value 0)
      (and (native/native-scalar? value) (zero? (native/payload value)))
      (and (map? value) (= 0 (:tag value)))))
(defn- name-node! [ops world value]
  (let [node (node! ops world value :ctor)]
    (when-not (and (contains? #{1 2} (:tag node)) (= 2 (count (:fields node))))
      (fail "Malformed guest Name" {:node node})) node))
(defn- cached-hash [node]
  ;; Real compiler-produced Names carry this computed scalar field. Minimal
  ;; prototype Names may omit layout entirely; compare those structurally.
  ;; Compare cache bytes directly so JS need not approximate unsigned UInt64.
  (when (:layout node)
    (mapv #(scalar/read-bytes (:layout node) (:scalar-bytes node)
                             {:index 2 :offset % :type "uint8" :region :scalar}) (range 8))))
(defn- same-name? [ops world left right]
  (loop [left left right right root? true seen #{}]
    (let [left-ref? ((:ref? ops) left) right-ref? ((:ref? ops) right)]
      (cond
        (and left-ref? right-ref? (= left right)) true
        (and (not left-ref?) (not right-ref?))
        (do (when-not (and (anonymous? left) (anonymous? right))
              (fail "Malformed guest Name terminator" {:left left :right right})) true)
        (not= left-ref? right-ref?)
        (do (when-not (anonymous? (if left-ref? right left))
              (fail "Malformed guest Name terminator" {:left left :right right})) false)
        :else
        (let [pair [left right]
              _ (when (contains? seen pair) (fail "Cyclic guest Name" {}))
              l (name-node! ops world left) r (name-node! ops world right)
              [lp lv] (:fields l) [rp rv] (:fields r)
              lh (when root? (cached-hash l)) rh (when root? (cached-hash r))]
          (cond
            (and (some? lh) (some? rh) (not= lh rh)) false
            (not= (:tag l) (:tag r)) false
            (not (if (= 1 (:tag l))
                   (= 1 (second (string/evaluate ops world "lean_string_dec_eq" [lv rv])))
                   (= (nat! ops world lv) (nat! ops world rv)))) false
            :else (recur lp rp false (conj seen pair))))))))

(defn- byte-node! [ops world value]
  (let [node (node! ops world value :byte-array)]
    (when-not (and (empty? (:fields node)) (vector? (:bytes node)))
      (fail "Malformed guest ByteArray" {:node node})) node))
(defn- allocate-bytes [ops world bytes]
  (let [[world value] ((:allocate ops) world :byte-array 248 [])
        node ((:node ops) world value)]
    [((:replace-node ops) world value (assoc node :bytes bytes)) value]))

(defn- replace-bytes [ops world value node bytes]
  (if (= 1 (:rc node))
    [((:replace-node ops) world value (assoc node :bytes bytes)) value]
    (let [[world copy] (allocate-bytes ops world bytes)]
      [((:release ops) world value 1) copy])))

(defn evaluate
  "Evaluate raw IR arguments using injected guest heap operations.
   Names and ByteArray getters borrow their arguments. Empty allocation borrows
   its capacity; mk consumes its Array. Push/set consume the ByteArray, mutating
   logically unique nodes or copying others (including persistent rc0). Native
   get returns zero and unchecked set is a no-op out of bounds; proof-bearing
   getters/setters reject violated preconditions. Bytes never own guest refs."
  [ops world symbol args]
  (let [spec (get supported-symbols symbol)]
    (when-not spec (fail "Unsupported object runtime extern" {:symbol symbol}))
    (when-not (= (:arity spec) (count args)) (fail "Object runtime arity mismatch" {:symbol symbol})))
  (let [[a b c] args]
    (case symbol
      "lean_name_eq" [world (if (same-name? ops world a b) 1 0)]
      "lean_mk_empty_byte_array"
      (let [capacity (nat! ops world a)]
        (when ((:ref? ops) a)
          (fail "ByteArray capacity must be a native small Nat" {:capacity capacity}))
        ;; lean.h borrows the Nat and rejects non-scalar capacities. Capacity
        ;; affects allocation only; the semantic vector starts with zero bytes.
        (when (> capacity #?(:clj 9223372036854775807 :cljs js/Number.MAX_SAFE_INTEGER))
          (fail "ByteArray capacity exceeds tagged Nat profile" {:capacity capacity}))
        (allocate-bytes ops world []))
      "lean_byte_array_mk"
      (let [node (node! ops world a :array)
            bytes (mapv #(scalar/integer! "uint8" %) (:fields node))
            [world result] (allocate-bytes ops world bytes)]
        [((:release ops) world a 1) result])
      "lean_byte_array_size" [world (count (:bytes (byte-node! ops world a)))]
      "lean_byte_array_get"
      ;; Raw lean.h extern returns zero out of bounds, including boxed big Nat.
      (let [bytes (:bytes (byte-node! ops world a)) index (nat! ops world b)]
        [world (if (and (not ((:ref? ops) b)) (< index (count bytes)))
                 (nth bytes (int index)) 0)])
      ("lean_byte_array_fget" "lean_byte_array_uget")
      (let [bytes (:bytes (byte-node! ops world a))
            index (if (= symbol "lean_byte_array_uget") (scalar/integer! "usize" b) (nat! ops world b))]
        (when-not (< index (count bytes))
          (fail "ByteArray getter precondition violated" {:index index :size (count bytes)}))
        [world (nth bytes (int index))])
      ("lean_byte_array_set" "lean_byte_array_fset" "lean_byte_array_uset")
      (let [node (byte-node! ops world a)
            index (if (= symbol "lean_byte_array_uset") (scalar/integer! "usize" b) (nat! ops world b))
            byte (scalar/integer! "uint8" c)]
        (if (< index (count (:bytes node)))
          (replace-bytes ops world a node (assoc (:bytes node) (int index) byte))
          (if (= symbol "lean_byte_array_set") [world a]
            (fail "ByteArray setter precondition violated" {:index index :size (count (:bytes node))}))))
      "lean_byte_array_push"
      (let [node (byte-node! ops world a) byte (scalar/integer! "uint8" b)
            bytes (conj (:bytes node) byte)]
        (replace-bytes ops world a node bytes)))))
