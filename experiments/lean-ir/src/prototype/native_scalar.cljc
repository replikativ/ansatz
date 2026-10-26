(ns prototype.native-scalar
  "An untyped native immediate. Its unsigned payload does not say Nat vs Int.
   Conversion is explicit at the runtime operation's typed ABI boundary.")

(defrecord RawNativeScalar [payload])
(defn native-scalar? [value] (instance? RawNativeScalar value))
(def ^:private small-values (mapv ->RawNativeScalar (range 256)))
(defn- fail [message data] (throw (ex-info message data)))

(defn native-scalar [payload]
  (when-not (and (integer? payload) (<= 0 payload)
                 #?(:clj (<= payload 9223372036854775807N)
                    :cljs (js/Number.isSafeInteger payload)))
    (fail "Native scalar payload outside exact tagged profile" {:payload payload}))
  (if (< payload 256) (nth small-values (int payload))
    (->RawNativeScalar #?(:clj (long payload) :cljs payload))))

(defn payload [value]
  (when-not (native-scalar? value) (fail "Expected raw native scalar" {:value value}))
  (:payload value))

(defn number-value
  "Borrow a persistent/imported MPZ value through injected heap operations."
  [ops world value]
  (if (and (:ref? ops) ((:ref? ops) value))
    (let [node ((:node ops) world value)]
      (when-not (and (= :mpz (:kind node)) (empty? (:fields node)) (integer? (:integer node)))
        (fail "Expected native MPZ number" {:value value}))
      (:integer node)) value))

(defn nat-value
  "Interpret an immediate in a Nat/index context; a negative Int never becomes Nat."
  ([value]
   (let [n (if (native-scalar? value) (payload value) value)]
     (when-not (and (integer? n) (<= 0 n) #?(:clj true :cljs (js/Number.isSafeInteger n)))
       (fail "Expected exact guest Nat" {:value value})) n))
  ([ops world value] (nat-value (number-value ops world value))))

(defn int-value
  "Pinned lean_scalar_to_int: unsigned32 then signed32. Host integers are already
   semantic Int, so stay intact. The3-arity form contextually borrows MPZ refs."
  ([value]
   (if (native-scalar? value)
     (let [n (rem (payload value) 4294967296)]
       (if (>= n 2147483648) (- n 4294967296) n))
     (do (when-not (and (integer? value) #?(:clj true :cljs (js/Number.isSafeInteger value)))
           (fail "Expected exact guest Int" {:value value})) value)))
  ([ops world value] (int-value (number-value ops world value))))

(defn unsigned-value [bits value]
  (when-not (contains? #{8 16 32 64} bits) (fail "Unsupported native scalar width" {:bits bits}))
  (let [modulus #?(:clj (bigint (.shiftLeft java.math.BigInteger/ONE bits))
                   :cljs (js/Math.pow 2 bits))]
    (if (native-scalar? value) (rem (payload value) modulus)
      (let [n (nat-value value)]
        (when-not (< n modulus) (fail "Unsigned value outside runtime width" {:bits bits :value value})) n))))

(defn pointer-word [value]
  #?(:clj (inc' (*' 2 (payload value)))
     :cljs (let [word (inc (* 2 (payload value)))]
             (when-not (js/Number.isSafeInteger word)
               (fail "Native pointer word outside exact JS profile" {:value value})) word)))

#?(:clj
   (do
     (def ^:private scalar-carrier-generation (Object.))
     (def ^:private scalar-carrier-root native-scalar?)
     (defn scalar-carrier-token [] scalar-carrier-generation)
     (defn builtin-scalar-carrier? [] (identical? scalar-carrier-root native-scalar?))))
