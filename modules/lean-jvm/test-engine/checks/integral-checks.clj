(ns java-ir-integral-checks
  "Unsigned lane arithmetic through exact original declarations and wrappers."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.edn :as edn]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def fixture "test/fixtures/java-integral-runtime/original-rows.json")
(def max-word (.subtract (.shiftLeft java.math.BigInteger/ONE 64) java.math.BigInteger/ONE))
(def high (.shiftLeft java.math.BigInteger/ONE 63))
(defn carrier [n] (if (<= n Long/MAX_VALUE) (long n) (biginteger n)))
(defn context []
  (let [rows (mapv #(get % "row") (json/read-str (slurp fixture)))
        helpers [(c/decl "box-word" [(c/p 1 "usize")] "object"
                   (c/let-ir 2 "object" {:box {:ty "usize" :x {:idx 1}}} (c/ret 2)))
                 (c/decl "unbox-word" [(c/p 1 "object")] "usize"
                   (c/let-ir 2 "usize" {:unbox {:x {:idx 1}}}
                     ["dec" {:idx 1} 1 true false (c/ret 2)]))
                 (c/decl "overwrite-word" [(c/p 1 "object") (c/p 2 "usize")] "object"
                   ["uset" {:idx 1} 0 {:idx 2} (c/ret 1)])]]
    (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(into rows (x/raw helpers))]))))
(defn word [ctx engine n] (j/call ctx engine "box-word" [(carrier n)]))
(defn word-op [ctx engine name values output-word? boxed?]
  (let [value (j/call ctx engine (str "USize." name (when boxed? "._boxed"))
                       (if boxed? (mapv #(word ctx engine %) values) (mapv carrier values)))]
    (if (and boxed? output-word?) (j/call ctx engine "unbox-word" [value]) value)))

(deftest exact-fixture-and-all-captured-scalar-abis
  (let [manifest (edn/read-string (slurp "test/fixtures/java-integral-runtime/provenance.edn"))
        rows (json/read-str (slurp fixture))]
    (is (= 46 (count rows)))
    (is (= (:fixture-sha256 manifest) (corpus/sha256 fixture)))
    (doseq [r rows :when (get-in r ["row" "ir" "extern"])]
      (is (string? (j/invoke-static (.getMethod ^Class (:class *basis*) "validateExternAbi"
                                                (into-array Class [java.util.Map])) [(get r "row")]))))))

(deftest modular-usize-arithmetic-and-unsigned-order-direct-and-boxed
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [a [0 1 Long/MAX_VALUE high max-word] b [0 1 Long/MAX_VALUE high max-word]
              boxed? [false true]]
        (doseq [[name expected] [["add" (.and (.add (biginteger a) (biginteger b)) max-word)]
                                ["sub" (.and (.subtract (biginteger a) (biginteger b)) max-word)]
                                ["mul" (.and (.multiply (biginteger a) (biginteger b)) max-word)]
                                ["land" (.and (biginteger a) (biginteger b))]]]
          (is (= expected (word-op ctx engine name [a b] true boxed?))))
        (doseq [[name expected] [["decEq" (if (= a b) 1 0)] ["decLt" (if (< a b) 1 0)]
                                ["decLe" (if (<= a b) 1 0)]]]
          (is (= expected (word-op ctx engine name [a b] false boxed?)))))
      (finally (j/close! ctx engine)))))

(deftest shifts-mask-distance-mod64-and-right-shift-is-logical
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [a [0 1 high max-word] distance [0 1 63 64 65 max-word] boxed? [false true]
              :let [k (.intValue (.and (biginteger distance) (biginteger 63)))]]
        (is (= (.and (.shiftLeft (biginteger a) k) max-word)
               (word-op ctx engine "shiftLeft" [a distance] true boxed?)))
        (is (= (.shiftRight (biginteger a) k)
               (word-op ctx engine "shiftRight" [a distance] true boxed?))))
      (finally (j/close! ctx engine)))))

(deftest conversions-preserve-mathematical-nat-and-truncate-narrow-lanes
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [n [0 1 Long/MAX_VALUE high max-word] boxed? [false true]]
        (is (= n (word-op ctx engine "toNat" [n] false boxed?)))
        (is (= (str n) (word-op ctx engine "repr" [n] false boxed?))))
      (doseq [n [0 1 (.add (.shiftLeft java.math.BigInteger/ONE 64) (biginteger 17))]]
        (let [expected (.and (biginteger n) max-word)
              direct (j/call ctx engine "USize.ofNat" [(carrier n)])
              boxed (j/call ctx engine "USize.ofNat._boxed" [(carrier n)])]
          (is (= expected direct (j/call ctx engine "unbox-word" [boxed])))))
      (doseq [n [0 1 255 256 4294967295 (.add (.shiftLeft java.math.BigInteger/ONE 100) (biginteger 257))]]
        (let [expected (.longValue (.and (biginteger n) (biginteger 4294967295)))
              direct (j/call ctx engine "UInt32.ofNatLT" [(carrier n) 0])
              boxed (j/call ctx engine "UInt32.ofNatLT._boxed" [(carrier n) 0])]
          (is (= expected direct boxed))
          (is (= (bit-and expected 255) (j/call ctx engine "UInt32.toUInt8._boxed" [boxed])))))
      (doseq [a [0 1 4294967295] b [0 1 4294967295]]
        (is (= (bit-and (+ a b) 4294967295) (j/call ctx engine "UInt32.add._boxed" [a b]))))
      (doseq [a [0 1 127 128 255] b [0 1 127 128 255]]
        (is (= (bit-and a b) (j/call ctx engine "UInt8.land._boxed" [a b])))
        (is (= (if (= a b) 1 0) (j/call ctx engine "UInt8.decEq._boxed" [a b])))
        (is (= (if (<= a b) 1 0) (j/call ctx engine "UInt8.decLe._boxed" [a b]))))
      (doseq [n [0 1 127 128 255]] (is (= n (j/call ctx engine "UInt8.toNat._boxed" [n]))))
      (finally (j/close! ctx engine)))))

(deftest boxed-word-forks-have-independent-packed-scalar-storage
  (let [ctx (context) engine (j/machine ctx) value (word ctx engine max-word)
        child (j/fork! ctx engine [value]) child-engine (:engine child) child-value (first (:roots child))]
    (try
      (is (not (identical? value child-value)))
      (is (identical? child-value (j/call ctx child-engine "overwrite-word" [child-value 0])))
      (is (= 0 (j/call ctx child-engine "unbox-word" [child-value])))
      (is (= max-word (j/call ctx engine "unbox-word" [value])))
      (finally (j/close! ctx engine) (j/close! ctx child-engine)))))

(deftest public-negative-wide-and-inexact-scalars-and-bad-proofs-reject
  (let [ctx (context)]
    (doseq [value [-1 (.add max-word java.math.BigInteger/ONE) 1.5]
            :let [engine (j/machine ctx)]]
      (is (re-find #"unsigned scalar|Unsigned scalar" (c/failure #(j/call ctx engine "USize.add" [value 0])))))
    (doseq [[label args pattern] [["USize.ofNatLT" [1 42] #"proof requires erased"]
                                ["UInt32.ofNatLT" [1 42] #"proof requires erased"]
                                ["UInt32.ofNatLT" [-1 0] #"Invalid Nat"]]]
      (let [engine (j/machine ctx)] (is (re-find pattern (c/failure #(j/call ctx engine label args))))))))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-integral-checks)))
