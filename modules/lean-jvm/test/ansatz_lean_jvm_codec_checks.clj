(ns ansatz-lean-jvm-codec-checks
  (:require [clojure.test :refer [deftest is run-tests]] [ansatz.lean.jvm.codec :as codec])
  (:import [java.math BigInteger] [ansatz.lean.jvm LeanUnit]))
(defn- descriptor [kinds]
  {"arguments" (mapv #(hash-map "kind" %) kinds) "result" {"kind" "unit"} "effect" "pure"})
(defn- code [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo error (:code (ex-data error)))))

(deftest variable-arity-leaf-carriers-roundtrip-exactly
  (let [big (.shiftLeft BigInteger/ONE 200)
        inputs [true big (- (bigint big)) "λ\u0000😀" LeanUnit/INSTANCE]
        kinds ["bool" "nat" "int" "string" "unit"]
        encoded (codec/encode-arguments (descriptor kinds) (object-array inputs))
        decoded (mapv #(codec/decode-leaf {"kind" %1} %2) kinds encoded)]
    (is (= inputs decoded))
    (is (= [Long BigInteger BigInteger String Long] (mapv class encoded)))
    (is (identical? LeanUnit/INSTANCE (last decoded))))
  (is (= -9223372036854775808N (codec/decode-leaf {"kind" "int"} Long/MIN_VALUE)))
  (is (empty? (codec/encode-arguments (descriptor []) (object-array [])))))

(deftest invalid-host-values-and-excessive-work-refuse-before-start
  (doseq [[kind value expected] [["nat" -1 "InvalidArgument"]
                                ["int" 1.5 "UnsupportedArgumentType"]
                                ["bool" 1 "UnsupportedArgumentType"]
                                ["unit" nil "UnsupportedArgumentType"]
                                ["string" "\uD800" "InvalidArgument"]
                                ["nat" (.shiftLeft BigInteger/ONE 4096) "ResourceLimit"]
                                ["string" (apply str (repeat 65537 "a")) "ResourceLimit"]]]
    (is (= expected (code #(codec/encode-arguments (descriptor [kind]) (object-array [value]))))))
  (is (= "ArityMismatch" (code #(codec/encode-arguments (descriptor ["bool" "nat"]) (object-array [true]))))))

(deftest numeric-subclasses-never-gain-codec-authority
  (let [called (atom false)
        hostile (proxy [BigInteger] ["1208925819614629174706176"]
                  (signum [] (reset! called true) (throw (AssertionError. "Untrusted signum callback"))))]
    (is (= "UnsupportedArgumentType" (code #(codec/encode-leaf {"kind" "nat"} hostile))))
    (is (= "UnsupportedArgumentType"
           (code #(codec/encode-leaf {"kind" "int"} (clojure.lang.BigInt/fromBigInteger hostile)))))
    (is (false? @called))))

(deftest malformed-runtime-values-refuse-without-casting
  (doseq [[kind value] [["bool" (long 2)] ["unit" (long 1)] ["nat" (long -1)] ["int" true]]]
    (is (= "RuntimeBoundary" (code #(codec/decode-leaf {"kind" kind} value)))))
  (is (= "UnsupportedArgumentType"
         (code #(codec/encode-leaf {"kind" "product" "first" {"kind" "nat"} "second" {"kind" "bool"}}
                                   [1 true])))))

(defn check! [] (run-tests 'ansatz-lean-jvm-codec-checks))
