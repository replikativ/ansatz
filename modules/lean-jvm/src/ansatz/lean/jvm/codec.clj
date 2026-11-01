(ns ansatz.lean.jvm.codec
  "Type-directed host carriers. Leaf conversion allocates no guest Nodes and
   can finish before crossing the interpreter's invocation boundary."
  (:require [ansatz.lean.jvm.signature :as signature])
  (:import [java.math BigInteger] [ansatz.lean.jvm LeanUnit]))

(def ^:private integer-classes #{Byte Short Integer Long BigInteger clojure.lang.BigInt})
(def ^:private maximum-integer-bits 4096)
(def ^:private maximum-string-units 65536)
(defn- need [ok code message]
  (when-not ok (throw (ex-info message {:code code}))))
(defn- integer! [kind value result?]
  (need (contains? integer-classes (class value))
        (if result? "RuntimeBoundary" "UnsupportedArgumentType") "Expected an exact integer carrier")
  (let [value (cond
                (= BigInteger (class value)) value
                (= clojure.lang.BigInt (class value)) (.toBigInteger ^clojure.lang.BigInt value)
                :else (BigInteger/valueOf (.longValue ^Number value)))]
    ;; BigInt can wrap a BigInteger subclass; validate before virtual numeric calls.
    (need (= BigInteger (class value)) (if result? "RuntimeBoundary" "UnsupportedArgumentType")
          "Integer carrier contains an unsupported subclass")
    (need (or (= "int" kind) (not (neg? (.signum ^BigInteger value))))
          (if result? "RuntimeBoundary" "InvalidArgument") "Nat must be nonnegative")
    ;; Refuse oversized values before constructing a normalized signed carrier.
    (need (<= (.bitLength ^BigInteger value) maximum-integer-bits) "ResourceLimit" "Integer exceeds host codec bit budget")
    (need (<= (.bitLength (.abs ^BigInteger value)) maximum-integer-bits) "ResourceLimit" "Integer exceeds host codec bit budget")
    value))
(defn- string! [value result?]
  (need (= String (class value)) (if result? "RuntimeBoundary" "UnsupportedArgumentType") "Expected a String")
  (let [^String value value size (.length value)]
    (need (<= size maximum-string-units) "ResourceLimit" "String exceeds host codec extent")
    (loop [offset 0]
      (when (< offset size)
        (let [c (.charAt value offset)]
          (cond
            (Character/isHighSurrogate c)
            (do (need (and (< (inc offset) size) (Character/isLowSurrogate (.charAt value (inc offset))))
                      (if result? "RuntimeBoundary" "InvalidArgument") "String contains malformed UTF-16")
                (recur (+ offset 2)))
            (Character/isLowSurrogate c)
            (need false (if result? "RuntimeBoundary" "InvalidArgument") "String contains malformed UTF-16")
            :else (recur (inc offset)))))))
  value)

(defn encode-leaf
  "Convert one supported leaf to the interpreter's object-lane carrier. Container
   construction has a separate ownership protocol and is not simulated here."
  [type value]
  (case (get type "kind")
    ("nat" "int") (let [n (integer! (get type "kind") value false)]
                      (if (<= (.bitLength ^BigInteger n) 63) (Long/valueOf (.longValue ^BigInteger n)) n))
    "bool" (do (need (= Boolean (class value)) "UnsupportedArgumentType" "Bool expects Boolean")
               (long (if value 1 0)))
    "string" (string! value false)
    "unit" (do (need (identical? LeanUnit/INSTANCE value) "UnsupportedArgumentType" "Unit expects LeanUnit.INSTANCE")
               (long 0))
    (throw (ex-info "This argument type needs a managed constructor codec" {:code "UnsupportedArgumentType"}))))

(defn decode-leaf
  "Decode a value without taking or releasing guest ownership. Caller retains
   custody of the actual owned result root until all decoding finishes."
  [type value]
  (case (get type "kind")
    ("nat" "int") (do (need (#{Long BigInteger} (class value)) "RuntimeBoundary" "Malformed runtime integer")
                      (integer! (get type "kind") value true))
    "bool" (do (need (and (= Long (class value)) (#{0 1} value)) "RuntimeBoundary" "Malformed runtime Bool")
               (= 1 value))
    "string" (string! value true)
    "unit" (do (need (and (= Long (class value)) (zero? (long value))) "RuntimeBoundary" "Malformed runtime Unit")
               LeanUnit/INSTANCE)
    (throw (ex-info "This result type needs an authenticated constructor codec" {:code "UnsupportedSignature"}))))

(defn encode-arguments
  "Snapshot and validate the whole argument list before guest execution."
  [descriptor arguments]
  (signature/validate! descriptor)
  (let [types (get descriptor "arguments") arity (count types)]
    (need (= (class (object-array 0)) (class arguments)) "UnsupportedArgumentType" "Explicit argument array required")
    (need (= arity (alength ^objects arguments)) "ArityMismatch" "Wrong number of explicit arguments")
    (let [snapshot (aclone ^objects arguments)]
      (object-array (map-indexed (fn [index type] (encode-leaf type (aget snapshot index))) types)))))
