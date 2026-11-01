(ns allocation-heartbeat-counter-v1
  "Pure UInt64 virtual allocation counter. No wall-clock/native-block parity.")
(def modulus 18446744073709551616N)
(def max-set-bits 4096)
(defn- need [ok message] (when-not ok (throw (ex-info message {:profile :allocation-heartbeat-counter-v1}))))
(defn nat-value [x]
  (need (or (and (instance? Long x) (<= 0 x))
            (and (identical? java.math.BigInteger (class x)) (not (neg? (.signum ^java.math.BigInteger x)))))
        "Expected actual immutable Java Nat carrier")
  (need (<= (.bitLength (biginteger x)) max-set-bits) "Setter Nat exceeds explicit lab bit bound")
  ;; No arbitrary host BigInt/Number/Node, no lossy truncation before modulo.
  (bigint x))
(defn unsigned-allocation [raw]
  (need (instance? Long raw) "Actual raw Java long allocation field required")
  (mod (bigint raw) modulus))
(defn read-count [raw offset]
  (need (and (integer? offset) (<= 0 offset) (< offset modulus)) "Invalid branch-local UInt64 offset")
  (mod (-' (unsigned-allocation raw) offset) modulus))
(defn set-offset [raw nat]
  (mod (-' (unsigned-allocation raw) (mod (nat-value nat) modulus)) modulus))
(defn result-carrier [n]
  (need (and (integer? n) (<= 0 n) (< n modulus)) "UInt64 result required")
  (if (<= n Long/MAX_VALUE) (long n) (biginteger n)))

(defn fork-offset
  "Preserve the parent's virtual count even if a fork uses a different raw mark."
  [parent-raw parent-offset child-raw]
  (mod (-' (unsigned-allocation child-raw) (read-count parent-raw parent-offset)) modulus))
