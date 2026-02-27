;; Copyright (c) 2026 Simmis GmbH. All rights reserved.
;; CIC kernel for Clojure — Universe levels.
;; Thin wrapper over Java Level class.

(ns cic.kernel.level
  "Universe levels matching Lean's Level type.
   Uses Java Level class for ~40 bytes per level vs ~120 for Clojure vectors.
   Level comparison follows Lean 4's kernel level.cpp algorithm."
  (:import [cic.kernel Level]))

(def zero Level/ZERO_LEVEL)

(defn succ [^Level l] (Level/succ l))
(defn level-max [^Level l1 ^Level l2] (Level/max l1 l2))
(defn imax [^Level l1 ^Level l2] (Level/imax l1 l2))
(defn param [name] (Level/param name))

(defn tag [^Level l]
  (case (.tag l)
    0 :zero
    1 :succ
    2 :max
    3 :imax
    4 :param))

(defn level-zero? [^Level l] (= Level/ZERO (.tag l)))
(defn succ? [^Level l] (= Level/SUCC (.tag l)))
(defn max? [^Level l] (= Level/MAX (.tag l)))
(defn imax? [^Level l] (= Level/IMAX (.tag l)))
(defn param? [^Level l] (= Level/PARAM (.tag l)))

(defn succ-pred ^Level [^Level l] (.succPred l))
(defn max-lhs ^Level [^Level l] (.maxLhs l))
(defn max-rhs ^Level [^Level l] (.maxRhs l))
(defn imax-lhs ^Level [^Level l] (.imaxLhs l))
(defn imax-rhs ^Level [^Level l] (.imaxRhs l))
(defn param-name [^Level l] (.paramName l))

(defn has-param?
  "Does this level contain any Level.param?"
  [^Level l]
  (Level/hasParam l))

(defn is-never-zero?
  "Returns true if this level is known to never be zero."
  [^Level l]
  (Level/isNeverZero l))

(defn to-nat
  "If level is a concrete natural number, return it. Else nil."
  [^Level l]
  (let [n (Level/toNat l)]
    (when (>= n 0) n)))

(defn from-nat
  "Create a level from a natural number."
  [n]
  (Level/fromNat (long n)))

(defn instantiate
  "Substitute level params using a substitution map."
  [^Level l subst]
  (let [^java.util.HashMap hm (java.util.HashMap. ^java.util.Map subst)]
    (Level/instantiate l hm)))

(defn simplify
  "Simplify a level expression to a normal form."
  ^Level [^Level l]
  (Level/simplify l))

(defn level-leq
  "Check if l1 <= l2 for all possible assignments of level parameters."
  [^Level l1 ^Level l2]
  (Level/leq l1 l2))

(defn level=
  "Definitional equality of levels."
  [^Level l1 ^Level l2]
  (Level/eq l1 l2))

(defn level<=
  "Level l1 is <= l2."
  [^Level l1 ^Level l2]
  (Level/leq l1 l2))

(defn ->string
  "Display a level as a human-readable string."
  [^Level l]
  (.toString l))
