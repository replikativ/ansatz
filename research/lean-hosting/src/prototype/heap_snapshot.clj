(ns prototype.heap-snapshot
  "Deep immutable-value diagnostics plus storage-only heap-hint delegates.
   Runtime storage proofs do not claim deep payload immutability or authority."
  (:require [prototype.machine :as m] [prototype.native-scalar :as native]
            [prototype.heap-hint :as hint])
  (:import [java.lang.ref WeakReference] [java.util HashMap ArrayList]
           [clojure.lang PersistentHashMap PersistentArrayMap PersistentVector]))

(def ^:private scalar-classes
  #{Boolean Character Byte Short Integer Long Float Double
    java.math.BigInteger java.math.BigDecimal clojure.lang.BigInt clojure.lang.Ratio})
(defn standard-map? [value] (hint/standard-map? value))
(defn- scalar? [value]
  (or (nil? value) (string? value) (keyword? value) (symbol? value)
      (and (some? value) (contains? scalar-classes (class value)))))
(defn- immutable-value? [value]
  (loop [pending [value]]
    (if (empty? pending) true
      (let [value (peek pending) pending (pop pending)]
        (cond
          (scalar? value) (recur pending)
          (m/ref? value) (if (integer? (:id value)) (recur pending) false)
          (instance? prototype.machine.Tag value) (if (integer? (:tag value)) (recur pending) false)
          (native/native-scalar? value) (if (integer? (:payload value)) (recur pending) false)
          (instance? prototype.machine.Builtin value) (recur (conj pending (:name value)))
          (= PersistentVector (class value)) (recur (into pending value))
          (standard-map? value) (recur (reduce-kv (fn [out k v] (conj out k v)) pending value))
          :else false)))))
(defn canonical-node?
  "Conservative storage proof: standard immutable maps/vectors and known scalar
   guest carriers only. Custom persistent implementations and borrowed arrays
   never qualify, even if their current contents happen to compare equal."
  [node]
  (and (standard-map? node) (= PersistentVector (class (:fields node)))
       (immutable-value? node)))


(defn storage-node? [node] (hint/storage-node? node))
(defn clear-cache! [] (hint/clear-cache!))
(defn cache-summary [] (hint/cache-summary))
(defn proof [heap] (hint/proof heap))
(defn remember! [heap long-keys?] (hint/remember! heap long-keys?))
;; Compatibility for bounded cache-structure diagnostics; contains weak refs only.
(def ^:private hints @#'prototype.heap-hint/hints)
