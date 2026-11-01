(ns ansatz.research.ir.source-data-snapshot
  "Bounded readonly storage witness for pure owned source ModuleData graphs.
   This issues no source, module, checking or import capability. RC is excluded."
  (:require [java-prelude-finalizer-lineage-v1 :as lineage])
  (:import [java.util IdentityHashMap Arrays] [java.math BigInteger]))
(def limits {:nodes 200000 :edges 600000 :bytes 16777216 :characters 4194304 :visits 1000000 :depth 4096})
(defn- need [ok message] (when-not ok (throw (ex-info message {:profile :source-data-storage-witness-v1}))))
(defn- field [x k] (#'lineage/field x k))
(defn- node? [ctx x] (and (some? x) (identical? (:node-class ctx) (class x))))
(defn- kind-metadata [ctx x]
  (let [method (doto (.getDeclaredMethod (class (:engine ctx)) "kindMetadata"
                          (into-array Class [(:node-class ctx)])) (.setAccessible true))]
    (.invoke method nil (object-array [x]))))
(defn- leaf [x]
  (cond
    (identical? Long (class x)) [:long x]
    (identical? String (class x)) [:string x]
    (identical? BigInteger (class x))
    (do (need (<= (.bitLength ^BigInteger x) 4096) "Source data integer exceeds bit bound") [:integer x])
    :else (throw (ex-info "Unknown/mutable source data leaf" {}))))
(defn- sample [ctx x]
  (need (node? ctx x) "Source data node belongs to a foreign runtime class")
  (let [e (:engine ctx) array? (field x "array") tag (.getInt ^java.lang.reflect.Field (:tag ctx) x)
        bytes? (= tag 248) fs ^objects (.get ^java.lang.reflect.Field (:fields ctx) x)
        bs ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) x)]
    (need (and (false? (field x "ref")) (false? (field x "readyTask")) (nil? (field x "closure")))
          "Source data contains mutable/effectful handles or closures")
    (#'lineage/guard-node e (cond array? "array" bytes? "byteArray" :else "constructorNode") x)
    (need (or array? bytes? (<= 0 tag 243)) "Unsupported source data node kind")
    (let [n (cond array? (.arraySize x) bytes? (.byteArraySize x) :else (alength fs))
          metadata (kind-metadata ctx x)]
      (need (and (<= 0 n 1000000) (if array? (<= n (alength fs)) true)) "Invalid source data logical size")
      (need (and (<= (alength bs) (:bytes limits)) (<= (alength fs) (:edges limits))) "Source data storage extent bound")
      (need (if (or array? bytes?) (some? metadata) (nil? metadata)) "Unknown constructor kind metadata")
      ;; PointerMetadata/SharingMetadata carry no payload. The actual engine
      ;; guard still validates their realm/dead state; semantic array metadata
      ;; is fully represented by kind, live extent and capacity below.
      {:node x :tag tag :array? array? :bytes? bytes? :metadata-kind (some-> metadata class)
       :capacity (alength fs) :logical-size n :children (mapv #(aget fs %) (range (if array? n (alength fs))))
       :scalars (aclone bs)})))
(defn capture!
  "Capture all roots together, preserving aliases and rejecting cycles/handles.
   BASIS supplies actual reflective Node fields; reads never acquire RC credits."
  [basis engine roots]
  (need (and (vector? roots) (<= 1 (count roots) 17)) "Bounded source data roots required")
  (let [ctx (assoc (select-keys basis [:node-class :tag :fields :scalars]) :engine engine)
        colors (IdentityHashMap.)]
    (loop [todo (mapv #(vector :enter % 0) roots) records [] visits 0 edges 0 bytes 0 characters 0]
      (need (and (<= visits (:visits limits)) (<= edges (:edges limits)) (<= bytes (:bytes limits))
                 (<= characters (:characters limits)) (<= (count records) (:nodes limits)))
            "Source data snapshot exceeds explicit bounds")
      (if (empty? todo)
        {:context ctx :roots roots :records records}
        (let [[op value depth] (peek todo) tail (pop todo)]
          (need (<= depth (:depth limits)) "Source data snapshot depth bound")
          (cond
            (= :leave op) (do (.put colors value :done) (recur tail records (inc visits) edges bytes characters))
            (not (node? ctx value))
            (do (leaf value) (recur tail records (inc visits) edges bytes
                                    (+ characters (if (string? value) (count value) 0))))
            (= :active (.get colors value)) (throw (ex-info "Cyclic source data graph" {}))
            (= :done (.get colors value)) (recur tail records (inc visits) edges bytes characters)
            :else
            (let [entry (sample ctx value) children (:children entry)]
              (.put colors value :active)
              (recur (into (conj tail [:leave value depth]) (map #(vector :enter % (inc depth)) children))
                     (conj records entry) (inc visits) (+ edges (count children))
                     (+ bytes (alength ^bytes (:scalars entry))) characters))))))))
(defn validate!
  "Compare every captured node's complete live storage. RC counts may change;
   semantic kind/size, scalar bytes, child order and aliases may not. Harmless
   pointer/sharing annotations are not serialized source payload."
  [snapshot]
  (need (and (map? snapshot) (vector? (:records snapshot))) "Actual private source snapshot required")
  (let [ctx (:context snapshot)]
    (doseq [old (:records snapshot)]
      (let [now (sample ctx (:node old))]
        (need (and (= (select-keys old [:tag :array? :bytes? :capacity :logical-size])
                      (select-keys now [:tag :array? :bytes? :capacity :logical-size]))
                   (identical? (:metadata-kind old) (:metadata-kind now))
                   (Arrays/equals ^bytes (:scalars old) ^bytes (:scalars now))
                   (= (count (:children old)) (count (:children now)))
                   (every? true? (map (fn [a b]
                                        (if (node? ctx a) (identical? a b)
                                          (and (not (node? ctx b)) (= (leaf a) (leaf b)))))
                                      (:children old) (:children now))))
              "Owned source ModuleData graph changed"))))
  snapshot)
