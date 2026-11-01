(ns prototype.session-compiler-options
  "Owner-free public compiler selection; never an execution/admission receipt."
  (:require [prototype.machine :as m]
            [prototype.runtime-abi :as abi]
            [prototype.typed-ir :as typed]
            [prototype.typed-blocks :as blocks]))

(defn- pure-copy
  "Copy finite ordinary immutable data, discarding all metadata. Charge shared
   DAGs once, but bound their edges too; no caller container or opaque owner escapes."
  [root]
  (let [pending (java.util.ArrayDeque.) memo (java.util.IdentityHashMap.) heights (java.util.IdentityHashMap.)
        work (volatile! 0) characters (volatile! 0) numeric-bits (volatile! 0)]
    (.addLast pending (object-array [root nil 0]))
    (while (not (.isEmpty pending))
      (let [entry ^objects (.removeLast pending) x (aget entry 0) children (aget entry 1) depth (aget entry 2)]
        (when (> depth 256) (m/fail "Session compiler nesting budget" {}))
        (when-not (.containsKey memo x)
          (when (> (vswap! work inc) 200000) (m/fail "Session compiler data budget" {}))
          (if children
            (.put memo x
                  (let [height (inc (reduce max 0 (map #(.get heights %) children)))
                        _ (when (> height 256) (m/fail "Session compiler nesting budget" {}))
                        _ (.put heights x height)
                        values (mapv #(.get memo %) children)]
                    (cond (map? x) (into {} (map vec (partition 2 values)))
                          (set? x) (set values)
                          :else values)))
            (cond
              (contains? #{clojure.lang.PersistentArrayMap clojure.lang.PersistentHashMap
                            clojure.lang.PersistentVector clojure.lang.PersistentHashSet} (class x))
              (let [edges (* (if (map? x) 2 1) (count x))]
                (when (> (vswap! work + edges) 200000)
                  (m/fail "Session compiler data budget" {}))
                (let [children (if (map? x) (into [] (mapcat identity) x) (vec x))]
                  (.addLast pending (object-array [x children depth]))
                  (doseq [child (rseq children)] (.addLast pending (object-array [child nil (inc depth)])))))
              (or (nil? x) (boolean? x))
              (do (.put heights x 0) (.put memo x x))
              (contains? #{Long Integer Short Byte clojure.lang.BigInt java.math.BigInteger} (class x))
              (let [bits (cond
                           (= java.math.BigInteger (class x)) (.bitLength ^java.math.BigInteger x)
                           (= clojure.lang.BigInt (class x)) (.bitLength (.toBigInteger ^clojure.lang.BigInt x))
                           :else 64)]
                (when (or (> bits 4096) (> (vswap! numeric-bits + bits) 1048576))
                  (m/fail "Session compiler numeric budget" {}))
                (.put heights x 0) (.put memo x x))
              (or (string? x) (keyword? x))
              (do (when (> (vswap! characters + (if (string? x) (count x)
                                                 (+ (count (name x)) (count (namespace x))))) 4194304)
                    (m/fail "Session compiler string budget" {}))
                  (.put heights x 0) (.put memo x x))
              :else (m/fail "Session compiler options require pure immutable data" {}))))))
    (.get memo root)))

(defn- code-key [function]
  ;; Reuse M1's stack-safe, identity-memoized executable key and its exact numeric
  ;; representation contract. The companion placeholder is equal on both sides;
  ;; real producer facts are subsequently checked by the selected compiler.
  (typed/typed-code-key (assoc (dissoc function :typed-ir)
                              :typed-ir {:schema "lean-typed-companion/1"}) {}))

(defn- same-code! [functions name expected]
  (let [actual (some-> (get functions name) (dissoc :typed-ir) pure-copy)]
    (when-not (and actual (= (code-key expected) (code-key actual)))
      (m/fail "Session compiler selection does not match executable code" {:name name}))))

(defn validate
  "Return bounded immutable raw options. Revalidate selected executable facts on
   every session construction, including reference/mutable sessions, without loading
   Pattern there. JVM construction still runs the existing full compiler validators."
  [functions requested]
  (when-not (and (contains? #{clojure.lang.PersistentArrayMap clojure.lang.PersistentHashMap} (class requested))
                 (every? #{:scalar-wrappers :typed-tail} (keys requested)))
    (m/fail "Invalid session compiler options" {}))
  (let [options (pure-copy requested)
        wrappers (when (contains? options :scalar-wrappers)
                   (let [ds (:scalar-wrappers options)]
                     (when-not (and (map? ds) (<= (count ds) 64))
                       (m/fail "Invalid session scalar wrapper selection" {}))
                     ds))
        tail (when (contains? options :typed-tail)
               (let [config (:typed-tail options)]
                 (when-not (and (map? config)
                                (= #{:typed-functions :roots :descriptors :profile :budgets} (set (keys config)))
                                (map? (:typed-functions config)) (<= (count (:typed-functions config)) 16)
                                (vector? (:roots config)) (<= (count (:roots config)) 16)
                                (map? (:descriptors config)) (<= (count (:descriptors config)) 64))
                   (m/fail "Invalid session typed-tail selection" {}))
                 (doseq [[name f] (:typed-functions config)]
                   (when-not (= "lean-typed-companion/1" (get-in f [:typed-ir :schema]))
                     (m/fail "Missing session typed companion" {:name name}))
                   (same-code! functions name f))
                 (let [budgets (:budgets config)
                       base [:max-functions :max-instructions :max-blocks :max-work :max-registers]
                       extra [:max-params :max-emission :max-constants :max-chunk-cost]]
                   (when-not (and (map? budgets) (= (set (concat base extra)) (set (keys budgets)))
                                  (every? #(and (integer? %) (pos? %) (<= % Integer/MAX_VALUE)) (vals budgets))
                                  (<= (:max-functions budgets) 16) (<= (:max-params budgets) 16))
                     (m/fail "Invalid session typed-tail budgets" {}))
                   ;; M2 validates rooted facts/profile without loading Pattern or
                   ;; constructing a represented plan on non-JVM backends.
                   (blocks/prepare-unit
                    (:typed-functions config) (:roots config) (:profile config)
                    (into {} (for [[name d] (:descriptors config)
                                   :let [d (abi/validate-scalar-description! d)]]
                               [name {:params (:params d) :result-type (:result-type d)
                                      :generation (:semantic-generation d) :extern (:extern d)}]))
                    (select-keys budgets base)))
                 config))]
    (doseq [[name descriptor] (concat wrappers (:descriptors tail))]
      (let [d (abi/validate-scalar-description! descriptor)
            params (mapv :id (:params d)) dest (inc (reduce max 0 params))]
        (when-not (= name (:name d)) (m/fail "Session wrapper name mismatch" {}))
        (same-code! functions name
                    {:params params :runtime-extern (:extern d)
                     :body [:let dest [:runtime (:extern d) (mapv #(vector :var %) params)]
                            [:return [:var dest]]]})))
    options))
