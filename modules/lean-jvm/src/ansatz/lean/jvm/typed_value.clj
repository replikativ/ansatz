(ns ansatz.lean.jvm.typed-value
  "Immutable Clojure views of detached typed values. Descriptors describe values;
  only the Java typed-storage boundary validates and admits storage."
  (:import [ansatz.lean.jvm LeanType LeanData LeanBytes LeanChoice LeanUnit]
           [java.util Optional Iterator List Map ArrayDeque IdentityHashMap]))

(declare view unwrap materialize host-value collection-equal collection-hash genuine-view?)

(defprotocol ^:private BackedValue
  (backing-value [value])
  (backing-type [value]))

(defn unwrap
  "Return a genuine view's original detached Java carrier; leave other values alone."
  [value]
  (if (genuine-view? value) (backing-value value) value))

(defn- map-like? [x] (instance? Map x))

(defn- ordered? [x] (or (sequential? x) (instance? List x)))

(defn collection-equal
  "Stack-safe Clojure collection equivalence, including ordinary collections."
  ([left right] (collection-equal left right true))
  ([left right equiv?]
  (loop [pending (list [left right]) work 0]
    (when (> work 1000000) (throw (IllegalArgumentException. "Equality exceeds value bound")))
    (if-let [[a b] (first pending)]
      (cond
        (identical? a b) (recur (next pending) (inc work))
        (map-like? a)
        (if (and (map-like? b) (= (count a) (count b)))
          (let [pairs (reduce (fn [pairs [k v]]
                               (if (contains? b k) (conj pairs [v (get b k)])
                                   (reduced ::different))) [] a)]
            (if (= ::different pairs) false
                (recur (into (next pending) pairs) (inc work)))) false)
        (ordered? a)
        (if (ordered? b)
          ;; Keep sequence cursors on the work stack; List iteration stays linear.
          (let [sa (seq a) sb (seq b)]
            (cond (and (nil? sa) (nil? sb)) (recur (next pending) (inc work))
                  (or (nil? sa) (nil? sb)) false
                  :else (recur (conj (next pending) [(next sa) (next sb)] [(first sa) (first sb)]) (inc work))))
          false)
        :else (if (if equiv? (clojure.lang.Util/equiv a b) (clojure.lang.Util/equals a b)) (recur (next pending) (inc work)) false))
      true))))

(defn collection-hash
  "Iterative ordinary Clojure hasheq (or Java collection hashCode)."
  ([value] (collection-hash value true))
  ([value hasheq?]
   (loop [tasks [[:visit value]] results [] work 0]
     (when (> work 1000000) (throw (IllegalArgumentException. "Hash exceeds value bound")))
     (if-let [[op x n] (peek tasks)]
       (case op
         :visit
         (cond
           (map? x)
           (let [entries (vec x)]
             (recur (into (conj (pop tasks) [:map nil (count x)])
                          (mapcat (fn [[k v]] [[:visit v] [:visit k]]) (rseq entries)))
                    results (inc work)))
           (ordered? x)
           (let [items (vec (seq x))]
             (recur (into (conj (pop tasks) [:ordered nil (count items)])
                          (map (fn [v] [:visit v]) (rseq items))) results (inc work)))
           :else (recur (pop tasks) (conj results (if hasheq? (clojure.lang.Util/hasheq x) (clojure.lang.Util/hash x))) (inc work)))
         :ordered
         (let [start (- (count results) n)
               h (reduce (fn [h v] (unchecked-add-int (unchecked-multiply-int 31 h) v))
                         1 (subvec results start))]
           (recur (pop tasks) (conj (subvec results 0 start) (if hasheq? (clojure.lang.Murmur3/mixCollHash h n) h)) (inc work)))
         :map
         (let [start (- (count results) (* 2 n))
               h (reduce (fn [h [k v]]
                           (unchecked-add-int h (if hasheq?
                             (clojure.lang.Murmur3/mixCollHash (unchecked-add-int (unchecked-multiply-int 31 (unchecked-add-int 31 k)) v) 2)
                             (bit-xor k v))))
                         0 (partition 2 (subvec results start)))]
           (recur (pop tasks) (conj (subvec results 0 start) (if hasheq? (clojure.lang.Murmur3/mixCollHash h n) h)) (inc work))))
       (peek results)))))

(defn- map-keys [^LeanType type source]
  (case (.name (.kind type))
    "NOMINAL" [:lean/type :lean/constructor :lean/fields]
    "OPTION" [:some]
    "SUM" [(if (.isLeft ^LeanChoice source) :left :right)]
    "EXCEPT" [(if (.isLeft ^LeanChoice source) :error :ok)]))

(declare indexed-view)
(defn- map-value [^LeanType type source k missing]
  (case (.name (.kind type))
    "NOMINAL"
    (case k
      :lean/type (.orElseThrow (.nominalId type))
      :lean/constructor (.name (.constructor ^LeanData source))
      :lean/fields (indexed-view nil (.fields ^LeanData source)
                                (mapv #(.type ^ansatz.lean.jvm.LeanType$Field %) (.fields (.constructor ^LeanData source))))
      missing)
    "OPTION" (if (= k :some) (view (first (.arguments type)) (.get ^Optional source)) missing)
    (if (= k (first (map-keys type source)))
      (view (.get (.arguments type) (if (.isLeft ^LeanChoice source) 0 1)) (.value ^LeanChoice source)) missing)))

;; deftype classes are final. Explicit clojure.lang.IFn methods also preserve wrong-arity behavior.
(defmacro ^:private define-map-view []
  `(deftype ~'TypedMap [~'^LeanType type ~'source ~'metadata]
     BackedValue (~'backing-value [~'_] ~'source) (~'backing-type [~'_] ~'type)
     clojure.lang.IMeta (~'meta [~'_] ~'metadata)
     clojure.lang.IObj (~'withMeta [~'_ ~'m] (~'TypedMap. ~'type ~'source ~'m))
     clojure.lang.Counted (~'count [~'_] (count (map-keys ~'type ~'source)))
     clojure.lang.ILookup
     (~'valAt [~'_ ~'k] (map-value ~'type ~'source ~'k nil))
     (~'valAt [~'_ ~'k ~'missing] (map-value ~'type ~'source ~'k ~'missing))
     clojure.lang.Associative
     (~'containsKey [~'_ ~'k] (boolean (some #(= ~'k %) (map-keys ~'type ~'source))))
     (~'entryAt [~'this ~'k] (when (.containsKey ~'this ~'k) (clojure.lang.MapEntry/create ~'k (.valAt ~'this ~'k))))
     (~'assoc [~'this ~'k ~'v] (assoc (with-meta (into {} ~'this) ~'metadata) ~'k ~'v))
     clojure.lang.IPersistentMap
     (~'assocEx [~'this ~'k ~'v] (if (.containsKey ~'this ~'k) (throw (RuntimeException. "Key already present")) (.assoc ~'this ~'k ~'v)))
     (~'without [~'this ~'k] (dissoc (with-meta (into {} ~'this) ~'metadata) ~'k))
     clojure.lang.IPersistentCollection
     (~'cons [~'this ~'v] (conj (with-meta (into {} ~'this) ~'metadata) ~'v))
     (~'empty [~'_] (with-meta {} ~'metadata))
     (~'equiv [~'this ~'other] (collection-equal ~'this ~'other))
     clojure.lang.IKVReduce
     (~'kvreduce [~'this ~'f ~'init]
       (loop [~'ks (seq (map-keys ~'type ~'source)) ~'acc ~'init]
         (if ~'ks
           (let [~'k (first ~'ks) ~'result (~'f ~'acc ~'k (.valAt ~'this ~'k))]
             (if (reduced? ~'result) @~'result (recur (next ~'ks) ~'result)))
           ~'acc)))
     clojure.lang.Seqable (~'seq [~'_] (seq (map #(clojure.lang.MapEntry/create % (map-value ~'type ~'source % nil)) (map-keys ~'type ~'source))))
     clojure.lang.MapEquivalence
     java.util.Map
     (~'size [~'this] (count ~'this))
     (~'isEmpty [~'_] false)
     (~'get [~'this ~'k] (.valAt ~'this ~'k))
     (~'containsValue [~'this ~'v] (boolean (some #(clojure.lang.Util/equals ~'v %) (vals ~'this))))
     (~'keySet [~'this] (java.util.Collections/unmodifiableSet (set (keys ~'this))))
     (~'values [~'this] (java.util.Collections/unmodifiableList (vec (vals ~'this))))
     (~'entrySet [~'this] (java.util.Collections/unmodifiableSet (set (seq ~'this))))
     (~'put [~'_ ~'k ~'v] (throw (UnsupportedOperationException. "Immutable view")))
     (~'remove [~'_ ~'k] (throw (UnsupportedOperationException. "Immutable view")))
     (~'putAll [~'_ ~'m] (throw (UnsupportedOperationException. "Immutable view")))
     (~'clear [~'_] (throw (UnsupportedOperationException. "Immutable view")))
     java.lang.Iterable (~'iterator [~'this] (clojure.lang.SeqIterator. (seq ~'this)))
     clojure.lang.IHashEq (~'hasheq [~'this] (int (collection-hash ~'this)))
     clojure.lang.IFn
     ~@(for [n (range 21)]
         (let [args (mapv #(symbol (str "a" %)) (range n))]
           `(~'invoke [~'this ~@args]
             ~(case n
                1 `(.valAt ~'this ~(first args))
                2 `(.valAt ~'this ~(first args) ~(second args))
                `(throw (clojure.lang.ArityException. ~n "typed-value-map"))))))
     (~'invoke [~'this ~@(map #(symbol (str "a" %)) (range 20)) ~'^objects rest]
       (throw (clojure.lang.ArityException. (+ 20 (alength ~'rest)) "typed-value-map")))
     (~'call [~'this] (.invoke ~'this))
     (~'run [~'this] (.invoke ~'this))
     (~'applyTo [~'this ~'args] (case (bounded-count 3 ~'args) 1 (.valAt ~'this (first ~'args)) 2 (.valAt ~'this (first ~'args) (second ~'args)) (throw (clojure.lang.ArityException. (count ~'args) "typed-value-map"))))
     Object
     (~'equals [~'this ~'other] (collection-equal ~'this ~'other false))
     (~'hashCode [~'this] (int (collection-hash ~'this false)))
     (~'toString [~'_] "#<immutable Lean map view>")))
(define-map-view)

(defn- read-index [^LeanType type ^List source types i]
  (view (if types (nth types i) (first (.arguments type))) (.get source i)))
(defn- index-seq [^LeanType type ^List source types]
  (let [^Iterator cursor (.iterator source)]
    (map-indexed (fn [i value] (view (if types (nth types i) (first (.arguments type))) value))
                 (iterator-seq cursor))))

(deftype TypedVector [^LeanType type ^List source types metadata]
  BackedValue (backing-value [_] source) (backing-type [_] type)
  clojure.lang.IMeta (meta [_] metadata)
  clojure.lang.IObj (withMeta [_ m] (TypedVector. type source types m))
  clojure.lang.Counted (count [_] (.size source))
  clojure.lang.Indexed
  (nth [_ i] (read-index type source types i))
  (nth [_ i missing] (if (< -1 i (.size source)) (read-index type source types i) missing))
  clojure.lang.ILookup
  (valAt [this k] (.valAt this k nil))
  (valAt [this k missing] (if (and (integer? k) (< -1 k (.size source))) (nth this (int k)) missing))
  clojure.lang.Associative
  (containsKey [_ k] (and (integer? k) (< -1 k (.size source))))
  (entryAt [this k] (when (.containsKey this k) (clojure.lang.MapEntry/create k (get this k))))
  (assoc [this k v] (assoc (with-meta (vec (seq this)) metadata) k v))
  clojure.lang.IPersistentVector
  (assocN [this i v] (assoc (with-meta (vec (seq this)) metadata) i v))
  (length [_] (.size source))
  clojure.lang.IPersistentStack
  (peek [this] (when (pos? (.size source)) (nth this (dec (.size source)))))
  (pop [this] (pop (with-meta (vec (seq this)) metadata)))
  clojure.lang.IPersistentCollection
  (cons [this v] (conj (with-meta (vec (seq this)) metadata) v))
  (empty [_] (with-meta [] metadata))
  (equiv [this other] (collection-equal this other))
  clojure.lang.Sequential
  clojure.lang.Seqable (seq [_] (seq (index-seq type source types)))
  clojure.lang.Reversible (rseq [this] (rseq (with-meta (vec (seq this)) metadata)))
  java.lang.Iterable (iterator [_] (.iterator ^Iterable (index-seq type source types)))
  java.util.List
  (size [_] (.size source))
  (isEmpty [_] (.isEmpty source))
  (get [_ i] (read-index type source types i))
  (contains [this v] (boolean (some #(clojure.lang.Util/equals % v) (seq this))))
  (containsAll [this values] (every? #(.contains this %) values))
  (^objects toArray [this] (.toArray ^List (vec (seq this))))
  (^objects toArray [this ^objects array] (.toArray ^List (vec (seq this)) array))
  (indexOf [this v] (.indexOf ^List (vec (seq this)) v))
  (lastIndexOf [this v] (.lastIndexOf ^List (vec (seq this)) v))
  (listIterator [this] (.listIterator ^List (vec (seq this))))
  (listIterator [this i] (.listIterator ^List (vec (seq this)) i))
  (subList [this start end] (.subList ^List (vec (seq this)) start end))
  (add [_ v] (throw (UnsupportedOperationException. "Immutable view")))
  (add [_ i v] (throw (UnsupportedOperationException. "Immutable view")))
  (addAll [_ values] (throw (UnsupportedOperationException. "Immutable view")))
  (addAll [_ i values] (throw (UnsupportedOperationException. "Immutable view")))
  (set [_ i v] (throw (UnsupportedOperationException. "Immutable view")))
  (^Object remove [_ ^int i] (throw (UnsupportedOperationException. "Immutable view")))
  (^boolean remove [_ ^Object v] (throw (UnsupportedOperationException. "Immutable view")))
  (removeAll [_ values] (throw (UnsupportedOperationException. "Immutable view")))
  (retainAll [_ values] (throw (UnsupportedOperationException. "Immutable view")))
  (clear [_] (throw (UnsupportedOperationException. "Immutable view")))
  clojure.lang.IHashEq (hasheq [this] (int (collection-hash this)))
  clojure.lang.IFn
  (invoke [this ] (throw (clojure.lang.ArityException. 0 "typed-value-vector")))
  (invoke [this a0] (if (integer? a0) (nth this (int a0)) (throw (IllegalArgumentException. "Key must be integer"))))
  (invoke [this a0 a1] (throw (clojure.lang.ArityException. 2 "typed-value-vector")))
  (invoke [this a0 a1 a2] (throw (clojure.lang.ArityException. 3 "typed-value-vector")))
  (invoke [this a0 a1 a2 a3] (throw (clojure.lang.ArityException. 4 "typed-value-vector")))
  (invoke [this a0 a1 a2 a3 a4] (throw (clojure.lang.ArityException. 5 "typed-value-vector")))
  (invoke [this a0 a1 a2 a3 a4 a5] (throw (clojure.lang.ArityException. 6 "typed-value-vector")))
  (invoke [this a0 a1 a2 a3 a4 a5 a6] (throw (clojure.lang.ArityException. 7 "typed-value-vector")))
  (invoke [this a0 a1 a2 a3 a4 a5 a6 a7] (throw (clojure.lang.ArityException. 8 "typed-value-vector")))
  (invoke [this a0 a1 a2 a3 a4 a5 a6 a7 a8] (throw (clojure.lang.ArityException. 9 "typed-value-vector")))
  (invoke [this a0 a1 a2 a3 a4 a5 a6 a7 a8 a9] (throw (clojure.lang.ArityException. 10 "typed-value-vector")))
  (invoke [this a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10] (throw (clojure.lang.ArityException. 11 "typed-value-vector")))
  (invoke [this a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11] (throw (clojure.lang.ArityException. 12 "typed-value-vector")))
  (invoke [this a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12] (throw (clojure.lang.ArityException. 13 "typed-value-vector")))
  (invoke [this a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13] (throw (clojure.lang.ArityException. 14 "typed-value-vector")))
  (invoke [this a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14] (throw (clojure.lang.ArityException. 15 "typed-value-vector")))
  (invoke [this a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15] (throw (clojure.lang.ArityException. 16 "typed-value-vector")))
  (invoke [this a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16] (throw (clojure.lang.ArityException. 17 "typed-value-vector")))
  (invoke [this a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17] (throw (clojure.lang.ArityException. 18 "typed-value-vector")))
  (invoke [this a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18] (throw (clojure.lang.ArityException. 19 "typed-value-vector")))
  (invoke [this a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19] (throw (clojure.lang.ArityException. 20 "typed-value-vector")))
  (invoke [this a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 ^objects rest] (throw (clojure.lang.ArityException. (+ 20 (alength rest)) "typed-value-vector")))
  (call [this] (.invoke this))
  (run [this] (.invoke this))
  (applyTo [this args] (if (= 1 (bounded-count 2 args)) (.invoke this (first args)) (throw (clojure.lang.ArityException. (count args) "typed-value-vector"))))
  Object
  (equals [this other] (collection-equal this other false))
  (hashCode [this] (int (collection-hash this false)))
  (toString [_] "#<immutable Lean indexed view>"))

(defn- genuine-view? [value]
  (or (instance? TypedMap value) (instance? TypedVector value)))

(defn- indexed-view [type source types] (TypedVector. type source types nil))

(defn view
  "Expose a detached Java value under its closed type without copying its payload."
  [^LeanType type value]
  (if (genuine-view? value) value
      (case (.name (.kind type))
        "NOMINAL" (TypedMap. type value nil)
        "OPTION" (when (.isPresent ^Optional value) (TypedMap. type value nil))
        ("SUM" "EXCEPT") (TypedMap. type value nil)
        ("LIST" "ARRAY") (indexed-view type value nil)
        "PRODUCT" (indexed-view type value (.arguments type))
        "UNIT" nil
        "CHAR" (let [cp (int value)] (if (<= cp 65535) (char cp) cp))
        value)))

(defn- require-value [ok message]
  (when (.isInterrupted (Thread/currentThread))
    (throw (java.util.concurrent.CancellationException. "Typed value conversion interrupted")))
  (when-not ok (throw (IllegalArgumentException. message))))

(def ^:private java-sequence-class
  (Class/forName "ansatz.lean.jvm.ValueBridge$Sequence" false (.getClassLoader LeanType)))
(def ^:private java-fields-class
  (Class/forName "ansatz.lean.jvm.ValueBridge$Fields" false (.getClassLoader LeanType)))

(defn- java-indexed-view? [value]
  (let [klass (class value)]
    (or (identical? klass java-sequence-class) (identical? klass java-fields-class))))

(defn- bounded-vector [value]
  (require-value (or (sequential? value) (instance? List value)) "Expected ordered fields/elements")
  (loop [xs (seq value) result (transient []) n 0]
    (if xs
      (do (require-value (< n 100000) "Container exceeds value bound")
          (recur (next xs) (conj! result (first xs)) (inc n)))
      (persistent! result))))

(defn- host-shape [^LeanType type value]
  (let [arguments (.arguments type)]
    (case (.name (.kind type))
      "NOMINAL"
      (do (require-value (and (map? value) (= #{:lean/type :lean/constructor :lean/fields} (set (keys value)))) "Invalid nominal map keys")
          (require-value (= (.orElseThrow (.nominalId type)) (:lean/type value)) "Nominal identity mismatch")
          (let [constructor (.constructor type (:lean/constructor value))
                fields (bounded-vector (:lean/fields value))
                types (mapv #(.type ^ansatz.lean.jvm.LeanType$Field %) (.fields constructor))]
            (require-value (= (count fields) (count types)) "Wrong constructor arity")
            [fields types (fn [xs] {"lean/type" (:lean/type value) "lean/constructor" (:lean/constructor value) "lean/fields" xs})]))
      ("LIST" "ARRAY" "PRODUCT")
      (let [values (bounded-vector value)
            types (if (= "PRODUCT" (.name (.kind type))) (vec arguments) (vec (repeat (count values) (first arguments))))]
        (require-value (= (count types) (count values)) "Product requires two fields")
        [values types identity])
      "OPTION"
      (cond
        (nil? value) [[] [] (fn [_] (Optional/empty))]
        (and (map? value) (= #{:some} (set (keys value))))
        [[(:some value)] [(first arguments)] (fn [xs] (Optional/of (first xs))) ]
        (instance? Optional value)
        (if (.isPresent ^Optional value)
          [[(.get ^Optional value)] [(first arguments)] (fn [xs] (Optional/of (first xs)))]
          [[] [] (fn [_] value)])
        :else (throw (IllegalArgumentException. "Option expects nil or {:some value}")))
      ("SUM" "EXCEPT")
      (let [[a b] (if (= "SUM" (.name (.kind type))) [:left :right] [:error :ok])
            java? (instance? LeanChoice value)
            left? (if java? (.isLeft ^LeanChoice value) (contains? value a))
            key (if left? a b)]
        (require-value (or java? (and (map? value) (= #{key} (set (keys value))))) "Invalid Sum/Except branch tag")
        [[(if java? (.value ^LeanChoice value) (get value key))] [(.get arguments (if left? 0 1))]
         (fn [xs] (if left? (LeanChoice/left (first xs)) (LeanChoice/right (first xs))))])
      nil)))

(defn host-value
  "Convert ordinary Clojure input under a detached closed type. Genuine views
  unwrap before traversal, preserving certified storage. LeanType.create remains
  the authority for construction, type/range validation and storage admission."
  [^LeanType type value]
  (let [memo (IdentityHashMap.) active (IdentityHashMap.)]
    (loop [tasks [[:visit type value 0]] results [] work 0]
      (require-value (<= work 100000) "Host conversion exceeds value bound")
      (if-let [[op ^LeanType t v depth extra] (peek tasks)]
        (case op
          :visit
          (do
            (require-value (<= depth 1024) "Host conversion exceeds depth bound")
            (let [typed? (genuine-view? v)
                  known (some-> (.get memo v) (get t))]
              (cond
                typed?
                (do (when-let [actual (backing-type v)] (require-value (= actual t) "Typed view type mismatch"))
                    (recur (pop tasks) (conj results (backing-value v)) (inc work)))
                known (recur (pop tasks) (conj results known) (inc work))
                (or (instance? LeanData v) (instance? LeanBytes v) (java-indexed-view? v))
                (recur (pop tasks) (conj results v) (inc work))
                :else
                (if-let [[values types finish] (host-shape t v)]
                  (do
                    (require-value (not (contains? (or (.get active v) #{}) t)) "Cyclic host value")
                    (.put active v (conj (or (.get active v) #{}) t))
                    (recur (into (conj (pop tasks) [:finish t v depth [(count values) finish]])
                                 (map (fn [ct cv] [:visit ct cv (inc depth)]) (rseq types) (rseq values)))
                           results (inc work)))
                  (let [scalar (case (.name (.kind t))
                                 "UNIT" (do (require-value (or (nil? v) (identical? v LeanUnit/INSTANCE)) "Unit expects nil") LeanUnit/INSTANCE)
                                 "CHAR" (cond (char? v) (int v)
                                              (instance? clojure.lang.BigInt v) (.toBigInteger ^clojure.lang.BigInt v)
                                              :else v)
                                 ("NAT" "INT" "MACHINE_INT" "WORD") (if (instance? clojure.lang.BigInt v) (.toBigInteger ^clojure.lang.BigInt v) v)
                                 v)]
                    (recur (pop tasks) (conj results scalar) (inc work)))))))
          :finish
          (let [[n finish] extra start (- (count results) n)
                result (finish (into [] (subvec results start)))]
            (.put active v (disj (.get active v) t))
            (.put memo v (assoc (or (.get memo v) {}) t result))
            (recur (pop tasks) (conj (subvec results 0 start) result) (inc work))))
        (peek results)))))

(defn materialize
  "Explicitly copy a view into ordinary Clojure maps/vectors. LeanBytes becomes
  a fresh byte array; Unit remains nil and Option Unit remains {:some nil}."
  [value]
  (let [memo (IdentityHashMap.) active (IdentityHashMap.)]
    (loop [tasks [[:visit value 0]] results [] work 0]
      (require-value (<= work 100000) "Materialization exceeds value bound")
      (if-let [[op v depth n finish] (peek tasks)]
        (case op
          :visit
          (do (require-value (<= depth 1024) "Materialization exceeds depth bound")
              (cond
                (.containsKey memo v) (recur (pop tasks) (conj results (.get memo v)) (inc work))
                (or (map? v) (ordered? v))
                (let [map-value? (map? v)
                      keys (when map-value? (vec (keys v)))
                      children (if map-value? (mapv #(get v %) keys) (bounded-vector v))
                      finish (if map-value? #(zipmap keys %) identity)]
                  (require-value (not (.containsKey active v)) "Cyclic materialization input")
                  (.put active v true)
                  (recur (into (conj (pop tasks) [:finish v depth (count children) finish])
                               (map #(vector :visit % (inc depth)) (rseq children))) results (inc work)))
                :else (recur (pop tasks) (conj results (if (instance? LeanBytes v) (.toByteArray ^LeanBytes v) v)) (inc work))))
          :finish
          (let [start (- (count results) n) result (finish (into [] (subvec results start)))]
            (.remove active v) (.put memo v result)
            (recur (pop tasks) (conj (subvec results 0 start) result) (inc work))))
        (peek results)))))
