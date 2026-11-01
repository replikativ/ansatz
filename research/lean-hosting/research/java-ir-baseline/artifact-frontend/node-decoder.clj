(ns ansatz.research.ir.node-decoder-v1
  "Bounded research decoder. Borrowed storage only; no source/code authority."
  (:require [prototype.ir-value :as ir] [prototype.constructor-layout :as layout])
  (:import [java.util IdentityHashMap] [java.math BigInteger]
           [java.lang.reflect Field Method InvocationTargetException]))

(def defaults {:max-nodes 100000 :max-visits 1000000 :max-depth 10000
               :max-array 100000 :max-edges 1000000 :max-chars 2000000
               :max-nat-bits 4096 :max-output 1000000})
(defn- fail [code] (throw (ex-info (str "IR decoder: " (name code)) {:code code})))
(defn- validate-kind! [kind]
  ;; Validate before hashing a caller-supplied nested vector for typed memo use.
  (loop [k kind depth 0]
    (when (> depth 32) (fail :schema-depth))
    (cond
      (keyword? k)
      (when-not (contains? #{:nat :bool :string :name :var-id :join-id :arg :literal
                            :ctor-info :ir-type :expr :param :alt :body :decl-info
                            :extern-entry :extern-data :decl :witness-row :witness} k)
        (fail :schema-kind))
      (and (vector? k) (= 2 (count k)) (keyword? (nth k 0))
           (contains? #{:array :list :option} (nth k 0)))
      (recur (nth k 1) (inc depth))
      :else (fail :schema-kind))))
(defn- field [^Class c n] (doto (.getDeclaredField c n) (.setAccessible true)))
(defn- method [^Class c n types]
  (doto (.getDeclaredMethod c n (into-array Class types)) (.setAccessible true)))
(defn- call [^Method m target args]
  (try (.invoke m target (object-array args))
       (catch InvocationTargetException _ (fail :node-or-branch-invalid))))
(defn- stamp [s]
  (let [e (:engine s) fs (:engine-fields s)]
    (doseq [k ["closed" "disposed" "untrackedFailure" "advancing"]]
      (when (.getBoolean ^Field (get fs k) e) (fail :engine-not-borrowable)))
    (let [phase (.invoke ^Method (:phase s) e (object-array 0))]
      (when-not (contains? #{"idle" "running" "host-call" "code-call" "complete"} phase)
        (fail :engine-phase))
      {:phase phase
       :counts (mapv #(.get ^Field (get fs %) e)
                     ["instructions" "allocations" "stores" "retains" "releases" "shellDeletes"])
       :identities (mapv #(.get ^Field (get fs %) e)
                        ["program" "pc" "hostRequest" "codeRequest" "runtimeAction"])})))
(defn- live! [holder]
  (let [s @holder]
    (when-not s (fail :closed))
    (when-not (identical? (:thread s) (Thread/currentThread)) (fail :wrong-thread))
    (when (.isInterrupted (Thread/currentThread)) (fail :interrupted))
    (when (> (System/nanoTime) (:deadline-nanos s)) (fail :deadline))
    (let [a (:stamp s) b (stamp s)]
      (when-not (and (= (:phase a) (:phase b)) (= (:counts a) (:counts b))
                     (every? true? (map identical? (:identities a) (:identities b))))
        (fail :engine-progressed))) s))
(defn- charge! [s counters key amount maximum]
  (let [n (+ (get @counters key 0) amount)]
    (when (> n (get s maximum)) (fail maximum))
    (swap! counters assoc key n)))
(defn- node? [s v] (and (some? v) (identical? (:node-class s) (class v))))
(defn- guard-node! [s v]
  (call (:node-guard s) (:engine s) [v])
  (when (neg? (.getInt ^Field (get-in s [:node-fields "rc"]) v)) (fail :negative-rc)))
(defn- view! [holder views counters token world v]
  (when-not (identical? token world) (fail :foreign-scope))
  (let [s (live! holder) fs (:node-fields s)]
    (when-not (node? s v) (fail :node-class))
    (guard-node! s v)
    (or (.get ^IdentityHashMap views v)
        (let [array? (.getBoolean ^Field (get fs "array") v)
              _ (if array?
                  (when (or (.get ^Field (get fs "closure") v)
                            (.getBoolean ^Field (get fs "ref") v)
                            (.getBoolean ^Field (get fs "readyTask") v)) (fail :array-kind))
                  (do (call (:ctor-guard s) (:engine s) [v])
                      (when (.get ^Field (get fs "closure") v) (fail :closure))))
              fields ^objects (.get ^Field (get fs "fields") v)
              bytes ^bytes (.get ^Field (get fs "scalars") v)
              tag (.getInt ^Field (get fs "tag") v)
              n (if array? (int (call (:array-size s) v [])) (alength fields))
              extent (alength bytes)]
          (when-not (if array? (and (= tag 246) (zero? extent) (<= 0 n (alength fields) (:max-array s)))
                        (and (<= 0 tag 243) (< n 256) (< extent 1024))) (fail :storage-shape))
          (when (>= (.size ^IdentityHashMap views) (:max-nodes s)) (fail :max-nodes))
          (charge! s counters :edges (+ n extent) :max-edges)
          (let [base {:kind (if array? :array :ctor) :tag tag
                      :fields (mapv #(aget fields %) (range n))
                      :layout (when (pos? extent) {:objects n :usize 0 :ssize extent})
                      :scalar-bytes (into {} (map (fn [i] [(+ (* 8 n) i) (Byte/toUnsignedInt (aget bytes i))]) (range extent)))}
                result (if (and (not array?) (zero? (rem extent 8))) (layout/clone-storage base) base)]
            (.put ^IdentityHashMap views v result) result)))))
(defn- scalar! [s kind v]
  ;; Packed Bool children are synthesized Integers by the shared schema reader.
  (cond
    (and (= kind :bool) (contains? #{0 1} v)) nil
    (identical? Long (class v))
    (do (when (neg? (long v)) (fail :negative-nat))
        (when (> (- 64 (Long/numberOfLeadingZeros (long v))) (:max-nat-bits s))
          (fail :nat-bound)))
    (identical? BigInteger (class v))
    (when (or (neg? (.signum ^BigInteger v)) (> (.bitLength ^BigInteger v) (:max-nat-bits s))) (fail :nat-bound))
    (identical? String (class v)) (when (> (.length ^String v) (:max-chars s)) (fail :string-bound))
    :else (fail :scalar-class)))
(defn- leaf-chars [v]
  (cond (string? v) (.length ^String v)
        (instance? BigInteger v) (inc (long (Math/ceil (* 0.30103 (.bitLength ^BigInteger v)))))
        (integer? v) 20 :else 0))
(defn- metrics! [s depth children own-chars]
  ;; Expanded schema cost counts memo aliases again. Constant64 covers fixed JSON
  ;; keys/labels per schema node; it is a conservative bound, not serialized size.
  (let [units (inc (reduce + 0 (map :units children)))
        chars (+ 64 own-chars (reduce + 0 (map :chars children)))
        height (inc (reduce max 0 (map :height children)))]
    (when (> units (:max-output s)) (fail :max-output))
    (when (> chars (:max-chars s)) (fail :max-chars))
    (when (> (+ depth height -1) (:max-depth s)) (fail :max-depth))
    {:units units :chars chars :height height}))

(defn open-decoder
  "One paused invocation; close in finally before any guest/release/helper work.
   project accepts a typed schema kind. Own the root independently. Ordinary
   unstamped foreign Nodes cannot be universally recognized by engine guards."
  [basis engine limits]
  (when-not (and (map? limits) (every? (conj (set (keys defaults)) :deadline-nanos) (keys limits))
                 (integer? (:deadline-nanos limits)) (> (:deadline-nanos limits) (System/nanoTime)))
    (fail :limits))
  (let [limits (merge defaults limits)]
    (doseq [[k ceiling] defaults]
      (when-not (and (integer? (get limits k)) (<= 1 (get limits k) ceiling)) (fail :limits)))
    (when-not (identical? (:class basis) (class engine)) (fail :engine-class))
    (let [cls ^Class (:class basis) nc ^Class (:node-class basis)
          s (merge limits {:engine engine :thread (Thread/currentThread) :node-class nc
                           :engine-fields (into {} (map #(vector % (field cls %))
                             ["closed" "disposed" "untrackedFailure" "advancing" "instructions" "allocations" "stores" "retains" "releases" "shellDeletes" "program" "pc" "hostRequest" "codeRequest" "runtimeAction"]))
                           :node-fields (into {} (map #(vector % (field nc %)) ["rc" "array" "ref" "readyTask" "closure" "fields" "scalars" "tag"]))
                           :node-guard (method cls "node" [Object]) :ctor-guard (method cls "constructorNode" [Object])
                           :array-size (.getMethod nc "arraySize" (make-array Class 0))
                           :phase (.getMethod cls "phase" (make-array Class 0))})
          holder (atom (assoc s :stamp (stamp s))) token (Object.)
          views (IdentityHashMap.) memo (IdentityHashMap.) counters (atom {}) busy (atom false)
          read (ir/specification-reader
                 {:ref? #(and (some? %) (identical? nc (class %)))
                  :node #(view! holder views counters token %1 %2)} token)
          close! (fn [] (reset! holder nil) (.clear views) (.clear memo) nil)
          project
          (fn [kind value]
            (live! holder)
            (when-not (compare-and-set! busy false true) (fail :reentrant))
            (try
              (validate-kind! kind)
              (loop [todo [[:visit kind value 0]] results [] active (IdentityHashMap.)]
                (let [s (live! holder)]
                  (if (empty? todo)
                    (do (when-not (= 1 (count results)) (fail :result-stack)) (:value (peek results)))
                    (let [[op a b depth extra] (peek todo) todo (pop todo)]
                      (if (= op :visit)
                        (let [is-node (node? s b)
                              _ (charge! s counters :visits 1 :max-visits)
                              _ (when (> depth (:max-depth s)) (fail :max-depth))
                              _ (if is-node (guard-node! s b) (scalar! s a b))
                              cached (when is-node (get (.get memo b) a))]
                          (when (and is-node (contains? (or (.get active b) #{}) a)) (fail :cycle))
                          (if cached
                            (do (when (> (+ depth (:height cached) -1) (:max-depth s)) (fail :max-depth))
                                (recur todo (conj results cached) active))
                            (let [shape (read a b)]
                              (if (contains? shape :value)
                                (let [entry (assoc (metrics! s depth [] (leaf-chars (:value shape))) :value (:value shape))]
                                  (when is-node (.put memo b (assoc (or (.get memo b) {}) a entry)))
                                  (recur todo (conj results entry) active))
                                (let [children (:children shape)]
                                  (when-not (and (vector? children) (<= (count children) (:max-array s))) (fail :children-bound))
                                  (when (> (+ (count todo) (count children) 1) (:max-visits s)) (fail :stack-bound))
                                  (when is-node (.put active b (conj (or (.get active b) #{}) a)))
                                  (recur (into (conj todo [:finish a b depth [(:build shape) (count children)]])
                                               (map (fn [[k v]] [:visit k v (inc depth)]) (rseq children))) results active))))))
                        (let [[build n] extra start (- (count results) n)
                              children (subvec results start) metric (metrics! s depth children 0)
                              entry (assoc metric :value (build (mapv :value children)))]
                          (when (node? s b)
                            (.put active b (disj (.get active b) a))
                            (.put memo b (assoc (or (.get memo b) {}) a entry)))
                          (recur todo (conj (subvec results 0 start) entry) active)))))))
              (catch Exception e
                ;; Shared schema errors may include raw Node values. Do not retain
                ;; those through exception data/causes after scope closure.
                (let [code (or (:code (ex-data e)) :schema-rejected)]
                  (close!) (fail code)))
              (finally (reset! busy false))))]
      {:project project :close! close!
       :stats (fn [] (assoc @counters :open? (some? @holder) :views (.size views) :memo-nodes (.size memo)))})))
