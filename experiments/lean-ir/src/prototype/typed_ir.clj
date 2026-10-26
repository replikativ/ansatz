(ns prototype.typed-ir
  "Demand-only producer facts. Node IDs describe producer IR, never executable PCs."
  (:require [prototype.fingerprint :as fingerprint]
            [prototype.machine :as m]))

(defn type! [ty]
  (when-not (contains? #{"erased" "object" "tobject" "tagged" "void" "uint8" "uint16" "uint32" "uint64" "usize" "float" "float32"} ty)
    (m/fail "Unsupported imported runtime type" {:type ty})))

(defn- natural! [n]
  (when-not (and (integer? n) (<= 0 n Integer/MAX_VALUE))
    (m/fail "Invalid typed producer ID or index" {:value n}))
  n)

(defn- boolean! [b]
  (when-not (boolean? b) (m/fail "Missing typed ownership or RC annotation" {:value b}))
  b)

(defn- parameters [xs]
  (when-not (vector? xs) (m/fail "Invalid typed parameters" {}))
  (let [ps (mapv (fn [p] (type! (:ty p))
                   {:id (natural! (get-in p [:x :idx])) :type (:ty p)
                    :borrow (boolean! (:borrow p))}) xs)]
    (when-not (= (count ps) (count (set (map :id ps))))
      (m/fail "Duplicate typed parameter" {}))
    ps))

(defn- plain! [value]
  ;; Reject opaque/mutable values before hashing: no JVM identity or raw owner
  ;; can escape in a source key. Body children have already become digests.
  (loop [pending [value]]
    (when (seq pending)
      (let [x (peek pending) pending (pop pending) c (class x)]
        (cond
          (or (nil? x) (string? x) (keyword? x) (boolean? x) (contains? #{Byte Short Integer Long Float Double java.math.BigInteger java.math.BigDecimal clojure.lang.BigInt clojure.lang.Ratio} c)) (recur pending)
          (or (= c clojure.lang.PersistentArrayMap) (= c clojure.lang.PersistentHashMap))
          (do (when (contains? x :idx) (natural! (:idx x)))
              (recur (into pending (mapcat identity x))))
          (= c clojure.lang.PersistentVector) (recur (into pending x))
          :else (m/fail "Typed source requires immutable producer data" {:class (some-> c .getName)})))))
  value)

(defn- name! [name]
  (loop [part name]
    (when-not (= (class part) clojure.lang.PersistentVector)
      (m/fail "Invalid typed producer name" {}))
    (case (first part)
      "anonymous" (when-not (= 1 (count part)) (m/fail "Invalid typed producer name" {}))
      "str" (do (when-not (and (= 3 (count part)) (string? (nth part 2)))
                  (m/fail "Invalid typed producer name" {}))
                (recur (second part)))
      "num" (do (when-not (and (= 3 (count part))
                               (or (and (integer? (nth part 2)) (not (neg? (nth part 2))))
                                   (and (string? (nth part 2)) (re-matches #"0|[1-9][0-9]*" (nth part 2)))))
                  (m/fail "Invalid typed producer name" {}))
                (recur (second part)))
      (m/fail "Invalid typed producer name" {})))
  name)

(defn- operand! [arg]
  (when-not (= "erased" arg)
    (when-not (and (map? arg) (= #{:var} (set (keys arg)))
                   (= #{:id} (set (keys (:var arg))))
                   (= #{:idx} (set (keys (get-in arg [:var :id])))))
      (m/fail "Invalid typed operand" {}))
    (natural! (get-in arg [:var :id :idx]))))

(defn- operands! [args]
  (when-not (vector? args) (m/fail "Invalid typed operands" {}))
  (doseq [a args] (operand! a)))

(defn- expression! [expr]
  (when-not (and (map? expr) (= 1 (count expr))) (m/fail "Invalid typed expression" {}))
  (let [[op data] (first expr)]
    (case op
      (:fap :pap) (do (name! (:c data)) (operands! (:ys data)))
      :ap (do (natural! (get-in data [:x :idx])) (operands! (:ys data)))
       :ctor (let [i (:i data)]
              (when-not (and (map? i) (every? #(and (integer? %) (<= 0 % 1048576)) (map i [:size :usize :ssize]))
                             (< (:size i) 256) (< (+ (* 8 (:usize i)) (:ssize i)) 1024))
                (m/fail "Invalid constructor layout" {:layout i}))
              (natural! (:cidx i)) (operands! (:ys data))
              (when-not (= (:size i) (count (:ys data))) (m/fail "Constructor field count mismatch" {:constructor data})))
      (:proj :uproj) (do (natural! (get-in data [:x :idx])) (natural! (:i data)))
      :sproj (do (natural! (get-in data [:x :idx])) (natural! (:n data)) (natural! (:offset data)))
      (:unbox :isShared) (natural! (get-in data [:x :idx]))
      :box (do (type! (:ty data)) (natural! (get-in data [:x :idx])))
      :lit (let [v (:v data)]
             (cond
               (= #{:num} (set (keys v))) (let [n (get-in v [:num :v])]
                                           (when-not (and (integer? n) (not (neg? n)))
                                             (m/fail "Invalid typed literal" {})))
               (= #{:str} (set (keys v))) (when-not (string? (get-in v [:str :v])) (m/fail "Invalid typed literal" {}))
               :else (m/fail "Invalid typed literal" {})))
      (m/fail "Unsupported typed expression" {:op op}))))

(defn- node-shape [node]
  (when-not (= (class node) clojure.lang.PersistentVector)
    (m/fail "Invalid typed producer instruction" {}))
  (let [[op a b c d e f] node
        arity (get {"vdecl" 5 "jdecl" 5 "case" 5 "del" 3 "setTag" 4
                    "inc" 6 "dec" 6 "set" 5 "uset" 5 "sset" 7
                    "jmp" 3 "ret" 2 "unreachable" 1} op)]
    (when-not (= arity (count node)) (m/fail "Invalid typed producer instruction" {:op op}))
    (case op
      "vdecl" (do (type! b) (expression! c) {:children [d] :payload (assoc node 4 nil)
                             :facts {:op :vdecl :id (natural! (:idx a)) :type b}})
      "jdecl" {:children [c d] :payload (assoc node 3 nil 4 nil)
                :facts {:op :jdecl :join-id (natural! (:idx a)) :params (parameters b)}}
      "case" (do (type! c) (name! a)
                 (when-not (vector? d) (m/fail "Invalid typed alternatives" {}))
                 (let [alts (mapv (fn [alt]
                                    (when-not (and (vector? alt)
                                                   (or (and (= "ctor" (first alt)) (= 3 (count alt)))
                                                       (and (= "default" (first alt)) (= 2 (count alt)))))
                                      (m/fail "Invalid typed alternative" {}))
                                    (if (= "ctor" (first alt))
                                      {:child (nth alt 2) :payload (assoc alt 2 nil)
                                       :tag (natural! (:cidx (second alt)))}
                                      {:child (second alt) :payload (assoc alt 1 nil) :tag :default})) d)]
                   {:children (mapv :child alts) :payload (assoc node 4 (mapv :payload alts))
                    :facts {:op :case :scrutinee-id (natural! (:idx b)) :type c
                            :name a :alternatives (mapv :tag alts)}}))
      ("inc" "dec") {:children [e] :payload (assoc node 5 nil)
                       :facts {:op (keyword op) :id (natural! (:idx a)) :count (natural! b)
                               :check (boolean! c) :persistent (boolean! d)}}
      "del" {:children [b] :payload (assoc node 2 nil) :facts {:op :del :id (natural! (:idx a))}}
      "setTag" {:children [c] :payload (assoc node 3 nil)
                 :facts {:op :set-tag :id (natural! (:idx a)) :tag (natural! b)}}
      ("set" "uset") (do (if (= op "set") (operand! c) (natural! (:idx c)))
                       {:children [d] :payload (assoc node 4 nil)
                        :facts {:op (keyword op) :id (natural! (:idx a)) :index (natural! b)}})
      "sset" (do (type! e) (natural! (:idx d)) {:children [f] :payload (assoc node 6 nil)
                             :facts {:op :sset :id (natural! (:idx a)) :index (natural! b)
                                     :offset (natural! c) :type e}})
      "jmp" (do (operands! b) {:children [] :payload node :facts {:op :jmp :join-id (natural! (:idx a))}})
      "ret" (do (operand! a) {:children [] :payload node :facts {:op :ret}})
      "unreachable" {:children [] :payload node :facts {:op :unreachable}})))

(defn companion
  "Extract one selected fdecl. Identity-memoized postorder preserves producer DAG
   sharing. Only compact facts and Merkle keys survive; no raw row/body is held."
  [fdecl]
  (type! (:type fdecl))
  (name! (:f fdecl))
  (let [signature {:params (parameters (:xs fdecl)) :result-type (:type fdecl)}
        root (:body fdecl) cache (java.util.IdentityHashMap.)
        visiting (java.util.IdentityHashMap.) pending (java.util.ArrayDeque.)
        nodes (java.util.ArrayList.)]
    (.addLast pending (object-array [root nil]))
    (while (not (.isEmpty pending))
      (let [entry ^objects (.removeLast pending) node (aget entry 0) shape (aget entry 1)]
        (when-not (.containsKey cache node)
          (if shape
            (let [children (mapv #(.get cache %) (:children shape))
                  payload (plain! (:payload shape))
                  digest (fingerprint/uncached-key [payload (mapv :digest children)])
                  id (.size nodes)]
              (.add nodes (assoc (:facts shape) :children (mapv :id children)))
              (.put cache node {:id id :digest digest})
              (.remove visiting node))
            (do
              (when (.containsKey visiting node) (m/fail "Cyclic typed producer body" {}))
              (.put visiting node true)
              (let [shape (node-shape node)]
                (.addLast pending (object-array [node shape]))
                (doseq [child (rseq (:children shape))]
                  (when-not (.containsKey cache child)
                    (.addLast pending (object-array [child nil]))))))))))
    (let [header (plain! (dissoc fdecl :body)) source (.get cache root)]
      {:schema "lean-typed-companion/1" :node-space :producer-ir
       :source-key (fingerprint/uncached-key [header (:digest source)])
       :signature signature :root (:id source) :nodes (vec nodes)})))

(defn- executable-key [root]
  ;; Local identity memo only. The key is separate from legacy fingerprints;
  ;; complete opaque-literal identity guards are propagated, never discarded.
  (let [cache (java.util.IdentityHashMap.) pending (java.util.ArrayDeque.)]
    (.addLast pending (object-array [root nil]))
    (while (not (.isEmpty pending))
      (let [entry ^objects (.removeLast pending) x (aget entry 0) children (aget entry 1)]
        (when (and (not (record? x)) (or (map? x) (vector? x))
                   (not (contains? #{clojure.lang.PersistentArrayMap clojure.lang.PersistentHashMap
                                     clojure.lang.PersistentVector} (class x))))
          (m/fail "Typed key requires immutable executable containers" {}))
        (when-not (.containsKey cache x)
          (if children
            (let [ks (mapv #(.get cache %) children)
                  map-node? (map? x)
                  ds (if map-node? (sort (map vec (partition 2 (map first ks)))) (mapv first ks))
                  [digest _] (fingerprint/uncached-key [(if map-node? :map :vector) ds])]
              (.put cache x [digest (into #{} (mapcat second) ks)]))
            (if (and (not (record? x)) (or (map? x) (vector? x)))
              (let [children (if (map? x) (into [] (mapcat identity) x) x)]
                (.addLast pending (object-array [x children]))
                (doseq [child (rseq children)]
                  (when-not (.containsKey cache child) (.addLast pending (object-array [child nil])))))
              (.put cache x (fingerprint/uncached-key x)))))))
    (.get cache root)))

(defn typed-code-key
  "Explicit profile plus the complete executable function and producer facts.
   Per-call identity memo bounds shared executable DAGs; no root cache or raw
   producer row is retained. Metadata supplies no authority."
  [function profile]
  (when-not (= "lean-typed-companion/1" (get-in function [:typed-ir :schema]))
    (m/fail "Missing typed companion" {}))
  (plain! profile)
  (let [[body-digest opaque] (executable-key (dissoc function :typed-ir))
        [digest other] (fingerprint/uncached-key
                       [:typed-code/v1 profile body-digest (:typed-ir function)])]
    [digest (into opaque other)]))
