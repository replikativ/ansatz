(ns ansatz.export.evidence
  "Scoped full-CI evidence from a captured store view. Validate the reachable raw
   Expr DAG before constructing any Exprs, then materialize only that DAG with an
   invocation-local cache. This is neither kernel admission nor an untrusted-file
   decoder: storage/PSS already deserializes CI shells, Names and Levels. Their
   reachable retained size is checked here, not the underlying PSS IO allocation."
  (:require [ansatz.export.types]
            [ansatz.kernel.constant-info :as constant-info])
  (:import [ansatz.kernel Name Level Expr ConstantInfo]
           [ansatz.export.types CIShell]
           [java.nio ByteBuffer]
           [java.nio.charset StandardCharsets CodingErrorAction]
           [java.util IdentityHashMap HashMap ArrayDeque]))

(def ^:private limit-keys
  #{:declarations :shell-items :expr-nodes :expr-edges :expr-depth :raw-bytes
    :name-nodes :name-chars :name-depth :level-nodes :level-depth})

(def ^:private shell-keys
  #{:tag :name :lps :type-id :value-id :unsafe? :hints :safety :all :quot-kind
    :num-params :num-indices :ctors :num-nested :is-rec :is-reflexive :is-unsafe
    :induct-name :cidx :num-fields :num-motives :num-minors :rules :is-k
    :ctor :nfields :rhs-id :regular})

(def ^:private required-variant-keys
  {0 #{:unsafe?}
   1 #{:value-id :hints :safety :all}
   2 #{:value-id :all}
   3 #{:value-id :all :unsafe?}
   4 #{:quot-kind}
   5 #{:num-params :num-indices :all :ctors :num-nested :is-rec :is-reflexive :is-unsafe}
   6 #{:induct-name :cidx :num-params :num-fields :is-unsafe}
   7 #{:all :num-params :num-indices :num-motives :num-minors :rules :is-k :is-unsafe}})

(defn- fail [message data]
  (throw (ex-info message (assoc data :type ::invalid-evidence))))

(defn- validate-limits! [limits]
  (when-not (and (map? limits) (= limit-keys (set (keys limits)))
                 (every? #(and (integer? %) (pos? %) (<= % Long/MAX_VALUE)) (vals limits))
                 ;; Existing Expr/Name/Level equality and some Expr constructors
                 ;; recurse. This profile deliberately refuses deeper evidence.
                 (every? #(<= (get limits %) 256) [:expr-depth :name-depth :level-depth]))
    (fail "Explicit finite evidence limits required; supported depth is at most 256" {}))
  limits)

(defn- charge! [usage limits key amount]
  (let [total (+' (get @usage key 0) amount)]
    (when (> total (get limits key))
      (fail "Store evidence limit exceeded" {:limit key :maximum (get limits key) :actual total}))
    (vswap! usage assoc key total)))

(defn- depth! [usage limits key depth]
  (when (> depth (get limits key))
    (fail "Store evidence depth exceeded" {:limit key :maximum (get limits key) :actual depth}))
  (vswap! usage update key (fnil max 0) depth))

(defn- id! [id]
  (when-not (and (integer? id) (<= 0 id Integer/MAX_VALUE))
    (fail "Invalid stored DAG id" {:id id}))
  (long id))

(defn- strict-text [^bytes raw]
  (str (.decode (doto (.newDecoder StandardCharsets/UTF_8)
                  (.onMalformedInput CodingErrorAction/REPORT)
                  (.onUnmappableCharacter CodingErrorAction/REPORT))
                (ByteBuffer/wrap raw))))

(defn- decode-raw
  "Validate one complete binary ExprStore record, with no Expr construction."
  [^bytes raw]
  (let [bb (ByteBuffer/wrap raw)
        tag (bit-and 255 (.get bb))
        read-id #(id! (.getInt bb))
        read-name #(vector :name (read-id))
        read-level #(vector :level (read-id))
        read-bytes (fn [n]
                     (when-not (<= 0 n (.remaining bb))
                       (fail "Invalid stored literal length" {:length n}))
                     (let [bs (byte-array n)] (.get bb bs) bs))
        spec (case tag
               0 (let [index (.getLong bb)]
                   (when (neg? index) (fail "Negative bound variable" {}))
                   {:tag tag :scalar index})
               1 {:tag tag :level (read-level)}
               2 (let [name (read-name) n (bit-and 65535 (.getShort bb))]
                   (when (> n (quot (.remaining bb) 4))
                     (fail "Invalid stored universe argument count" {}))
                   {:tag tag :name name :levels (mapv (fn [_] (read-level)) (range n))})
               3 {:tag tag :children [(read-id) (read-id)]}
               (4 5) (let [binder (bit-and 255 (.get bb))]
                       (when-not (<= 0 binder 3) (fail "Invalid binder information" {}))
                       {:tag tag :binder binder :name (read-name) :children [(read-id) (read-id)]})
               6 {:tag tag :name (read-name) :children [(read-id) (read-id) (read-id)]}
               7 (let [bs (read-bytes (bit-and 65535 (.getShort bb)))]
                   (when (or (zero? (alength bs)) (neg? (aget bs 0)))
                     (fail "Invalid stored natural literal" {}))
                   {:tag tag :literal bs})
               8 {:tag tag :literal (strict-text (read-bytes (.getInt bb)))}
               9 {:tag tag :children [(read-id)]}
               10 (let [name (read-name) index (.getInt bb)]
                    (when (neg? index) (fail "Negative projection index" {}))
                    {:tag tag :name name :scalar (long index) :children [(read-id)]})
               11 {:tag tag :scalar (.getLong bb)}
               (fail "Unknown stored expression tag" {:tag tag}))]
    (when (pos? (.remaining bb)) (fail "Trailing stored expression bytes" {}))
    spec))

(defn- shell-data [value]
  (let [m (if (instance? CIShell value) (.data ^CIShell value) value)]
    (when-not (and (map? m) (contains? #{0 1 2 3 4 5 6 7} (:tag m))
                   (instance? Name (:name m)))
      (fail "Full evidence requires a DAG ConstantInfo shell" {}))
    (doseq [key (into #{:tag :name :lps :type-id} (get required-variant-keys (:tag m)))]
      (when (or (not (contains? m key)) (nil? (get m key)))
        (fail "Incomplete stored ConstantInfo shell" {:field key})))
    (doseq [key (cond-> [:lps]
                  (contains? #{1 2 3 5 7} (:tag m)) (conj :all)
                  (= 5 (:tag m)) (conj :ctors))]
      (when-not (vector? (get m key))
        (fail "Stored ConstantInfo Name array must be a vector" {:field key})))
    (when (= 7 (:tag m))
      (when-not (vector? (:rules m)) (fail "Stored recursor rules must be a vector" {})))
    m))

(defn- validate-variant! [shell]
  ;; Called only after the invocation-wide shell/Name budgets have traversed
  ;; these collections; do not scan a potentially huge array before its gate.
  (doseq [key [:lps :all :ctors] :when (contains? shell key)]
    (when-not (every? #(instance? Name %) (get shell key))
      (fail "Stored ConstantInfo array contains a non-Name" {:field key})))
  (doseq [rule (:rules shell)]
    (when-not (and (map? rule) (instance? Name (:ctor rule))
                   (integer? (:nfields rule)) (<= 0 (:nfields rule) Integer/MAX_VALUE)
                   (some? (:rhs-id rule)))
      (fail "Incomplete stored recursor rule" {}))))

(defn- shell-roots [shell]
  (into [(id! (:type-id shell))]
        (case (:tag shell)
          (1 2 3) [(id! (:value-id shell))]
          7 (mapv #(id! (:rhs-id %)) (:rules shell))
          [])))

(defn- validate-shell!
  "Count shell collections before materializing CI arrays; walk only supported
   immutable scalar/Name values. Expression ids are checked separately."
  [shell usage limits visit-name!]
  (let [stack (ArrayDeque.)
        push! (fn [item]
                (charge! usage limits :shell-items 1)
                (when (some? item) (.push stack item)))]
    (push! shell)
    (while (not (.isEmpty stack))
      (let [item (.pop stack)]
        (cond
          (instance? Name item) (visit-name! item)
          (map? item) (doseq [[key value] item]
                        (charge! usage limits :shell-items 1)
                        (when-not (contains? shell-keys key) (fail "Invalid CI shell key" {}))
                        (push! value))
          (vector? item) (doseq [value item] (push! value))
          (or (keyword? item) (boolean? item) (integer? item)) nil
          :else (fail "Unsupported CI shell value" {:class (.getName (class item))}))))))

(defn materialize
  "Read exactly the requested Name vector from captured sources. No declaration
   dependency expansion, branch-head reread, fallback resolver or shared CI cache.
   `sources` contains :shell/:expr/:name/:level lookup functions; resolve-shell is
   the existing pure CI-shell constructor. Limits are all explicit, invocation
   wide, and include every reachable proof body. Returns {:constants :usage}.
   The caller retains its borrowed store lifetime throughout this operation."
  [requested sources limits resolve-shell]
  (validate-limits! limits)
  (when-not (and (vector? requested) (every? #(instance? Name %) requested)
                 (every? ifn? (map sources [:shell :expr :name :level])) (ifn? resolve-shell))
    (fail "Invalid scoped evidence request" {}))
  (when (> (count requested) (:declarations limits))
    (fail "Too many requested declarations" {:limit :declarations}))
  (let [usage (volatile! {:declarations (count requested)})
        names (HashMap.) levels (HashMap.)
        name-heights (IdentityHashMap.) level-heights (IdentityHashMap.)
        specs (HashMap.) heights (HashMap.) order (java.util.ArrayList.)]
    (letfn [(visit-name! [^Name root]
              (loop [n root stack []]
                (cond
                  (nil? n) (fail "Invalid Name prefix" {})
                  (.containsKey name-heights n)
                  (reduce (fn [height ^Name parent]
                            (let [height (inc height)]
                              (depth! usage limits :name-depth height)
                              (.put name-heights parent height) height))
                          (.get name-heights n) (rseq stack))
                  :else
                  (do
                    (charge! usage limits :name-nodes 1)
                    (depth! usage limits :name-depth (inc (count stack)))
                    (case (int (.tag n))
                      0 (do (.put name-heights n 1)
                            (reduce (fn [height ^Name parent]
                                      (let [height (inc height)]
                                        (depth! usage limits :name-depth height)
                                        (.put name-heights parent height) height))
                                    1 (rseq stack)))
                      1 (do (when-not (string? (.str n)) (fail "Invalid Name string" {}))
                            (charge! usage limits :name-chars (.length ^String (.str n)))
                            (recur (.prefix n) (conj stack n)))
                      2 (recur (.prefix n) (conj stack n))
                      (fail "Unknown Name tag" {}))))))
            (visit-level! [^Level root]
              (let [stack (ArrayDeque.) active (IdentityHashMap.)]
                (.push stack [root false])
                (while (not (.isEmpty stack))
                  (let [[^Level level finish?] (.pop stack)]
                    (when-not (instance? Level level) (fail "Invalid stored Level" {}))
                    (when-not (.containsKey level-heights level)
                      (let [children (case (int (.tag level))
                                       0 [] 1 [(.o0 level)] (2 3) [(.o0 level) (.o1 level)]
                                       4 (do (visit-name! (.o0 level)) [])
                                       (fail "Unsupported stored Level tag" {}))]
                        (if finish?
                          (let [height (inc (reduce max 0 (map #(.get level-heights %) children)))]
                            (depth! usage limits :level-depth height)
                            (.put level-heights level height)
                            (.remove active level))
                          (do
                            (when (.containsKey active level) (fail "Cyclic stored Level" {}))
                            (charge! usage limits :level-nodes 1)
                            (when (> (inc (.size active)) (:level-depth limits))
                              (fail "Stored Level traversal depth exceeded" {:limit :level-depth}))
                            (.put active level true)
                            (.push stack [level true])
                            (doseq [child (reverse children)] (.push stack [child false]))))))))))
            (name-ref! [[_ id]]
              (or (.get names id)
                  (let [value ((:name sources) id)]
                    (when-not (instance? Name value) (fail "Missing stored Name" {:name-id id}))
                    (visit-name! value) (.put names id value) value)))
            (level-ref! [[_ id]]
              (or (.get levels id)
                  (let [value ((:level sources) id)]
                    (when-not (instance? Level value) (fail "Missing stored Level" {:level-id id}))
                    (visit-level! value) (.put levels id value) value)))
            (visit-expr! [root]
              (let [stack (ArrayDeque.) active (java.util.HashSet.)]
                (.push stack [root false])
                (while (not (.isEmpty stack))
                  (let [[id finish?] (.pop stack)]
                    (when-not (.containsKey heights id)
                      (if finish?
                        (let [spec (.get specs id)
                              height (inc (reduce max 0 (map #(.get heights %) (:children spec))))]
                          (depth! usage limits :expr-depth height)
                          (.put heights id height) (.add order id) (.remove active id))
                        (do
                          (when (.contains active id) (fail "Cyclic stored Expr DAG" {:expr-id id}))
                          (charge! usage limits :expr-nodes 1)
                          (when (> (inc (.size active)) (:expr-depth limits))
                            (fail "Stored Expr traversal depth exceeded" {:limit :expr-depth}))
                          (let [raw ((:expr sources) id)]
                            (when-not (bytes? raw) (fail "Missing stored Expr bytes" {:expr-id id}))
                            (charge! usage limits :raw-bytes (alength ^bytes raw))
                            (let [spec (decode-raw (aclone ^bytes raw))]
                              (when-let [n (:name spec)] (name-ref! n))
                              (when-let [l (:level spec)] (level-ref! l))
                              (doseq [l (:levels spec)] (level-ref! l))
                              (charge! usage limits :expr-edges (count (:children spec)))
                              (.put specs id spec) (.add active id)
                              (.push stack [id true])
                              (doseq [child (reverse (:children spec))]
                                (.push stack [child false])))))))))))
            (assemble [spec ^HashMap values]
              (let [children (mapv #(.get values %) (:children spec))
                    binder (get [:default :implicit :strict-implicit :inst-implicit] (:binder spec))]
                (case (:tag spec)
                  0 (Expr/bvar (:scalar spec))
                  1 (let [level (level-ref! (:level spec))] (Expr/sort level (Level/hasParam level)))
                  2 (let [ls (mapv level-ref! (:levels spec))]
                      (Expr/mkConst (name-ref! (:name spec)) ls (boolean (some #(Level/hasParam %) ls))))
                  3 (Expr/app (nth children 0) (nth children 1))
                  4 (Expr/lam (name-ref! (:name spec)) (nth children 0) (nth children 1) binder)
                  5 (Expr/forall (name-ref! (:name spec)) (nth children 0) (nth children 1) binder)
                  6 (Expr/mkLet (name-ref! (:name spec)) (nth children 0) (nth children 1) (nth children 2))
                  7 (Expr/litNat (java.math.BigInteger. ^bytes (:literal spec)))
                  8 (Expr/litStr (:literal spec))
                  9 (Expr/mdata nil (nth children 0))
                  10 (Expr/proj (name-ref! (:name spec)) (:scalar spec) (nth children 0))
                  11 (Expr/fvar (:scalar spec)))))]
      ;; Name equality/hash/PSS comparison can recurse through prefixes. Admit
      ;; requested Names before duplicate hashing or any backend shell lookup.
      (doseq [requested-name requested] (visit-name! requested-name))
      (when-not (= (count requested) (count (set requested)))
        (fail "Duplicate requested evidence name" {}))
      (let [shells (mapv (fn [requested-name]
                           (let [shell (shell-data ((:shell sources) requested-name))]
                             (visit-name! (:name shell))
                             (when-not (= requested-name (:name shell))
                               (fail "Stored shell Name differs from requested Name" {}))
                             (validate-shell! shell usage limits visit-name!)
                             (validate-variant! shell)
                             (doseq [root (shell-roots shell)] (visit-expr! root))
                             shell)) requested)
            values (HashMap.)]
        ;; Every requested shell and reachable raw DAG passed before the first
        ;; Expr constructor. This cache is never shared with normal defs-only IO.
        (doseq [id order]
          (let [value (assemble (.get specs id) values)]
            (set! (.-storeId ^Expr value) (int id))
            (.put values id value)))
        {:constants (into {} (map (fn [shell]
                                    (let [ci (resolve-shell shell (fn [id]
                                                                    (or (.get values (id! id))
                                                                        (fail "Unadmitted expression root" {}))))]
                                      (when-not (constant-info/complete? ci)
                                        (fail "Incomplete materialized ConstantInfo" {}))
                                      [(:name shell) ci]))) shells)
         :usage @usage}))))
