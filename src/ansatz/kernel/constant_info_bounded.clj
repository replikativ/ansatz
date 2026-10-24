(ns ansatz.kernel.constant-info-bounded
  "Exact bounded comparison of quiescent, already materialized declarations.
   No kernel admission, hydration, AST equality/hash, or metadata interpretation."
  (:import [ansatz.kernel ConstantInfo ConstantInfo$RecursorRule Expr Name Level]
           [java.math BigInteger]
           [java.util IdentityHashMap ArrayDeque]
           [clojure.lang IPersistentVector PersistentVector]))

(def ^:private limit-keys #{:pairs :edges :scalar-bytes :items :depth})
(defn- fail [message data] (throw (ex-info message (assoc data :type ::invalid-comparison))))
(defn- invalid [] (fail "Incomplete or unsupported declaration comparison payload" {}))
(defn- require-type [class value]
  (when-not (.isInstance ^Class class value) (invalid)) value)
(defn- standard-vector? [x] (identical? PersistentVector (class x)))
(defn- object-array? [x] (instance? (class (object-array 0)) x))
(def ^:private expression-store-level-list-classes
  ;; Exact carriers created by ExprStore.resolve, not arbitrary List callbacks.
  #{(class (java.util.Collections/emptyList))
    (class (java.util.Arrays/asList (object-array 0)))})
(defn- expression-store-level-list? [value]
  (contains? expression-store-level-list-classes (class value)))

(defn- fields
  "Typed semantic edges only. Array fields remain lazy; never copy an input array."
  [kind value]
  (case kind
    :ci
    (let [^ConstantInfo c (require-type ConstantInfo value)
          base [[:name (.name c)] [[:array :name] (.levelParams c)] [:expr (.type c)]]]
      (into [[:long (long (.tag c))]]
            (concat base
                    (case (int (.tag c))
                      0 [[:boolean (.isUnsafe c)]]
                      1 [[:expr (.value c)] [:long (.getHintsCode c)] [:safety (.safety c)]
                         [[:array :name] (.all c)]]
                      2 [[:expr (.value c)] [[:array :name] (.all c)]]
                      3 [[:expr (.value c)] [[:array :name] (.all c)] [:boolean (.isUnsafe c)]]
                      4 [[:quot (.quotKind c)]]
                      5 [[:long (.numParams c)] [:long (.numIndices c)] [[:array :name] (.all c)]
                         [[:array :name] (.ctors c)] [:long (.numNested c)] [:boolean (.isRec c)]
                         [:boolean (.isReflexive c)] [:boolean (.isUnsafe c)]]
                      6 [[:name (.inductName c)] [:long (.cidx c)] [:long (.numParams c)]
                         [:long (.numFields c)] [:boolean (.isUnsafe c)]]
                      7 [[[:array :name] (.all c)] [:long (.numParams c)] [:long (.numIndices c)]
                         [:long (.numMotives c)] [:long (.numMinors c)]
                         [[:array :rule] (.rules c)] [:boolean (.isK c)] [:boolean (.isUnsafe c)]]
                      (invalid)))))
    :rule (let [^ConstantInfo$RecursorRule r (require-type ConstantInfo$RecursorRule value)]
            [[:name (.ctor r)] [:long (.nfields r)] [:expr (.rhs r)]])
    :name (let [^Name n (require-type Name value)]
            (into [[:long (long (.tag n))]]
                  (case (int (.tag n))
                    0 [] 1 [[:name (.prefix n)] [:string (.str n)]]
                    2 [[:name (.prefix n)] [:long (.num n)]] (invalid))))
    :level (let [^Level l (require-type Level value)]
             (into [[:long (long (.tag l))]]
                   (case (int (.tag l))
                     0 [] 1 [[:level (.o0 l)]]
                     (2 3) [[:level (.o0 l)] [:level (.o1 l)]]
                     4 [[:name (.o0 l)]] 5 [[:long (.o0 l)]] (invalid))))
    :expr (let [^Expr e (require-type Expr value)]
            (into [[:long (long (.tag e))]]
                  (case (int (.tag e))
                    (0 11 12) [[:long (.longVal e)]]
                    1 [[:level (.o0 e)]]
                    2 [[:name (.o0 e)] [:levels (.o1 e)]]
                    3 [[:expr (.o0 e)] [:expr (.o1 e)]]
                    (4 5) [[:name (.o0 e)] [:expr (.o1 e)] [:expr (.o2 e)] [:binder (.o3 e)]]
                    6 [[:name (.o0 e)] [:expr (.o1 e)] [:expr (.o2 e)] [:expr (.o3 e)]]
                    7 [[:nat (.o0 e)]] 8 [[:string (.o0 e)]]
                    ;; ExprStore/parser erase metadata; richer payloads have no
                    ;; bounded semantic contract here, even on identical nodes.
                    9 [[:nil (.o0 e)] [:expr (.o1 e)]]
                    10 [[:name (.o0 e)] [:long (.longVal e)] [:expr (.o1 e)]] (invalid))))
    :levels (cond
              (object-array? value) (map (fn [i] [:level (aget ^objects value i)]) (range (alength ^objects value)))
              (standard-vector? value) (map (fn [i] [:level (.nth ^IPersistentVector value i)])
                                            (range (.count ^IPersistentVector value)))
              (expression-store-level-list? value)
              (map (fn [i] [:level (.get ^java.util.List value i)])
                   (range (.size ^java.util.List value)))
              :else (invalid))
    (if (and (vector? kind) (= :array (first kind)))
      (do (when-not (object-array? value) (invalid))
          (map (fn [i] [(second kind) (aget ^objects value i)]) (range (alength ^objects value))))
      nil)))

(defn- field-count [kind value children]
  (cond
    (and (vector? kind) (= :array (first kind))) (alength ^objects value)
    (= :levels kind) (cond
                       (object-array? value) (alength ^objects value)
                       (standard-vector? value) (.count ^IPersistentVector value)
                       (expression-store-level-list? value) (.size ^java.util.List value)
                       :else (invalid))
    :else (count children)))

(defn- scalar-kind? [kind]
  (contains? #{:string :nat :long :boolean :safety :binder :quot :nil} kind))

(defn- scalar-size! [kind value]
  (case kind
    :string (do (require-type String value) (*' 2 (.length ^String value)))
    :nat (do (when-not (identical? BigInteger (class value)) (invalid))
             (when (neg? (.signum ^BigInteger value)) (invalid))
             (max 1 (quot (+ 7 (long (.bitLength ^BigInteger value))) 8)))
    :long (do (when-not (or (instance? Long value) (instance? Integer value)
                            (instance? Short value) (instance? Byte value)) (invalid)) 8)
    :boolean (do (when-not (instance? Boolean value) (invalid)) 1)
    :safety (do (when-not (and (integer? value) (<= 0 value 2)) (invalid)) 1)
    :binder (do (when-not (and (keyword? value) (contains? #{:default :implicit :strict-implicit :inst-implicit} value)) (invalid)) 1)
    :quot (do (when-not (and (keyword? value) (contains? #{:type :ctor :lift :ind} value)) (invalid)) 1)
    :nil (do (when-not (nil? value) (invalid)) 0)
    0))

(defn full-equal-batch-bounded?
  "Compare a finite PersistentVector of [left-CI right-CI] PersistentVectors.
   All pairs share validation/comparison memos and explicit positive limits
   {:pairs :edges :scalar-bytes :items :depth}. Validate both entire semantic DAGs
   before even an identical-CI shortcut. Identity memoization bounds shared DAG
   work; depth is the longest typed semantic path, including scalar/array nodes.
   :items charges visited nodes, batch containers/slots and array slots;
   :edges charges batch references and traversal/queue
   work, :scalar-bytes charges validated and compared leaf storage conservatively.
   Only Object[], exact PersistentVector and the exact JDK EmptyList/Arrays$ArrayList
   level carriers emitted by ExprStore are supported.
   Unknown metadata/collection payloads (including custom vectors) fail closed. Inputs must remain quiescent
   for the call: ConstantInfo fields and arrays are mutable. Returns a boolean;
   invalid/incomplete inputs or exceeded limits throw ExceptionInfo."
  [ci-pairs limits]
  (when-not (and (map? limits) (= limit-keys (set (keys limits)))
                 (every? #(and (integer? %) (pos? %) (<= % Long/MAX_VALUE)) (vals limits)))
    (fail "Explicit finite comparison limits required" {}))
  (let [usage (volatile! {})
        validated (atom {})
        pairs (IdentityHashMap.)
        charge! (fn [key amount]
                  (let [total (+' (get @usage key 0) amount)]
                    (when (> total (get limits key))
                      (fail "Declaration comparison limit exceeded"
                            {:limit key :maximum (get limits key) :actual total :usage @usage}))
                    (vswap! usage assoc key total)))
        depth! (fn [n]
                 (when (> n (:depth limits))
                   (fail "Declaration comparison depth exceeded" {:limit :depth :actual n})))
        memo (fn [kind]
               (or (get @validated kind)
                   (let [m (IdentityHashMap.)] (swap! validated assoc kind m) m)))
        validate! (fn [root]
                    (let [stack (ArrayDeque.)]
                      (.push stack [:ci root 1 false])
                      (while (not (.isEmpty stack))
                        (let [[kind value depth finish?] (.pop stack)
                              ^IdentityHashMap seen (memo kind)
                              state (.get seen value)]
                          (depth! depth)
                          (cond
                            finish?
                            (let [children (fields kind value)
                                  height (inc (reduce (fn [h [k v]]
                                                        ;; Accessors can freshly box primitive values on each
                                                        ;; fields call. Validated scalar leaves always have
                                                        ;; height one; only composite heights use identity.
                                                        (max h (if (scalar-kind? k) 1
                                                                   (long (.get ^IdentityHashMap (memo k) v))))) 0 children))]
                              (.put seen value height) (depth! (+ depth (dec height))))
                            (= :active state) (fail "Cyclic declaration comparison payload" {})
                            (some? state) (depth! (+ depth (dec (long state))))
                            :else
                            (let [children (fields kind value)
                                  n (field-count kind value children)]
                              (charge! :items (inc n))
                              (charge! :edges (*' 2 n))
                              (charge! :scalar-bytes (scalar-size! kind value))
                              (.put seen value :active)
                              (.push stack [kind value depth true])
                              ;; Queue order is irrelevant to equality; each child
                              ;; finishes before a sibling with the same identity.
                              (doseq [[k v] children] (.push stack [k v (inc depth) false]))))))))]
    (when-not (standard-vector? ci-pairs) (invalid))
    ;; Count is O(1) for the exact known vector implementation. Charge all
    ;; containers/slots before inspecting even the first candidate pair.
    (let [n (.count ^IPersistentVector ci-pairs)]
      (charge! :items (inc' (*' 4 n)))
      (charge! :edges (*' 3 n))
      (doseq [pair ci-pairs]
        (when-not (and (standard-vector? pair) (= 2 (.count ^IPersistentVector pair))) (invalid)))
      (doseq [[left right] ci-pairs]
        (validate! left)
        (validate! right)))
    (let [stack (ArrayDeque.)]
      (doseq [[left right] ci-pairs] (.push stack [:ci left right]))
      (loop []
        (if (.isEmpty stack)
          true
          (let [[kind a b] (.pop stack)]
            (if (identical? a b)
              (recur)
              (let [^IdentityHashMap row (or (.get pairs a)
                                             (let [r (IdentityHashMap.)] (.put pairs a r) r))
                    kinds (.get row b)]
                (if (contains? kinds kind)
                  (recur)
                  (do
                    (charge! :pairs 1)
                    (.put row b (conj (or kinds #{}) kind))
                    (let [ac (fields kind a) bc (fields kind b)
                          an (field-count kind a ac) bn (field-count kind b bc)]
                      (if (not= an bn)
                        false
                        (if (zero? an)
                          (do (charge! :scalar-bytes (+' (scalar-size! kind a) (scalar-size! kind b)))
                              ;; Only prevalidated scalar leaves reach =.
                              (if (or (contains? #{:ci :rule :name :level :expr :levels} kind)
                                      (vector? kind) (= a b))
                                (recur) false))
                          (do
                            (charge! :edges (*' 3 an))
                            (if (every? (fn [[[ak _] [bk _]]] (= ak bk)) (map vector ac bc))
                              (do (doseq [[[ak av] [_ bv]] (map vector ac bc)]
                                    (.push stack [ak av bv]))
                                  (recur))
                              false)))))))))))))))

(defn full-equal-bounded?
  "One-pair convenience wrapper; limits/accounting match the batch API."
  [left right limits]
  (full-equal-batch-bounded? [[left right]] limits))
