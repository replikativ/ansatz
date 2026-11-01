(ns prototype.guest-encoding
  "Owned guest values reconstructed by actual pinned Lean constructors. Java
   cache bits are never copied. Local descriptor builders are not guest state;
   only returned immutable worlds/owned values cross the callback boundary."
  (:require [prototype.machine :as m] [prototype.runtime-string :as string]
            [prototype.imported-kernel :as imported])
  (:import [ansatz.kernel Name Level Expr ConstantInfo ConstantInfo$RecursorRule]
           [java.util IdentityHashMap]))
(def names-helper ["str" ["str" ["str" ["anonymous"] "KernelEncoding"] "decodeNames"] "_boxed"])
(def family-helper ["str" ["str" ["str" ["anonymous"] "KernelEncoding"] "decodeFamily"] "_boxed"])
(defn- fail [message data] (throw (ex-info message data)))
(defn- binder [value]
  (or ({:default 0 :implicit 1 :strict-implicit 2 :inst-implicit 3} value)
      (fail "Unsupported Java binder annotation" {:value value})))
(defn- node-spec [kind value originals]
  (case kind
    :name
    (let [^Name n value]
      (when-not (instance? Name n) (fail "Guest encoder requires structured Java Names" {:value value}))
      (case (.tag n)
        0 {:kind 0 :children []}
        1 {:kind 1 :text (.str n) :children [[:name (.prefix n)]]}
        2 (do (when (neg? (.num n)) (fail "Negative Java Name numeric component" {}))
              {:kind 2 :number (.num n) :children [[:name (.prefix n)]]})))
    :level
    (let [^Level u value]
      (when-not (instance? Level u) (fail "Expected Java Level" {}))
      (case (.tag u)
        0 {:kind 0 :children []}
        1 {:kind 1 :children [[:level (.o0 u)]]}
        (2 3) {:kind (.tag u) :children [[:level (.o0 u)] [:level (.o1 u)]]}
        4 {:kind 4 :children [[:name (.o0 u)]]}
        (fail "Unresolved Java universe in guest encoder" {})))
    :expr
    (let [^Expr e value original (when originals (.get ^IdentityHashMap originals e))]
      (when-not (instance? Expr e) (fail "Expected Java Expr" {}))
      (if original {:kind 99 :original original :children []}
        (case (.tag e)
          0 {:kind 0 :number (.longVal e) :children []}
          1 {:kind 1 :children [[:level (.o0 e)]]}
          2 {:kind 2 :children (into [[:name (.o0 e)]] (map #(vector :level %) (seq (.o1 e))))}
          3 {:kind 3 :children [[:expr (.o0 e)] [:expr (.o1 e)]]}
          (4 5) {:kind (.tag e) :number (binder (.o3 e))
                 :children [[:name (.o0 e)] [:expr (.o1 e)] [:expr (.o2 e)]]}
          ;; No guessed Lean letE.nondep or erased mdata reconstruction.
          (6 9) (fail "Java let/metadata reconstruction requires lossless guest provenance"
                      {:runtime-limit :guest-expression-provenance})
          7 {:kind 7 :number (.o0 e) :children []}
          8 {:kind 8 :text (.o0 e) :children []}
          10 {:kind 10 :number (.longVal e) :children [[:name (.o0 e)] [:expr (.o1 e)]]}
          (fail "Unresolved Java Expr in guest encoder" {:tag (.tag e)}))))))
(defn- builder [originals]
  {:rows (atom {:name [] :level [] :expr []})
   :memo {:name (IdentityHashMap.) :level (IdentityHashMap.) :expr (IdentityHashMap.)}
   :originals originals})
(defn- node-index! [{:keys [rows memo originals]} kind value]
  (loop [todo [[:visit kind value]] active {:name #{} :level #{} :expr #{}}]
    (if (empty? todo) (.get ^IdentityHashMap (get memo kind) value)
      (let [[op current-kind current spec] (peek todo) todo (pop todo)
            ^IdentityHashMap cache (get memo current-kind)]
        (if (= op :visit)
          (if (.containsKey cache current) (recur todo active)
            (do
              (when (contains? (get active current-kind) current) (fail "Cyclic Java encoding graph" {}))
              (let [spec (node-spec current-kind current originals)]
                (recur (into (conj todo [:build current-kind current spec])
                             (map (fn [[kind value]] [:visit kind value]) (reverse (:children spec))))
                       (update active current-kind conj current)))))
          (let [dependencies (mapv (fn [[kind value]] (.get ^IdentityHashMap (get memo kind) value)) (:children spec))
                row (assoc (dissoc spec :children) :args dependencies)
                index (count (get @rows current-kind))]
            (swap! rows update current-kind conj row)
            (.put cache current index)
            (recur todo (update active current-kind disj current))))))))
(defn- array [world values] (m/allocate world :array 246 values))
(defn- allocate-nodes [world rows]
  (let [[world values]
        (reduce (fn [[world out] {:keys [kind number text args original] :or {number 0 text ""}}]
                  (when-not (and (integer? number) (<= 0 number)) (fail "Invalid guest descriptor Nat" {:value number}))
                  (let [[world args] (array world args)
                        [world original] (if original
                                           (do (m/node world original)
                                               (m/allocate (m/retain world original 1) :ctor 1 [original]))
                                           [world 0])
                        [world node] (m/allocate world :ctor 0 [kind number text args original])]
                    [world (conj out node)])) [world []] rows)]
    (array world values)))
(defn- unwrap [world result entry-result]
  (let [node (when (m/ref? result) (m/node world result))]
    (when-not (and (= :ctor (:kind node)) (contains? #{0 1} (:tag node)) (= 1 (count (:fields node))))
      (fail "Malformed guest encoder result" {:checkpoint world :result result}))
    (if (= 0 (:tag node))
      (fail "Guest encoding rejected descriptors"
            {:checkpoint world :result result :message (string/string-value {:ref? m/ref? :node m/node} world (first (:fields node)))})
      (let [value (first (:fields node))
            world (-> world (m/retain value 1) (m/release result 1))]
        ;; A top-level invoker can leave its owned Except in :result; scoped
        ;; invokers already restored the parent's control. Consuming the Except
        ;; must neither leave that freed wrapper as a root nor add/change a
        ;; parent's result slot. Normalize only this slot, on success only.
        [(if entry-result (assoc world :result (val entry-result)) (dissoc world :result)) value]))))
(defn encode-names
  "Encode structured Java Names into one caller-owned guest Array Name using
   real Lean constructors. invoke returns [world owned-Except] from a scoped raw
   helper or a host adapter over raw/call. The encoder consumes that wrapper;
   any pre-existing entry :result remains the caller's alias, without an extra
   retain/release. Other returned control belongs to the supplied invoker.
   Success preserves the entry :result slot's presence/value and leaves other
   invoker control fields untouched. Failure preserves its actual checkpoint."
  ([world invoke names] (encode-names world invoke names {}))
  ([world invoke names {:keys [helper] :or {helper names-helper}}]
   (let [entry-result (find world :result)
         builder (builder nil) roots (mapv #(node-index! builder :name %) names)
         [world inputs] (allocate-nodes world (:name @(:rows builder)))
         [world roots] (array world roots)
         [world result] (invoke world helper [inputs roots])]
     (unwrap world result entry-result))))
(defn encode-name
  ([world invoke name] (encode-name world invoke name {}))
  ([world invoke name options]
   (let [[world names] (encode-names world invoke [name] options)
         values (:fields (m/node world names))]
     (when-not (= 1 (count values)) (fail "Guest Name encoder returned wrong root count" {}))
     (let [value (first values)] [(-> world (m/retain value 1) (m/release names 1)) value]))))

(defn- constant-spec! [builder ^ConstantInfo constant]
  (let [n #(node-index! builder :name %) e #(node-index! builder :expr %)
        names #(mapv n (seq %))
        common {:kind (.tag constant) :name (n (.name constant)) :levels (names (.levelParams constant))
                :type (e (.type constant)) :all (names (.all constant))
                :parent 0 :numbers [] :ctors [] :flags [] :rules []}]
    (case (.tag constant)
      5 (assoc common :numbers [(.numParams constant) (.numIndices constant) (.numNested constant)]
                      :ctors (names (.ctors constant))
                      :flags (mapv #(if % 1 0) [(.isRec constant) (.isUnsafe constant) (.isReflexive constant)]))
      6 (assoc common :parent (n (.inductName constant)) :numbers [(.cidx constant) (.numParams constant) (.numFields constant)]
                      :flags [(if (.isUnsafe constant) 1 0)])
      7 (assoc common :numbers [(.numParams constant) (.numIndices constant) (.numMotives constant) (.numMinors constant)]
                      :flags (mapv #(if % 1 0) [(.isK constant) (.isUnsafe constant)])
                      :rules (mapv (fn [^ConstantInfo$RecursorRule rule]
                                     [(n (.ctor rule)) (.nfields rule) (e (.rhs rule))]) (.rules constant)))
      (fail "Unsupported generated constant kind" {:tag (.tag constant)}))))
(defn- allocate-constants [world specs]
  (let [[world out]
        (reduce
          (fn [[world out] {:keys [kind name levels type all parent numbers ctors flags rules]}]
            (let [[world levels] (array world levels) [world all] (array world all)
                  [world numbers] (array world numbers) [world ctors] (array world ctors) [world flags] (array world flags)
                  [world rules] (reduce (fn [[world out] rule]
                                         (let [[world value] (m/allocate world :ctor 0 rule)] [world (conj out value)]))
                                       [world []] rules)
                  [world rules] (array world rules)
                  [world input] (m/allocate world :ctor 0 [kind name levels type all parent numbers ctors flags rules])]
              [world (conj out input)])) [world []] specs)]
    (array world out)))
(defn encode-family
  "One guest decode call, followed by exact full ConstantInfo reprojection. Returns
   an owned Array ConstantInfo. Does not admit or publish anything. Original Java
   Expr identities can map to borrowed original guest roots via :original-expressions.
   Successful cleanup preserves the entry result slot as encode-names does."
  ([world invoke constants] (encode-family world invoke constants {}))
  ([world invoke constants {:keys [helper original-expressions] :or {helper family-helper}}]
   (let [entry-result (find world :result)
         builder (builder original-expressions) specs (mapv #(constant-spec! builder %) constants)
         [world names] (allocate-nodes world (:name @(:rows builder)))
         [world levels] (allocate-nodes world (:level @(:rows builder)))
         [world expressions] (allocate-nodes world (:expr @(:rows builder)))
         [world inputs] (allocate-constants world specs)
         [world result] (invoke world helper [names levels expressions inputs])
         [world value] (unwrap world result entry-result)
         node (m/node world value)]
     (when-not (and (= :array (:kind node)) (= (count constants) (count (:fields node))))
       (fail "Guest encoded family has wrong shape/completeness" {:checkpoint world :value value}))
     (doseq [[expected raw] (map vector constants (:fields node))]
       (when-not (= (imported/checking-shape expected)
                    (imported/checking-shape (imported/project-constant world raw)))
         (fail "Guest encoded constant differs from checked Java family" {:checkpoint world :name (.name ^ConstantInfo expected)})))
     [world value])))
