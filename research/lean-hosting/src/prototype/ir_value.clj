(ns prototype.ir-value
  "Borrow pinned Lean4.33.1 IR values into RuntimeCompileShim's existing JSON shape.
   Sources: Lean/Compiler/IR/Basic.lean, Compiler/ExternAttr.lean, and the exact
   deriving rules in Elab/Deriving/FromToJson.lean. FnBody/Alt use the shim's
   explicit array encoding. VarId/JoinPointId, DeclInfo and ExternAttrData erase
   single-field wrappers. No cross-world memo, admission, execution or ownership
   effects occur. Names preserve arbitrary Nat numeric segments as decimal strings."
  (:require [prototype.machine :as m]
            [prototype.native-scalar :as native]
            [prototype.constructor-layout :as layout]
            [prototype.runtime-string :as string]))

(def ^:private ops {:ref? m/ref? :node m/node})
(defn- fail [message data] (throw (ex-info message data)))
(defn- tag [carrier world value]
  (cond ((:ref? carrier) value) (:tag ((:node carrier) world value))
        (native/native-scalar? value) (native/payload value)
        (instance? prototype.machine.Tag value) (:tag value)
        (integer? value) value
        :else (fail "Invalid typed IR constructor carrier" {})))
(defn- ctor! [carrier world value expected objects scalars]
  (if ((:ref? carrier) value)
    (let [node ((:node carrier) world value)]
      (when-not (and (= expected (:tag node)) (vector? (:fields node))
                     (layout/constructor-layout? node objects scalars))
        (fail "Invalid typed IR constructor layout" {:tag expected :value value})) node)
    (if (and (zero? objects) (zero? scalars) (= expected (tag carrier world value)))
      {:fields []}
      (fail "Expected typed IR constructor reference" {:tag expected}))))
(defn- text! [carrier world value]
  (when ((:ref? carrier) value)
    (let [node ((:node carrier) world value)]
      (when-not (and (= :string (:kind node)) (= 249 (:tag node))
                     (vector? (:fields node)) (empty? (:fields node))
                     (nil? (:layout node)) (empty? (:scalar-bytes node)))
        (fail "Invalid typed IR String layout" {}))))
  (let [s (string/string-value carrier world value)]
    (string/evaluate {} nil "lean_string_utf8_byte_size" [s]) s))
(defn- array! [carrier world value]
  (when-not ((:ref? carrier) value) (fail "Expected typed IR array reference" {}))
  (let [node ((:node carrier) world value)]
    (when-not (and (= :array (:kind node)) (= 246 (:tag node)) (vector? (:fields node))
                   (nil? (:layout node)) (empty? (:scalar-bytes node)))
      (fail "Invalid typed IR array layout" {}))
    (:fields node)))
(defn- leaf [value] {:value value})
(defn- form [shape label fields] {:shape shape :label label :fields fields})
(defn- named [label fields] (form :named label fields))
(defn- record-form [fields] (form :record nil fields))
(defn- array-form [label fields] (form :array label fields))

(def ^:private ir-types
  [(named :float []) (named :uint8 []) (named :uint16 []) (named :uint32 [])
   (named :uint64 []) (named :usize []) (named :erased []) (named :object [])
   (named :tobject []) (named :float32 [])
   (named :struct [[:leanTypeName [:option :name]] [:types [:array :ir-type]]])
   (named :union [[:leanTypeName :name] [:types [:array :ir-type]]])
   (named :tagged []) (named :void [])])
(def ^:private expressions
  [(named :ctor [[:i :ctor-info] [:ys [:array :arg]]])
   (named :reset [[:n :nat] [:x :var-id]])
   (named :reuse [[:x :var-id] [:i :ctor-info] [:updtHeader :bool] [:ys [:array :arg]]])
   (named :proj [[:i :nat] [:x :var-id]])
   (named :uproj [[:i :nat] [:x :var-id]])
   (named :sproj [[:n :nat] [:offset :nat] [:x :var-id]])
   (named :fap [[:c :name] [:ys [:array :arg]]])
   (named :pap [[:c :name] [:ys [:array :arg]]])
   (named :ap [[:x :var-id] [:ys [:array :arg]]])
   (named :box [[:ty :ir-type] [:x :var-id]])
   (named :unbox [[:x :var-id]]) (named :lit [[:v :literal]])
   (named :isShared [[:x :var-id]])])
(def ^:private bodies
  [(array-form "vdecl" [[:x :var-id] [:ty :ir-type] [:e :expr] [:b :body]])
   (array-form "jdecl" [[:j :join-id] [:xs [:array :param]] [:v :body] [:b :body]])
   (array-form "set" [[:x :var-id] [:i :nat] [:y :arg] [:b :body]])
   (array-form "setTag" [[:x :var-id] [:cidx :nat] [:b :body]])
   (array-form "uset" [[:x :var-id] [:i :nat] [:y :var-id] [:b :body]])
   (array-form "sset" [[:x :var-id] [:i :nat] [:offset :nat] [:y :var-id] [:ty :ir-type] [:b :body]])
   (array-form "inc" [[:x :var-id] [:n :nat] [:c :bool] [:persistent :bool] [:b :body]])
   (array-form "dec" [[:x :var-id] [:n :nat] [:c :bool] [:persistent :bool] [:b :body]])
   (array-form "del" [[:x :var-id] [:b :body]])
   (array-form "case" [[:tid :name] [:x :var-id] [:xType :ir-type] [:cs [:array :alt]]])
   (array-form "ret" [[:x :arg]]) (array-form "jmp" [[:j :join-id] [:ys [:array :arg]]])
   (array-form "unreachable" [])])
(def ^:private declarations
  [(named :fdecl [[:f :name] [:xs [:array :param]] [:type :ir-type] [:body :body] [:info :decl-info]])
   (named :extern [[:f :name] [:xs [:array :param]] [:type :ir-type] [:ext :extern-data]])])
(def ^:private extern-entries
  [(named :adhoc [[:backend :name]])
   (named :inline [[:backend :name] [:pattern :string]])
   (named :standard [[:backend :name] [:fn :string]]) (named :opaque [])])

(defn- describe-form [carrier world value index {:keys [shape label fields]}]
  (let [objects (count (remove #(= :bool (second %)) fields))
        scalars (- (count fields) objects)
        node (ctor! carrier world value index objects scalars)
        children (loop [fields fields object-index 0 scalar-index 0 children []]
                   (if-let [[_ kind] (first fields)]
                     (if (= :bool kind)
                       (recur (next fields) object-index (inc scalar-index)
                              (conj children [:bool (get (:scalar-bytes node) (+ (* 8 objects) scalar-index))]))
                       (recur (next fields) (inc object-index) scalar-index
                              (conj children [kind (nth (:fields node) object-index)]))) children))]
    {:children children
     :build (fn [values]
              (let [record (zipmap (map first fields) values)]
                (case shape
                  :record record
                  :named (if (empty? fields) (name label) {label record})
                  :array (into [label] values))))}))
(defn- variant [carrier world value forms]
  (let [index (tag carrier world value)]
    (when-not (and (integer? index) (<= 0 index) (< index (count forms)))
      (fail "Unknown pinned typed IR constructor" {:tag index :variants (count forms)}))
    (describe-form carrier world value index (nth forms (int index)))))

(defn- describe [carrier world kind value]
  (if (vector? kind)
    (let [[container child] kind]
      (case container
        :array {:children (mapv #(vector child %) (array! carrier world value)) :build identity}
        :option (case (tag carrier world value)
                  0 (do (ctor! carrier world value 0 0 0) (leaf nil))
                  1 (let [[v] (:fields (ctor! carrier world value 1 1 0))]
                      {:children [[child v]] :build first})
                  (fail "Invalid typed IR Option" {}))
        :list (case (tag carrier world value)
                0 (do (ctor! carrier world value 0 0 0) (leaf '()))
                1 (let [[head tail] (:fields (ctor! carrier world value 1 2 0))]
                    {:children [[child head] [kind tail]] :build (fn [[h t]] (cons h t))})
                (fail "Invalid typed IR List" {}))
        (fail "Unknown typed IR container" {:kind kind})))
    (case kind
      :nat (leaf (native/nat-value carrier world value))
      :string (leaf (text! carrier world value))
      :bool (do (when-not (contains? #{0 1} value) (fail "Invalid typed IR packed Bool" {:value value}))
                (leaf (= 1 value)))
      (:var-id :join-id) {:children [[:nat value]] :build (fn [[n]] {:idx n})}
      :name (case (tag carrier world value)
              0 (do (ctor! carrier world value 0 0 0) (leaf ["anonymous"]))
              1 (let [[p s] (:fields (ctor! carrier world value 1 2 8))]
                  {:children [[:name p] [:string s]] :build (fn [[p s]] ["str" p s])})
              2 (let [[p n] (:fields (ctor! carrier world value 2 2 8))]
                  {:children [[:name p] [:nat n]] :build (fn [[p n]] ["num" p (str n)])})
              (fail "Invalid typed IR Name" {}))
      :ir-type (variant carrier world value ir-types)
      :arg (variant carrier world value [(named :var [[:id :var-id]]) (named :erased [])])
      :literal (variant carrier world value [(named :num [[:v :nat]]) (named :str [[:v :string]])])
      :ctor-info (describe-form carrier world value 0 (record-form [[:name :name] [:cidx :nat] [:size :nat] [:usize :nat] [:ssize :nat]]))
      :expr (variant carrier world value expressions)
      :param (describe-form carrier world value 0 (record-form [[:x :var-id] [:borrow :bool] [:ty :ir-type]]))
      :alt (variant carrier world value [(array-form "ctor" [[:info :ctor-info] [:b :body]])
                                (array-form "default" [[:b :body]])])
      :body (variant carrier world value bodies)
      :decl-info {:children [[[:option :name] value]]
                  :build (fn [[name]] (if (nil? name) {} {:sorryDep name}))}
      :extern-entry (variant carrier world value extern-entries)
      :extern-data {:children [[[:list :extern-entry] value]] :build (fn [[entries]] {:entries (vec entries)})}
      :decl (variant carrier world value declarations)
      :witness-row (describe-form carrier world value 0
                     (record-form [[:name :name] [:ir :decl] [:sourceLocal :bool] [:sourceModule [:option :name]]]))
      :witness
      (let [shape (describe-form carrier world value 0
                    (record-form [[:schema :string] [:producer :string] [:leanCommit :string] [:wordBits :nat]
                                  [:target :string] [:name :name] [:boxedTarget :name]
                                  [:declarations [:array :witness-row]] [:missingDependencies [:array :name]]
                                  [:sorryDep [:option :name]]]))
            build (:build shape)]
        (assoc shape :build (fn [values]
                             (let [w (build values)]
                               (-> w (assoc :runtimeProfile (select-keys w [:wordBits :target]))
                                   (dissoc :wordBits :target))))))
      (fail "Unknown typed IR projection kind" {:kind kind}))))

(defn ^:no-doc specification-reader
  "Pinned typed-IR decomposition over caller-owned readonly storage operations.
   OPERATIONS supplies :ref? and :node; :node returns the existing constructor,
   array, String and MPZ storage-view shapes. Capture one WORLD/scope identity.
   The caller owns exact carrier/kind validation, borrow lifetime, cycle checks,
   typed memoization and resource bounds. This factory neither walks a graph nor
   grants source, kernel or executable-code authority. Existing m.World callers
   continue through project; alternate walkers need not create a whole World."
  [operations world]
  (when-not (and (map? operations) (fn? (:ref? operations)) (fn? (:node operations)))
    (fail "Typed IR reader requires explicit readonly storage operations" {}))
  (fn [kind value] (describe operations world kind value)))

(defn project
  "Borrow VALUE under explicit pinned KIND (:decl, :name, :body, :expr,
   :ir-type, :witness, etc.). Result contains only immutable host JSON values.
   Memoization is per invocation and typed: erased representations can alias
   unrelated types. Cycles/malformed layouts fail; no RC or guest state changes."
  [world kind value]
  (let [read (specification-reader ops world)]
    (loop [todo [[:visit kind value]] results [] active #{} memo {}]
      (if (empty? todo)
        (do (when-not (= 1 (count results)) (fail "Invalid typed IR projection stack" {})) (peek results))
        (let [[op a b c] (peek todo) todo (pop todo)]
          (case op
            :visit
            (let [key (when (m/ref? b) [(:id b) a])]
              (cond
                (and key (contains? active key)) (fail "Cyclic typed IR value" {:kind a})
                (and key (contains? memo key)) (recur todo (conj results (get memo key)) active memo)
                :else
                (let [shape (read a b)]
                  (if (contains? shape :value)
                    (recur todo (conj results (:value shape)) active (if key (assoc memo key (:value shape)) memo))
                    (let [children (:children shape)]
                      (recur (into (conj todo [:finish key (count children) (:build shape)])
                                   (map #(into [:visit] %) (rseq children)))
                             results (if key (conj active key) active) memo))))))
            :finish
            (let [start (- (count results) b) children (into [] (subvec results start)) result (c children)]
              (recur todo (conj (subvec results 0 start) result) (disj active a)
                     (if a (assoc memo a result) memo)))))))))

(defn project-decl [world value] (project world :decl value))
(defn project-name [world value] (project world :name value))
(defn project-witness [world value] (project world :witness value))
