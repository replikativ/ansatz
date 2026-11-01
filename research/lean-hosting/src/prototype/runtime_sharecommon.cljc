(ns prototype.runtime-sharecommon
  "Lean 4.33.1 runtime/sharecommon.cpp sharecommon_quick_fn (819816b2).
   Borrow input, own output; rebuild constructors/arrays, intern exact raw bodies,
   reuse terminal representatives, leave opaque objects alone. Explicit stack.
   :sharecommon-profile defaults :native-layout. Explicit :immutable-text-v1
   admits immutable host Strings by value, which can increase sharing of enclosing
   constructors: this profile does NOT promise native pointer identity for text.
   Represented native String objects retain exact capacity-sensitive semantics in
   either profile. Native hash integers/allocator costs are not exposed here."
  (:require [prototype.native-scalar :as native] [prototype.scalar :as scalar] [prototype.constructor-layout :as constructor]))
(def supported-symbols {"lean_sharecommon_quick" {:arity 2}})
(defn- fail [s d] (throw (ex-info s d)))
(defn- keep! [ops w v] ((:retain ops) w v 1))
(defn- drop! [ops w v] ((:release ops) w v 1))
(defn- bytes! [xs]
  (when-not (and (vector? xs) (every? #(and (integer? %) (<= 0 % 255)) xs))
    (fail "Invalid ShareCommon byte storage" {})) xs)
(defn- immediate-key [profile v]
  (cond
    (native/native-scalar? v) [:scalar (native/payload v)]
    (and (integer? v) (<= 0 v) #?(:clj (<= v 9223372036854775807N) :cljs (js/Number.isSafeInteger v))) [:scalar v]
    (and (map? v) (= #{:tag} (set (keys v)))) [:scalar (native/nat-value (:tag v))]
    (and (= profile :immutable-text-v1) (string? v)) [:host-text v]
    :else (fail "ShareCommon needs a represented native value or explicit immutable-text profile"
                {:profile profile :value-type (str (type v))})))
(defn- ctor-storage [node]
  (when (seq (remove #{:kind :tag :fields :rc :layout :scalar-bytes :native-source-id :native-object-bytes :raw-clone-layout} (keys node)))
    (fail "ShareCommon constructor contains unrepresented runtime metadata" {}))
  (when (and (nil? (:layout node)) (seq (:scalar-bytes node)))
    (fail "ShareCommon scalar bytes lack constructor layout" {}))
  (let [n (count (:fields node)) layout (:layout node)
        _ (when layout (scalar/layout! layout))
        _ (when (and layout (not= n (:objects layout))) (fail "ShareCommon constructor layout mismatch" {}))
        size (if layout (+ (* 8 (:usize layout)) (:ssize layout)) 0)
        padded (* 8 (quot (+ size 7) 8)) base (* 8 n) memory (:scalar-bytes node {})]
    (when-not (and (integer? (:tag node)) (<= 0 (:tag node) 243) (< n 256))
      (fail "Invalid ShareCommon constructor" {}))
    (let [bytes (mapv (fn [i]
                        (if (contains? memory (+ base i)) (get memory (+ base i))
                          (if (< i size) (fail "Uninitialized ShareCommon scalar bytes" {:offset i}) 0)))
                      (range padded))]
      (bytes! bytes)
      {:bytes bytes :memory (into {} (map-indexed (fn [i b] [(+ base i) b]) bytes))})))
(defn- capacity! [node size]
  (let [cap (:native-capacity node)]
    (when-not (and (integer? cap) (<= size cap) #?(:clj true :cljs (js/Number.isSafeInteger cap)))
      (fail "ShareCommon terminal requires explicit native capacity" {:kind (:kind node)})) cap))
(defn- terminal-key [node]
  (when-not (empty? (:fields node)) (fail "ShareCommon terminal has object fields" {}))
  (case (:kind node)
    :mpz (do (when-not (and (= 250 (:tag node)) (integer? (:integer node))) (fail "Malformed MPZ" {}))
             [:mpz (:integer node)])
    :string (let [bytes (bytes! (:utf8-bytes node)) size (inc (count bytes)) cap (capacity! node size)]
              (when-not (and (= 249 (:tag node)) (= size (:native-byte-size node))
                             (integer? (:native-utf8-length node)) (<= 0 (:native-utf8-length node)))
                (fail "Incomplete native String layout for ShareCommon" {}))
              [:string size cap (:native-utf8-length node) bytes])
    (:byte-array :scalar-array :float-array)
    (let [width (case (:kind node) :byte-array 1 :float-array 8 (:element-bytes node))
          bytes (bytes! (if (= :float-array (:kind node))
                          (vec (mapcat #(scalar/float-bytes "float" %) (:values node))) (:bytes node)))]
      (when-not (and (= 248 (:tag node)) (integer? width) (<= 1 width 255) (zero? (rem (count bytes) width)))
        (fail "Malformed native scalar array" {}))
      (let [size (quot (count bytes) width)] [:sarray width size (capacity! node size) bytes]))))
(def ^:private opaque-kinds #{:closure :thunk :task :promise :ref :external :reserved :mutex :resource :stream})
(defn evaluate [ops world symbol args]
  (when-not (and (= symbol "lean_sharecommon_quick") (= 2 (count args)))
    (fail "Invalid ShareCommon runtime call" {:symbol symbol}))
  (let [profile (or (:sharecommon-profile world) (get-in world [:world-context :sharecommon-profile]) :native-layout)
        _ (when-not (contains? #{:native-layout :immutable-text-v1} profile) (fail "Unknown ShareCommon profile" {:profile profile}))
        root (second args) ref? (:ref? ops) node (:node ops)
        token (fn [v] (if (ref? v) [:pointer (:id v)] (immediate-key profile v)))]
    (if-not (ref? root) (do (token root) [world root])
      ;; State owns borrowed root and a list of every fresh canonical object.
      ;; Local memo tables borrow these anchors; they never own hidden guest refs.
      (let [world (keep! ops world root) [world state] ((:allocate ops) world :ctor 0 [root 0])]
        (loop [world world work [[:visit root]] memo {} intern {} active #{}]
          (if-let [[action value details] (peek work)]
            (let [work (pop work) id (:id value)]
              (if (= action :visit)
                (if (contains? memo id) (recur world work memo intern active)
                  (let [n (node world value) kind (:kind n)]
                    (cond
                      (contains? opaque-kinds kind) (recur world work (assoc memo id value) intern active)
                      (contains? #{:mpz :string :byte-array :scalar-array :float-array} kind)
                      (let [k (terminal-key n) canonical (get intern k value)]
                        (recur world work (assoc memo id canonical) (assoc intern k canonical) active))
                      (contains? #{:ctor :array} kind)
                      (do (when (contains? active id) (fail "Cyclic ShareCommon graph" {:id id}))
                          (let [_ (when (and (= kind :array) (not= 246 (:tag n)))
                                    (fail "Malformed ShareCommon object Array" {}))
                                fields (vec (:fields n)) storage (when (= kind :ctor) (ctor-storage n))]
                            (recur world (into (conj work [:build value [n storage]])
                                               (map #(vector :visit %) (reverse (filter ref? fields))))
                                   memo intern (conj active id))))
                      :else (fail "Unsupported ShareCommon object layout" {:kind kind}))))
                (let [[n storage] details
                      fields (mapv #(if (ref? %) (get memo (:id %)) %) (:fields n))
                      k (if (= :array (:kind n)) [:array (mapv token fields)]
                            [:ctor (:tag n) (count fields) (mapv token fields) (:bytes storage)])]
                  (if-let [canonical (get intern k)]
                    (recur world work (assoc memo id canonical) intern (disj active id))
                    (let [world (reduce #(keep! ops %1 %2) world fields)
                          [world result] ((:allocate ops) world (:kind n) (:tag n) fields)
                          fresh (node world result)
                          fresh (if (= :array (:kind n)) (assoc fresh :native-capacity (count fields))
                                  (constructor/clone-storage
                                    (cond-> (assoc fresh :scalar-bytes (:memory storage))
                                      (seq (:bytes storage))
                                      (assoc :layout {:objects (count fields) :usize 0 :ssize (count (:bytes storage))}))))
                          world ((:replace-node ops) world result fresh)
                          state-node (node world state) [source prior] (:fields state-node)
                          world (keep! ops world prior)
                          [world owners] ((:allocate ops) world :ctor 1 [result prior])
                          world ((:replace-node ops) world state (assoc state-node :fields [source owners]))
                          world (drop! ops world prior)]
                      (recur world work (assoc memo id result) (assoc intern k result) (disj active id)))))))
            (let [result (get memo (:id root)) world (keep! ops world result)]
              [(drop! ops world state) result])))))))

