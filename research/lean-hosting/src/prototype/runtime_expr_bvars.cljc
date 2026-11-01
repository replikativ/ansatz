(ns prototype.runtime-expr-bvars
  "Pinned Lean4.33.1 kernel/expr.cpp:385–442 loose-bvar queries/lowering.
   Borrowed Expr/Nats; Bool or owned Expr result. Cached range prunes traversal;
   binder depth is uint32, with native overflow guards. Boxed indices return
   false/no-op. Lower compares full native scalar start/delta before uint32
   conversion, as its C wrapper does. Existing Expr rebuilds preserve annotations
   and pointer identity. No Java checking projection or guest callbacks."
  (:require [prototype.native-scalar :as native] [prototype.scalar :as scalar]
            [prototype.runtime-expr-transform :as transform]))
(def supported-symbols {"lean_expr_has_loose_bvar" {:arity 2} "lean_expr_lower_loose_bvars" {:arity 3}})
(defn- fail [s d] (throw (ex-info s d)))
(defn- retain [ops w v] ((:retain ops) w v 1))
(defn- release [ops w v] ((:release ops) w v 1))
(defn- u32 [n] (rem n 4294967296))
(defn- scalar-nat [ops v]
  (when-not ((:ref? ops) v)
    (let [n (native/nat-value v)]
      (when-not #?(:clj (<= n 9223372036854775807N) :cljs (js/Number.isSafeInteger n))
        (fail "Nat is outside exact native scalar representation" {})) n)))
(defn- node! [ops w v]
  (when-not ((:ref? ops) v) (fail "Expected loose-bvar Expr reference" {}))
  (let [n ((:node ops) w v) arity ({0 1 1 1 2 1 3 1 4 2 5 2 6 3 7 3 8 4 9 1 10 2 11 3} (:tag n))]
    (when-not (and (= :ctor (:kind n)) (some? arity) (= arity (count (:fields n))))
      (fail "Malformed loose-bvar Expr" {:tag (:tag n)})) n))
(defn- bvar-range [node]
  (rem (quot (scalar/read-bytes (:layout node) (:scalar-bytes node)
              {:index (count (:fields node)) :offset 0 :type "uint64" :region :scalar})
             #?(:clj 17592186044416N :cljs 17592186044416)) 1048576))
(defn- children [node offset]
  (let [indices (case (:tag node) 5 [0 1] (6 7) [1 2] 8 [1 2 3] 10 [1] 11 [2] [])]
    (mapv (fn [i] [i (:id (nth (:fields node) i))
                    (if (or (and (contains? #{6 7} (:tag node)) (= i 2))
                            (and (= 8 (:tag node)) (= i 3))) (u32 (inc offset)) offset)]) indices)))
(defn- at [root id] (assoc root :id id))
(defn- save-result [ops w state result]
  (let [n ((:node ops) w state) [root prior] (:fields n) w (retain ops w prior)
        [w owners] ((:allocate ops) w :ctor 1 [result prior])
        w ((:replace-node ops) w state (assoc n :fields [root owners]))]
    (release ops w prior)))
(defn evaluate [ops w symbol args]
  (when-not (= (get-in supported-symbols [symbol :arity]) (count args))
    (fail "Invalid loose-bvar primitive call" {:symbol symbol}))
  (let [root (first args) initial (node! ops w root) index (scalar-nat ops (second args))]
    (if (= symbol "lean_expr_has_loose_bvar")
      (if (nil? index) [w 0]
        (let [index (u32 index)]
          (loop [todo [[(:id root) 0]] seen #{}]
            (if-let [[id depth :as key] (peek todo)]
              (let [todo (pop todo) n (node! ops w (at root id)) wanted (u32 (+ index depth))]
                (cond
                  (contains? seen key) (recur todo seen)
                  (or (< wanted index) (>= wanted (bvar-range n))) (recur todo (conj seen key))
                  (and (= 0 (:tag n)) (= wanted (native/nat-value ops w (first (:fields n))))) [w 1]
                  :else (recur (into todo (map (fn [[_ id offset]] [id offset]) (reverse (children n depth))))
                               (conj seen key)))) [w 0]))))
      (let [delta (scalar-nat ops (nth args 2))]
        (if (or (nil? index) (nil? delta) (< index delta)
                (zero? (u32 delta)) (>= (u32 index) (bvar-range initial)))
          [(retain ops w root) root]
          (let [start (u32 index) delta (u32 delta)
                [w state] ((:allocate ops) (retain ops w root) :ctor 0 [root 0])]
            (loop [w w todo [[:visit (:id root) 0]] memo {}]
              (if-let [[action id depth details] (peek todo)]
                (let [todo (pop todo) key [id depth] value (at root id)]
                  (if (= action :build)
                    (let [n (node! ops w value)
                          fields (reduce (fn [fields [i child-id child-depth]]
                                           (assoc fields i (at root (get memo [child-id child-depth]))))
                                         (vec (:fields n)) details)
                          [w result] (transform/rebuild ops w value fields)]
                      (recur (save-result ops w state result) todo (assoc memo key (:id result))))
                    (if (contains? memo key) (recur w todo memo)
                      (let [n (node! ops w value) cutoff (u32 (+ start depth))
                            terminal? (or (< cutoff start) (>= cutoff (bvar-range n)))
                            index (when (= 0 (:tag n)) (native/nat-value ops w (first (:fields n))))
                            descendants (when-not terminal? (children n depth))]
                        (cond
                          (and (not terminal?) index (>= index cutoff))
                          (let [[w result] (transform/make-bvar ops w (max 0 (- index delta)))]
                            (recur (save-result ops w state result) todo (assoc memo key (:id result))))
                          (or terminal? (empty? descendants))
                          (recur (save-result ops (retain ops w value) state value) todo (assoc memo key id))
                          :else (recur w (into (conj todo [:build id depth descendants])
                                              (map (fn [[_ id offset]] [:visit id offset]) (reverse descendants))) memo))))))
                (let [result (at root (get memo [(:id root) 0])) w (retain ops w result)]
                  [(release ops w state) result])))))))))
