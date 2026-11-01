(ns prototype.runtime-expr-transform
  "Pinned kernel abstract.cpp/instantiate.cpp/expr.cpp de Bruijn operations.
   No checking projection: names, metadata, binder annotations and guest sharing
   remain guest values. Cached fields follow Lean/Expr.lean:473–513. Inputs are
   borrowed, output owned. A temporary heap node owns traversal/cache values;
   work and memo keys contain only scalar IDs, depth and mode."
  (:require [prototype.runtime-expr :as expr] [prototype.runtime-string :as string]
            [prototype.runtime-object :as object] [prototype.native-scalar :as native]
            [prototype.scalar :as scalar]))
(def supported-symbols
  (into {} (map (fn [[s n]] [s {:arity n}])
                {"lean_expr_abstract_range" 3 "lean_expr_abstract" 2
                 "lean_expr_instantiate1" 2 "lean_expr_instantiate" 2
                 "lean_expr_instantiate_range" 4 "lean_expr_instantiate_rev" 2
                 "lean_expr_instantiate_rev_range" 4 "lean_expr_lift_loose_bvars" 3})))
(defn- fail [s d] (throw (ex-info s d)))
(defn- pow2 [n] #?(:clj (bigint (.shiftLeft java.math.BigInteger/ONE n)) :cljs (js/Math.pow 2 n)))
(defn- bits [n offset width] (rem (quot n (pow2 offset)) (pow2 width)))
(defn- node! [ops world value]
  (when-not ((:ref? ops) value) (fail "Expected guest Expr reference" {}))
  (let [node ((:node ops) world value) counts {0 1 1 1 2 1 3 1 4 2 5 2 6 3 7 3 8 4 9 1 10 2 11 3}]
    (when-not (and (= :ctor (:kind node)) (= (get counts (:tag node)) (count (:fields node))))
      (fail "Malformed transform Expr" {:tag (:tag node)})) node))
(defn- scalar-at [node offset type]
  (scalar/read-bytes (:layout node) (:scalar-bytes node)
                    {:index (count (:fields node)) :offset offset :type type :region :scalar}))
(defn- data [ops world value] (scalar-at (node! ops world value) 0 "uint64"))
(defn- mix [ops world a b] (second (string/evaluate ops world "lean_uint64_mix_hash" [a b])))
(defn- retain [ops world v] ((:retain ops) world v 1))
(defn- release [ops world v] ((:release ops) world v 1))
(defn- allocate-expr [ops world tag fields cache annotation]
  (let [world (reduce #(retain ops %1 %2) world fields)
        [world value] ((:allocate ops) world :ctor tag fields)
        layout {:objects (count fields) :usize 0 :ssize (if (some? annotation) 9 8)}
        memory (scalar/write-bytes layout {} {:index (count fields) :offset 0 :type "uint64" :region :scalar} cache)
        memory (if (some? annotation)
                 (scalar/write-bytes layout memory {:index (count fields) :offset 8 :type "uint8" :region :scalar} annotation) memory)]
    [((:replace-node ops) world value (assoc ((:node ops) world value) :layout layout :scalar-bytes memory)) value]))
(defn make-bvar "Borrow an index and return an owned bvar with exact native cache." [ops world index]
  (let [n (native/nat-value ops world index)
        cache (second (expr/evaluate ops world "lean_expr_mk_data" [(mix ops world 7 n) (inc n) 0 0 0 0 0]))]
    (allocate-expr ops world 0 [index] cache nil)))
(defn- name-hash [ops world value]
  (if ((:ref? ops) value) (scalar-at ((:node ops) world value) 0 "uint64") 1723))
(defn- zero?* [ops value]
  (and (not ((:ref? ops) value))
       (or (= 0 value) (and (native/native-scalar? value) (= 0 (native/payload value)))
           (and (map? value) (= 0 (:tag value))))))
(defn- level-cache [ops world value]
  (if (zero?* ops value) 2221
    (let [node ((:node ops) world value)]
      (when-not (and (= :ctor (:kind node))
                     (= (get {1 1 2 2 3 2 4 1 5 1} (:tag node)) (count (:fields node))))
        (fail "Invalid level in Expr rebuild" {}))
      (scalar-at node 0 "uint64"))))
(defn- level-list [ops world value]
  (loop [value value seen #{} out []]
    (if (zero?* ops value) out
      (let [node ((:node ops) world value)]
        (when (contains? seen (:id value)) (fail "Cyclic Expr universe list" {}))
        (when-not (and (= :ctor (:kind node)) (= 1 (:tag node)) (= 2 (count (:fields node))))
          (fail "Malformed Expr universe list" {}))
        (recur (second (:fields node)) (conj seen (:id value)) (conj out (first (:fields node))))))))
(defn- rebuild-universes [ops world tag fields]
  (let [levels (if (= tag 3) [(fields 0)] (level-list ops world (fields 1)))
        caches (mapv #(level-cache ops world %) levels)
        hashes (mapv #(bits % 0 32) caches)
        hash (if (= tag 3) (mix ops world 11 (first hashes))
               (mix ops world 5 (mix ops world (name-hash ops world (fields 0))
                                    (reduce #(mix ops world %1 %2) 7 hashes))))
        cache (second (expr/evaluate ops world "lean_expr_mk_data"
                        [hash 0 0 0 0 (reduce max 0 (map #(bits % 32 1) caches))
                         (reduce max 0 (map #(bits % 33 1) caches))]))]
    (allocate-expr ops world tag fields cache nil)))
(defn rebuild
  "Borrow original Expr and replacement fields. Reuse its exact pointer when
   unchanged, otherwise compute fresh cache bytes while retaining all fields.
   Sort/constant universe updates and app/binders/let/mdata/proj are accepted."
  [ops world original fields]
  (let [node (node! ops world original) old (vec (:fields node)) fields (vec fields) tag (:tag node)]
    (when-not (= (count old) (count fields)) (fail "Transform field arity mismatch" {}))
    (if (= old fields) [(retain ops world original) original]
      (if (contains? #{3 4} tag) (rebuild-universes ops world tag fields)
      (let [indices (case tag 5 [0 1] (6 7) [1 2] 8 [1 2 3] 10 [1] 11 [2]
                         (fail "Unsupported Expr structural rebuild" {:tag tag}))
            caches (mapv #(data ops world (nth fields %)) indices)
            hashes (mapv #(bits % 0 32) caches)
            depth (inc (reduce max (map #(bits % 32 8) caches)))
            ranges (mapv #(bits % 44 20) caches)
            bvar-range (case tag (6 7) (max (ranges 0) (max 0 (dec (ranges 1))))
                            8 (max (ranges 0) (ranges 1) (max 0 (dec (ranges 2))))
                            (reduce max ranges))
            hash (case tag
                   5 nil
                   (6 7) (mix ops world depth (mix ops world (hashes 0) (hashes 1)))
                   8 (mix ops world depth (mix ops world (hashes 0) (mix ops world (hashes 1) (hashes 2))))
                   10 (mix ops world depth (hashes 0))
                   11 (mix ops world depth
                           (mix ops world (name-hash ops world (fields 0))
                                (mix ops world (mod (native/nat-value ops world (fields 1)) (pow2 64)) (hashes 0)))))
            cache (if (= tag 5) (second (expr/evaluate ops world "lean_expr_mk_app_data" caches))
                    (second (expr/evaluate ops world "lean_expr_mk_data"
                              (into [hash bvar-range depth] (map (fn [i] (reduce max (map #(bits % i 1) caches))) (range 40 44))))))
            annotation (when (contains? #{6 7 8} tag) (scalar-at node 8 "uint8"))]
        (allocate-expr ops world tag fields cache annotation))))))
(defn- array-fields [ops world value]
  (let [node ((or (:borrow-node ops) (:node ops)) world value)]
    (when-not (= :array (:kind node)) (fail "Expected transform substitution array" {})) (:fields node)))
(defn- scalar-nat [ops world value]
  (when-not ((:ref? ops) value) (native/nat-value ops world value)))
(defn- u32 [n] (rem n 4294967296))
(defn- source-ref [template id] (assoc template :id id))
(defn- children [node offset]
  (let [f (vec (:fields node)) next-offset (u32 (inc offset))]
    (case (:tag node)
      5 [[0 (:id (f 0)) offset] [1 (:id (f 1)) offset]]
      (6 7) [[1 (:id (f 1)) offset] [2 (:id (f 2)) next-offset]]
      8 [[1 (:id (f 1)) offset] [2 (:id (f 2)) offset] [3 (:id (f 3)) next-offset]]
      10 [[1 (:id (f 1)) offset]] 11 [[2 (:id (f 2)) offset]] [])))
(defn- save-result [ops world state key result]
  ;; RESULT is owned. The old list owner is transferred from state to its new
  ;; cons; no guest reference is stored exclusively in metadata.
  (let [node ((:node ops) world state) [root substitutions prior] (:fields node)
        world (retain ops world prior)
        [world list] ((:allocate ops) world :ctor 1 [result prior])
        world ((:replace-node ops) world state
                (-> node (assoc :fields [root substitutions list]) (assoc-in [:memo key] (:id result))))]
    (release ops world prior)))
(defn- replace-state [ops world state f] ((:replace-node ops) world state (f ((:node ops) world state))))
(defn- abstract-hit [ops world node substitutions n offset]
  (when (contains? #{1 2} (:tag node))
    (loop [i (dec n)]
      (when (<= 0 i)
        (let [candidate (node! ops world (nth substitutions i))]
          (if (and (= (:tag node) (:tag candidate))
                   (= 1 (second (object/evaluate ops world "lean_name_eq"
                                  [(first (:fields node)) (first (:fields candidate))]))))
            (+ offset (- n i 1)) (recur (dec i))))))))
(defn evaluate [ops world symbol args]
  (when-not (= (get-in supported-symbols [symbol :arity]) (count args))
    (fail "Invalid Expr transform runtime call" {:symbol symbol}))
  (let [root (first args) _ (node! ops world root)
        abstract? (contains? #{"lean_expr_abstract" "lean_expr_abstract_range"} symbol)
        lift? (= symbol "lean_expr_lift_loose_bvars")
        one? (= symbol "lean_expr_instantiate1")
        range? (contains? #{"lean_expr_instantiate_range" "lean_expr_instantiate_rev_range"} symbol)
        reversed? (contains? #{"lean_expr_instantiate_rev" "lean_expr_instantiate_rev_range"} symbol)
        substitutions (cond lift? [] one? [(second args)] :else (array-fields ops world (last args)))
        [begin end] (if range?
                      (let [b (scalar-nat ops world (second args)) e (scalar-nat ops world (nth args 2))]
                        (when-not (and b e (<= b e (count substitutions)))
                          (fail "Invalid Expr instantiate range" {:runtime-limit :native-panic})) [b e])
                      [0 (count substitutions)])
        substitutions (if range? (mapv #(nth substitutions %) (range (int begin) (int end))) substitutions)
        n (if (= symbol "lean_expr_abstract_range")
            (if-some [n (scalar-nat ops world (second args))] (min n (count substitutions)) (count substitutions))
            (count substitutions))
        cutoff (when lift? (scalar-nat ops world (second args)))
        delta (when lift? (scalar-nat ops world (nth args 2)))
        spec {:abstract? abstract? :lift? lift? :one? one? :reversed? reversed?
              :n n :cutoff (when cutoff (u32 cutoff)) :delta (when delta (u32 delta))}
        ;; Keep the actual array owner, rather than a hidden vector of refs.
        subst-owner (cond lift? 0 one? (second args) :else (last args))
        world (retain ops (retain ops world root) subst-owner)
        [world state] ((:allocate ops) world :expr-transform 0 [root subst-owner 0])
        initial-mode (if lift? [:lift (:cutoff spec) (:delta spec)] :main)
        world (replace-state ops world state #(assoc % :memo {} :active #{} :work [[:visit initial-mode (:id root) 0]]))]
    (loop [world world]
      (let [state-node ((:node ops) world state) frame (peek (:work state-node))]
        (if-not frame
          (let [id (get (:memo state-node) [initial-mode (:id root) 0]) result (source-ref root id)
                world (retain ops world result)]
            [(release ops world state) result])
          (let [[action mode id offset details] frame key [mode id offset]
                value (source-ref root id)
                world (replace-state ops world state #(update % :work pop))]
            (cond
              (= action :alias)
              (let [result (source-ref root (get (:memo ((:node ops) world state)) details))]
                (recur (save-result ops (retain ops world result) state key result)))
              (= action :build)
              (let [node (node! ops world value)
                    memo (:memo ((:node ops) world state))
                    fields (reduce (fn [fields [i child child-offset]]
                                     (assoc fields i (source-ref root (get memo [mode child child-offset]))))
                                   (vec (:fields node)) details)
                    [world result] (rebuild ops world value fields)
                    world (replace-state ops world state #(update % :active disj key))]
                (recur (save-result ops world state key result)))
              (contains? (:memo state-node) key) (recur world)
              :else
              (do
                (when (contains? (:active state-node) key) (fail "Cyclic Expr transform input" {}))
                (let [node (node! ops world value) cache (data ops world value) bvar-range (bits cache 44 20)
                      lift-mode? (vector? mode)
                      [_ s d] (when lift-mode? mode)
                      threshold (when s (u32 (+ s offset)))
                      skip? (if lift-mode?
                              (or (nil? s) (nil? d) (zero? d) (< threshold s) (>= threshold bvar-range))
                              (if abstract? (and (zero? (bits cache 40 1)) (zero? (bits cache 41 1)) (zero? (bits cache 42 1)))
                                  (or (and (zero? n) (not reversed?)) (>= offset bvar-range))))
                      hit (when (and abstract? (not lift-mode?) (not skip?))
                            (abstract-hit ops world node substitutions n offset))
                      bvar (when (= 0 (:tag node)) (native/nat-value ops world (first (:fields node))))]
                  (cond
                    skip? (recur (save-result ops (retain ops world value) state key value))
                    (some? hit) (let [[world result] (make-bvar ops world hit)]
                                  (recur (save-result ops world state key result)))
                    (and lift-mode? bvar (>= bvar threshold))
                    (let [[world result] (make-bvar ops world (+ bvar d))]
                      (recur (save-result ops world state key result)))
                    (and (not abstract?) (not lift-mode?) bvar (>= bvar offset))
                    (if (< bvar (+ offset n))
                      (let [i (- bvar offset) i (if reversed? (- n i 1) i)
                            replacement (nth substitutions (int i))
                            lift-mode [:lift 0 offset]
                            lift-key [lift-mode (:id replacement) 0]]
                        (recur (replace-state ops world state
                                 #(update % :work into [[:alias mode id offset lift-key]
                                                       [:visit lift-mode (:id replacement) 0]]))))
                      (let [[world result] (make-bvar ops world (- bvar n))]
                        (recur (save-result ops world state key result))))
                    :else
                    (let [children (children node offset)]
                      (if (empty? children)
                        (recur (save-result ops (retain ops world value) state key value))
                        (recur (replace-state ops world state
                                 #(-> % (update :active conj key)
                                      (update :work into
                                        (into [[:build mode id offset children]]
                                              (map (fn [[_ child depth]] [:visit mode child depth]) (rseq children)))))))))))))))))))
