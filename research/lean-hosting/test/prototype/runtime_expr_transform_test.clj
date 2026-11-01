(ns prototype.runtime-expr-transform-test
  (:require [clojure.test :refer [deftest is]] [clojure.data.json :as json]
            [clojure.string :as str] [clojure.walk :as walk] [prototype.runtime-expr-transform :as transform]
            [prototype.runtime-expr :as expr] [prototype.runtime-string :as string]
            [prototype.machine :as m] [prototype.scalar :as scalar]
            [prototype.native-scalar :as native] [prototype.mutable :as u]))
(def ops {:ref? m/ref? :node m/node :allocate m/allocate :retain m/retain :release m/release :replace-node m/replace-node})
(def mutable-ops
  {:ref? m/ref? :node (fn [s r] (update (#'u/node s r) :fields vec))
   :allocate (fn [s k t f] [s (#'u/allocate! s k t f nil)])
   :retain (fn [s v n] (u/retain! s v n) s) :release (fn [s v n] (u/release! s v n) s)
   :replace-node #'u/replace-node!})
(defn- word [world tag fields value annotation]
  (let [[world ref] (m/scalar-constructor world tag fields {:objects (count fields) :usize 0 :ssize (if annotation 9 8)})
        layout (:layout (m/node world ref))
        bytes (scalar/write-bytes layout {} {:index (count fields) :offset 0 :type "uint64" :region :scalar} value)
        bytes (if annotation (scalar/write-bytes layout bytes {:index (count fields) :offset 8 :type "uint8" :region :scalar} annotation) bytes)]
    [(assoc-in world [:heap (:id ref) :scalar-bytes] bytes) ref]))
(defn- fvar [world tag]
  (let [[world name] (word world 1 [0 "x"] 0 nil)
        cache (second (expr/evaluate ops world "lean_expr_mk_data" [13 0 0 (if (= tag 1) 1 0) (if (= tag 2) 1 0) 0 0]))]
    (word world tag [name] cache nil)))
(defn- app [world a b]
  (let [world (-> world (m/retain a 1) (m/retain b 1))
        data #(second (expr/evaluate ops world "lean_expr_data" [%]))
        cache (second (expr/evaluate ops world "lean_expr_mk_app_data" [(data a) (data b)]))]
    (word world 5 [a b] cache nil)))
(defn- bvar-index [world value] (native/nat-value ops world (first (:fields (m/node world value)))))

(deftest abstraction-is-borrowed-and-last-duplicate-wins-with-cached-sharing
  (let [[world f] (fvar (m/world {}) 1)
        [world root] (app world f f)
        world (m/retain world f 2)
        [world subst] (m/allocate world :array 246 [f f])
        before world
        [next result] (transform/evaluate ops world "lean_expr_abstract_range" [root 2 subst])
        children (:fields (m/node next result))
        cleaned (m/release next result 1)]
    (is (= [0 0] (mapv #(bvar-index next %) children)))
    (is (= (first children) (second children)))
    (is (= 2 (:rc (m/node next (first children)))))
    (is (= (:heap before) (:heap cleaned)))
    (is (not-any? #(= :expr-transform (:kind %)) (vals (:heap next))))
    (is (= (:rc (m/node before root)) (:rc (m/node next root)))))
  (let [[world f] (fvar (m/world {}) 1)
        [world meta] (fvar world 2)
        [world subst] (m/allocate world :array 246 [meta])
        [world result] (transform/evaluate ops world "lean_expr_abstract_range" [f 1 subst])]
    (is (= f result))
    (is (= 2 (:rc (m/node world f))))))

(deftest capture-avoiding-substitution-lifts-under-binders
  (let [[world zero] (transform/make-bvar ops (m/world {}) 0)
        [world one] (transform/make-bvar ops world 1)
        [world prototype] (word world 6 [0 zero one] 0 2)
        ;; Force exact constructor cache computation through one changed field.
        [world lambda] (transform/rebuild ops world prototype [0 one one])
        before world
        [next result] (transform/evaluate ops world "lean_expr_instantiate1" [lambda zero])
        [_ type body] (:fields (m/node next result))]
    (is (= 0 (bvar-index next type)))
    (is (= 1 (bvar-index next body)))
    (is (= 2 (scalar/read-bytes (:layout (m/node next result)) (:scalar-bytes (m/node next result))
                               {:index 3 :offset 8 :type "uint8" :region :scalar})))
    (is (= (:heap before) (:heap (m/release next result 1))))))

(def ^:dynamic *build-cache* nil)
(defn build [world value]
  (if-let [existing (when (and *build-cache* (= "expr" (:kind value))) (get @*build-cache* (:nodeId value)))]
    [(m/retain world existing 1) existing]
    (let [result (cond
    (map? value)
    (case (:kind value)
      "name" (if (= 0 (:tag value)) [world 0]
               (let [[world parent] (build world (:parent value))]
                 (word world (:tag value) [parent (if (= 2 (:tag value)) (bigint (:value value)) (:value value))]
                       (bigint (:hash value)) nil)))
      "expr" (let [[world fields] (reduce (fn [[world fields] field]
                                            (let [[world field] (build world field)] [world (conj fields field)]))
                                          [world []] (:fields value))]
               (word world (:tag value) fields (bigint (:data value)) (:annotation value))))
    (= value "empty-metadata") (m/allocate world :ctor 0 [0])
    (string? value) [world (bigint value)]
    :else [world value])]
      (when (and *build-cache* (= "expr" (:kind value)))
        (swap! *build-cache* assoc (:nodeId value) (second result)))
      result)))
(defn- normalized-name [world value]
  (if-not (m/ref? value) {:kind "name" :tag 0}
    (let [node (m/node world value) [parent value] (:fields node)]
      {:kind "name" :tag (:tag node) :parent (normalized-name world parent)
       :value (if (= 2 (:tag node)) (str (native/nat-value ops world value)) value)
       :hash (str (scalar/read-bytes (:layout node) (:scalar-bytes node)
                                    {:index 2 :offset 0 :type "uint64" :region :scalar}))})))
(defn normalized [world value]
  (let [node (m/node world value) fields (:fields node) tag (:tag node)
        expr #(normalized world %) name #(normalized-name world %)
        fields (case tag 0 [(str (native/nat-value ops world (fields 0)))]
                        (1 2) [(name (fields 0))] 3 [0] 4 [(name (fields 0)) 0]
                        5 (mapv expr fields)
                        (6 7) [(name (fields 0)) (expr (fields 1)) (expr (fields 2))]
                        8 [(name (fields 0)) (expr (fields 1)) (expr (fields 2)) (expr (fields 3))]
                        10 ["empty-metadata" (expr (fields 1))]
                        11 [(name (fields 0)) (str (native/nat-value ops world (fields 1))) (expr (fields 2))])]
    {:kind "expr" :tag tag :fields fields
     :data (str (second (expr/evaluate ops world "lean_expr_data" [value])))
     :annotation (when (contains? #{6 7 8} tag)
                   (scalar/read-bytes (:layout node) (:scalar-bytes node) {:index (count (:fields node)) :offset 8 :type "uint8" :region :scalar}))}))

(defn- boxed-nat [world value]
  (let [n (bigint value)]
    (if (<= n 9223372036854775807N) [world n]
      (let [[world ref] (m/allocate world :mpz 250 [])]
        [(assoc-in world [:heap (:id ref) :integer] n) ref]))))
(defn- case-world [case]
  (binding [*build-cache* (atom {})]
  (let [[world root] (build (m/world {}) (:input case))
        [world substitutions] (reduce (fn [[w out] value] (let [[w v] (build w value)] [w (conj out v)]))
                                      [world []] (:substitutions case))
        [world array] (m/allocate world :array 246 substitutions)
        [world params] (reduce (fn [[w out] value] (let [[w v] (boxed-nat w value)] [w (conj out v)]))
                              [world []] (:params case))
        symbol (:symbol case)
        args (clojure.core/case symbol "lean_expr_instantiate1" [root (first substitutions)]
                          "lean_expr_abstract_range" [root (first params) array]
                          "lean_expr_lift_loose_bvars" (into [root] params)
                          ("lean_expr_instantiate_range" "lean_expr_instantiate_rev_range") (conj (into [root] params) array)
                          [root array])]
    [world root args])))
(deftest native-differential-caches-binder-depth-ranges-and-ownership
  (let [cases (mapv #(json/read-str % :key-fn keyword) (str/split-lines (slurp "fixtures/runtime-expr-transforms.jsonl")))]
    (is (= 195 (count cases)))
    (doseq [case cases]
      (let [[world root args] (case-world case)
            [next result] (transform/evaluate ops world (:symbol case) args)
            mutable (u/thaw world)
            [_ mutable-result] (transform/evaluate mutable-ops mutable (:symbol case) args)
            mutable-world (u/freeze mutable)]
        (is (= (walk/postwalk #(if (map? %) (dissoc % :nodeId) %) (:output case)) (normalized next result)) (:label case))
        (is (= (:sameRoot case) (= root result)) (:label case))
        (is (= (:heap world) (:heap (m/release next result 1))) (:label case))
        (is (= result mutable-result) (:label case))
        (is (= (:heap next) (:heap mutable-world)) (:label case))))))

(deftest deep-dags-use-an-explicit-heap-work-stack
  (let [[world free] (fvar (m/world {}) 1)
        [world root] (loop [world world root free n 3000]
                       (if (zero? n) [world root]
                         (let [[world root] (app world root free)] (recur world root (dec n)))))
        [world subst] (m/allocate (m/retain world free 1) :array 246 [free])
        before world
        [world result] (transform/evaluate ops world "lean_expr_abstract_range" [root 1 subst])]
    (is (= 3000 (loop [value result depth 0]
                  (let [node (m/node world value)]
                    (if (= 5 (:tag node)) (recur (first (:fields node)) (inc depth)) depth)))))
    (is (= (:heap before) (:heap (m/release world result 1))))))

(defn- build-level [world value]
  (if (= 0 (:tag value)) [world 0]
    (let [[world fields] (reduce (fn [[world fields] child]
                                  (let [[world child] (if (map? child) (build-level world child) [world child])]
                                    [world (conj fields child)])) [world []] (:fields value))]
      (word world (:tag value) fields (bigint (:data value)) nil))))
(defn- build-levels [world values]
  (reduce (fn [[world out] value] (let [[world value] (build-level world value)] [world (conj out value)])) [world []] values))
(deftest native-sort-and-constant-rebuild-caches-include-universe-flags-and-list-hash
  (let [cases (mapv #(json/read-str % :key-fn keyword) (str/split-lines (slurp "fixtures/runtime-expr-rebuilds.jsonl")))]
    (is (= 6 (count cases)))
    (doseq [case cases]
      (let [[world before-levels] (build-levels (m/world {}) (:before case))
            [world after-levels] (build-levels world (:after case))
            [world before] (if (= 3 (:tag case)) [world before-levels]
                              (let [[world list] (m/guest-list world before-levels)] [world [0 list]]))
            [world after] (if (= 3 (:tag case)) [world after-levels]
                             (let [[world list] (m/guest-list world after-levels)] [world [0 list]]))
            [world original] (word world (:tag case) before (bigint (:beforeData case)) nil)
            before-world world
            [world result] (transform/rebuild ops world original after)]
        (is (= (bigint (:afterData case)) (second (expr/evaluate ops world "lean_expr_data" [result]))))
        (is (= after (:fields (m/node world result))))
        (is (= (:heap before-world) (:heap (m/release world result 1))))))))
