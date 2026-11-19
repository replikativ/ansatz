(ns ansatz.clj-model-colls-test
  "PR G2a: sequences, maps, sets, strings, higher-order functions, varargs and `case` in the
   kernel model of Clojure (ansatz.clj-model.colls, ansatz.clj-model.translate)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.clj-check :as cc]
            [ansatz.clj-model :as m]
            [ansatz.clj-model.translate :as tr]
            [ansatz.clj-model.boundary :as b]
            [ansatz.surface.data :as data]))

(defn- define-models! []
  ;; a map-transforming function over Value: select-keys, update, reduce over a vector of keys
  (a/foreign ^:model summarize [m :- Value] Value
             (fn [m]
               (let [r (update (select-keys m [:a :b]) :a (fn [x] (if (int? x) x 0)))]
                 (assoc r :sum (reduce (fn [acc k] (+ acc (get r k 0))) 0 [:a :b])))))
  ;; a variadic function: the extra declared parameters reach `more` as a seq
  (a/foreign ^:model sum3 [x :- Int, y :- Int, z :- Int] Int (fn [x & more] (reduce + x more)))
  ;; case: hashed-key equality tests, a list groups alternatives
  (a/foreign ^:model code [s :- String] Int (fn [s] (case s "a" 1 ("b" "c") 2 0)))
  ;; sorted keys of a map, as a vector of strings
  (a/foreign ^:model key-names [m :- Value] Value (fn [m] (mapv name (sort (keys m))))))

(defn- setup [f]
  (binding [a/*verbose* false]
    (a/load-init!)
    (data/install-value-type!)
    (b/install-codecs!)
    (define-models!)
    (f)))

(use-fixtures :once fixtures/isolated-session setup)

(defn- run-op [k & xs]
  (if-let [{v :some} (m/opt-value (apply (m/model-fn k) (map m/edn->cljv xs)))]
    (m/cljv->edn v)
    :none))

(defn- run-args
  "Run a variadic model op (one chain of arguments)."
  [k & xs]
  (if-let [{v :some} (m/opt-value ((m/model-fn k) (nth (m/edn->cljv (vec xs)) 1)))]
    (m/cljv->edn v)
    :none))

(defn- big-map [] (zipmap (map #(keyword (str "k" %)) (range 10)) (range 10)))

(deftest ops-at-runtime
  (doseq [[k args expected]
          [["CljM.seq" [[]] nil] ["CljM.seq" ['(1 2)] '(1 2)] ["CljM.first" [{:a 1}] [:a 1]]
           ["CljM.first" [#{1 2}] :none] ["CljM.first" [#{1}] 1] ["CljM.rest" [[1]] ()]
           ["CljM.conj1" [nil 1] '(1)] ["CljM.conj1" [[1] 2] [1 2]] ["CljM.conj1" [{} [:a 1]] {:a 1}]
           ["CljM.into" [{} #{[:a 1] [:b 2]}] :none] ["CljM.into" [#{} [1 1 2]] #{1 2}]
           ["CljM.range" [0 3 1] (seq [0 1 2])] ["CljM.range" [0 10 0] :none] ["CljM.take" [2 [1 2 3]] (seq [1 2])]
           ["CljM.nth3" [{} -1 :nf] :nf] ["CljM.sort" [#{3 1 2}] (seq [1 2 3])] ["CljM.sort" [[1 "a"]] :none]
           ["CljM.subs3" ["abc" 1 2] "b"] ["CljM.subs" ["😀" 0] :none]
           ["CljM.name" [:a/b] "b"] ["CljM.keyword" ["a/b"] :a/b] ["CljM.count" ["ab"] 2] ["CljM.count" ["😀"] :none]
           ["CljM.hashMapOk" [{:a 1}] :none]]]
    (is (m/strict= expected (apply run-op k args)) (str k " " (pr-str args))))
  (doseq [[k args expected]
          [["CljM.str" [1 :a nil "s" \c -12] "1:asc-12"] ["CljM.merge" [nil false] nil] ["CljM.merge" [5] 5]
           ["CljM.max" [3 9 2] 9] ["CljM.max" ["a"] "a"] ["CljM.concat" [[1] '(2)] (seq [1 2])]]]
    (is (m/strict= expected (apply run-args k args)) (str k " " (pr-str args)))))

(deftest hash-order-taint
  (testing "a seq over a hash-ordered collection has its elements but no order"
    (let [ks (run-op "CljM.keys" (big-map))]
      (is (:ansatz.clj-model/unordered (meta ks)))
      (is (m/strict= (keys (big-map)) ks))
      (is (m/strict= (map identity (reverse (keys (big-map)))) ks) "compared as a multiset")))
  (testing "(first (keys m)) is no claim on a hash map; (sort (keys m)) is"
    (let [first-row {:id :showcase/first-keys :form '(first (keys m)) :params '[[m :kmap]]}
          sort-row {:id :showcase/sort-keys :form '(sort (keys m)) :params '[[m :kmap]]}
          f (:counts (cc/run-model-row first-row))
          s (:counts (cc/run-model-row sort-row))]
      (is (zero? (:model-bug f)))
      (is (pos? (:no-claim f)) "the first key of a map of 9+ entries depends on hash order")
      (is (zero? (:model-bug s)))
      (is (zero? (:no-claim s)) "sorting forgets the order")))
  (testing "a hash map never shrinks back into an array map"
    (let [row {:id :showcase/hash-map-dissoc :params '[[x :int]]
               :form '(vec (keys (dissoc (hash-map :a 1 :b 2 :c 3 :d 4 :e 5 :f 6 :g 7 :h 8 :i x) :a)))}
          {:keys [counts]} (cc/run-model-row row)]
      (is (zero? (:model-bug counts)))
      (is (zero? (:agree counts)) "an 8-entry hash map's order is never claimed")
      (is (pos? (:no-claim counts))))
    (is (= :none (run-op "CljM.dissoc" (big-map) :k0)))
    (is (instance? clojure.lang.PersistentHashMap (dissoc (big-map) :k0 :k1)) "the Clojure fact"))
  (testing "the boundary hands the impl array maps: a small hash map cannot reach it from a DSL caller"
    (let [->clj (:->clj (b/codec 'Value))
          m (->clj (data/edn->value (zipmap (map #(keyword (str "k" %)) (range 8)) (range 8))))]
      (is (instance? clojure.lang.PersistentArrayMap m))))
  (testing "a small map is an array map: its iteration order is known"
    (is (= '(:b :a) (run-op "CljM.keys" (array-map :b 1 :a 2))))))

(deftest functions-are-a-second-sort
  (testing "higher-order calls take Lean lambdas; values in function position are invoked"
    (doseq [[form ok?] '[[(fn [xs] (map (fn [x] (* x x)) xs)) true]
                         [(fn [m k] (m k)) true]
                         [(fn [xs] (filter #{1 2} xs)) true]
                         [(fn [xs] (map (comp inc (partial * 2)) xs)) true]
                         [(fn [xs] (let [f (fn [x] (inc x))] (f (first xs)))) true]
                         [(fn [x] (fn [y] y)) false]
                         [(fn [x] [inc]) false]]]
      (let [r (try (tr/translate form 'ansatz.clj-model-colls-test 'f) :ok
                   (catch clojure.lang.ExceptionInfo ex (:reason (ex-data ex))))]
        (is (= (if ok? :ok :escaping-fn) r) (pr-str form)))))
  (testing "a fn literal picks its arity per call, as Clojure does"
    (let [row {:id :showcase/arity :form '[((fn ([x] [:one x]) ([x & r] [:many r])) a) ((fn ([x] x) ([x & r] r)) a b)]
               :params '[[a :int] [b :int]]}
          {:keys [counts]} (cc/run-model-row row)]
      (is (zero? (:model-bug counts)))
      (is (zero? (:no-claim counts))))))

(deftest value-showcase
  (is (= {:a 1 :b 2 :sum 3} (data/value->edn (summarize (data/edn->value {:a 1 :b 2 :c 9})))))
  (is (= {:a 0 :sum 0} (data/value->edn (summarize (data/edn->value {:a "x"}))))
      "an absent :b counts 0; a non-int :a becomes 0")
  (let [{:keys [status faithful]} (cc/check-model! 'summarize :runs 40)]
    (is (zero? (:model-bug faithful)))
    (is (pos? (:agree faithful)))
    (is (#{:conforming :nonconforming} status)))
  (is (= ["a" "b" "c"] (data/value->edn (key-names (data/edn->value {:c 1 :a 2 :b 3})))))
  (is (zero? (get-in (cc/check-model! 'key-names :runs 40) [:faithful :model-bug]))))

(deftest varargs-and-case
  (is (= 6 (sum3 1 2 3)))
  (is (= {:clj-model/fixed 1 :clj-model/rest? true} (:arity (b/info 'sum3))))
  (let [{:keys [status faithful witnesses]} (cc/check-model! 'sum3 :runs 30)]
    (is (zero? (:model-bug faithful)))
    (is (= :nonconforming status) "Long/MAX_VALUE edges overflow")
    (is (some #(= "java.lang.ArithmeticException" (get-in % [:clojure :threw])) witnesses)))
  (is (= [1 2 2 0] (mapv code ["a" "b" "c" "z"])))
  (is (= :conforming (:status (cc/check-model! 'code :runs 30)))))
