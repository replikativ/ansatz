(ns prototype.guest-json-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.data.json :as json]
            [clojure.java.io :as io]
            [prototype.guest-json :as guest]
            [prototype.machine :as m]
            [prototype.native-scalar :as native]
            [prototype.module-data :as data])
  (:import [java.math BigDecimal]))

(defn encode
  "Small MODEL encoder for host tests, not native layout evidence. Returns an
   owned Json; maps accept string/keyword keys. Native fixtures test independently."
  [world value]
  (cond
    (nil? value) [world 0]
    (boolean? value)
    (let [[world ref] (m/scalar-constructor world 1 [] {:objects 0 :usize 0 :ssize 1})]
      [(update-in world [:heap (:id ref)] m/write-scalar-node
                  {:index 0 :offset 0 :type "uint8" :region :scalar} (if value 1 0)) ref])
    (number? value)
    (let [[n exponent] (if (instance? BigDecimal value)
                         (if (neg? (.scale ^BigDecimal value)) [(.toBigIntegerExact ^BigDecimal value) 0]
                           [(.unscaledValue ^BigDecimal value) (.scale ^BigDecimal value)])
                         (if (integer? value) [value 0] (throw (ex-info "Exact model Json number required" {}))))
          [world number] (m/allocate world :ctor 0 [n exponent])]
      (m/allocate world :ctor 2 [number]))
    (string? value) (m/allocate world :ctor 3 [value])
    (vector? value)
    (let [[world fields] (reduce (fn [[w fields] v] (let [[w v] (encode w v)] [w (conj fields v)])) [world []] value)
          [world array] (m/allocate world :array 246 fields)]
      (m/allocate world :ctor 4 [array]))
    (map? value)
    (let [entries (sort-by first @#'guest/string-compare
                          (map (fn [[k v]] [(if (keyword? k) (subs (str k) 1) k) v]) value))
          [world tree size]
          (reduce (fn [[w tree size] [k v]]
                    (let [[w v] (encode w v)
                          [w tree] (m/allocate w :ctor 0 [(inc size) k v tree 1])]
                      [w tree (inc size)])) [world 1 0] entries)]
      (m/allocate world :ctor 5 [tree]))
    :else (throw (ex-info "Unsupported model Json value" {}))))

(deftest model-json-covers-all-constructors-and-borrowed-ownership
  (let [value {"null" nil "false" false "true" true "integer" -123456789012345678901234567890N
               "decimal" -1.2500M "empty" [] "nested" [{"λ😀" "NUL\u0000\n\"\\"}]}
        [world root] (encode (m/world {}) value)
        before world]
    (is (= value (guest/project world root)))
    (is (= (json/read-str (json/write-str value) :key-fn keyword :bigdec true)
           (guest/project world root {:key-fn keyword})))
    (is (identical? before world))
    (is (every? #(= 1 (:rc %)) (vals (:heap world))))
    (is (= {} (:heap (m/release world root 1))))))

(deftest exact-number-contexts-and-scales
  (let [[w number] (m/allocate (m/world {}) :ctor 0 [(native/native-scalar 4294967295) (native/native-scalar 0)])
        [w root] (m/allocate w :ctor 2 [number])]
    (is (= -1 (guest/project w root))))
  (doseq [[n scale expected] [[100 2 1] [-125 2 -1.25M] [1 1000 (BigDecimal. "1E-1000")]
                              [0 999999999999999999999999N 0]]]
    (let [[w number] (m/allocate (m/world {}) :ctor 0 [n scale])
          [w root] (m/allocate w :ctor 2 [number])]
      (is (= expected (guest/project w root)))))
  (doseq [[n scale] [[1 2147483648N] [1 -1] ["bad" 0]]]
    (let [[w number] (m/allocate (m/world {}) :ctor 0 [n scale])
          [w root] (m/allocate w :ctor 2 [number])]
      (is (thrown? clojure.lang.ExceptionInfo (guest/project w root))))))

(deftest deep-nesting-and-cycles
  (let [[w root] (loop [w (m/world {}) root 0 n 5000]
                   (if (zero? n) [w root]
                     (let [[w a] (m/allocate w :array 246 [root])
                           [w root] (m/allocate w :ctor 4 [a])]
                       (recur w root (dec n)))))
        value (guest/project w root)]
    (is (nil? (loop [value value n 5000] (if (zero? n) value (recur (first value) (dec n)))))))
  (let [[w a] (m/allocate (m/world {}) :array 246 [])
        [w root] (m/allocate w :ctor 4 [a])
        w (assoc-in w [:heap (:id a) :fields] [root])]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Cyclic" (guest/project w root)))))

(deftest malformed-layouts-and-object-invariants-fail-closed
  (doseq [value [1 2 (m/->Tag 4) (native/native-scalar 5) "string"]]
    (is (thrown? clojure.lang.ExceptionInfo (guest/project (m/world {}) value))))
  (doseq [node [{:kind :ctor :tag 6 :fields []}
                {:kind :ctor :tag 3 :fields ["a" "b"]}
                {:kind :ctor :tag 1 :fields [] :layout {:objects 0 :usize 0 :ssize 1} :scalar-bytes {0 2}}
                {:kind :ctor :tag 1 :fields [] :layout {:objects 0 :usize 0 :ssize 8} :scalar-bytes {0 1}}
                {:kind :array :tag 246 :fields []}]]
    (let [world (assoc-in (m/world {}) [:heap 0] (assoc node :rc 1))]
      (is (thrown? clojure.lang.ExceptionInfo (guest/project world (m/->Ref 0))))))
  (let [[w bad] (m/allocate (m/world {}) :ctor 3 [(str (char 55296))])]
    (is (thrown? clojure.lang.ExceptionInfo (guest/project w bad))))
  (let [[w text] (m/allocate (m/world {}) :string 249 [0])
        w (assoc-in w [:heap (:id text) :text] "hidden invalid pointer field")
        [w root] (m/allocate w :ctor 3 [text])]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"String layout" (guest/project w root))))
  (doseq [[size key left-key] [[99 "b" "a"] [2 "a" "b"] [2 "a" "a"]]]
    (let [[w left] (m/allocate (m/world {}) :ctor 0 [1 left-key 0 1 1])
          [w tree] (m/allocate w :ctor 0 [size key 0 left 1])
          [w root] (m/allocate w :ctor 5 [tree])]
      (is (thrown? clojure.lang.ExceptionInfo (guest/project w root)))))
  (let [[w root] (encode (m/world {}) {"a" 1 "b" 2})]
    (is (thrown? clojure.lang.ExceptionInfo (guest/project w root {:key-fn (constantly :same)}))))
  (let [[w root] (encode (m/world {}) {"\uE000" 1 "𐀀" 2})]
    (is (= {"\uE000" 1 "𐀀" 2} (guest/project w root)))))

(def native-fixture "fixtures/guest-json-native.jsonl")
(def native-expected "fixtures/guest-json-native.expected.json")
(deftest pinned-native-compacted-json-oracle
  (let [result (data/load-file (m/world {}) native-fixture {:sha256 "6b7c20d43f934c90163583169bf8e723f7f540027b02af160c7e314b8c81df90"})
        world (:world result) roots (:roots result)
        expected (json/read-str (slurp native-expected) :bigdec true)]
    (is (= 18 (count roots)))
    (is (= expected (mapv #(guest/project world %) roots)))
    (is (= (mapv #(json/read-str (json/write-str %) :key-fn keyword :bigdec true) expected)
           (mapv #(guest/project world % {:key-fn keyword}) roots)))
    (is (= 285 (count (:heap world))))
    (is (every? zero? (map :rc (vals (:heap world)))))))
