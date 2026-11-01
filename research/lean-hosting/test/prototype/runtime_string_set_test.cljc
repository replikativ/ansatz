(ns prototype.runtime-string-set-test
  (:require [prototype.runtime-string :as runtime] [prototype.machine :as m]
            #?(:clj [prototype.raw-interop :as raw]) [prototype.native-scalar :as native]
            #?(:clj [clojure.test :refer [deftest is]] :cljs [cljs.test :refer-macros [deftest is]])))
(def ops {:ref? m/ref? :node m/node :release m/release
          :replace-node (fn [world ref node] (assoc-in world [:heap (:id ref)] node))})
(def examples
  [["PreludeIdentity" 0 80 "PreludeIdentity"] ["abc" 1 66 "aBc"] ["abc" 1 233 "aéc"]
   ["é😀Z" 0 65 "A😀Z"] ["é😀Z" 2 955 "éλZ"] ["é😀Z" 6 128512 "é😀😀"]
   ["é😀Z" 1 65 "é😀Z"] ["abc" 3 65 "abc"] ["" 0 65 ""] ["abc" 100 65 "abc"]
   ["a\u0000b" 1 128512 "a😀b"] ["abc" 0 0 "\u0000bc"] ["éa" 2 66 "éB"] ["é" 0 233 "é"]])
(deftest utf8-set-matches-native-bytes-and-position-boundaries
  (doseq [[text index cp expected] examples arity [3 4]]
    (let [world (m/world {}) args (cond-> [text index cp] (= arity 4) (conj m/erased))
          [after result] (runtime/evaluate ops world "lean_string_utf8_set" args)]
      (is (= expected result)) (is (= world after))))
  (doseq [index [1 3 4 5 7 8  #?(:clj 9223372036854775808N :cljs 9007199254740991)]]
    (is (= "é😀Z" (second (runtime/evaluate ops (m/world {}) "lean_string_utf8_set" ["é😀Z" index 65])))))
  (doseq [cp [55296 57343 1114112]]
    (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
          (runtime/evaluate ops (m/world {}) "lean_string_utf8_set" ["abc" 0 cp]))))
  (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"arity"
        (runtime/evaluate ops (m/world {}) "lean_string_utf8_set" ["abc" 0]))))
(defn heap-string [world text]
  (let [[world ref] (m/allocate world :string 249 [])]
    [(assoc-in world [:heap (:id ref) :text] text) ref]))
(deftest native-ownership-and-copy-behavior-on-every-backend
  #?(:clj
     (doseq [backend [:reference :mutable :jvm]
             [text index cp expected same? shared?]
             [["abc" 1 66 "aBc" true false] ["abc" 1 66 "aBc" false true]
              ["abc" 1 233 "aéc" false false] ["éa" 2 66 "éB" true false]
              ["é" 0 233 "é" false false] ["é😀Z" 1 65 "é😀Z" true false]
              ["abc" 3 65 "abc" true false]]]
       (let [name ["set"] functions {name {:params [0 1 2 3]
                                          :body [:let 4 [:runtime "lean_string_utf8_set" (mapv #(vector :var %) [0 1 2 3])]
                                                 [:return [:var 4]]]}}
             [world source] (heap-string (m/world functions) text)
             world (if shared? (m/retain world source 1) world)
             session (raw/open-functions functions {} {:backend backend :fuel 100})
             result (raw/call session world name [source (native/native-scalar index) (native/native-scalar cp) m/erased])
             after (:state result) value (:value result)]
         (is (= expected (runtime/string-value ops after value)))
         (is (= same? (= source value)))
         (is (= text (runtime/string-value ops world source)))
         (if same? (is (= (:rc (m/node world source)) (:rc (m/node after source))))
           (if shared? (is (= 1 (:rc (m/node after source)))) (is (not (contains? (:heap after) (:id source))))))))))
(deftest boxed-nat-and-persistent-string-owners-are-preserved
  (let [[world source] (heap-string (m/world {}) "abc")
        [world index] (m/allocate world :mpz 250 [])
        world (assoc-in world [:heap (:id index) :integer] 1)
        [after result] (runtime/evaluate ops world "lean_string_utf8_set" [source index 65])]
    (is (= source result)) (is (= world after)))
  (let [[world source] (heap-string (m/world {}) "abc") world (m/mark-persistent world source)
        [after result] (runtime/evaluate ops world "lean_string_utf8_set" [source 0 65])]
    (is (= "Abc" result)) (is (= world after))))
#?(:cljs (defn -main [] (cljs.test/run-tests 'prototype.runtime-string-set-test)))
#?(:cljs (set! *main-cli-fn* -main))
