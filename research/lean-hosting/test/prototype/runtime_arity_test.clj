(ns prototype.runtime-arity-test
  (:require [clojure.test :refer [deftest is testing]]
            [prototype.runtime-prim :as prim]
            [prototype.runtime-string :as string]
            [prototype.runtime-abi :as abi]
            [prototype.machine :as m]
            [prototype.native-scalar :as native]
            [prototype.raw-interop :as raw]))

(def ops {:ref? m/ref? :node m/node :release m/release
          :replace-node (fn [world ref node] (assoc-in world [:heap (:id ref)] node))})
(def shapes
  [{:params [{:ty "object" :borrow false} {:ty "tobject" :borrow true} {:ty "uint32" :borrow false}]
    :return-type "object"}
   {:params [{:ty "object" :borrow false} {:ty "tobject" :borrow false} {:ty "uint32" :borrow false}
             {:ty "erased" :borrow false}]
    :return-type "object"}])
(defn- name-of [n] ["str" ["anonymous"] (str "set" n)])
(defn- row [shape]
  (let [name (name-of (count (:params shape)))]
    {:name name :ir {:extern {:f name :type (:return-type shape)
                             :xs (mapv (fn [i p] (assoc p :x {:idx i})) (range) (:params shape))
                             :ext {:entries [{:standard {:backend ["str" ["anonymous"] "c"]
                                                         :fn "lean_string_utf8_set"}}]}}}}))
(defn- heap-string [world text]
  (let [[world value] (m/allocate world :string 249 [])]
    [(assoc-in world [:heap (:id value) :text] text) value]))

(deftest primitive-dispatch-accepts-both-string-set-forms
  ;; These enter runtime-prim, where the old :arity-first check rejected3 before
  ;; reaching the existing dual-arity String implementation.
  (doseq [arity [3 4]
          [text index cp expected] [["abc" 1 66 "aBc"] ["abc" 1 233 "aéc"]
                                    ["é😀Z" 2 955 "éλZ"] ["a\u0000b" 1 128512 "a😀b"]
                                    ["é😀Z" 1 65 "é😀Z"] ["abc" 3 65 "abc"]]]
    (let [world (m/world {}) args (cond-> [text index cp] (= arity 4) (conj m/erased))
          [after value] (prim/evaluate ops world "lean_string_utf8_set" args)]
      (is (identical? world after)) (is (= expected value))))
  (doseq [args [[] ["abc"] ["abc" 0] ["abc" 0 65 m/erased m/erased]]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Runtime extern arity mismatch"
          (prim/evaluate ops (m/world {}) "lean_string_utf8_set" args))))
  ;; The explicit set is authoritative even when a fallback :arity is present.
  (with-redefs [prim/supported-symbols (assoc prim/supported-symbols "lean_string_utf8_set"
                                       {:arity 4 :arities #{3}})]
    (is (= "Abc" (second (prim/evaluate ops (m/world {}) "lean_string_utf8_set" ["abc" 0 65]))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"arity"
          (prim/evaluate ops (m/world {}) "lean_string_utf8_set" ["abc" 0 65 m/erased])))))

(deftest registered-legacy-and-proof-shapes-run-on-every-backend
  (is (= (set shapes) (set (get @abi/signatures "lean_string_utf8_set"))))
  (let [functions (into {} (map (comp abi/lower row)) shapes)]
    (doseq [backend [:reference :mutable :jvm] arity [3 4]
            [text index cp expected same? owner]
            [["abc" 1 66 "aBc" true :unique] ["abc" 1 66 "aBc" false :shared]
             ["abc" 1 233 "aéc" false :unique] ["é😀Z" 1 65 "é😀Z" true :unique]
             ["abc" 0 65 "Abc" false :persistent]]]
      (let [[world source] (heap-string (m/world functions) text)
            world (case owner :shared (m/retain world source 1) :persistent (m/mark-persistent world source) world)
            session (raw/open-functions functions {} {:backend backend :fuel 100})
            args (cond-> [source (native/native-scalar index) cp]
                   (= arity 4) (conj m/erased))
            result (raw/call session world (name-of arity) args)
            after (:state result) value (:value result)]
        (is (= expected (string/string-value ops after value)))
        (is (= same? (= source value)))
        (is (= text (string/string-value ops world source)))
        (cond same? (is (= (:rc (m/node world source)) (:rc (m/node after source))))
              (= owner :shared) (is (= 1 (:rc (m/node after source))))
              (= owner :persistent) (is (= 0 (:rc (m/node after source))))
              :else (is (not (contains? (:heap after) (:id source)))))))
    ;; Accepting both counts must not relax ownership/type signature validation.
    (doseq [shape shapes]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"ownership/type"
            (abi/lower (update-in (row shape) [:ir :extern :xs 1 :borrow] not)))))))

(deftest all-multi-arity-registrations-keep-their-supported-forms
  ;; Full source audit found one dual-key spec (String.set) and five Nat-cast
  ;; arity sets. Exercise both accepted forms and out-of-range counts for all.
  (let [multi (into {} (filter (comp :arities val)) prim/supported-symbols)]
    (is (= #{"lean_string_utf8_set" "lean_uint8_of_nat" "lean_uint16_of_nat"
             "lean_uint32_of_nat" "lean_uint64_of_nat" "lean_usize_of_nat"} (set (keys multi))))
    (doseq [[symbol spec] multi :when (not= symbol "lean_string_utf8_set")]
      (is (= #{1 2} (:arities spec)))
      (is (= [nil 42] (prim/evaluate {} nil symbol [42])))
      (is (= [nil 42] (prim/evaluate {} nil symbol [42 m/erased])))
      (doseq [args [[] [42 m/erased m/erased]]]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"arity" (prim/evaluate {} nil symbol args)))))))
