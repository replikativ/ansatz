(ns prototype.ir-value-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [prototype.ir-value :as ir]
            [prototype.guest-json :as guest-json]
            [prototype.eval-const :as eval-const]
            [prototype.module-store :as store]
            [prototype.machine :as m]
            [prototype.native-scalar :as native]
            [prototype.module-data :as data]))

(defn constructor
  "MODEL storage helper; native fixtures independently prove layout fidelity."
  [world tag fields bytes]
  (if (empty? bytes) (m/allocate world :ctor tag fields)
    (let [objects (count fields)
          [world r] (m/scalar-constructor world tag fields {:objects objects :usize 0 :ssize (count bytes)})]
      [(reduce-kv (fn [w i b]
                    (update-in w [:heap (:id r)] m/write-scalar-node
                               {:index objects :offset i :type "uint8" :region :scalar} b)) world (vec bytes)) r])))
(defn string-name [world text]
  (constructor world 1 [0 text] (repeat 8 0)))
(defn array [world values] (m/allocate world :array 246 values))

(deftest typed-declaration-model-preserves-names-abi-and-json-shape
  (let [[w name] (string-name (m/world {}) "a.b😀")
        [w param] (constructor w 0 [123 7] [1])
        [w params] (array w [param])
        [w arg] (constructor w 0 [123] [])
        [w body] (constructor w 10 [arg] [])
        [w root] (constructor w 0 [name params 7 body 0] [])
        before w
        expected {:fdecl {:f ["str" ["anonymous"] "a.b😀"]
                          :xs [{:x {:idx 123} :borrow true :ty "object"}]
                          :type "object" :body ["ret" {:var {:id {:idx 123}}}] :info {}}}]
    (is (= expected (ir/project-decl w root)))
    (is (identical? before w))
    (is (every? #(= 1 (:rc %)) (vals (:heap w))))
    (is (empty? (:heap (m/release w root 1))))))

(deftest arbitrary-numeric-name-and-contextual-erased-wrappers
  (let [n (inc' (bigint (.shiftLeft java.math.BigInteger/ONE 130)))
        [w mpz] (m/allocate (m/world {}) :mpz 250 [])
        w (assoc-in w [:heap (:id mpz) :integer] n)
        [w name] (constructor w 2 [0 mpz] (repeat 8 0))]
    (is (= ["num" ["anonymous"] (str n)] (ir/project-name w name))))
  (let [n (bigint (.shiftLeft java.math.BigInteger/ONE 160))
        [w mpz] (m/allocate (m/world {}) :mpz 250 [])
        w (assoc-in w [:heap (:id mpz) :integer] n)
        w (m/retain w mpz 1)
        [w expr] (constructor w 1 [mpz mpz] [])]
    ;; The exact same physical ref is Nat and erased VarId in different fields.
    (is (= {:reset {:n n :x {:idx n}}} (ir/project w :expr expr))))
  (let [[w name] (string-name (m/world {}) "sorry.source")
        [w some] (constructor w 1 [name] [])]
    (is (= {:sorryDep ["str" ["anonymous"] "sorry.source"]}
           (ir/project w :decl-info some))))
  (is (= {} (ir/project (m/world {}) :decl-info (native/native-scalar 0))))
  (is (= {:idx 4294967295} (ir/project (m/world {}) :var-id (native/native-scalar 4294967295)))))

(deftest packed-bools-and-extern-wrapper-layouts
  (doseq [a [0 1] b [0 1]]
    (let [[w root] (constructor (m/world {}) 6 [3 2 12] [a b])]
      (is (= ["inc" {:idx 3} 2 (= 1 a) (= 1 b) ["unreachable"]]
             (ir/project w :body root)))))
  (let [[w backend] (string-name (m/world {}) "c")
        [w entry] (constructor w 2 [backend "some_symbol"] [])
        [w entries] (constructor w 1 [entry 0] [])]
    (is (= {:entries [{:standard {:backend ["str" ["anonymous"] "c"] :fn "some_symbol"}}]}
           (ir/project w :extern-data entries))))
  (is (= {:entries []} (ir/project (m/world {}) :extern-data 0)))
  (is (= "erased" (ir/project (m/world {}) :arg 1))))

(deftest deep-ir-and-malformed-graphs
  (let [[w root] (loop [w (m/world {}) root 12 n 5000]
                   (if (zero? n) [w root]
                     (let [[w root] (constructor w 6 [0 1 root] [0 1])]
                       (recur w root (dec n)))))
        projected (ir/project w :body root)]
    (is (= ["unreachable"]
           (loop [body projected n 5000]
             (if (zero? n) body (recur (nth body 5) (dec n)))))))
  (doseq [[kind value] [[:expr 13] [:ir-type 14] [:body 13] [:arg 2] [:decl 0] [:name 3]]]
    (is (thrown? clojure.lang.ExceptionInfo (ir/project (m/world {}) kind value))))
  (let [[w root] (constructor (m/world {}) 6 [0 1 12] [2 1])]
    (is (thrown? clojure.lang.ExceptionInfo (ir/project w :body root))))
  (let [[w root] (constructor (m/world {}) 6 [0 1 12] [0 1])
        w (assoc-in w [:heap (:id root) :fields 2] root)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Cyclic" (ir/project w :body root)))))

(deftest typed-witness-header-model
  (let [[w name] (string-name (m/world {}) "missing")
        w (m/retain w name 2)
        [w rows] (array w [])
        [w missing] (array w [name])
        [w root] (constructor w 0 ["lean-eval-const-witness/1" "RuntimeCompileShim.exportEvalConstWitness"
                                    "pin" 64 "x86_64-unknown-linux-gnu" name name rows missing 0] [])]
    (is (= {:schema "lean-eval-const-witness/1" :producer "RuntimeCompileShim.exportEvalConstWitness"
            :leanCommit "pin" :runtimeProfile {:wordBits 64 :target "x86_64-unknown-linux-gnu"}
            :name ["str" ["anonymous"] "missing"] :boxedTarget ["str" ["anonymous"] "missing"]
            :declarations [] :missingDependencies [["str" ["anonymous"] "missing"]] :sorryDep nil}
           (ir/project-witness w root)))
    (is (empty? (:heap (m/release w root 1))))))

(deftest pinned-native-all-constructor-declarations
  (let [result (data/load-file (m/world {}) "fixtures/ir-value-native.jsonl" {:sha256 "af68df3d04a38a71ebdb45863ffaac6ff954b89d1f9458b2b21b5d09b480e2bd"})
        world (:world result)
        expected (json/read-str (slurp "fixtures/ir-value-native.expected.json") :key-fn keyword :bigdec true)]
    (is (= 54 (count (:roots result))))
    (is (= expected (mapv #(ir/project-decl world %) (:roots result))))
    (is (every? zero? (map :rc (vals (:heap world)))))))

(deftest pinned-native-typed-witnesses-equal-current-json-witnesses
  (let [result (data/load-file (m/world {}) "fixtures/ir-witness-native.jsonl" {:sha256 "c5b3902b3ad1446800f57c0fd32726173ff84faab388c46173b0aa34d487f59f"})
        world (:world result)
        expected (json/read-str (slurp "fixtures/ir-witness-native.expected.json") :key-fn keyword :bigdec true)]
    (is (= 4 (count (:roots result))))
    (is (= expected (mapv #(ir/project-witness world %) (:roots result))))
    (is (every? zero? (map :rc (vals (:heap world)))))))

(deftest pinned-native-deep-ir-equals-actual-tojson-without-host-recursion
  (let [result (store/load-file (m/world {}) "fixtures/ir-deep-native.jsonl" {:cache-size 128 :sha256 "e3d1ce9ddf10cf64c0612ef90584a252a7675187a08b20d26a8e822bc7e9f19b"})]
    (with-open [source ^java.io.Closeable (:source result)]
      (let [world (:world result) [decl json] (:roots result)
            actual (ir/project-decl world decl)
            expected (guest-json/project world json {:key-fn keyword})]
        (is (= 4096 (get-in result [:manifest :input :depth])))
        (is (eval-const/ir-equal? expected actual))
        (is (empty? (:heap world)))))))
