(ns prototype.runtime-sharecommon-test
  (:require [clojure.test :refer [deftest is testing]] [prototype.machine :as m]
            [prototype.mutable :as u] [prototype.raw-interop :as raw]
            [prototype.runtime-prim :as prim] [prototype.runtime-sharecommon :as share]
            [prototype.scalar :as scalar] [prototype.native-scalar :as native]))
(def ops {:ref? m/ref? :node m/node :allocate m/allocate :retain m/retain :release m/release :replace-node m/replace-node})
(defn ctor [w tag fields]
  (m/allocate (reduce #(m/retain %1 %2 1) w fields) :ctor tag fields))
(defn run-share [backend w root]
  (let [functions {:test {:params [1] :body [:let 2 [:runtime "lean_sharecommon_quick" [[:imm 0] [:var 1]]] [:return [:var 2]]]}}
        session (raw/open-functions functions {} {:backend backend}) original prim/evaluate]
    (with-redefs [prim/evaluate (fn [ops w symbol args]
                                (if (= symbol "lean_sharecommon_quick") (share/evaluate ops w symbol args)
                                  (original ops w symbol args)))]
      (raw/call session (assoc w :functions functions) :test [root]))))
(deftest copies-constructors-and-maximizes-sharing-without-consuming-input
  (doseq [backend [:reference :mutable :jvm]]
    (let [[w a] (ctor (m/world {}) 3 [0]) [w b] (ctor w 3 [(native/native-scalar 0)])
          [w root] (ctor w 2 [a b])
          {:keys [state value]} (run-share backend w root)
          [x y] (:fields (m/node state value))]
      (is (not= root value)) (is (= x y)) (is (not= a x))
      (is (= 2 (:rc (m/node state x))))
      (is (= (:heap w) (:heap (m/release state value 1)))))))
(deftest opaque-identity-and-array-copies
  (doseq [backend [:reference :mutable :jvm]]
    (let [[w a] (m/allocate (m/world {}) :ref 253 [0]) [w b] (m/allocate w :ref 253 [0])
          [w root] (m/allocate (-> w (m/retain a 2) (m/retain b 1)) :array 246 [a b a])
          {:keys [state value]} (run-share backend w root)]
      (is (not= value root)) (is (= [a b a] (:fields (m/node state value))))
      (is (= 3 (:native-capacity (m/node state value))))
      (is (= (:heap w) (:heap (m/release state value 1)))))))
(deftest profile-is-explicit-and-survives-mutable-snapshot
  (doseq [backend [:reference :mutable :jvm]]
    (let [[w a] (ctor (m/world {}) 1 ["name"])
          [w b] (ctor w 1 [(String. "name")]) [w root] (ctor w 2 [a b])]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"explicit immutable-text" (run-share backend w root)))
      (let [w (assoc w :sharecommon-profile :immutable-text-v1)
            {:keys [state value]} (run-share backend w root)]
        (is (= :immutable-text-v1 (:sharecommon-profile state)))
        (is (apply = (:fields (m/node state value))))
        (is (= (:heap w) (:heap (m/release state value 1)))))))
  (let [w (assoc (m/world {}) :sharecommon-profile :immutable-text-v1)]
    (is (= :immutable-text-v1 (:sharecommon-profile (u/freeze (u/thaw w)))))))
(defn terminal [w kind tag extra]
  (let [[w r] (m/allocate w kind tag [])]
    [(m/replace-node w r (merge (m/node w r) extra)) r]))
(deftest terminals-reuse-first-native-representative-and-capacity-matters
  (let [s {:text "a" :utf8-bytes [97] :native-byte-size 2 :native-utf8-length 1 :native-capacity 2}
        [w a] (terminal (m/world {}) :string 249 s)
        [w b] (terminal w :string 249 s)
        [w c] (terminal w :string 249 (assoc s :native-capacity 10))
        [w root] (ctor w 1 [a b c]) [w result] (share/evaluate ops w "lean_sharecommon_quick" [0 root])]
    (is (= [a a c] (:fields (m/node w result)))))
  (let [[w a] (terminal (m/world {}) :mpz 250 {:integer 9999999999999999999999N})
        [w b] (terminal w :mpz 250 {:integer 9999999999999999999999N})
        [w root] (ctor w 1 [a b]) [w result] (share/evaluate ops w "lean_sharecommon_quick" [0 root])]
    (is (= [a a] (:fields (m/node w result))))))
(deftest scalar-cache-and-padding-bytes-are-not-structural-expression-equality
  (let [[w a] (m/scalar-constructor (m/world {}) 0 [] {:objects 0 :usize 0 :ssize 1})
        w (assoc-in w [:heap (:id a) :scalar-bytes] {0 3})
        [w b] (m/scalar-constructor w 0 [] {:objects 0 :usize 0 :ssize 8})
        w (assoc-in w [:heap (:id b) :scalar-bytes] (zipmap (range 8) [3 0 0 0 0 0 0 0]))
        [w c] (m/scalar-constructor w 0 [] {:objects 0 :usize 0 :ssize 8})
        w (assoc-in w [:heap (:id c) :scalar-bytes] (zipmap (range 8) [3 0 0 0 0 0 0 1]))
        [w root] (ctor w 1 [a b c]) [w result] (share/evaluate ops w "lean_sharecommon_quick" [0 root])
        [x y z] (:fields (m/node w result))]
    (is (= x y)) (is (not= x z))))
(deftest deeply-nested-graph-is-stack-safe
  (let [[w root] (loop [w (m/world {}) n 4000 root 0]
                   (if (zero? n) [w root] (let [[w r] (m/allocate w :ctor 1 [root])] (recur w (dec n) r))))
        [next result] (share/evaluate ops w "lean_sharecommon_quick" [0 root])]
    (is (not= root result))
    (is (= (:heap w) (:heap (m/release next result 1))))))
(deftest unrepresented-layouts-fail-closed-and-persistent-input-stays-immutable
  (let [[w r] (ctor (m/world {}) 1 [0])
        w (assoc-in w [:heap (:id r) :rc] 0)
        [next result] (share/evaluate ops w "lean_sharecommon_quick" [0 r])]
    (is (not= r result)) (is (= 0 (:rc (m/node next r))))
    (is (= (:heap w) (:heap (m/release next result 1))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"metadata"
          (share/evaluate ops (assoc-in w [:heap (:id r) :work] [1]) "lean_sharecommon_quick" [0 r]))))
  (let [[w r] (terminal (m/world {}) :byte-array 248 {:bytes [1 2]})]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"capacity"
          (share/evaluate ops w "lean_sharecommon_quick" [0 r])))))
(deftest native-oracle-shape-canaries
  ;; RuntimeShareCommonOracle.c independently emits these same three relations.
  (let [[w a] (m/allocate (m/world {}) :array 246 [7])
        [w b] (m/allocate w :array 246 [7])
        w (assoc-in w [:heap (:id b) :native-capacity] 10)
        [w root] (ctor w 3 [a b])
        [w r] (share/evaluate ops w "lean_sharecommon_quick" [0 root]) [x y] (:fields (m/node w r))]
    (is (= x y)) (is (not= a x)) (is (= 1 (:native-capacity (m/node w x))))))
