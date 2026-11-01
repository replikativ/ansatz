(ns prototype.runtime-object-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m]
            [prototype.runtime-object :as runtime]
            [prototype.scalar :as scalar]))

(def ops {:ref? m/ref? :node m/node :allocate m/allocate :release m/release :retain m/retain
          :replace-node (fn [world value node] (assoc-in world [:heap (:id value)] node))})
(defn evaluate [world symbol args] (runtime/evaluate ops world symbol args))
(defn name-component [world parent tag payload] (m/allocate world :ctor tag [parent payload]))
(defn cached [world value hash]
  (let [layout {:objects 2 :usize 0 :ssize 8}
        bytes (scalar/write-bytes layout {} {:index 2 :offset 0 :type "uint64" :region :scalar} hash)]
    (update-in world [:heap (:id value)] assoc :layout layout :scalar-bytes bytes)))

(deftest empty-byte-array-capacity-is-not-size
  (doseq [capacity [0 16 9223372036854775807N]]
    (let [before (m/world {})
          [world bytes] (evaluate before "lean_mk_empty_byte_array" [capacity])]
      (is (= {:kind :byte-array :tag 248 :fields [] :rc 1 :bytes []} (m/node world bytes)))
      (is (= [world 0] (evaluate world "lean_byte_array_size" [bytes])))
      (is (empty? (:heap before)))))
  (doseq [capacity [-1 0.5 9223372036854775808N]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (evaluate (m/world {}) "lean_mk_empty_byte_array" [capacity])))))

(deftest name-equality-preserves-component-kinds-and-borrows
  (let [[world a] (name-component (m/world {}) (m/->Tag 0) 1 "1")
        [world b] (name-component world 0 2 1)
        [world c] (name-component world 0 1 "1")
        [world d] (name-component world c 1 "é😀")
        [world e] (name-component world a 1 "é😀")]
    (is (= [world 1] (evaluate world "lean_name_eq" [(m/->Tag 0) 0])))
    (is (= [world 0] (evaluate world "lean_name_eq" [a b])))
    (is (= [world 1] (evaluate world "lean_name_eq" [a c])))
    (is (= [world 1] (evaluate world "lean_name_eq" [d e])))
    (is (= [world 0] (evaluate world "lean_name_eq" [d c])))
    (is (= [world 0] (evaluate world "lean_name_eq" [a 0])))
    (is (= [world 1] (evaluate world "lean_name_eq" [a a])))
    (let [[world x] (name-component world 0 2 18446744073709551617N)
          [world y] (name-component world 0 2 18446744073709551617N)]
      (is (= [world 1] (evaluate world "lean_name_eq" [x y]))))))

(deftest native-name-hash-shortcut-and-collisions
  (let [[world a] (name-component (m/world {}) 0 1 "a")
        [world b] (name-component world 0 1 "b")
        [world c] (name-component world 0 1 "a")
        ;; Cached computed fields can collide: structural comparison is required.
        world (-> world (cached a 18446744073709551615N)
                  (cached b 18446744073709551615N) (cached c 18446744073709551615N))]
    (is (= [world 0] (evaluate world "lean_name_eq" [a b])))
    (is (= [world 1] (evaluate world "lean_name_eq" [a c])))
    (let [world (cached world c 17)]
      (is (= [world 0] (evaluate world "lean_name_eq" [a c])) "native rejects mismatched caches first"))))

(deftest deep-names-use-explicit-loop
  (let [[world left right]
        (loop [i 0 world (m/world {}) left 0 right (m/->Tag 0)]
          (if (= i 12000) [world left right]
            (let [[world left] (name-component world left 1 "component")
                  [world right] (name-component world right 1 "component")]
              (recur (inc i) world left right))))]
    (is (= [world 1] (evaluate world "lean_name_eq" [left right])))))

(deftest byte-array-conversion-consumes-array-ownership
  (let [[world array] (m/allocate (m/world {}) :array 246 [0 127 128 255])
        [converted bytes] (evaluate world "lean_byte_array_mk" [array])
        shared (m/retain world array 1)
        [copied shared-bytes] (evaluate shared "lean_byte_array_mk" [array])]
    (is (not (contains? (:heap converted) (:id array))))
    (is (= {:kind :byte-array :tag 248 :fields [] :rc 1 :bytes [0 127 128 255]}
           (m/node converted bytes)))
    (is (= 1 (:rc (m/node copied array))))
    (is (= [0 127 128 255] (:bytes (m/node copied shared-bytes))))
    (is (= [converted 4] (evaluate converted "lean_byte_array_size" [bytes])))
    (doseq [[i byte] (map-indexed vector [0 127 128 255])]
      (is (= [converted byte] (evaluate converted "lean_byte_array_fget" [bytes i m/erased]))))))

(deftest byte-array-push-copies-nonexclusive-nodes
  (let [[world array] (m/allocate (m/world {}) :array 246 [255])
        [world bytes] (evaluate world "lean_byte_array_mk" [array])
        [unique updated] (evaluate world "lean_byte_array_push" [bytes 0])
        shared (m/retain world bytes 1)
        [copied copy] (evaluate shared "lean_byte_array_push" [bytes 128])
        persistent (assoc-in world [:heap (:id bytes) :rc] 0)
        [forked fork] (evaluate persistent "lean_byte_array_push" [bytes 127])]
    (is (= bytes updated))
    (is (= [255 0] (:bytes (m/node unique bytes))))
    (is (not= bytes copy))
    (is (= [255] (:bytes (m/node copied bytes))))
    (is (= 1 (:rc (m/node copied bytes))))
    (is (= [255 128] (:bytes (m/node copied copy))))
    (is (not= bytes fork))
    (is (= [255] (:bytes (m/node forked bytes))))
    (is (= 0 (:rc (m/node forked bytes))))
    (is (= [255 127] (:bytes (m/node forked fork))))
    (is (= [255] (:bytes (m/node world bytes))))))

(deftest byte-array-getters-borrow-and-distinguish-checked-bounds
  (let [[world bytes] (evaluate (m/world {}) "lean_mk_empty_byte_array" [0])
        [world bytes] (evaluate world "lean_byte_array_push" [bytes 255])]
    (is (= [world 255] (evaluate world "lean_byte_array_uget" [bytes 0 m/erased])))
    (is (= [world 255] (evaluate world "lean_byte_array_get" [bytes 0])))
    (is (= [world 0] (evaluate world "lean_byte_array_get" [bytes 1])))
    (is (= [world 0] (evaluate world "lean_byte_array_get" [bytes 18446744073709551617N])))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"precondition"
          (evaluate world "lean_byte_array_uget" [bytes 1 m/erased])))))

(deftest byte-array-set-consumes-copies-and-keeps-out-of-bounds-noop
  (let [[world bytes] (evaluate (m/world {}) "lean_mk_empty_byte_array" [3])
        [world bytes] (evaluate world "lean_byte_array_push" [bytes 1])]
    (doseq [[symbol extra] [["lean_byte_array_set" []]
                          ["lean_byte_array_fset" [m/erased]]
                          ["lean_byte_array_uset" [m/erased]]]]
      (let [args (into [bytes 0 255] extra)
            [unique same] (evaluate world symbol args)
            [shared copy] (evaluate (m/retain world bytes 1) symbol args)
            persistent (assoc-in world [:heap (:id bytes) :rc] 0)
            [forked fork] (evaluate persistent symbol args)]
        (is (= bytes same))
        (is (= [255] (:bytes (m/node unique same))))
        (is (not= bytes copy))
        (is (= [1] (:bytes (m/node shared bytes))))
        (is (= 1 (:rc (m/node shared bytes))))
        (is (= [255] (:bytes (m/node shared copy))))
        (is (not= bytes fork))
        (is (= [1] (:bytes (m/node forked bytes))))
        (is (= 0 (:rc (m/node forked bytes))))
        (is (= [255] (:bytes (m/node forked fork))))
        (is (= [1] (:bytes (m/node world bytes))))))
    (doseq [index [1 18446744073709551617N]]
      (let [shared (m/retain world bytes 1)]
        (is (= [shared bytes] (evaluate shared "lean_byte_array_set" [bytes index 0])))))
    (doseq [symbol ["lean_byte_array_fset" "lean_byte_array_uset"]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"precondition"
            (evaluate world symbol [bytes 1 0 m/erased]))))))

(deftest invalid-runtime-objects-and-bounds-fail-explicitly
  (let [[world array] (m/allocate (m/world {}) :array 246 [256])]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unsigned range"
          (evaluate world "lean_byte_array_mk" [array]))))
  (let [[world array] (m/allocate (m/world {}) :array 246 [])
        [world bytes] (evaluate world "lean_byte_array_mk" [array])]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"precondition"
          (evaluate world "lean_byte_array_fget" [bytes 0 m/erased])))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unsigned range"
          (evaluate world "lean_byte_array_push" [bytes -1])))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"arity"
          (evaluate world "lean_name_eq" [0])))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"terminator"
          (evaluate world "lean_name_eq" [0 3])))))
