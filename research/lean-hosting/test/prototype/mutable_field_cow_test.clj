(ns prototype.mutable-field-cow-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m] [prototype.mutable :as u]
            [prototype.kernel-bridge-test :as guest])
  (:import [java.util HashMap]))

(defn- node [state ref] (.get ^java.util.Map (:heap state) (:id ref)))

(deftest immutable-fields-survive-read-and-nonfield-updates-without-copying
  (let [[world ref] (guest/ctor (m/world {}) 0 [7] 1)
        fields (:fields (m/node world ref)) state (u/thaw world)]
    (is (identical? (m/node world ref) (node state ref)))
    (is (= 7 (u/project state ref 0)))
    (u/retain! state ref 1)
    (is (identical? fields (:fields (node state ref))))
    (u/release! state ref 1)
    (u/set-constructor-tag! state ref 1)
    (u/scalar-store! state ref {:index 1 :offset 0 :type "uint8" :region :scalar} 42)
    (is (identical? fields (:fields (node state ref))))
    (let [frozen (u/freeze state)]
      (is (identical? fields (:fields (m/node frozen ref))))
      (is (= 42 (u/scalar-get state ref {:index 1 :offset 0 :type "uint8" :region :scalar})))
      (is (= 0 (:tag (m/node world ref)))))))

(deftest first-write-copies-once-and-every-snapshot-remains-independent
  (let [[world ref] (m/allocate (m/world {}) :ctor 0 [1 2])
        left (u/thaw world) right (u/thaw world)]
    (u/store! left ref 0 3)
    (let [owned (:fields (node left ref)) captured (u/freeze left)]
      (is (not (vector? owned)))
      (u/store! left ref 1 4)
      (is (identical? owned (:fields (node left ref))))
      (u/store! right ref 0 5)
      (is (= [1 2] (:fields (m/node world ref))))
      (is (= [3 2] (:fields (m/node captured ref))))
      (is (= [3 4] (:fields (m/node (u/freeze left) ref))))
      (is (= [5 2] (:fields (m/node (u/freeze right) ref)))))))

(deftest invalid-writes-do-not-acquire-storage-and-rc-transition-remains-valid
  (let [[world ref] (m/allocate (m/world {}) :ctor 0 [1])
        state (u/thaw (m/retain world ref 1)) fields (:fields (node state ref))]
    (is (thrown? clojure.lang.ExceptionInfo (u/store! state ref 0 2)))
    (is (identical? fields (:fields (node state ref))))
    (u/release! state ref 1)
    (is (thrown? clojure.lang.ExceptionInfo (u/store! state ref 1 2)))
    (is (identical? fields (:fields (node state ref))))
    (u/store! state ref 0 2)
    (is (= [2] (:fields (m/node (u/freeze state) ref)))))
  (let [[world ref] (m/allocate (m/world {}) :ctor 0 [1])
        state (u/thaw (m/mark-persistent world ref)) fields (:fields (node state ref))]
    (is (thrown? clojure.lang.ExceptionInfo (u/store! state ref 0 2)))
    (is (identical? fields (:fields (node state ref))))))

(deftest nonvector-input-is-private-even-when-persistent
  (doseq [rc [0 1]]
    (let [[world ref] (m/allocate (m/world {}) :ctor 0 [1])
          input (object-array [1])
          world (-> world (assoc-in [:heap (:id ref) :fields] input)
                    (assoc-in [:heap (:id ref) :rc] rc))
          left (u/thaw world) right (u/thaw world)
          frozen (u/freeze left)]
      (is (vector? (:fields (m/node frozen ref))))
      (is (not (identical? input (:fields (node left ref)))))
      (is (not (identical? (:fields (node left ref)) (:fields (node right ref)))))
      (aset input 0 9)
      (is (= [1] (:fields (m/node frozen ref))))
      (is (= 1 (u/project left ref 0)))
      (is (= 1 (u/project right ref 0))))))

(deftest exclusive-array-release-and-repeated-stores-preserve-owners-and-forks
  (let [[world child] (m/resource (m/world {}) :child)
        [world old] (m/allocate world :ctor 0 [child])
        world (m/retain world child 1)
        [world array] (m/allocate world :array 246 [old])
        left (u/thaw world) right (u/thaw world)]
    (is (= array (u/runtime-value! left "lean_array_uset" [m/erased array 0 7 m/erased])))
    (let [owned (:fields (node left array)) captured (u/freeze left)]
      (is (= 1 (:rc (m/node captured child))))
      (is (not (contains? (:heap captured) (:id old))))
      (is (= 2 (:rc (m/node world child))))
      (is (= [old] (:fields (m/node world array))))
      (is (= array (u/runtime-value! left "lean_array_uset" [m/erased array 0 8 m/erased])))
      (is (identical? owned (:fields (node left array))))
      (is (= [7] (:fields (m/node captured array))))
      (is (= [8] (:fields (m/node (u/freeze left) array))))
      (is (= (u/freeze (u/thaw world)) (u/freeze right)))
      (u/release! left array 1)
      (u/release! left child 1)
      (is (= [[:released :child]] (:events (u/freeze left)))))))

(deftest persistent-reference-and-task-replacement-are-snapshot-local
  (let [[world ref] (m/allocate (m/world {}) :ref 253 [1])
        world (m/mark-persistent world ref)
        state (u/thaw world)]
    (is (= 0 (u/runtime-value! state "lean_st_ref_set" [m/erased m/erased ref 2 m/erased])))
    (is (= [2] (:fields (m/node (u/freeze state) ref))))
    (is (= [1] (:fields (m/node world ref)))))
  (let [[world promise] (m/expr (m/world {}) [:runtime "lean_io_promise_new"
                                           (vec (repeat 3 [:imm m/erased]))])
        task (first (:fields (m/node world promise)))
        world (m/mark-persistent world promise)
        state (u/thaw world)]
    (u/runtime-value! state "lean_io_promise_resolve" [m/erased 42 promise m/erased])
    (is (= :ready (:task-state (m/node (u/freeze state) task))))
    (is (= :promise-pending (:task-state (m/node world task))))))
