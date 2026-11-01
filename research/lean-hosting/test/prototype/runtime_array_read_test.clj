(ns prototype.runtime-array-read-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.runtime-prim :as runtime]))

(deftest read-only-array-operations-borrow-storage-and-preserve-owners
  (let [[world child] (m/resource (m/world {}) :child)
        [world array] (m/allocate world :array 246 [child 7])
        reads (atom 0)
        ops {:ref? m/ref? :node (fn [& _] (throw (ex-info "Copied borrowed array" {})))
             :borrow-node (fn [world ref]
                            (swap! reads inc)
                            (update (m/node world ref) :fields object-array))
             :retain m/retain}]
    (doseq [symbol ["lean_array_size" "lean_array_get_size"]]
      (is (= [world 2] (runtime/evaluate ops world symbol [m/erased array]))))
    (doseq [symbol ["lean_array_fget_borrowed" "lean_array_uget_borrowed" "lean_array_get_borrowed"]]
      (is (= [world child] (runtime/evaluate ops world symbol
                            (if (= symbol "lean_array_get_borrowed") [m/erased 0 array 0] [m/erased array 0 m/erased])))))
    (doseq [symbol ["lean_array_fget" "lean_array_uget" "lean_array_get"]]
      (let [[after result] (runtime/evaluate ops world symbol
                             (if (= symbol "lean_array_get") [m/erased 0 array 0] [m/erased array 0 m/erased]))]
        (is (= child result))
        (is (= 2 (:rc (m/node after child))))
        (is (= [child 7] (:fields (m/node after array))))))
    (is (= 8 @reads))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"out of bounds"
          (runtime/evaluate ops world "lean_array_uget" [m/erased array 2 m/erased])))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Incorrect runtime object kind"
          (runtime/evaluate ops world "lean_array_size" [m/erased child])))))

(deftest mutable-reads-do-not-materialize-large-arrays-or-change-forks
  (let [[world child] (m/resource (m/world {}) :child)
        [world array] (m/allocate world :array 246 (vec (repeat 100000 child)))
        state (u/thaw world)
        before (u/freeze state)
        ;; Count the old materialization path directly, rather than depending on
        ;; timing ratios or an implementation-mirroring expected expression.
        original-vec clojure.core/vec
        large-copies (atom 0)]
    (with-redefs [clojure.core/vec (fn [value]
                                    (when (and (instance? (Class/forName "[Ljava.lang.Object;") value)
                                               (= 100000 (alength ^objects value)))
                                      (swap! large-copies inc))
                                    (original-vec value))]
      (dotimes [_ 20]
        (is (= 100000 (u/runtime-value! state "lean_array_size" [m/erased array])))
        (is (= child (u/runtime-value! state "lean_array_uget_borrowed" [m/erased array 99999 m/erased])))))
    (is (zero? @large-copies))
    (is (= before (u/freeze state)))
    (is (= before (u/freeze (u/thaw before))))))

(deftest exclusive-array-updates-do-not-copy-whole-storage
  (let [[world old] (m/resource (m/world {}) :old)
        [world value] (m/resource world :new)
        [world array] (m/allocate world :array 246 (assoc (vec (repeat 100000 0)) 17 old))
        state (u/thaw world)
        original-vec clojure.core/vec
        copies (atom 0)]
    (with-redefs [clojure.core/vec (fn [value]
                                    (when (and (instance? (Class/forName "[Ljava.lang.Object;") value)
                                               (= 100000 (alength ^objects value)))
                                      (swap! copies inc))
                                    (original-vec value))]
      (is (= array (u/runtime-value! state "lean_array_uset" [m/erased array 17 value m/erased]))))
    (is (zero? @copies))
    (let [after (u/freeze state)]
      (is (= [[:released :old]] (:events after)))
      (is (= value (nth (:fields (m/node after array)) 17)))
      (is (= old (nth (:fields (m/node world array)) 17)))
      (is (= 1 (:rc (m/node after value)))))))
