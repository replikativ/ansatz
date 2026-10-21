(ns prototype.runtime-array-set-test
  "Checked Array.set! shares the native in-bounds COW/ownership semantics.
   The native panic/default path is an explicitly rejected prototype profile."
  (:require [prototype.machine :as m]
            [prototype.native-heap :as imported]
            [prototype.native-scalar :as native]
            [prototype.runtime-prim :as runtime]
            #?(:cljs [prototype.runtime-query-test])
            #?(:clj [prototype.mutable :as u])
            #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])))

(def ops {:ref? m/ref? :node m/node :allocate m/allocate :retain m/retain :release m/release
          :replace-node m/replace-node})
(defn evaluate [world array index value]
  (runtime/evaluate ops world "lean_array_set" [m/erased array index value]))
(defn fixture []
  (let [[world old] (m/resource (m/world {}) :old)
        [world new] (m/resource world :new)
        [world array] (m/allocate world :array 246 [old])]
    [world array old new]))

(deftest checked-array-set-transfers-owners-and-copies-nonexclusive-arrays
  (doseq [mode [:unique :shared :persistent]]
    (let [[initial array old new] (fixture)
          before (case mode :unique initial :shared (m/retain initial array 1)
                       :persistent (m/mark-persistent
                                    (assoc-in initial [:heap (:id old)]
                                              {:kind :ctor :tag 0 :rc 1 :fields []}) array))
          [after result] (evaluate before array (native/native-scalar 0) new)]
      (is (= (= mode :unique) (= array result)))
      (is (= [new] (:fields (m/node after result))))
      (is (= 1 (:rc (m/node after result))))
      (is (= 1 (:rc (m/node after new))))
      (is (= [old] (:fields (m/node before array))))
      (if (= mode :unique)
        (do (is (not (contains? (:heap after) (:id old))))
            (is (= [[:released :old]] (:events after))))
        (do (is (= [old] (:fields (m/node after array))))
            (is (= (if (= mode :shared) 1 0) (:rc (m/node after array))))
            (is (= (if (= mode :shared) 1 0) (:rc (m/node after old)))))))))

(deftest imported-array-set-copies-without-mutating-source-or-child
  (let [array (m/->Ref 0) old (m/->Ref 1)
        nodes {0 {:kind :array :tag 246 :rc 0 :fields [old]}
               1 {:kind :string :tag 249 :rc 0 :fields [] :text "old"}}
        source (reify imported/NativeSource
                 (contains-id? [_ id] (and (integer? id) (<= 0 id 1)))
                 (lookup-node [_ id] (get nodes id)))
        [before new] (m/resource (assoc (m/world {}) :native-imports [source] :next-id 2) :new)
        [after result] (evaluate before array 0 new)]
    (is (= 3 (:id result)))
    (is (= [new] (:fields (m/node after result))))
    (is (= nodes (into {} (for [id [0 1]] [id (m/node after (m/->Ref id))]))))
    (is (= 1 (count (:heap before))))
    (is (= 2 (count (:heap after))))
    (is (= [[:released :new]] (:events (m/release after result 1))))))

(deftest checked-array-set-panic-profile-traps-before-any-ownership-change
  (doseq [index [1 1099511627776]]
    (let [[world array old new] (fixture)
          called (atom [])
          guarded (assoc ops :retain (fn [& _] (swap! called conj :retain))
                             :release (fn [& _] (swap! called conj :release))
                             :allocate (fn [& _] (swap! called conj :allocate)))]
      (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"native panic path unsupported"
            (runtime/evaluate guarded world "lean_array_set" [m/erased array index new])))
      (is (empty? @called))
      (is (= [old] (:fields (m/node world array))))
      (is (= 1 (:rc (m/node world new))))))
  ;; Native checked set rejects every boxed Nat index, even a noncanonical small
  ;; MPZ. No proof-bearing unchecked operation is used to bypass that check.
  (let [[world array _ new] (fixture)
        [world index] (m/allocate world :mpz 250 [])
        world (assoc-in world [:heap (:id index) :integer] 0)]
    (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"native panic path unsupported"
          (evaluate world array index new)))))

#?(:clj
   (deftest mutable-array-set-has-identical-cow-and-fork-behavior
     (doseq [shared? [false true]]
       (let [[world array _ new] (fixture)
             world (if shared? (m/retain world array 1) world)
             [expected result] (evaluate world array 0 new)
             machine (u/thaw world)
             actual (u/runtime-value! machine "lean_array_set" [m/erased array (native/native-scalar 0) new])]
         (is (= result actual))
         (is (= (:heap expected) (:heap (u/freeze machine))))
         (is (= (:events expected) (:events (u/freeze machine))))))
     (let [[world array _ new] (fixture) machine (u/thaw world) before (u/freeze machine)]
       (is (thrown-with-msg? clojure.lang.ExceptionInfo #"native panic path unsupported"
             (u/runtime-value! machine "lean_array_set" [m/erased array 1 new])))
       (is (= before (u/freeze machine))))))

#?(:cljs (do (defn -main [] (cljs.test/run-tests 'prototype.runtime-array-set-test 'prototype.runtime-query-test))
             (set! *main-cli-fn* -main)))
