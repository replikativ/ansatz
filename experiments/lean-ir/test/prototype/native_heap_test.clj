(ns prototype.native-heap-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.native-heap :as imported]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.block-compile :as blocks]
            [prototype.lazy-runtime :as lazy]
            [prototype.native-scalar :as native]))

(defn source [base end nodes reads]
  (reify imported/NativeSource
    (contains-id? [_ id] (and (integer? id) (<= base id) (< id end)))
    (lookup-node [_ id]
      (swap! reads conj id)
      (let [node (get nodes id)]
        (if (instance? Exception node) (throw node) node)))))
(defn fixture []
  (let [reads (atom [])
        nodes {100 {:kind :ctor :tag 0 :rc 0 :fields [(m/->Ref 101)]}
               101 {:kind :array :tag 246 :rc 0 :fields [(native/native-scalar 0) (m/->Ref 102)]}
               102 {:kind :string :tag 249 :rc 0 :fields [] :text "é😀"}
               103 {:kind :mpz :tag 250 :rc 0 :fields [] :integer 1099511627776}
               104 {:kind :byte-array :tag 248 :rc 0 :fields [] :bytes [0 127 255]}}
        source (source 100 105 nodes reads)]
    {:world (assoc (m/world {}) :native-imports [source] :next-id 105)
     :source source :nodes nodes :reads reads}))

(deftest native-membership-makes-rc-and-persistence-independent-of-graph-size
  (let [{:keys [world source reads]} (fixture) root (m/->Ref 100)
        [world wrapper] (m/allocate world :ctor 1 [root])]
    (is (= world (m/retain world root 100 true)))
    (is (= world (m/release world root 100 true)))
    (is (= world (m/mark-persistent world root)))
    (is (= root (m/assert-persistent world root)))
    (let [after (m/mark-persistent world wrapper)]
      (is (= 0 (:rc (m/node after wrapper))))
      (is (= 1 (count (:heap after)))))
    (is (empty? @reads))
    (let [machine (u/thaw world) before (u/freeze machine)]
      (u/retain! machine root 100 true)
      (u/release! machine root 100 true)
      (u/mark-persistent! machine root)
      (is (= root (u/assert-persistent! machine root)))
      (is (= before (u/freeze machine)))
      (is (identical? source (first (:native-imports (u/freeze machine))))))
    (is (empty? @reads))))

(deftest immutable-native-fields-are-readable-in-all-execution-backends
  (let [{:keys [world source]} (fixture)
        functions {:read {:params [0] :body [:let 1 [:project [:var 0] 0]
                                           [:let 2 [:runtime "lean_array_fget_borrowed"
                                                    [[:imm m/erased] [:var 1] [:imm 1] [:imm m/erased]]]
                                            [:return [:var 2]]]]}}
        initial (m/start (assoc world :functions functions) :read [(m/->Ref 100)])
        eager (blocks/compile-program functions nil {:lexical-joins true})
        delayed (lazy/open-program functions)]
    (doseq [fuel (range 5)]
      (let [expected (m/run initial fuel)]
        (is (= expected (u/freeze (u/run! (u/thaw initial) fuel)))))
      (is (= (m/run initial fuel) (u/freeze (blocks/run! eager (u/thaw initial) fuel))))
      (is (= (m/run initial fuel) (u/freeze (lazy/run! delayed (u/thaw initial) fuel)))))
    (let [done (m/run initial)]
      (is (= (m/->Ref 102) (:result done)))
      (is (empty? (:heap done)))
      (is (identical? source (first (:native-imports done)))))))

(deftest arrays-and-bytes-copy-on-write-and-forks-share-only-immutable-source
  (let [{:keys [world source nodes]} (fixture)
        root (m/->Ref 101)
        machine (u/thaw world)
        left (u/runtime-value! machine "lean_array_push" [m/erased root 7])
        left-world (u/freeze machine)
        sibling (u/thaw world)
        right (u/runtime-value! sibling "lean_array_push" [m/erased root 8])
        right-world (u/freeze sibling)]
    (is (= 105 (:id left) (:id right)))
    (is (= [(native/native-scalar 0) (m/->Ref 102) 7] (:fields (m/node left-world left))))
    (is (= [(native/native-scalar 0) (m/->Ref 102) 8] (:fields (m/node right-world right))))
    (is (= (get nodes 101) (m/node world root) (m/node left-world root) (m/node right-world root)))
    (is (= 1 (count (:heap left-world)) (count (:heap right-world))))
    (is (identical? source (first (:native-imports left-world))))
    (is (empty? (:heap world)))
    (let [result (u/runtime-value! machine "lean_byte_array_push" [(m/->Ref 104) 42])
          after (u/freeze machine)]
      (is (= [0 127 255 42] (:bytes (m/node after result))))
      (is (= [0 127 255] (:bytes (m/node world (m/->Ref 104))))))
    (u/release! machine left 1)
    (is (not (contains? (:heap (u/freeze machine)) (:id left))))))

(deftest native-array-updates-match-at-every-fuel-boundary
  (let [{:keys [world]} (fixture)
        functions {:push {:params [0] :body [:let 1 [:runtime "lean_array_push"
                                                   [[:imm m/erased] [:var 0] [:imm 7]]]
                                           [:return [:var 1]]]}}
        initial (m/start (assoc world :functions functions) :push [(m/->Ref 101)])
        eager (blocks/compile-program functions nil {:lexical-joins true})
        delayed (lazy/open-program functions)]
    (doseq [fuel (range 4)]
      (let [expected (m/run initial fuel)]
        (is (= expected (u/freeze (u/run! (u/thaw initial) fuel)))))
      (is (= (m/run initial fuel) (u/freeze (blocks/run! eager (u/thaw initial) fuel))))
      (is (= (m/run initial fuel) (u/freeze (lazy/run! delayed (u/thaw initial) fuel)))))
    (let [done (m/run initial)]
      (is (= 105 (:id (:result done))))
      (is (= 1 (count (:heap done)))))))

(deftest native-imports-reject-mutation-id-collisions-and-read-failures
  (let [{:keys [world]} (fixture) root (m/->Ref 100) machine (u/thaw world)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"immutable imported"
          (m/replace-node world root {:kind :ctor :tag 0 :rc 1 :fields []})))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unique field"
          (u/store! machine root 0 7)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"reserved imported"
          (m/allocate (assoc world :next-id 102) :ctor 0 [])))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"reserved imported"
          (u/constructor! (u/thaw (assoc world :next-id 102)) 1 [0])))
    (let [shadowed (assoc-in world [:heap 100] {:kind :ctor :tag 0 :rc 1 :fields []})]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"shadowed" (m/node shadowed root)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"shadowed" (u/project (u/thaw shadowed) root 0)))))
  (doseq [[node message] [[nil #"Missing verified"]
                         [(ex-info "Source read failed" {}) #"Source read failed"]
                         [{:kind :array :tag 246 :rc 1 :fields []} #"Malformed immutable"]
                         [{:kind :ref :tag 253 :rc 0 :fields []} #"Malformed immutable"]
                         [{:kind :array :tag 246 :rc 0 :fields (object-array [])} #"Malformed immutable"]]]
    (let [reads (atom []) src (source 10 11 {10 node} reads)
          world (assoc (m/world {}) :native-imports [src] :next-id 11)
          ref (m/->Ref 10)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo message (m/node world ref)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo message (u/project (u/thaw world) ref 0)))
      (is (empty? (:heap world))))))
