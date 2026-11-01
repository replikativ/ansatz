(ns prototype.runtime-ops-table-test
  "Shared primitive capabilities remain machine-local at use and preserve the
   original call-entry function snapshot, including nested Var redefinition."
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.lazy-runtime :as lazy]
            [prototype.raw-interop :as raw]
            [prototype.runtime-prim :as runtime]
            [prototype.native-heap :as native]))

(defn captured-ops [machine]
  (let [observed (atom nil)]
    (with-redefs [runtime/evaluate (fn [ops actual _ _]
                                   (is (identical? machine actual))
                                   (reset! observed ops) [actual 0])]
      (u/runtime-value! machine "test-capture-only" []))
    @observed))

(deftest one-immutable-table-serves-independent-machines-without-sharing-runtime-state
  (let [a (u/thaw (assoc (m/world {}) :initializing? true :environment {"SIDE" "left"}))
        b (u/thaw (assoc (m/world {}) :initializing? false :environment {"SIDE" "right"}))
        ops (captured-ops a)]
    (is (identical? ops (captured-ops b)))
    (is (every? ifn? (vals ops)))
    ((:set-stdio-runtime ops) a :left-stdio)
    ((:set-task-runtime ops) b :right-task)
    (is (= :left-stdio ((:get-stdio-runtime ops) a)))
    (is (nil? ((:get-stdio-runtime ops) b)))
    (is (nil? ((:get-task-runtime ops) a)))
    (is (= :right-task ((:get-task-runtime ops) b)))
    (is (true? ((:initializing? ops) a)))
    (is (false? ((:initializing? ops) b)))
    (is (= "left" (second ((:get-env ops) a "SIDE"))))
    (is (= "right" (second ((:get-env ops) b "SIDE"))))))

(deftest per-call-function-values-survive-redefinition-during-evaluation
  (let [machine (u/thaw (m/world {}))
        original (captured-ops machine)
        seen (atom nil)]
    (with-redefs [m/pointer-address (fn [_ _] 11)
                  u/take-entropy! (fn [s _] [s [1]])
                  m/ref? (fn [_] :first-ref)
                  u/node (fn [_ _] :first-node)
                  u/replace-node! (fn [s _ _] s)
                  runtime/evaluate
                  (fn [ops actual _ _]
                    (reset! seen ops)
                    (with-redefs [m/pointer-address (fn [_ _] 22)
                                  u/take-entropy! (fn [s _] [s [2]])
                                  m/ref? (fn [_] :second-ref)
                                  u/node (fn [_ _] :second-node)
                                  u/replace-node! (fn [_ _ _] :second-world)]
                      (is (= 11 ((:pointer-address ops) actual 0)))
                      (is (= [1] (second ((:take-entropy ops) actual 1))))
                      (is (= :first-ref ((:ref? ops) 0)))
                      (is (= :first-node ((:borrow-node ops) actual 0)))
                      (is (identical? actual ((:replace-node ops) actual 0 {}))))
                    [actual 42])]
      (is (= 42 (u/runtime-value! machine "test-capture-only" []))))
    (is (not (identical? original @seen)))
    (is (identical? original (captured-ops machine)))))

(def entry
  {:params [0 1]
   :body [:let 2 [:runtime "lean_array_set" [[:imm m/erased] [:var 0] [:imm 0] [:var 1]]]
          [:let 3 [:runtime "lean_array_uget_borrowed" [[:imm m/erased] [:var 2] [:imm 0] [:imm m/erased]]]
           [:let 4 [:runtime "lean_nat_add" [[:imm 41] [:imm 1]]]
            [:return [:var 2]]]]]})
(def observed-keys [:heap :events :globals :stats :next-id :status :result :body :locals :joins :frames])
(defn execute [world backend fuel]
  (case backend
    :reference (m/run world fuel)
    :mutable (u/freeze (u/run! (u/thaw world) fuel))
    :jvm (u/freeze (lazy/run! (lazy/open-program (:functions world)) (u/thaw world) fuel))))

(deftest ownership-and-every-fuel-cut-match-reference-on-shared-and-unique-arrays
  (doseq [shared? [false true]]
    (let [[world old] (m/resource (m/world {:entry entry}) :old)
          [world new] (m/resource world :new)
          [world array] (m/allocate world :array 246 [old])
          world (if shared? (m/retain world array 1) world)
          started (m/start world :entry [array new])]
      (doseq [fuel (range 6)]
        (let [expected (execute started :reference fuel)]
          (doseq [backend [:mutable :jvm]]
            (let [actual (execute started backend fuel)]
              (is (true? (= (select-keys expected observed-keys)
                            (select-keys actual observed-keys))) (str backend " fuel=" fuel))
              (when (= :done (:status actual))
                (is (= [new] (:fields (m/node actual (:result actual)))))))))))))

(deftest imported-native-arrays-stay-immutable-and-errors-retain-input-checkpoint
  (let [array (m/->Ref 0) old (m/->Ref 1)
        nodes {0 {:kind :array :tag 246 :rc 0 :fields [old]}
               1 {:kind :string :tag 249 :rc 0 :fields [] :text "borrowed"}}
        source (reify native/NativeSource
                 (contains-id? [_ id] (and (integer? id) (<= 0 id 1)))
                 (lookup-node [_ id] (get nodes id)))
        [world new] (m/resource (assoc (m/world {:entry entry}) :native-imports [source] :next-id 2) :new)
        expected (execute (m/start world :entry [array new]) :reference 20)]
    (doseq [backend [:mutable :jvm]]
      (let [actual (execute (m/start world :entry [array new]) backend 20)]
        (is (true? (= (select-keys expected observed-keys) (select-keys actual observed-keys))))
        (is (not= array (:result actual)))
        (is (true? (= nodes (into {} (for [id [0 1]] [id (m/node actual (m/->Ref id))])))))))
    (let [machine (u/thaw world) before (u/freeze machine)
          failure (try (u/runtime-value! machine "lean_array_set" [m/erased array 1 new])
                       nil (catch clojure.lang.ExceptionInfo e e))]
      (is (some? failure))
      (is (true? (= before (u/freeze machine)))))
    (doseq [backend [:reference :mutable :jvm]]
      (let [bad {:params [0 1] :body [:let 2 [:runtime "lean_array_set" [[:imm m/erased] [:var 0] [:imm 1] [:var 1]]]
                                     [:return [:var 2]]]}
            functions {:bad bad}
            session (raw/open-functions functions {} {:backend backend :fuel 20})
            before (assoc world :functions functions)
            failure (try (raw/call session before :bad [array new])
                         nil (catch clojure.lang.ExceptionInfo e e))]
        (is (some? failure))
        (is (true? (= (:heap before) (:heap (:checkpoint (ex-data failure))))))
        (is (= (:events before) (:events (:checkpoint (ex-data failure)))))
        (is (some? (:checkpoint-session (ex-data failure))))))))
