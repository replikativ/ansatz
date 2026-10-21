(ns prototype.global-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.import-ir :as ir]
            [prototype.block-compile :as blocks]
            [prototype.lazy-runtime :as lazy]
            [prototype.initialization :as init]))

(defn runners [functions]
  [#(m/run %1 %2)
   #(u/freeze (u/run! (u/thaw %1) %2))
   (let [p (blocks/compile-program functions nil {:lexical-joins true})]
     #(u/freeze (blocks/run! p (u/thaw %1) %2)))
   (let [p (lazy/open-program functions)]
     #(u/freeze (lazy/run! p (u/thaw %1) %2)))])

(deftest persistent-graph-and-ownership
  (let [[s child] (m/allocate (m/world {}) :ctor 1 [42])
        [s root] (m/expr s [:closure :identity [[:imm child]]])
        marked (m/mark-persistent s root)]
    (is (= [0 0] (mapv :rc (vals (:heap marked)))))
    (is (= marked (m/release (m/retain marked root 100 true) root 100 true)))
    (is (= 1 (second (m/expr marked [:shared? [:imm root]]))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"invariant" (m/retain s root 1 true)))
    (let [mutable (u/thaw s)]
      (u/mark-persistent! mutable root)
      (u/retain! mutable root 100 true)
      (u/release! mutable root 100 true)
      (is (= (:heap marked) (:heap (u/freeze mutable))))
      (is (= (:heap s) (:heap (u/freeze (u/thaw s)))))))
  (let [[s r] (m/resource (m/world {}) :external)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported persistent" (m/mark-persistent s r)))
    (let [mutable (u/thaw s)]
      (is (thrown? clojure.lang.ExceptionInfo (u/mark-persistent! mutable r)))
      (is (= (:heap s) (:heap (u/freeze mutable)))))))

(def global-functions
  {:value {:params [] :body [:global :value :initialize]}
   :initialize {:params [] :body [:let 0 [:ctor 1 [[:imm 42]]] [:return [:var 0]]]}
   :reader {:params [] :body [:call 0 [:direct :value] []
                             [:inc [:var 0] 1 [:dec [:var 0] 1 [:return [:var 0]] true] true]]}})

(deftest globals-every-boundary-and-forks
  (let [initial (m/start (m/world global-functions) :reader [])
        expected (m/run initial)]
    (doseq [run (runners global-functions) fuel (range 14)]
      (let [paused (run initial fuel)]
        (is (= (m/run initial fuel) paused))
        (when (= :paused (:status paused))
          (is (= expected (run (m/resume paused nil) 100))))))
    (is (= 1 (get-in expected [:stats :allocations])))
    (is (= 0 (:rc (m/node expected (:result expected)))))
    (doseq [run (runners global-functions)]
      (let [again (run (m/start expected :reader []) 100)]
        (is (= (:result expected) (:result again)))
        (is (= (:heap expected) (:heap again)))
        (is (= 1 (get-in again [:stats :allocations])))))
    (doseq [run (runners global-functions)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Recursive global"
             (run (m/start (assoc-in (m/world global-functions) [:globals :value] {:status :initializing}) :value []) 100))))))

(deftest persistent-annotations-are-checked-in-all-backends
  (let [functions {:bad {:params [0] :body [:inc [:var 0] 1 [:return [:var 0]] true]}}
        [s r] (m/allocate (m/world functions) :ctor 1 [42])]
    (doseq [run (runners functions)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"invariant" (run (m/start s :bad [r]) 10))))))

(defn native-functions []
  (let [catalogue (ir/index-bundles ["fixtures/globals.jsonl"])
        root (first (filter #(= "GlobalProbe.readValues" (ir/name-label %)) (keys (:declarations catalogue))))]
    [root (ir/load-closure catalogue [root]
                          (fn [row]
                            (if-let [f (get-in row [:ir :extern])]
                              (do (when-not (= "Nat.add" (ir/name-label (:f f))) (m/fail "Unexpected fixture extern" {:row row}))
                                  [(:f f) {:params [0 1] :body [:let 2 [:prim :add [[:var 0] [:var 1]]] [:return [:var 2]]]}])
                              (ir/lower-declaration row))))]))

(deftest native-exported-global-list-and-repeated-read
  (let [[root functions] (native-functions)
        initial (m/start (m/world functions) root [(m/->Tag 0)])
        expected (m/run initial)]
    (is (= [41 42] (m/list-values expected (:result expected))))
    (is (= 5 (count (:globals expected))))
    (is (every? #(zero? (:rc %)) (vals (:heap expected))))
    (doseq [run (runners functions) fuel (range (inc (get-in expected [:stats :steps])))]
      (let [paused (run initial fuel)]
        (is (= (m/run initial fuel) paused))
        (when (= :paused (:status paused))
          (is (= expected (run (m/resume paused nil) 1000))))))
    (doseq [run (runners functions)]
      (let [again (run (m/start expected root [(m/->Tag 0)]) 1000)]
        (is (= (:result expected) (:result again)))
        (is (= (:heap expected) (:heap again)))))))

(deftest constructor-shell-deletion-preserves-child-ownership
  (let [functions {:f {:params [0] :body [:let 1 [:project [:var 0] 0]
                                         [:set-tag [:var 0] 2
                                          [:del [:var 0] [:return [:var 1]]]]]}}
        [s child] (m/allocate (m/world functions) :ctor 1 [42])
        [s root] (m/allocate s :ctor 1 [child])
        initial (m/start s :f [root]) expected (m/run initial)]
    (doseq [run (runners functions) fuel (range 7)]
      (is (= (m/run initial fuel) (run initial fuel))))
    (is (= child (:result expected)))
    (is (= #{(:id child)} (set (keys (:heap expected)))))
    (is (= 1 (:rc (m/node expected child))))))

(deftest native-explicit-io-initialization
  (let [catalogue (ir/index-bundles ["fixtures/globals.jsonl"])
        named (fn [label] (first (filter #(= label (ir/name-label %)) (keys (:declarations catalogue)))))
        root (named "readInitialized") name (named "initializedNat")
        functions (ir/load-closure catalogue [root])
        world (m/world functions)]
    (doseq [run (runners functions)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"has not been initialized"
            (run (m/start world root [(m/->Tag 0)]) 100))))
    (doseq [backend [:reference :mutable :jvm]]
      (let [ready (init/run world [name] backend 100)
            again (init/run ready [name] backend 100)]
        (is (= 73 (:result ready)))
        (is (empty? (:heap ready)))
        (is (= (:heap ready) (:heap again)))
        (is (= (:globals ready) (:globals again)))
        (is (= (get-in ready [:stats :allocations]) (get-in again [:stats :allocations])))))
    (let [initial (init/start world name) expected (m/run initial)]
      (doseq [run (runners functions) fuel (range 10)]
        (let [paused (run initial fuel)]
          (is (= (m/run initial fuel) paused))
          (when (= :paused (:status paused))
            (is (= expected (run (m/resume paused nil) 100)))))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"active continuation"
          (init/start (m/start world root [(m/->Tag 0)]) name)))))

(deftest persistent-closure-captures-survive-application
  ;; Native closures require fixed < arity and boxed application n > 0.
  (let [functions {:apply {:params [0] :body [:tail [:closure [:var 0]] [[:imm 0]]]}
                   :read {:params [0 2] :body [:let 1 [:project [:var 0] 0] [:return [:var 1]]]}}
        [s child] (m/allocate (m/world functions) :ctor 1 [42])
        [s closure] (m/expr s [:closure :read [[:imm child]]])
        s (m/mark-persistent s closure)]
    (doseq [run (runners functions)]
      (let [result (run (m/start s :apply [closure]) 100)]
        (is (= 42 (:result result)))
        (is (= (:heap s) (:heap result)))))))

(deftest source-time-plan-preserves-local-action-order
  (let [catalogue (ir/index-bundles ["fixtures/source-globals.jsonl"])
        linked (init/link-local-plan catalogue []
                 (fn [row]
                   (if-let [f (get-in row [:ir :extern])]
                     (do (when-not (= "Nat.add" (ir/name-label (:f f))) (m/fail "Unexpected fixture extern" {:row row}))
                         [(:f f) {:params [0 1] :body [:let 2 [:prim :add [[:var 0] [:var 1]]] [:return [:var 2]]]}])
                     (ir/lower-declaration row))))
        functions (:functions linked)
        names (mapv #(ir/name-label (get-in % [:action :name])) (get-in linked [:plan :actions]))]
    (is (= ["GlobalProbe.values" "initializedNat" "initializedWide" "initializedList"]
           (vec (remove #(clojure.string/starts-with? % "_private.") names))))
    (is (= ["value" "initialize" "io" "initialize" "initialize"]
           (mapv #(get-in % [:action :kind]) (get-in linked [:plan :actions]))))
    (doseq [backend [:reference :mutable :jvm]]
      (let [ready (init/run-local-plan linked (m/world functions) backend 1000)
            again (init/run-local-plan linked ready backend 1000)
            get-value (fn [label] (some (fn [[n entry]] (when (and (string? (first n)) (= label (ir/name-label n))) (:value entry))) (:globals ready)))]
        (is (= 73 (get-value "initializedNat")))
        (is (= 18446744073709551615N (get-value "initializedWide")))
        (is (= [41 42] (m/list-values ready (get-value "initializedList"))))
        (is (= (:heap ready) (:heap again)))
        (is (= (:globals ready) (:globals again)))
        (is (= (get-in ready [:stats :allocations]) (get-in again [:stats :allocations])))))))

(deftest deleting-immediate-and-erased-shells-is-a-native-noop
  (let [functions {:immediates {:params [] :body [:del [:imm m/erased]
                                                [:del [:imm (m/->Tag 0)]
                                                 [:del [:imm 0] [:return [:imm 7]]]]]}}
        initial (m/start (m/world functions) :immediates [])]
    (doseq [run (runners functions) fuel (range 6)]
      (let [paused (run initial fuel)]
        (is (= (m/run initial fuel) paused))
        (when (= :paused (:status paused))
          (is (= (m/run initial) (run (m/resume paused nil) 100))))))))
