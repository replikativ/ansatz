(ns prototype.eval-const-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.eval-const :as eval]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]))

(defn n [text] ["str" ["anonymous"] text])
(def root (n "evalConst"))
(def exporter (n "exportActualEnvironment"))
(def apply-answer (n "applyAnswer"))

(defn run-evaluation [backend fixture]
  (let [binding (eval/make-binding exporter)
        bindings {"lean_eval_const" binding}
        params (get-in binding [:signature :params])
        row {:kind "decl" :name root
             :ir {:extern {:f root :xs (mapv (fn [i p] (assoc p :x {:idx i})) (range 1 5) params)
                           :type "object" :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"] :fn "lean_eval_const"}}]}}}}
        functions {root (second (raw/lower bindings row))
                   exporter {:params [1 2 3]
                             :body [:dec [:var 1] 1 [:dec [:var 2] 1
                                     [:let 4 [:ctor 0 [[:imm (slurp fixture)]]]
                                      [:return [:var 4]]]]]}
                   apply-answer {:params [1 2] :body [:tail [:closure [:var 1]] [[:imm 0] [:var 2]]]}}
        session (raw/open-functions functions bindings {:backend backend})
        [world environment] (m/allocate (m/world functions) :ctor 0 [])
        [world name] (m/scalar-constructor world 1 [0 "answer"] {:objects 2 :usize 0 :ssize 8})
        world (assoc-in world [:heap (:id name) :scalar-bytes] (zipmap (range 16 24) (repeat 0)))
        result (raw/call session world root [m/erased environment 0 name])]
    {:result result :parent world :environment environment :name name}))

(deftest fresh-eval-const-returns-a-boxed-closure-without-applying-zero-arguments
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [result parent environment name]} (run-evaluation backend "fixtures/runtime-compiled-identity.jsonl")
          state (:state result)
          except (m/node state (:value result)) closure (first (:fields except))
          state (m/release (m/retain state closure 1) (:value result) 1)
          answer (raw/call (:session result) state apply-answer [closure 42])]
      (is (= 1 (:tag except)))
      (is (= :closure (:kind (m/node (:state result) closure))))
      (is (= ["str" (n "answer") "_boxed"] (:function (m/node (:state result) closure))))
      (is (= 42 (:value answer)))
      (is (= 1 (:rc (m/node (:state answer) environment))))
      (is (= 1 (:rc (m/node (:state answer) name))))
      (is (not (contains? (:functions parent) (n "answer")))))))

(deftest fresh-nullary-eval-const-loads-and-boxes-the-value
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [result environment name]} (run-evaluation backend "fixtures/runtime-compiled-nullary.jsonl")
          state (:state result) except (m/node state (:value result))]
      (is (= 1 (:tag except)))
      (is (= [42] (:fields except)))
      (is (= 1 (:rc (m/node state environment))))
      (is (= 1 (:rc (m/node state name))))
      (is (= :ready (get-in state [:globals (n "answer") :status]))))))
