(ns prototype.sci-bridge
  "Optional experiment: SCI owns world roots; guest instructions execute directly."
  (:require [clojure.test :refer [deftest is run-tests]]
            [prototype.examples :as ex]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.block-compile :as b]
            [sci.core :as sci]))

(defn branch-demo
  ([] (branch-demo :persistent))
  ([backend]
   (branch-demo backend (:captured (ex/fork-demo))))
  ([backend captured]
  (let [compiled (when (contains? #{:blocks :regions :calls} backend)
                   (b/compile-program (:functions captured) nil
                                      {:lexical-joins (contains? #{:regions :calls} backend)
                                       :leaf-calls (= :calls backend) :compact-registers (= :calls backend)}))
        resume (case backend
                 :persistent (fn [state value] (m/run (m/resume state value)))
                 :mutable (fn [state value]
                            (u/freeze (u/run! (u/resume! (u/thaw state) value))))
                 (:blocks :regions :calls) (fn [state value]
                           (u/freeze (b/run! compiled (u/resume! (u/thaw state) value)))))
        ctx (sci/init {:runtime-mode :forkable
                       :namespaces {'guest {'initial captured
                                            'resume resume}}})]
    (sci/eval-string* ctx "(def state (atom guest/initial))")
    ;; Fork between evaluations: SCI's source world must be quiescent.
    (let [left (sci/fork ctx)
          right (sci/fork ctx)]
      (sci/eval-string* left "(swap! state guest/resume 10)")
      (sci/eval-string* right "(swap! state guest/resume 20)")
      {:captured captured
       :parent (sci/eval-string* ctx "@state")
       :left (sci/eval-string* left "@state")
       :right (sci/eval-string* right "@state")}))))

(deftest isolated-guest-worlds
  (let [{:keys [captured parent left right]} (branch-demo)]
    (is (= captured parent))
    (is (= :suspended (:status parent)))
    (is (= [10 20] (mapv :result [left right])))
    (is (= [[] [[:released :test-resource]] [[:released :test-resource]]]
           (mapv :events [parent left right])))
    (is (= [1 0 0] (mapv #(count (:heap %)) [parent left right])))))

(deftest mutable-regions-preserve-world-semantics
  ;; Only immutable snapshots cross back into SCI's world cells.
  (is (= (branch-demo :persistent) (branch-demo :mutable))))

(deftest compiled-regions-preserve-world-semantics
  (is (= (branch-demo :persistent) (branch-demo :blocks))))

(deftest lexical-regions-preserve-world-semantics
  (is (= (branch-demo :persistent) (branch-demo :regions)))
  (let [functions {:fork {:params [0]
                          :body [:suspend 1
                                 [:join 42 [2] [:dec [:var 0] 1 [:return [:var 2]]]
                                  [:jump 42 [[:var 1]]]]]}}
        [world resource] (m/resource (m/world functions) :lexical-capture)
        captured (m/run (m/start world :fork [resource]))
        result (branch-demo :regions captured)]
    (is (= (branch-demo :persistent captured) result))
    (is (= [10 20] (mapv :result [(:left result) (:right result)])))
    (is (= [[] [[:released :lexical-capture]] [[:released :lexical-capture]]]
           (mapv :events [(:parent result) (:left result) (:right result)])))))

(deftest specialized-calls-preserve-fork-and-resource-effects
  (let [functions {:inc {:params [0] :body [:let 1 [:prim :inc [[:var 0]]] [:return [:var 1]]]}
                   :fork {:params [0] :body [:suspend 1 [:call 2 [:direct :inc] [[:var 1]]
                                                         [:dec [:var 0] 1 [:return [:var 2]]]]]}}
        [world resource] (m/resource (m/world functions) :call-capture)
        captured (m/run (m/start world :fork [resource]))
        result (branch-demo :calls captured)]
    (is (= (branch-demo :persistent captured) result))
    (is (= [11 21] (mapv :result [(:left result) (:right result)])))
    (is (= [[] [[:released :call-capture]] [[:released :call-capture]]]
           (mapv :events [(:parent result) (:left result) (:right result)])))))

(defn -main [& _]
  (let [result (run-tests 'prototype.sci-bridge)]
    (shutdown-agents)
    (when (pos? (+ (:fail result) (:error result)))
      (System/exit 1))))
