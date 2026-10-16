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
  (let [captured (:captured (ex/fork-demo))
        compiled (when (= :blocks backend) (b/compile-program (:functions captured)))
        resume (case backend
                 :persistent (fn [state value] (m/run (m/resume state value)))
                 :mutable (fn [state value]
                            (u/freeze (u/run! (u/resume! (u/thaw state) value))))
                 :blocks (fn [state value]
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

(defn -main [& _]
  (let [result (run-tests 'prototype.sci-bridge)]
    (shutdown-agents)
    (when (pos? (+ (:fail result) (:error result)))
      (System/exit 1))))
