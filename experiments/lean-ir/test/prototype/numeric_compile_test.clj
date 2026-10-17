(ns prototype.numeric-compile-test
  (:require [clojure.test :refer [deftest is run-tests]]
            [prototype.numeric-compile :as c]
            [prototype.bench :as b]
            [prototype.machine :as m]))

(deftest generated-tail-machine-matches-reference
  (let [functions {:even (b/tail-function :odd) :odd (b/tail-function :even)}
        invoke (:invoke (c/compile-program functions))]
    (doseq [target [:even :odd] n [0 1 2 17 100] acc [-10 0 9]]
      (is (= (:result (m/run (m/start (m/world functions) target [n acc])))
             (invoke target [n acc]))))
    (is (= 200000 (invoke :even [200000 0])))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"small integer"
                         (invoke :even [1 9007199254740991])))))

(deftest compiled-domain-and-coverage-guards
  (let [functions {:f {:params [0] :body [:return [:var 0]]}}
        invoke (:invoke (c/compile-program functions))]
    (is (thrown? clojure.lang.ExceptionInfo (invoke :f [1.5])))
    (is (thrown? clojure.lang.ExceptionInfo (invoke :f [])))
    (is (thrown? clojure.lang.ExceptionInfo (invoke :missing [1]))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported"
                       (c/compile-program {:f {:params [] :body [:suspend 0 [:return [:var 0]]]}})))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported"
                       (c/compile-program {:f {:params [] :body [:let 0 [:ctor 1 []] [:return [:var 0]]]}}))))

(deftest compiled-negative-boundary
  (let [invoke (:invoke (c/compile-program
                        {:f {:params [0] :body [:let 1 [:prim :dec [[:var 0]]] [:return [:var 1]]]}}))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"small integer"
                         (invoke :f [-9007199254740991])))))

(deftest compiled-case-fallback
  (let [functions {:f {:params [0] :body [:case [:var 0] [[1 [:return [:imm 10]]]
                                                                          [:default [:return [:imm 20]]]]]}}
        invoke (:invoke (c/compile-program functions))]
    (is (= [20 10 20] (mapv #(invoke :f [%]) [0 1 2])))))

(deftest compilation-does-not-resolve-caller-arithmetic
  (let [scratch (create-ns (gensym "guest-compiler-test"))]
    (try
      (binding [*ns* scratch]
        (clojure.core/refer 'clojure.core)
        (doseq [symbol '[inc dec long]]
          (ns-unmap scratch symbol)
          (intern scratch symbol (constantly 999)))
        (let [invoke (:invoke (c/compile-program {:even (b/tail-function :odd)
                                                :odd (b/tail-function :even)}))]
          (is (= 17 (invoke :even [17 0])))))
      (finally (remove-ns (ns-name scratch))))))

(defn -main [& _]
  (let [result (run-tests 'prototype.numeric-compile-test)]
    (shutdown-agents)
    (when (pos? (+ (:fail result) (:error result))) (System/exit 1))))
