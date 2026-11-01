(ns prototype.closure-application-test
  (:require [clojure.test :refer [deftest is testing]]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.block-compile :as blocks]
            [prototype.lazy-runtime :as lazy]
            [prototype.interop :as interop]))

(defn- runners [functions]
  (let [eager (blocks/compile-program functions)
        optimized (blocks/compile-program functions nil {:lexical-joins true :leaf-calls true :compact-registers true})
        demand (lazy/open-program functions)]
    [#(u/run! %1 %2) #(blocks/run! eager %1 %2)
     #(blocks/run! optimized %1 %2) #(lazy/run! demand %1 %2)]))

(defn- check-boundaries [initial]
  (let [done (m/run initial 1000)
        runs (runners (:functions initial))
        steps (- (get-in done [:stats :steps]) (get-in initial [:stats :steps]))]
    (doseq [run runs budget (range (+ 2 steps))]
      (let [paused (u/freeze (run (u/thaw initial) budget))]
        (is (= (m/run initial budget) paused))
        (when (= :paused (:status paused))
          ;; Independently thaw the same pause twice: surplus argument owners
          ;; and synthetic return continuations must belong to the snapshot.
          (doseq [_ (range 2)]
            (is (= done (u/freeze (run (u/resume! (u/thaw paused) nil) 1000))))))))
    done))

(deftest underapplication-copies-captures-and-transfers-owned-arguments
  (doseq [ownership [:unique :shared :persistent]]
    (testing (name ownership)
      (let [functions {:partial {:params [0 1] :body [:call 2 [:closure [:var 0]] [[:var 1]] [:return [:var 2]]]}
                       :finish {:params [0 1] :body [:tail [:closure [:var 0]] [[:var 1]]]}
                       :collect {:params [0 1 2] :body [:let 3 [:ctor 7 [[:var 0] [:var 1] [:var 2]]] [:return [:var 3]]]}}
            [s captured] (m/allocate (m/world functions) :ctor 1 [42])
            [s supplied] (m/resource s :supplied)
            [s closure] (m/expr s [:closure :collect [[:imm captured]]])
            s (case ownership :shared (m/retain s closure 1) :persistent (m/mark-persistent s closure) s)
            partial (check-boundaries (m/start s :partial [closure supplied]))
            result (:result partial)
            expected-captured-rc (case ownership :unique 1 :shared 2 :persistent 0)
            finished (check-boundaries (m/start partial :finish [result 9]))
            released (m/release finished (:result finished) 1)]
        (is (= :closure (:kind (m/node partial result))))
        (is (= [captured supplied] (:fields (m/node partial result))))
        (is (= expected-captured-rc (:rc (m/node partial captured))))
        (is (= 1 (:rc (m/node partial supplied))))
        (is (= (= ownership :unique) (not (contains? (:heap partial) (:id closure)))))
        (is (= [captured supplied 9] (:fields (m/node finished (:result finished)))))
        (is (= [[:released :supplied]] (:events released)))
        (is (= (case ownership :unique #{} :shared #{(:id closure) (:id captured)} :persistent #{(:id closure) (:id captured)})
               (set (keys (:heap released)))))))))

(deftest overapplication-keeps-surplus-in-resumable-guest-frames-and-restores-joins
  (let [functions {:entry {:params [0 1 2]
                           :body [:join 20 [4] [:return [:var 4]]
                                  [:call 3 [:closure [:var 0]] [[:var 1] [:var 2]] [:jump 20 [[:var 3]]]]]}
                   :first {:params [0] :body [:let 1 [:closure :second [[:var 0]]] [:return [:var 1]]]}
                   :second {:params [0 1] :body [:let 2 [:ctor 8 [[:var 0] [:var 1]]] [:return [:var 2]]]}}
        [s a] (m/resource (m/world functions) :a)
        [s b] (m/resource s :b)
        [s closure] (m/expr s [:closure :first []])
        initial (m/start s :entry [closure a b])
        paused (m/run initial 2)
        finished (check-boundaries initial)]
    (is (= 2 (count (:frames paused))))
    (is (= [:tail [:closure [:var 0]] [[:imm b]]] (:body (peek (:frames paused)))))
    (is (= 1 (:rc (m/node paused b))))
    (is (= [a b] (:fields (m/node finished (:result finished)))))
    (is (= [[:released :b] [:released :a]] (:events (m/release finished (:result finished) 1))))))

(deftest overapplication-can-return-another-partial-closure-or-a-builtin
  (let [functions {:entry {:params [0] :body [:tail [:closure [:var 0]] [[:imm 4] [:imm 5]]]}
                   :first {:params [0] :body [:let 1 [:closure :three [[:var 0]]] [:return [:var 1]]]}
                   :three {:params [0 1 2] :body [:return [:var 2]]}
                   :builtin {:params [0] :body [:return [:imm (m/->Builtin :inc)]]}}
        [s closure] (m/expr (m/world functions) [:closure :first []])
        partial (check-boundaries (m/start s :entry [closure]))
        [s builtin] (m/expr (m/world functions) [:closure :builtin []])]
    (is (= [4 5] (:fields (m/node partial (:result partial)))))
    (is (= :three (:function (m/node partial (:result partial)))))
    (is (= 6 (:result (check-boundaries (m/start s :entry [builtin])))))))

(deftest scalar-erased-proof-application-consumes-arguments
  (doseq [scalar [m/erased (m/->Tag 0) 42 9223372036854775807N]]
    (let [functions {:entry {:params [0] :body [:tail [:closure [:imm scalar]] [[:var 0]]]}}
          [s arg] (m/resource (m/world functions) :proof-argument)
          done (check-boundaries (m/start s :entry [arg]))]
      (is (= scalar (:result done)))
      (is (= [[:released :proof-argument]] (:events done)))
      (is (empty? (:heap done))))))

(deftest invalid-applications-trap-and-direct-calls-stay-exact
  (let [functions {:entry {:params [0] :body [:tail [:closure [:var 0]] [[:imm 1]]]}
                   :over {:params [0] :body [:tail [:closure [:var 0]] [[:imm 1] [:imm 2]]]}
                   :empty {:params [0] :body [:tail [:closure [:var 0]] []]}
                   :bad-result {:params [0] :body [:let 1 [:ctor 1 [[:var 0]]] [:return [:var 1]]]}
                   :two {:params [0 1] :body [:return [:var 0]]}}
        [s nonclosure] (m/allocate (m/world functions) :ctor 2 [3])
        [s closure] (m/expr s [:closure :bad-result []])
        [s full] (m/expr s [:closure :two [[:imm 1] [:imm 2]]])]
    (doseq [[entry callee message] [[:entry nonclosure #"Expected guest closure"]
                                  [:entry 9223372036854775808N #"Expected closure"]
                                  [:entry -1 #"Expected closure"]
                                  [:entry :arbitrary-host-value #"Expected closure"]
                                  [:over closure #"Expected guest closure"]
                                  [:empty closure #"Empty boxed"]
                                  [:entry full #"Invalid closure capture"]]
            run (cons (fn [s n] (m/run s n))
                      (map (fn [run] #(u/freeze (run (u/thaw %1) %2))) (runners functions)))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo message (run (m/start s entry [callee]) 100))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Guest arity mismatch" (m/start s :two [1])))
    (let [bad (assoc functions :direct {:params [] :body [:tail [:direct :two] [[:imm 1]]]})
            state (m/start (m/world bad) :direct [])]
      (doseq [run (runners bad)]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Guest arity mismatch" (run (u/thaw state) 100)))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Guest arity mismatch" (u/start! (u/thaw s) :two [1])))))

(deftest host-callback-invocation-uses-boxed-saturation
  (doseq [backend [:reference :mutable :jvm]]
    (let [entry ["str" ["anonymous"] "entry"]
          first-fn ["str" ["anonymous"] "first"]
          second-fn ["str" ["anonymous"] "second"]
          functions {entry {:params [] :body [:let 0 [:closure first-fn []]
                                               [:host "apply" [[:var 0]] 1 [:dec [:var 0] 1 [:return [:var 1]]]]]}
                     first-fn {:params [0] :body [:let 1 [:closure second-fn [[:var 0]]] [:return [:var 1]]]}
                     second-fn {:params [0 1] :body [:let 2 [:prim :add [[:var 0] [:var 1]]] [:return [:var 2]]]}}
          session (interop/open-functions functions {"apply" {:arguments [:closure] :result :nat
                                                             :fn (fn [{:keys [invoke]} f] (invoke f [4 5]))}} backend (lazy/code-cache))
          done (interop/call session entry [])]
      (is (= 9 (:value done)))
      (is (empty? (get-in done [:state :heap]))))))

(deftest generic-arity-and-repeated-overapplication-share-the-same-protocol
  ;; Native apply_1..16 and apply_m must agree on saturation; our generic path
  ;; covers both rather than retaining the native generated dispatch limits.
  (let [functions {:entry {:params [0] :body [:tail [:closure [:var 0]] (mapv #(vector :imm %) (range 3 19))]}
                   :finish {:params [0] :body [:tail [:closure [:var 0]] [[:imm 19]]]}
                   :wide {:params (vec (range 20)) :body [:let 20 [:ctor 1 [[:var 0] [:var 19]]] [:return [:var 20]]]}}
        [s closure] (m/expr (m/world functions) [:closure :wide (mapv #(vector :imm %) (range 3))])
        partial (check-boundaries (m/start s :entry [closure]))
        finished (check-boundaries (m/start partial :finish [(:result partial)]))]
    (is (= (vec (range 19)) (:fields (m/node partial (:result partial)))) )
    (is (= [0 19] (:fields (m/node finished (:result finished))))))
  (let [functions {:entry {:params [0 1 2 3] :body [:tail [:closure [:var 0]] [[:var 1] [:var 2] [:var 3]]]}
                   :first {:params [0] :body [:dec [:var 0] 1 [:let 1 [:closure :second []] [:return [:var 1]]]]}
                   :second {:params [0] :body [:dec [:var 0] 1 [:let 1 [:closure :third []] [:return [:var 1]]]]}
                   :third {:params [0] :body [:return [:var 0]]}}
        [s a] (m/resource (m/world functions) :first)
        [s b] (m/resource s :second)
        [s c] (m/resource s :third)
        [s closure] (m/expr s [:closure :first []])
        done (check-boundaries (m/start s :entry [closure a b c]))]
    (is (= c (:result done)))
    (is (= [[:released :first] [:released :second] [:released :third]]
           (:events (m/release done c 1))))))
