(ns prototype.module-init-query-test
  "Additional host-only isolation checks for ephemeral query scratch."
  (:require [clojure.test :refer [deftest is]]
            [prototype.module-init-capabilities :as cap]
            [prototype.machine :as m]))

(defn fixture []
  (let [a ["str" ["anonymous"] "A"] b ["str" ["anonymous"] "B"]
        producer (fn [name imports] {:schema "lean-init-plan/1" :module name :moduleSystem false
                                     :imports (mapv (fn [module] {:module module :meta false}) imports)
                                     :actions []})
        binding (get (cap/make-bindings
                       {:module-plans {a (producer a [b]) b (producer b [a])}
                        :initialized-symbols {"A" {:module a :phase :all}}}) "lean_run_mod_init_core")
        full (assoc (m/world {}) :initialized-modules #{[a :all] [b :all]})
        partial (assoc full :initialized-modules #{[a :all]})]
    {:binding binding :full full :partial partial}))
(defn query [binding world]
  (let [[after value] ((:handler binding) nil world ["A" m/erased])]
    {:available (:fields (m/node after value))
     :restored (m/release after value 1)}))

(deftest query-scratch-does-not-leak-across-alternating-worlds
  (let [{:keys [binding full partial]} (fixture)]
    (doseq [world (take 100 (cycle [full partial partial full]))]
      (let [result (query binding world)]
        (is (= (if (identical? full world) [1] [0]) (:available result)))
        (is (= (:heap world) (:heap (:restored result))))
        (is (identical? (:initialized-modules world) (:initialized-modules (:restored result))))))))

(deftest concurrent-queries-have-independent-scratch-and-read-only-worlds
  (let [{:keys [binding full partial]} (fixture)
        ready (java.util.concurrent.CountDownLatch. 2)
        go (java.util.concurrent.CountDownLatch. 1)
        results [(promise) (promise)]
        workers (mapv
                  (fn [world result]
                    (doto
                      (Thread.
                        (fn []
                          (.countDown ready)
                          (try
                            (when-not (.await go 2 java.util.concurrent.TimeUnit/SECONDS)
                              (throw (Exception. "query test gate timeout")))
                            (deliver result
                              (mapv (fn [_]
                                      (let [{:keys [available restored]} (query binding world)]
                                        [available (= (:heap world) (:heap restored))
                                         (identical? (:initialized-modules world) (:initialized-modules restored))]))
                                    (range 100)))
                            (catch Throwable e (deliver result e)))))
                      (.setDaemon true)))
                  [full partial] results)]
    (try
      (doseq [worker workers] (.start worker))
      (is (.await ready 2 java.util.concurrent.TimeUnit/SECONDS))
      (.countDown go)
      (let [observed (mapv #(deref % 2000 ::timeout) results)]
        (is (= (vec (repeat 100 [[1] true true])) (first observed)))
        (is (= (vec (repeat 100 [[0] true true])) (second observed))))
      (finally
        (.countDown go)
        (doseq [worker workers] (.join worker 2000))))))


(deftest equivalent-separately-allocated-names-do-not-skip-cycle-dependencies
  (let [a ["num" ["str" ["anonymous"] "A"] (long 1)]
        equivalent-a ["num" ["str" ["anonymous"] (String. "A")] (bigint 1)]
        b ["str" ["anonymous"] "B"]
        producer (fn [module imported] {:schema "lean-init-plan/1" :module module
                                        :moduleSystem false :actions []
                                        :imports [{:module imported :meta false}]})
        binding (get (cap/make-bindings
                       {:module-plans {a (producer a b) b (producer b equivalent-a)}
                        :initialized-symbols {"A" {:module a :phase :all}}})
                     "lean_run_mod_init_core")]
    (is (= a equivalent-a))
    (is (not (identical? a equivalent-a)))
    (doseq [[guards expected] [[#{[equivalent-a :all] [b :all]} [1]]
                               [#{[equivalent-a :all]} [0]]
                               [#{[b :all]} [0]]]]
      (let [world (assoc (m/world {}) :initialized-modules guards)
            [after result] ((:handler binding) nil world ["A" m/erased])]
        (is (= expected (:fields (m/node after result))))
        (is (identical? guards (:initialized-modules after)))
        (is (= (:heap world) (:heap (m/release after result 1))))))))
