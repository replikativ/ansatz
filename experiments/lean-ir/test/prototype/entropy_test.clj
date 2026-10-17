(ns prototype.entropy-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.entropy :as entropy]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.block-compile :as blocks]
            [prototype.lazy-runtime :as lazy]))

(deftest input-validation-is-atomic
  (let [world {:entropy {:bytes [0 255 1] :position 0 :source :test}}
        [advanced bytes] (entropy/take-bytes world 2)]
    (is (= [0 255] bytes))
    (is (= 2 (get-in advanced [:entropy :position])))
    (is (= 0 (get-in world [:entropy :position])))
    (is (= [advanced []] (entropy/take-bytes advanced 0)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"exhausted" (entropy/take-bytes advanced 2))))
  (doseq [world [{} {:entropy {:bytes [0] :position -1}}
                    {:entropy {:bytes [0] :position 2}} {:entropy {:bytes [256] :position 0}}]]
    (is (thrown? clojure.lang.ExceptionInfo (entropy/take-bytes world 1)))))

(deftest random-input-replays-through-pause-fork-and-mutable-snapshots
  (let [functions {:random {:params []
                           :body [:let 0 [:runtime "lean_io_get_random_bytes" [[:imm 2] [:imm m/erased]]]
                                  [:return [:var 0]]]}}
        initial (m/start (assoc (m/world functions) :entropy {:bytes [4 255 9] :position 0}) :random [])
        expected (m/run initial)
        eager (blocks/compile-program functions nil {:lexical-joins true})
        demand (lazy/open-program functions)
        runners [m/run #(u/freeze (u/run! (u/thaw %1) %2))
                 #(u/freeze (blocks/run! eager (u/thaw %1) %2))
                 #(u/freeze (lazy/run! demand (u/thaw %1) %2))]]
    (is (= 2 (get-in expected [:entropy :position])))
    (let [bytes (first (:fields (m/node expected (:result expected))))]
      (is (= [4 255] (:bytes (m/node expected bytes)))))
    (doseq [run runners fuel (range 4)]
      (let [paused (run initial fuel)]
        (is (= (m/run initial fuel) paused))
        (when (= :paused (:status paused))
          (is (= expected (run (m/resume paused nil) 100))))))
    (let [left (u/thaw initial) right (u/thaw initial)]
      (u/run! left 100)
      (is (= (:entropy initial) (:entropy (u/freeze right))))
      (is (= expected (u/freeze (u/run! right 100)))))))
