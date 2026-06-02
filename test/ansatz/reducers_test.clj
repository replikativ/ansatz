(ns ansatz.reducers-test
  (:require [ansatz.reducers :as r]
            [clojure.test :refer [deftest is]]))

(deftest pipeline-compiles-to-transducer
  (let [pipeline (-> r/empty
                     (r/map inc)
                     (r/filter even?)
                     (r/flat-map (fn [x] [x (* 10 x)])))]
    (is (= [2 20 4 40]
           (r/into [] pipeline [0 1 2 3])))
    (is (= 66
           (r/transduce pipeline + 0 [0 1 2 3])))
    (is (= [2 20 4 40]
           (vec (r/eduction pipeline [0 1 2 3]))))
    (is (= {:steps [{:op :map :fold-safe? true}
                    {:op :filter :fold-safe? true}
                    {:op :mapcat :fold-safe? true}]
            :fold-safe? true}
           (r/explain pipeline)))))

(deftest compose-preserves-left-to-right-order
  (let [pipeline (r/compose (r/map inc)
                            (r/filter odd?)
                            (r/map #(* % %)))]
    (is (= [1 9 25]
           (r/into [] pipeline [0 1 2 3 4])))))

(deftest lawful-fold-map-matches-sequential-transduce
  (let [xs (vec (range 1000))
        pipeline (-> r/empty
                     (r/map inc)
                     (r/filter #(not (zero? (mod % 3)))))
        value-f #(* % %)
        expected (r/transduce pipeline
                              (fn
                                ([] 0)
                                ([x] x)
                                ([acc x] (+ acc (value-f x))))
                              xs)]
    (doseq [grain [1 2 17 512]]
      (is (= expected
             (r/fold-map pipeline r/nat-add value-f xs {:grain grain}))
          (str "grain=" grain)))))

(deftest group-by-uses-value-monoid
  (let [xs (vec (range 1 31))
        pipeline (r/filter #(<= % 20))
        actual (r/group-by pipeline r/nat-add #(mod % 4) (constantly 1) xs {:grain 3})]
    (is (= {0 5, 1 5, 2 5, 3 5} actual))))

(deftest unsafe-monoid-is-rejected-by-lawful-fold
  (let [bad-spec (r/monoid-spec
                  {:name :bad/add
                   :unit-fn (constantly 0)
                   :combine +
                   :laws {:assoc 'Nat.add_assoc}})]
    (is (false? (r/lawful? bad-spec)))
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"Parallel fold requires a lawful MonoidSpec"
         (r/fold-map r/empty bad-spec identity [1 2 3])))
    (is (= 6
           (r/unchecked-fold-map r/empty (constantly 0) + identity [1 2 3]
                                 {:grain 1})))))
