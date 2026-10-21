(ns ansatz.kernel.level-reference-test
  "Small executed C++ kernel corpus. False can mean conservative incompleteness."
  (:require [ansatz.kernel.level :as level]
            [clojure.edn :as edn]
            [clojure.test :refer [deftest is testing]]))

(defn- decode-level [form]
  (if (= :zero form)
    level/zero
    (let [[tag a b] form]
      (case tag
        :param (level/param a)
        :succ (level/succ (decode-level a))
        :max (level/level-max (decode-level a) (decode-level b))
        :imax (level/imax (decode-level a) (decode-level b))))))

(deftest pinned-cpp-kernel-ordering
  (let [corpus (edn/read-string (slurp "test-data/kernel-reference/levels.edn"))]
    (doseq [{:keys [id lhs rhs reference-geq]} (:cases corpus)]
      (testing (str id " against " (get-in corpus [:reference :commit]))
        ;; Corpus uses geq(lhs,rhs); the public Clojure API uses leq(rhs,lhs).
        (is (= reference-geq
               (level/level<= (decode-level rhs) (decode-level lhs))))))))
