(ns prototype.binding-dependencies-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.binding-dependencies :as dependencies]))
(def name-root ["str" ["num" ["anonymous"] "42"] "λ.😀"])
(deftest finite-immutable-declarations-validate-before-name-hashing
  (let [roots [name-root name-root ["anonymous"]]]
    (is (identical? roots (dependencies/validate-roots roots)))
    (is (= roots (dependencies/declared-roots {"a" {:guest-helper-roots roots} "legacy" {}}))))
  (is (= [] (dependencies/declared-roots {"legacy" {}})))
  (let [roots (vec (repeat 1024 name-root))
        long-name ["str" ["anonymous"] (apply str (repeat 16384 "x"))]
        exact-characters (vec (repeat 16 long-name))]
    (is (identical? roots (dependencies/validate-roots roots)))
    (is (identical? exact-characters (dependencies/validate-roots exact-characters))))
  (let [poison (reify Object (hashCode [_] (throw (AssertionError. "Must validate before hashing"))))]
    (doseq [roots [nil (list name-root) (java.util.ArrayList. [name-root]) [poison]
                   [[poison ["anonymous"] "name"]] [["str" ["anonymous"] poison]]
                   [["anonymous" "extra"]] [["num" ["anonymous"] "01"]]
                   [["num" ["anonymous"] "-1"]] [["bogus"]]
                   (vec (repeat 1025 name-root))
                   [["str" ["anonymous"] (apply str (repeat 16385 "x"))]]
                   [(nth (iterate #(vector "str" % "x") ["anonymous"]) 256)]]]
      (is (thrown? clojure.lang.ExceptionInfo (dependencies/validate-roots roots)))))
  (is (thrown? clojure.lang.ExceptionInfo (dependencies/declared-roots {"bad" {:guest-helper-roots nil}})))
  (is (thrown? clojure.lang.ExceptionInfo
        (dependencies/declared-roots {"a" {:guest-helper-roots (vec (repeat 600 name-root))}
                                      "b" {:guest-helper-roots (vec (repeat 600 name-root))}})))
  (let [long-name ["str" ["anonymous"] (apply str (repeat 16384 "x"))]]
    (is (thrown? clojure.lang.ExceptionInfo (dependencies/validate-roots (vec (repeat 17 long-name)))))))

(deftest total-name-node-budget-counts-shared-and-duplicate-spines
  (let [one (nth (iterate #(vector "str" % "x") ["anonymous"]) 255)
        exact (vec (repeat 64 one))]
    ;; Each Name has255 str nodes+anonymous=256. Shared immutable prefixes and
    ;; duplicate root identity still count as occurrences:64*256=16,384.
    (is (identical? exact (dependencies/validate-roots exact)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (dependencies/validate-roots (conj exact ["anonymous"]))))))
