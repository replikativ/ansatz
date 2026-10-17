(ns prototype.module-plan-test
  (:require [clojure.test :refer [deftest is testing]]
            [prototype.module-plan :as plan]))

(defn- module-name [s] ["str" ["anonymous"] s])
(def a (module-name "A"))
(def b (module-name "B"))
(def c (module-name "C"))
(defn- action [id meta] {:action {:kind "io" :name (module-name id)} :meta meta})
(defn- module-plan [split imports actions]
  {:moduleSystem split :imports imports :actions actions})
(defn- labels [result]
  (mapv (fn [{:keys [action phase]}] [(last (:name action)) phase]) (:actions result)))

(deftest classic-order-and-duplicate-imports
  (let [plans {a (module-plan false [{:module b :meta false} {:module b :meta true}]
                              [(action "a1" true) (action "a2" false)])
               b (module-plan false [] [(action "b" false)])}
        result (plan/expand plans a :all)]
    (is (= [["b" :all] ["a1" :all] ["a2" :all]] (labels result)))
    (is (= #{[a :all] [b :all]} (:initialized result)))
    (is (= {:module a :phase :all :action (:action (action "a1" true)) :meta true}
           (second (:actions result))))))

(deftest split-import-and-local-filters
  (let [plans {a (module-plan true [{:module b :meta false} {:module c :meta true}]
                              [(action "am" true) (action "ar" false)])
               b (module-plan true [] [(action "br" false) (action "bm" true)])
               c (module-plan true [] [(action "cr" false) (action "cm" true)])}]
    (testing "runtime includes only ordinary imports and non-meta locals"
      (let [result (plan/expand plans a :runtime)]
        (is (= [["br" :runtime] ["ar" :runtime]] (labels result)))
        (is (= #{[a :runtime] [b :runtime]} (:initialized result)))))
    (testing "comptime calls meta imports at runtime, not comptime"
      (let [result (plan/expand plans a :comptime)]
        (is (= [["cr" :runtime] ["am" :comptime]] (labels result)))
        (is (= #{[a :comptime] [c :runtime]} (:initialized result)))))))

(deftest legacy-entry-imports-first-then-own-split-passes
  (let [plans {a (module-plan true [{:module b :meta true} {:module c :meta false}]
                              [(action "am1" true) (action "ar1" false)
                               (action "am2" true) (action "ar2" false)])
               b (module-plan true [] [(action "bm" true) (action "br" false)])
               c (module-plan true [] [(action "cr" false) (action "cm" true)])}
        result (plan/expand plans a :all)]
    (is (= [["br" :runtime] ["bm" :comptime]
            ["cr" :runtime] ["cm" :comptime]
            ["ar1" :runtime] ["ar2" :runtime]
            ["am1" :comptime] ["am2" :comptime]] (labels result)))
    (is (= (set (for [m [a b c] p [:all :runtime :comptime]] [m p]))
           (:initialized result)))
    (is (empty? (:actions (plan/expand plans a :all (:initialized result)))))))

(deftest preentered-guards-and-cycles
  (let [plans {a (module-plan false [{:module b :meta false}] [(action "a" false)])
               b (module-plan false [{:module a :meta false}] [(action "b" false)])}]
    (is (= [["b" :all] ["a" :all]] (labels (plan/expand plans a :all))))
    (is (= [["a" :all]] (labels (plan/expand plans a :all #{[b :all]}))))
    (is (= #{[a :all] [b :all]}
           (:initialized (plan/expand plans a :all #{[b :all]})))))
  (let [plans {a (module-plan true [{:module a :meta false}] [(action "a" false)])}]
    (is (= [["a" :runtime]] (labels (plan/expand plans a :all))))))

(deftest split-guards-are-independent
  (let [plans {a (module-plan true [] [(action "m" true) (action "r" false)])}
        result (plan/expand plans a :all #{[a :runtime]})]
    (is (= [["m" :comptime]] (labels result)))
    (is (= #{[a :runtime] [a :comptime] [a :all]} (:initialized result)))))

(deftest invalid-plans-and-phases
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Missing producer"
                       (plan/expand {} a :all)))
  (let [plans {a (module-plan false [] [])}]
    (doseq [phase [:runtime :comptime]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Classic Lean module"
                           (plan/expand plans a phase))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unknown module"
                         (plan/expand plans a :unknown))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Missing producer"
                       (plan/expand {a (module-plan true [{:module b :meta false}] [])} a :all))))
