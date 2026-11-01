(ns ansatz-lean-jvm-value-convention-checks
  "Host-carrier conversion models only; no guest allocation or type authority."
  (:require [clojure.test :refer [deftest is run-tests]]
            [ansatz.lean.jvm :as lean])
  (:import [java.util ArrayList Optional List]
           [ansatz.lean.jvm LeanChoice LeanUnit]))

(defn- leaf [kind] {"kind" kind})
(defn- option [element] {"kind" "option" "element" element})
(defn- product [first second] {"kind" "product" "first" first "second" second})
(defn- branch [kind left right]
  (if (= kind "sum") {"kind" kind "left" left "right" right}
      {"kind" kind "error" left "value" right}))
(defn- convert [type input]
  (first (#'lean/host-arguments {"arguments" [type]} [input])))
(defn- restored [type input] (#'lean/clojure-value type (convert type input)))
(defn- code-of [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo error (:code (ex-data error)))))

(deftest java-choice-and-tagged-maps-normalize-the-same-nested-option
  (doseq [[kind left-key right-key] [["sum" :left :right] ["except" :error :ok]]]
    (let [type (branch kind (option (leaf "unit")) (option (leaf "bool")))
          left-input (LeanChoice/left {:some nil})
          right-input (LeanChoice/right {:some false})
          ^LeanChoice left (convert type left-input)
          ^LeanChoice right (convert type right-input)]
      (is (.isLeft left))
      (is (.isPresent ^Optional (.value left)))
      (is (identical? LeanUnit/INSTANCE (.get ^Optional (.value left))))
      (is (not (.isLeft right)))
      (is (false? (.get ^Optional (.value right))))
      (is (= {left-key {:some nil}} (restored type left-input)))
      (is (= {right-key {:some false}} (restored type right-input)))
      (is (= (restored type left-input) (restored type {left-key {:some nil}})))
      (is (= (restored type right-input) (restored type {right-key {:some false}}))))))

(deftest products-inside-both-java-branch-kinds-convert-unit-recursively
  (doseq [[kind left-key right-key] [["sum" :left :right] ["except" :error :ok]]]
    (let [payload (product (leaf "unit") (option (leaf "unit")))
          type (branch kind payload payload)]
      (is (= {left-key [nil {:some nil}]} (restored type (LeanChoice/left [nil {:some nil}]))))
      (is (= {right-key [nil {:some nil}]} (restored type (LeanChoice/right [nil {:some nil}])))))))

(deftest optional-choice-product-carriers-can-be-mixed-without-losing-tags
  (let [payload (product (leaf "unit") (option (leaf "unit")))
        type (option (branch "sum" payload (leaf "bool")))
        input (Optional/of (LeanChoice/left [nil (Optional/of LeanUnit/INSTANCE)]))]
    (is (= {:some {:left [nil {:some nil}]}} (restored type input)))
    (is (= {:some {:left [nil {:some nil}]}}
           (restored type {:some (LeanChoice/left [LeanUnit/INSTANCE {:some nil}])})))))

(deftest none-some-none-and-some-some-unit-stay-distinct-inside-choice
  (let [type (branch "sum" (option (option (leaf "unit"))) (leaf "unit"))]
    (is (= {:left nil} (restored type (LeanChoice/left (Optional/empty)))))
    (is (= {:left {:some nil}} (restored type (LeanChoice/left {:some nil}))))
    (is (= {:left {:some {:some nil}}} (restored type (LeanChoice/left {:some {:some nil}}))))
    (is (= {:right nil} (restored type (LeanChoice/right LeanUnit/INSTANCE))))))

(deftest invalid-nested-carriers-are-still-refused-during-host-conversion
  (let [type (branch "except" (option (leaf "unit")) (product (leaf "unit") (option (leaf "unit"))))]
    (is (= "UnsupportedArgumentType" (code-of #(convert type (LeanChoice/left {:some nil :extra true})))))
    (is (= "UnsupportedArgumentType" (code-of #(convert type (LeanChoice/right [nil {:wrong nil}])))))
    (is (= "InvalidArgument" (code-of #(convert type (LeanChoice/right [nil])))))
    (is (= "UnsupportedArgumentType" (code-of #(convert type {:error nil :ok [nil nil]}))))))

(deftest conversion-snapshots-mutable-choice-payloads-without-mutating-input
  (let [payload (ArrayList. ^java.util.Collection [nil {:some nil}])
        input (LeanChoice/right payload)
        type (branch "except" (leaf "string") (product (leaf "unit") (option (leaf "unit"))))
        ^LeanChoice result (convert type input)]
    (is (identical? payload (.value input)))
    (is (nil? (.get payload 0)))
    (.set payload 0 "changed")
    (is (identical? LeanUnit/INSTANCE (.get ^List (.value result) 0)))
    (is (= {:ok [nil {:some nil}]} (#'lean/clojure-value type result)))
    (is (thrown? UnsupportedOperationException (.set ^List (.value result) 0 :changed)))))

(deftest java-choice-does-not-bypass-the-existing-recursive-budget
  (let [type (branch "sum" {"kind" "list" "element" (leaf "unit")} (leaf "unit"))
        input (LeanChoice/left (vec (repeat 100000 nil)))]
    (is (= "InvalidArgument" (code-of #(convert type input))))))

(defn check! [] (run-tests 'ansatz-lean-jvm-value-convention-checks))
