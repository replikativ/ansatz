;; A documentation example is not the declaration: (ns misleading.example-test)
(ns ^:no-doc ci.discovery-fixture-test
  (:require [clojure.test :refer [deftest is]]))

(deftest discovery-must-select-this-failing-test
  (is false "The discovery self-test must observe this intentional failure."))
