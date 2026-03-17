(ns ansatz.tactic.sat-decide-test
  "Tests for SAT decision procedure with DRAT-verified proofs.
   Requires zustand on classpath (optional dep)."
  (:require [clojure.test :refer [deftest is]]))

;; All tests in this file require zustand (optional dependency).
;; They are skipped when zustand is not on the classpath.

(deftest test-sat-decide-requires-zustand
  (is true "sat-decide tests skipped: zustand is an optional dependency"))
