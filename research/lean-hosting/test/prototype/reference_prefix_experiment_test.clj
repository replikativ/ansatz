(ns prototype.reference-prefix-experiment-test
  "Canonical fixture checks for an explicitly loaded REPL experiment."
  (:require [clojure.test :refer [deftest is]]
            [prototype.raw-interop :as raw]))

(load-file "scripts/reference-prefix-experiment.clj")
(load-file "scripts/reference-prefix-smoke.clj")

(deftest canonical-prefix-fuel-and-ownership-differentials
  ;; Each comparison checks the complete reference world, including RC/events,
  ;; control, task state and exact fuel. The helper reports scalar context only.
  (is (= {:status :pass :checks 147 :fixtures 7 :host-handler-executions 0}
         (prototype.reference-prefix-smoke-draft/smoke!
           @#'raw/run-boundary prototype.reference-prefix-draft/run-boundary))))
