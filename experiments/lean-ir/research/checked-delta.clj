(ns research.checked-delta
  "Compatibility entry points for the promoted live checked-base experiment."
  (:require [prototype.checked-delta :as delta]))

(def capture-base delta/capture-base)
(def verify-extension delta/verify-extension)
;; Retained only for the existing research mutation-witness checks.
(defn- expression-array-witnesses [certificate]
  (#'delta/expression-array-witnesses certificate))
