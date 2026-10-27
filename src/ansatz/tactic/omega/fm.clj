;; Compatibility facade; implementation follows Lean in ansatz.tactic.omega.core.
(ns ansatz.tactic.omega.fm
  (:require [ansatz.tactic.omega.core :as impl]))

(def solve-equalities impl/solve-equalities)
(def solve impl/solve)
