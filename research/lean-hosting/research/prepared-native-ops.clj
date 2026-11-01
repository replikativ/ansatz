(ns prepared-native-ops
  "Compatibility entry points for the original REPL experiments. Arithmetic
   and registry guards now live in the optional runtime's native-nat module."
  (:require [prototype.native-nat :as native]))

(def prepare-op native/prepare-op)
(def try-op native/try-op)
(def decline? native/decline?)
