(ns engine-support.delayed
  "Explicit delayed-assignment input models; execution uses the native Expr entry."
  (:refer-clojure :exclude [run!])
  (:require [clojure.test :refer [deftest is run-tests]]
            [engine-support.expr-context :as direct] [engine-support.expr :as expr]))

(defn array! [ctx e values]
  (reduce (fn [array value] (expr/call ctx e "Array.push" [0 array value])) (expr/call ctx e "Array.mkEmpty" [0 0]) values))

(defn named-fvar! [ctx e name] (expr/call ctx e "Lean.Expr.fvar._override" [name]))

(defn delayed-with-fvars! [ctx e m name pending fvars]
  ;; Same explicitly labeled storage adapter as Stage3; actual generic map
  ;; operations/getters/accessors execute original source. No monadic API claim.
  (let [record (expr/call ctx e "model-delayed-record" [fvars pending])
        m (expr/call ctx e "model-swap-expr-delayed-maps" [m])
        m (direct/assign! ctx e m name record)]
    [(expr/call ctx e "model-swap-expr-delayed-maps" [m]) record]))
