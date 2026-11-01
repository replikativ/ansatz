(ns prototype.heap-profile
  (:require [prototype.heap-examples :as h]
            [prototype.block-compile :as b]
            [prototype.mutable :as u]))

(defn -main [& _]
  (let [functions (h/functions) program (b/compile-program functions)
        initial (:initial (h/prepare functions :map (range 1000) false))]
    (dotimes [_ 200] (b/run! program (u/thaw initial))))
  (shutdown-agents))
