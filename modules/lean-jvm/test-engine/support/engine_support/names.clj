(ns engine-support.names)

(defn name-label [[op parent part]]
  (case op "anonymous" "" (let [p (name-label parent)] (str p (when (seq p) ".") part))))
