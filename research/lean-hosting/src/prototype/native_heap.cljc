(ns prototype.native-heap
  "Read-only, fully validated imported object ranges. Implementations expose only
   immutable RC0 data nodes; range membership never decodes or traverses data.")

(defprotocol NativeSource
  (contains-id? [source id] "Whether this verified source owns a reserved guest ID.")
  (lookup-node [source id] "Immutable RC0 node for an owned ID, nil otherwise."))

(defn imported? [sources id]
  (boolean (some #(contains-id? % id) sources)))

(defn lookup [sources id]
  (some #(when (contains-id? % id) (lookup-node % id)) sources))
