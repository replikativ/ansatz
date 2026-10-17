(ns prototype.heap-overlay
  "Local mutable Map overlay over a single persistent snapshot heap.
   Only changed entries allocate Java HashMap storage. The base is borrowed and
   must contain frozen immutable nodes; callers still normalize external arrays.
   Views are live; their iterators snapshot keys and expose immutable entries."
  (:import [ansatz.runtime HeapOverlay] [java.util HashSet Set]))

(defn overlay
  ([base] (overlay base (HashSet.)))
  ([base dirty-ids]
   (when-not (instance? clojure.lang.IPersistentMap base)
     (throw (ex-info "Heap overlay requires a persistent map base" {})))
   (HeapOverlay. base ^Set dirty-ids))
  ([base dirty-ids canonical-long-keys?]
   ;; Internal attestation from mutable/thaw's existing full validation pass.
   ;; Generic public Map use must leave this false unless every base key is Long.
   (when-not (instance? clojure.lang.IPersistentMap base)
     (throw (ex-info "Heap overlay requires a persistent map base" {})))
   (HeapOverlay. base ^Set dirty-ids (boolean canonical-long-keys?))))
