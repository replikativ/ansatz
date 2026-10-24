(ns ansatz.simp-sources
  "Shared Env extension keys and local registration bookkeeping. A dependency
   leaf so attribute/equation registration need not require the simplifier."
  (:require [ansatz.kernel.env :as env]))

(def index-key :simp-index)
(def captured-key :ansatz.simp-index/captured-index)
(def eager-key :ansatz.simp-index/eager-overlay)

(defn mark-local-registration
  "Mark an explicit simp registration to be served eagerly beside an existing
   base index. Initial store imports happen before an index is attached, so their
   large inherited corpus remains lazy. Low-level extension writers must use the
   same bookkeeping when adding local simp declarations after index attachment."
  [current declaration]
  (when-not (string? declaration)
    (throw (ex-info "Expected a declaration name for local simp registration" {})))
  (if (env/get-extension current index-key nil)
    (env/update-extension current eager-key #{} conj declaration)
    current))
