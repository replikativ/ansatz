(ns ansatz.meta.rec-ext
  "Lean 4.33.1 Meta/RecExt.lean: recExt, markAsRecursive, isRecursiveDefinition.
   Tags live in the persistent Env extensions and follow forks and session snapshots."
  (:require [ansatz.kernel.env :as env]))

(defn mark-as-recursive [environment decl-name]
  (env/update-extension environment :recursive-defs #{} conj decl-name))

(defn is-recursive-definition [environment decl-name]
  (contains? (env/get-extension environment :recursive-defs #{}) decl-name))
