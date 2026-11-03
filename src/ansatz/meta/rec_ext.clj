(ns ansatz.meta.rec-ext
  "Lean 4.33.1 Meta/RecExt.lean: recExt, markAsRecursive, isRecursiveDefinition.
   Tags live in the persistent Env extensions and follow forks and session snapshots."
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]))

(defn mark-as-recursive [environment decl-name]
  (env/update-extension environment :recursive-defs #{} conj decl-name))

(defn is-recursive-definition [environment decl-name]
  (let [tags (env/get-extension environment :recursive-defs #{})]
    (or (contains? tags decl-name) (contains? tags (name/->string decl-name)))))

(defn has-smart-unfolding-decl [environment decl-name]
  ;; Meta/WHNF.lean hasSmartUnfoldingDecl, exported by dump_attrs.lean.
  (contains? (env/get-extension environment :smart-unfolding-defs #{}) (name/->string decl-name)))
