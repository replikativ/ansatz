;; Build a store's CATALOGUE (`<store>/catalogue`): a datahike DB with the durable disc-tree
;; secondary index over the recall keys (`:idx/dt`, from discr-keys.ndjson.gz) and the @[simp]
;; LHS keys (`:idx/simp`, from simp-keys.ndjson.gz), in one transaction. Afterwards a fresh
;; process connects in ~130 ms instead of rebuilding a trie (ansatz.catalogue).
;;
;;   clj -J-Xmx4g -M:datahike scripts/build_catalogue.clj [store-name]
;;
;; Defaults to "mathlib"; needs the two sidecars (scripts/dump_recall_keys.clj,
;; scripts/dump_simp_keys.clj). Mathlib: ~440k entities, ~10-15 min, ~150 MB.
(require '[ansatz.catalogue :as cat] '[ansatz.store :as store])

(let [store-name (or (first *command-line-args*) "mathlib")
      store-path (or (store/resolve-existing store-name)
                     (throw (ex-info "no such store" {:store store-name})))]
  (println "Building catalogue for" store-path "...")
  (prn (cat/build! store-path))
  (shutdown-agents))
