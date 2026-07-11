;; Regenerate a store's persistent recall index (`<store>/discr-keys.ndjson.gz`):
;; the disc-tree conclusion key of every useful declaration, dumped once so
;; (a/init!) can rebuild the recall trie in seconds instead of re-keying the
;; library every session (see ansatz.recall).
;;
;;   clj -J-Xmx12g -M scripts/dump_recall_keys.clj [store-name]
;;
;; Defaults to "mathlib". The keying pass forces every declaration's type out
;; of PSS — for full Mathlib (~649k decls) expect ~1.5-2h and a ~16MB artifact;
;; it only needs to be re-run after a fresh import.
(require '[ansatz.core :as a]
         '[ansatz.recall :as recall]
         '[ansatz.export.storage :as storage]
         '[ansatz.store :as store])

(let [store-name (or (first *command-line-args*) "mathlib")
      _ (a/init! store-name)
      store-path (store/resolve-existing store-name)
      ctx (storage/prepare-verify (storage/open-store store-path) store-name)
      order (:decl-order ctx)
      path (str store-path "/discr-keys.ndjson.gz")
      tmp (str path ".tmp")
      _ (println "Dumping recall keys for" (count order) "decls (useful-filtered) ->" path)
      t0 (System/nanoTime)
      n (recall/dump-discr-keys! order (:resolve-fn ctx) tmp)]
  ;; write-then-rename: a crashed/killed dump must not destroy the artifact
  (.renameTo (java.io.File. tmp) (java.io.File. path))
  (println "Wrote" n "keys in" (quot (- (System/nanoTime) t0) 1000000000) "s")
  (shutdown-agents))
