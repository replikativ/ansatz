;; Regenerate a store's persistent @[simp] index (`<store>/simp-keys.ndjson.gz`):
;; the LHS disc-tree key of every inherited @[simp] lemma, dumped once so simp
;; serves the ~90k-lemma corpus lazily (candidate names by key, rule resolved on
;; demand) instead of resolving+keying the whole set on every call.
;;
;;   clj -J-Xmx8g -M scripts/dump_simp_keys.clj [store-name]
;;
;; Defaults to "mathlib". Keying forces each lemma's type/LHS out of PSS — for
;; full Mathlib's ~90k @[simp] lemmas expect tens of minutes; re-run only after
;; a fresh import (or after changing the keying).
(require '[ansatz.core :as a]
         '[ansatz.simp-index :as si]
         '[ansatz.kernel.env :as env]
         '[ansatz.export.storage :as storage]
         '[ansatz.store :as store])

(let [store-name (or (first *command-line-args*) "mathlib")
      _ (a/init! store-name)
      env0 (deref a/ansatz-env)
      store-path (store/resolve-existing store-name)
      names (map (fn [n] (if (instance? ansatz.kernel.Name n) (ansatz.kernel.name/->string n) (str n)))
                 (env/get-extension env0 :simp-lemmas #{}))
      ctx (storage/prepare-verify (storage/open-store store-path) store-name)
      resolve-fn (:resolve-fn ctx)
      path (str store-path "/simp-keys.ndjson.gz")
      tmp (str path ".tmp")
      _ (println "Dumping simp LHS keys for" (count names) "@[simp] lemmas ->" path)
      t0 (System/nanoTime)
      n (si/dump-simp-keys! names env0 resolve-fn tmp)]
  ;; write-then-rename: a killed dump must not truncate the live artifact
  (.renameTo (java.io.File. tmp) (java.io.File. path))
  (println "Wrote" n "keys in" (quot (- (System/nanoTime) t0) 1000000000) "s")
  (shutdown-agents))
