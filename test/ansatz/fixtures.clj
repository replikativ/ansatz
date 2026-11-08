(ns ansatz.fixtures
  "Explicit availability guards for optional, uncommitted test exports."
  (:require [clojure.java.io :as io]
            [clojure.test :as t]))

(defn available? [files]
  (let [missing (remove #(.exists (io/file %)) files)]
    (if (seq missing)
      (do (println "SKIP optional fixture:" (vec missing)) false)
      true)))

(defn requiring-files
  "Skip before setup when an optional export is absent; setup errors still propagate."
  [files & fixtures]
  (fn [run-tests]
    (when (available? files)
      ((t/join-fixtures fixtures) run-tests))))

(defn isolated-session
  "A :once fixture that restores the global Ansatz session after the namespace. Without it, a
   namespace's declarations leak into later namespaces in the same JVM: (a/load-init!) with the
   same bundle keeps the active Env, so a later namespace declaring the same name fails with
   \"Constant already declared\" — or passes only because CI's shard split (bin/test-namespaces)
   happens to separate the two. Compose it outermost: (use-fixtures :once isolated-session …)."
  [f]
  (let [cells [(requiring-resolve 'ansatz.state/ansatz-env)
               (requiring-resolve 'ansatz.state/ansatz-instance-index)
               (requiring-resolve 'ansatz.state/ansatz-discr-trie)
               (requiring-resolve 'ansatz.state/ansatz-simp-trie)
               (requiring-resolve 'ansatz.state/ansatz-store)
               (requiring-resolve 'ansatz.surface.ingest/arity-registry)
               (requiring-resolve 'ansatz.surface.ingest/codegen-registry)
               (requiring-resolve 'ansatz.surface.ingest/structure-registry)]
        atoms (map deref cells)
        saved (mapv deref atoms)]
    (try
      (f)
      (finally
        (doseq [[a v] (map vector atoms saved)] (reset! a v))))))
