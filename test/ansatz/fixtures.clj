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
