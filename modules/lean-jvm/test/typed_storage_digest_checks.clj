(ns ansatz-lean-jvm-typed-storage-digest-checks
  "Cross-language identity gate against freshly emitted actual Java metadata."
  (:require [clojure.data.json :as json]
            [ansatz.lean.jvm.type-graph :as graph])
  (:import [java.nio.file Files Path]))

(defn check! [path]
  (let [file (Path/of path (make-array String 0))]
    (assert (<= 1 (Files/size file) (* 4 1048576)) "Bounded fresh Java digest receipt required")
    (let [cases (json/read-str (Files/readString file))]
      (assert (= ["native004-recursive" "renumbered" "escaped-nested"] (mapv #(get % "label") cases)))
      (doseq [case cases]
        (let [canonical (get case "canonicalLogical") rows (get case "typeDigests")]
          (assert (= (graph/canonical-graph (get case "inputLogical")) canonical)
                  (str "Canonical graph mismatch: " (get case "label")))
          (assert (<= 1 (count rows) 8192) "Missing per-plan comparisons")
          (doseq [row rows]
            (let [type (get row "type")
                  ;; Metadata uses canonical IDs; builtin children may need to be
                  ;; temporarily selected as roots for the public model helper.
                  rooted (update canonical "roots" #(vec (distinct (conj % type))))]
              (assert (= (get row "digest") (graph/type-digest rooted type))
                      (str "Type identity mismatch: " (get case "label") " plan " (get row "plan")))))))
      (println "Typed storage Java/Clojure identity gate passed:"
               (count cases) "graphs," (reduce + (map #(count (get % "typeDigests")) cases)) "type digests")
      true)))

(when (seq *command-line-args*) (check! (first *command-line-args*)))
