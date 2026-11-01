;; Explicit ABI admission from the pinned source collection. Review the diff.
;; Optional arguments select module names for a narrow primitive-family update.
(require '[clojure.data.json :as json] '[clojure.edn :as edn]
         '[clojure.java.io :as io] '[clojure.pprint :as pprint]
         '[prototype.runtime-abi :as abi] '[prototype.runtime-prim :as prim])
(let [file "src/prototype/runtime_signatures.edn"
      old (edn/read-string (slurp file))
      collection (json/read-str (slurp "target/module-plans/collection.json"))
      modules (if (seq *command-line-args*)
                (do (doseq [module *command-line-args*]
                      (when-not (contains? (get collection "modules") module)
                        (throw (ex-info "Module is outside the completed pinned collection" {:module module}))))
                    *command-line-args*)
                (sort (keys (get collection "modules"))))
      paths (map #(io/file "target/module-plans" (str % ".jsonl")) modules)
      merged
      (reduce (fn [result path]
                (with-open [reader (io/reader path)]
                  (reduce (fn [result line]
                            ;; Source-local extern rows have no nested bodies.
                            (if-not (.contains ^String line "\"extern\":") result
                              (let [row (json/read-str line :key-fn keyword)
                                    ext (get-in row [:ir :extern]) symbol (abi/symbol-for ext)]
                                (if-not (contains? prim/supported-symbols symbol) result
                                  (update result symbol #(vec (distinct (conj (vec %) {:params (mapv (fn [p] (select-keys p [:ty :borrow])) (:xs ext)) :return-type (:type ext)}))))))))
                          result (line-seq reader)))) old paths)]
  (spit file (with-out-str (pprint/pprint (into (sorted-map) merged))))
  (println {:before (count old) :after (count merged) :modules (count modules) :exporter-sha256 (get collection "exporter-sha256")}))
