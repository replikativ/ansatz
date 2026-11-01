;; Run from research/lean-hosting:
;; clojure -J-Xss32m -J-Xmx4g -M scripts/pack-module-plans.clj
;; Optional arguments: input-directory store-directory index-hash-file stats-file.
(require '[clojure.data.json :as json]
         '[clojure.java.io :as io]
         '[prototype.declaration-store :as store])

(let [[input-root store-root index-path stats-path]
      (mapv #(or %1 %2) (concat *command-line-args* (repeat nil))
            ["target/module-plans" "target/parser-module-store"
             "target/parser-module-index.edn" "target/parser-module-pack-stats.edn"])
      collection-file (io/file input-root "collection.json")
      collection (json/read-str (slurp collection-file))
      modules (get collection "modules")
      paths (mapv #(str (io/file input-root (str % ".jsonl"))) (sort (keys modules)))
      actual (set (map #(.getName %) (filter #(.endsWith (.getName %) ".jsonl") (.listFiles (io/file input-root)))))
      expected (set (map #(str % ".jsonl") (keys modules)))
      started (System/nanoTime)]
  (when-not (and (seq modules) (= actual expected) (every? #(.isFile (io/file %)) paths))
    (throw (ex-info "Module collection is incomplete or has unexpected bundles"
                    {:expected (count expected) :actual (count actual)
                     :missing (vec (remove actual expected)) :unexpected (vec (remove expected actual))})))
  (println (pr-str {:kind :pack-start :modules (count modules)
                    :input-bytes (reduce + (map #(.length (io/file %)) paths))}))
  (flush)
  (let [catalogue (store/pack! store-root paths)
        hash (store/checkpoint! catalogue)
        reopened (store/open-index store-root hash)
        stats {:kind :pack-complete :root (get collection "root")
               :roots (or (get collection "roots") [(get collection "root")])
               :modules (count modules) :actions (reduce + (map #(get % "actions") (vals modules)))
               :declarations (count (:declarations catalogue))
               :producer-declarations (reduce + (map #(get % "declarations") (vals modules)))
               :input-bytes (reduce + (map #(.length (io/file %)) paths))
               :exporter-sha256 (get collection "exporter-sha256")
               :index-hash hash :store-path store-root :store-stats (store/stats catalogue)
               :reopen-stats (store/stats reopened)
               :elapsed-ms (long (/ (- (System/nanoTime) started) 1000000))}]
    (when-not (and (= (count (:declarations catalogue)) (count (:declarations reopened)))
                   (= (count modules) (count (:manifests reopened))))
      (throw (ex-info "Packed index verification failed" {:stats stats})))
    (doseq [path [index-path stats-path]] (io/make-parents path))
    (spit index-path (str (pr-str hash) "\n"))
    (spit stats-path (str (pr-str stats) "\n"))
    (println (pr-str stats))
    (flush)))
