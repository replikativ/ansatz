(ns ansatz.store.pack
  "Packing an imported store into the artifacts that are published for it.

   A store is published once per import — `<name>-<library tag>-f<store format>`, with a
   `-r<n>` suffix when the same library and format are imported again (our importer changed).
   The artifacts are `.tar.gz` parts plus a `store.edn` descriptor with each part's sha256;
   `ansatz.store.fetch` reads the same shape out of the published index.

   Only what a store IS travels: the blobs, the catalogue, the manifest and the Lean export
   inputs it was built from. Logs and verification checkpoints stay behind.

     clojure -M -m ansatz.store.pack <store-dir> <out-dir> [id]"
  (:require [ansatz.store :as store]
            [ansatz.store.archive :as archive]
            [clojure.java.io :as io]
            [clojure.pprint :as pprint]
            [clojure.string :as str])
  (:import [java.security MessageDigest]))

(def parts-spec
  "Part name → the store entries it carries. `catalogue` is optional (a store imported
   without the datahike module has none)."
  [["blobs.tar.gz" ["blobs"] true]
   ["catalogue.tar.gz" ["catalogue"] false]
   ["meta.tar.gz" ["manifest.edn" "inputs"] true]])

(defn- sha256-hex [f]
  (let [md (MessageDigest/getInstance "SHA-256")
        buf (byte-array (* 1024 1024))]
    (with-open [in (io/input-stream f)]
      (loop [] (let [r (.read in buf)] (when (pos? r) (.update md buf 0 r) (recur)))))
    (apply str (map #(format "%02x" %) (.digest md)))))

(defn store-id
  "The published identity of the store at `store-path`: name, library tag and store format,
   e.g. `mathlib-v4.33.1-f1`. `revision` marks a re-import of the same library and format."
  ([store-path] (store-id store-path nil))
  ([store-path revision]
   (let [m (store/check-format! store-path)
         nm (.getName (io/file store-path))
         tag (or (get-in m [:provenance :library/tag])
                 (throw (ex-info "store manifest has no :provenance :library/tag — re-run the setup script"
                                 {:store store-path})))]
     (str nm "-" tag "-f" (:store/format m) (when revision (str "-r" revision))))))

(defn pack!
  "Write the artifacts of the store at `store-path` into `out-dir`. Returns the descriptor."
  [store-path out-dir & {:keys [id revision]}]
  (let [m (store/check-format! store-path)
        id (or id (store-id store-path revision))
        out (io/file out-dir id)
        _ (.mkdirs out)
        parts (vec (for [[file entries required?] parts-spec
                         :let [present (filterv #(.exists (io/file store-path %)) entries)]
                         :when (or (seq present)
                                   (when required?
                                     (throw (ex-info (str "store is missing " (str/join ", " entries))
                                                     {:store store-path}))))]
                     (let [f (io/file out file)
                           {:keys [files]} (archive/pack! store-path f present)]
                       (println (format "  %-18s %6.2f GiB  %d files" file
                                        (/ (.length f) 1073741824.0) files))
                       {:file file :size (.length f) :sha256 (sha256-hex f) :files files})))
        descriptor {:store/id id
                    :store/name (.getName (io/file store-path))
                    :store/format (:store/format m)
                    :library (:provenance m)
                    :packed (java.util.Date.)
                    :parts parts}]
    (spit (io/file out "store.edn") (with-out-str (pprint/pprint descriptor)))
    ;; the line to paste into the index of the store repository
    (spit (io/file out "index-entry.edn")
          (with-out-str
            (pprint/pprint {(:store/name descriptor)
                            {(:store/format descriptor)
                             {:id id
                              :library/tag (get-in m [:provenance :library/tag])
                              :parts (mapv #(select-keys % [:file :size :sha256]) parts)}}})))
    (println (format "  %-18s %6.2f GiB total" "" (/ (reduce + 0 (map :size parts)) 1073741824.0)))
    (println "  descriptor:" (str (io/file out "store.edn")))
    descriptor))

(defn -main [& [store-path out-dir id]]
  (when-not (and store-path out-dir)
    (println "usage: clojure -M -m ansatz.store.pack <store-dir> <out-dir> [id]")
    (System/exit 2))
  (pack! store-path out-dir :id id)
  (shutdown-agents))
