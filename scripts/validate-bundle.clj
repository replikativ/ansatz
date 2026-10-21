;; Internal second phase of generate-bundle.py. Never promotes a candidate.
(require '[ansatz.bundle :as bundle]
         '[ansatz.bundle-metadata :as metadata]
         '[ansatz.export.parser :as parser]
         '[ansatz.export.replay :as replay]
         '[ansatz.export.codec :as codec]
         '[boring.core :as boring]
         '[clojure.data.json :as json]
         '[clojure.walk :as walk]
         '[clojure.java.io :as io])
(import '[ansatz.kernel ConstantInfo ExprStore]
        '[java.security MessageDigest]
        '[java.util Arrays]
        '[java.util.zip GZIPOutputStream])

(defn sha256 [payload]
  (apply str (map #(format "%02x" (bit-and 255 %))
                  (.digest (MessageDigest/getInstance "SHA-256") ^bytes payload))))
(defn payload [file] (java.nio.file.Files/readAllBytes (.toPath (io/file file))))
(defn compress! [file bytes]
  (io/make-parents file)
  (with-open [out (GZIPOutputStream. (io/output-stream file))] (.write out ^bytes bytes)))
(defn require! [condition message data]
  (when-not condition (throw (ex-info message data))))
(defn declaration-name [^ConstantInfo ci] (str (.name ci)))
(def legacy-supplemental-pattern
  #"(\._sizeOf_1|\._sizeOf_inst|\.sizeOf_spec)$|^SizeOf(\.|$)|^instSizeOf|^Prod\.Lex(\.|$)|^Lean\.Omega\.Prod\.")

(defn validate-candidate! [directory]
  (let [_ (require! (not (.exists (io/file directory "resources" bundle/manifest-resource)))
                    "Candidate already has a final manifest; use a fresh staging directory" {})
        recipe (json/read-str (slurp (io/file directory "generation.json")) :key-fn keyword)
        parsed (atom {})]
    (try
      (doseq [role [:init :lex :sizeof]]
        (swap! parsed assoc role (parser/parse-ndjson-file (io/file directory "raw" (str (name role) ".ndjson")))))
      (let [producer (walk/keywordize-keys (:meta (:init @parsed)))
            indexes (into {} (for [[role state] @parsed]
                               [role (into {} (map (juxt declaration-name identity)) (:decls state))]))
            registry (codec/registry (constantly nil))]
        (doseq [[role state] @parsed]
          (require! (= producer (walk/keywordize-keys (:meta state))) "Kernel producer headers differ" {:role role})
          (require! (= (count (:decls state)) (count (get indexes role)))
                    "Duplicate exported declarations" {:role role})
          (doseq [root (get-in recipe [:roots role])]
            (require! (contains? (get indexes role) root) "Export is missing a requested root"
                      {:role role :root root})))
        ;; Each closure is checked independently from an empty kernel Env.
        ;; No replay failure or declaration omission may become a successful candidate.
        (let [checks (into {}
                           (for [role [:init :lex :sizeof]
                                 :let [result (replay/replay (get-in @parsed [role :decls])
                                                             :verify? true :stop-on-error? true)]]
                             [role (:stats result)]))
              _ (do (println {:kernel-validated checks}) (flush))
              overlaps (for [[left right] [[:init :lex] [:init :sizeof] [:lex :sizeof]]
                             [name ci] (get indexes left)
                             :when (contains? (get indexes right) name)]
                         (do
                           ;; The full-CI codec includes checking fields, binder metadata,
                           ;; safety, hints, and recursor rules; local expression IDs do not.
                           (require! (Arrays/equals
                                      ^bytes (boring/encode ci {:registry registry})
                                      ^bytes (boring/encode (get-in indexes [right name]) {:registry registry}))
                                     "Overlapping kernel declarations differ"
                                     {:name name :left left :right right})
                           name))
              overlap-count (count overlaps)
              names (into #{} (mapcat keys) (vals indexes))
              selected (into {}
                             (for [role [:attrs :matchers :instances]
                                   :let [file (io/file directory "raw" (str (name role)
                                                                            (if (= role :instances) ".tsv" ".ndjson")))]]
                               [role (metadata/select-and-report role (metadata/parse role (slurp file)) names)]))
              resources-dir (io/file directory "resources")]
          (doseq [[role path] bundle/role-resources]
            (let [bytes (if (contains? metadata/roles role)
                          (.getBytes (metadata/render role (get-in selected [role :rows])) "UTF-8")
                          (payload (io/file directory "raw" (str (name role) ".ndjson"))))]
              (compress! (io/file resources-dir path) bytes)))
          (let [rows (mapv (fn [[role path]] {:role role :resource path
                                              :sha256 (sha256 (payload (io/file resources-dir path)))})
                           bundle/role-resources)
                manifest (bundle/generated-manifest recipe producer rows)
                reader (fn [path] (let [file (io/file resources-dir path)]
                                    (when (.isFile file) (payload file))))
                consumption (bundle/with-verified {:manifest manifest :read-resource reader}
                              (fn [_]
                                (try
                                  (bundle/assert-consumable!)
                                  {:supported true}
                                  (catch clojure.lang.ExceptionInfo error
                                    {:supported false :message (.getMessage error) :details (ex-data error)}))))
                report {:kernel checks :overlap-count overlap-count
                        ;; Root exclusions are not closure exclusions. Record actual
                        ;; dependencies intact; WF acceptance remains a promotion gate.
                        :legacy-supplemental-in-init
                        (vec (sort (filter #(re-find legacy-supplemental-pattern %) (keys (:init indexes)))))
                        :metadata (into {} (map (fn [[role value]] [role (:report value)])) selected)
                        :consumer consumption :promotion :not-performed
                        :activation-acceptance :not-run
                        :artifact/cohort (:artifact/cohort manifest)}]
            (spit (io/file directory "validation.edn") (pr-str report))
            ;; This is structural/generation metadata, not a serialized kernel certificate.
            ;; Write the final manifest only after every preceding gate completes.
            (spit (io/file resources-dir bundle/manifest-resource) (pr-str manifest))
            (println (select-keys report [:kernel :overlap-count :consumer :artifact/cohort]))
            report)))
      (finally
        (doseq [state (vals @parsed)] (.close ^ExprStore (:exprs state)))))))

(try
  (require! (= 1 (count *command-line-args*)) "Expected one staging directory" {})
  (validate-candidate! (first *command-line-args*))
  (shutdown-agents)
  (catch Throwable error
    ;; A failed replay can carry an entire Env/ExprStore; print only the bounded gate.
    (binding [*out* *err*]
      (println {:bundle-generation-error (.getMessage error)
                :details (select-keys (ex-data error) [:role :root :name :left :right :missing :result])}))
    (System/exit 1)))
