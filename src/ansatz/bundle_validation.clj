(ns ansatz.bundle-validation
  "Internal schema-2 /1 candidate validation. Produces staging files only after
   per-role checks and parser cleanup; never promotes or activates a bundle."
  (:require [ansatz.bundle :as bundle]
            [ansatz.bundle-metadata :as metadata]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.export.codec :as codec]
            [boring.core :as boring]
            [clojure.data.json :as json]
            [clojure.walk :as walk]
            [clojure.java.io :as io])
  (:import [ansatz.kernel ConstantInfo]
           [java.io ByteArrayOutputStream]
           [java.nio.file Files Path FileAlreadyExistsException]
           [java.nio.file.attribute FileAttribute]
           [java.nio ByteBuffer]
           [java.nio.charset StandardCharsets CodingErrorAction]
           [java.security MessageDigest]
           [java.util Arrays]
           [java.util.zip GZIPOutputStream]))

(defn- sha256 [payload]
  (apply str (map #(format "%02x" (bit-and 255 %))
                 (.digest (MessageDigest/getInstance "SHA-256") ^bytes payload))))
(defn- payload [file] (java.nio.file.Files/readAllBytes (.toPath (io/file file))))
(defn- compress [bytes]
  (let [buffer (ByteArrayOutputStream.)]
    (with-open [out (GZIPOutputStream. buffer)] (.write out ^bytes bytes))
    (.toByteArray buffer)))
(defn- require! [condition message data]
  (when-not condition (throw (ex-info message data))))
(defn- declaration-name [^ConstantInfo ci] (str (.name ci)))
(def ^:private legacy-supplemental-pattern
  #"(\._sizeOf_1|\._sizeOf_inst|\.sizeOf_spec)$|^SizeOf(\.|$)|^instSizeOf|^Prod\.Lex(\.|$)|^Lean\.Omega\.Prod\.")

(defn- strict-utf8 [bytes]
  (str (.decode (doto (.newDecoder StandardCharsets/UTF_8)
                  (.onMalformedInput CodingErrorAction/REPORT)
                  (.onUnmappableCharacter CodingErrorAction/REPORT))
                (ByteBuffer/wrap bytes))))

(defn- with-parsed-roles [raw-payloads f]
  ;; Fixed three-deep ownership scopes. An inner parse/body/close failure closes
  ;; every outer store, preserving that primary error and suppressing cleanup.
  (letfn [(consume [roles states]
            (if-let [role (first roles)]
              (parser/with-parser-state
                (parser/parse-ndjson-string (strict-utf8 (get raw-payloads role)))
                #(consume (next roles) (assoc states role %)))
              (f states)))]
    (consume [:init :lex :sizeof] {})))

(defn- compute-candidate! [directory recipe raw-payloads parsed]
  (let [producer (walk/keywordize-keys (:meta (:init parsed)))
        indexes (into {} (for [[role state] parsed]
                           [role (into {} (map (juxt declaration-name identity)) (:decls state))]))
        companions (into {}
                         (for [role [:attrs :matchers :instances]
                               :let [file (io/file directory "raw" (str (name role)
                                                                        (if (= role :instances) ".tsv" ".ndjson")))]]
                           [role (metadata/parse role (slurp file))]))
        registry (codec/registry (constantly nil))]
    (doseq [[role state] parsed]
      (require! (= producer (walk/keywordize-keys (:meta state))) "Kernel producer headers differ" {:role role})
      (require! (= (count (:decls state)) (count (get indexes role)))
                "Duplicate exported declarations" {:role role})
      (doseq [root (get-in recipe [:roots role])]
        (require! (contains? (get indexes role) root) "Export is missing a requested root"
                  {:role role :root root})))
    ;; /1 checks only the existing serialized global-reference contract. Witness
    ;; profile /2 remains planner-only. Union coverage cannot authorize a role.
    (metadata/assert-role-closure! companions (into {} (map (fn [[role index]] [role (set (keys index))])) indexes))
    (let [checks (into {}
                       (for [role [:init :lex :sizeof]
                             :let [result (replay/replay (get-in parsed [role :decls])
                                                         :verify? true :stop-on-error? true)]]
                         [role (:stats result)]))
          _ (do (println {:kernel-validated checks}) (flush))
          overlap-count
          (count
           (for [[left right] [[:init :lex] [:init :sizeof] [:lex :sizeof]]
                 [name ci] (get indexes left)
                 :when (contains? (get indexes right) name)]
             (do
               (require! (Arrays/equals
                          ^bytes (boring/encode ci {:registry registry})
                          ^bytes (boring/encode (get-in indexes [right name]) {:registry registry}))
                         "Overlapping kernel declarations differ"
                         {:name name :left left :right right})
               name)))
          names (into #{} (mapcat keys) (vals indexes))
          selected (into {} (for [role [:attrs :matchers :instances]]
                              [role (metadata/select-and-report role (get companions role) names)]))
          ;; Realize all raw/rendered/compressed payloads and report work before
          ;; leaving the ownership scopes. No CI, store or lazy parsed work escapes.
          resources (into {}
                          (for [[role path] bundle/role-resources]
                            [path (compress
                                   (if (contains? metadata/roles role)
                                     (.getBytes (metadata/render role (get-in selected [role :rows])) "UTF-8")
                                     (get raw-payloads role)))]))
          rows (mapv (fn [[role path]] {:role role :resource path :sha256 (sha256 (get resources path))})
                     bundle/role-resources)
          manifest (bundle/generated-manifest recipe producer rows)
          consumption (bundle/with-verified {:manifest manifest :read-resource resources}
                        (fn [_]
                          (try
                            (bundle/assert-consumable!)
                            {:supported true}
                            (catch clojure.lang.ExceptionInfo error
                              {:supported false :message (.getMessage error) :details (ex-data error)}))))
          report {:kernel checks :overlap-count overlap-count
                  :legacy-supplemental-in-init
                  (vec (sort (filter #(re-find legacy-supplemental-pattern %) (keys (:init indexes)))))
                  :metadata (into {} (map (fn [[role value]] [role (:report value)])) selected)
                  :consumer consumption :promotion :not-performed
                  :activation-acceptance :not-run :artifact/cohort (:artifact/cohort manifest)}]
      {:resources resources :manifest manifest :report report})))

(defn- write-manifest-temp! [^Path path manifest]
  (with-open [out (io/output-stream (.toFile path))]
    (.write out (.getBytes (pr-str manifest) StandardCharsets/UTF_8))))

(defn- publish-manifest-link! [^Path destination ^Path temporary]
  ;; Same-filesystem hardlink publication creates a complete final entry without
  ;; replacing an existing one. Unsupported filesystems fail closed. ATOMIC_MOVE
  ;; alone has implementation-defined replacement semantics if the target exists.
  (Files/createLink destination temporary))

(defn- delete-manifest-temp! [^Path path] (Files/deleteIfExists path))

(defn- write-manifest! [file manifest]
  (let [destination (.toPath (io/file file))
        temporary (Files/createTempFile (.getParent destination) ".ansatz-bundle-" ".tmp"
                                        (make-array FileAttribute 0))]
    (try
      ;; The stream has closed successfully before the final name can exist.
      (write-manifest-temp! temporary manifest)
      (publish-manifest-link! destination temporary)
      (catch Throwable original
        (try (delete-manifest-temp! temporary)
             (catch Throwable cleanup
               (when-not (identical? original cleanup) (.addSuppressed original cleanup))))
        (throw original)))
    ;; Publication has committed. Hygiene failure must not imply rollback or
    ;; erase another writer's marker; retain a bounded, truthful outcome instead.
    (try
      (delete-manifest-temp! temporary)
      {:published true :temporary-cleanup :removed}
      (catch Throwable cleanup
        (let [message (or (.getMessage cleanup) "")
              exception-class (.getName (class cleanup))]
          {:published true :temporary-cleanup :retained
           :diagnostic {:temporary-file (str (.getFileName temporary))
                        :message (subs message 0 (min 256 (count message)))
                        :exception-class (subs exception-class 0 (min 256 (count exception-class)))}})))))

(defn- claim-staging! [directory]
  ;; Retain the claim on success AND failure. It coordinates this validator's
  ;; writers only; no PID-based stealing, retry, or whole-filesystem claim.
  (try
    (Files/createFile (.toPath (io/file directory ".ansatz-bundle-validation.claim"))
                      (make-array FileAttribute 0))
    (catch FileAlreadyExistsException cause
      (throw (ex-info "Candidate staging directory was already claimed; use fresh staging"
                      {:type ::staging-claimed :stage :claim} cause)))))

(defn validate-candidate!
  "Validate the existing generator /1 staging directory. Every role must close
   its own global companion references before replay. Capture each raw role once
   and use those same bytes for strict UTF-8 parsing and compression. Close all parser stores
   before writing any candidate resources/report/final manifest. A close failure
   prevents commit; validation errors retain suppressed cleanup failures. An
   exclusive create-new staging claim is retained on success and failure, so any
   retry needs a fresh directory. The claim is not checking authority. Final
   publication uses a complete temporary file and a no-replace hardlink. A later
   temporary-cleanup failure returns :publication {:published true ...} with a
   bounded diagnostic. This is not general input budgeting, profile-2 witness
   validation or promotion."
  [directory]
  (let [manifest-file (io/file directory "resources" bundle/manifest-resource)
        _ (require! (not (.exists manifest-file))
                    "Candidate already has a final manifest; use a fresh staging directory" {})
        _ (claim-staging! directory)
        recipe (json/read-str (slurp (io/file directory "generation.json")) :key-fn keyword)
        raw-payloads (into {} (map (fn [role]
                                    [role (payload (io/file directory "raw" (str (name role) ".ndjson")))]))
                           [:init :lex :sizeof])
        {:keys [resources manifest report]}
        (with-parsed-roles raw-payloads #(compute-candidate! directory recipe raw-payloads %))]
    ;; Every successful parse has closed before this first staging write.
    (doseq [[path bytes] resources]
      (let [file (io/file directory "resources" path)]
        (io/make-parents file)
        (with-open [stream (io/output-stream file)] (.write stream ^bytes bytes))))
    (spit (io/file directory "validation.edn") (pr-str report))
    ;; Structural generation marker, not a proof certificate. Write LAST, and
    ;; propagate write failure instead of returning candidate success.
    (assoc report :publication (write-manifest! manifest-file manifest))))
