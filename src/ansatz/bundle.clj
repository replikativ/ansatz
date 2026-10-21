(ns ansatz.bundle
  "Integrity and compatibility checks for bundled resources. Schema 1 preserves
   legacy inventory history; schema 2 binds a pinned generation recipe and each
   producer to the artifact cohort. Neither grants kernel checking authority or
   authentication."
  (:require [ansatz.bundle-metadata :as metadata]
            [clojure.data.json :as json]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str])
  (:import [java.io ByteArrayInputStream ByteArrayOutputStream]
           [java.nio.charset StandardCharsets]
           [java.security MessageDigest]
           [java.util.zip GZIPInputStream]))

(def manifest-resource "ansatz/bundle.edn")
(def role-resources
  "The six resource paths consumed by this bundled-artifact format. A manifest
   must inventory these exact role/path pairs before packaging or activation."
  {:init "ansatz/init-medium.ndjson.gz"
   :lex "ansatz/lex-prelude.ndjson.gz"
   :sizeof "ansatz/sizeof-prelude.ndjson.gz"
   :attrs "ansatz/init-attrs.ndjson.gz"
   :matchers "ansatz/init-matchers.ndjson.gz"
   :instances "ansatz/init-instances.tsv.gz"})
(def ^:private kernel-roles #{:init :lex :sizeof})
(def ^:private metadata-roles #{:attrs :matchers :instances})
(def ^:private companion-dumpers
  {:attrs "scripts/dump_attrs.lean"
   :matchers "scripts/dump_matchers.lean"
   :instances "scripts/dump_instances.lean"})
(def ^:private generated-lean
  {:version "4.33.1" :githash "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"})

(defn classpath-bytes
  "Read a classpath resource into a byte array, or nil if absent. No extraction,
   kernel loading, or session mutation. Usable as verify!'s :read-resource hook."
  [resource]
  (when-let [url (io/resource resource)]
    (with-open [in (io/input-stream url)
                out (ByteArrayOutputStream.)]
      (io/copy in out)
      (.toByteArray out))))

(defn- required-bytes [reader resource]
  (let [payload (reader resource)]
    (when-not (bytes? payload)
      (throw (ex-info "Bundled resource is missing or is not bytes" {:resource resource})))
    payload))

(defn- sha256 [^bytes payload]
  (apply str (map #(format "%02x" (bit-and 255 %))
                  (.digest (MessageDigest/getInstance "SHA-256") payload))))

(defn inventory-cohort
  "Content identity for resource rows. Hash the UTF-8 bytes of the literal prefix
   ansatz-bundle-inventory/1 followed by LF, then rows sorted by [role resource].
   Each row is role (keyword name), TAB, resource, TAB, lowercase SHA256, LF.
   Return legacy-inventory-sha256:<hex>. This is consistency, not authentication;
   validate manifest row structure separately. Resource order is immaterial."
  [resources]
  (let [canonical (str "ansatz-bundle-inventory/1\n"
                       (apply str (for [{:keys [role resource sha256]} (sort-by (juxt :role :resource) resources)]
                                    (str (name role) "\t" resource "\t" sha256 "\n"))))]
    (str "legacy-inventory-sha256:" (sha256 (.getBytes canonical StandardCharsets/UTF_8)))))

(defn- nonempty-string? [value]
  (and (string? value) (not (str/blank? value))))

(defn- producer? [value]
  (and (map? value)
       (every? nonempty-string?
               [(get-in value [:exporter :name]) (get-in value [:exporter :version])
                (get-in value [:format :version]) (get-in value [:lean :version])
                (get-in value [:lean :githash])])))

(defn- hash? [value]
  (and (string? value) (boolean (re-matches #"[0-9a-f]{64}" value))))

(defn- relative-path? [value]
  (and (nonempty-string? value)
       (not (re-find #"[\\:\t\r\n]" value))
       (every? #(and (not (str/blank? %)) (not (contains? #{"." ".."} %)))
               (str/split value #"/" -1))))

(defn- validate-generation! [generation kernel-producer]
  (let [{:keys [lean exporter inputs roots]} generation]
    (when-not
     (and (map? generation)
          (= #{:profile :lean :exporter :inputs :roots :metadata-profile} (set (keys generation)))
          (= "ansatz-bundle-generator/1" (:profile generation))
          (= "ansatz-global-companions/1" (:metadata-profile generation))
          (= generated-lean lean (:lean kernel-producer))
          (= {:exporter {:name "lean4export" :version "3.1.0"}
              :format {:version "3.1.0"} :lean generated-lean} kernel-producer)
          (map? exporter)
          (= #{:commit :binary-sha256 :source-sha256 :toolchain} (set (keys exporter)))
          (string? (:commit exporter)) (re-matches #"[0-9a-f]{40}" (:commit exporter))
          (hash? (:binary-sha256 exporter)) (hash? (:source-sha256 exporter))
          (= "leanprover/lean4:v4.33.1" (:toolchain exporter))
          (vector? inputs) (seq inputs)
          (every? #(and (map? %) (= #{:path :sha256} (set (keys %)))
                        (relative-path? (:path %)) (hash? (:sha256 %))) inputs)
          (= (count inputs) (count (set (map :path inputs))))
          (every? (set (map :path inputs)) (vals companion-dumpers))
          (map? roots) (= kernel-roles (set (keys roots)))
          (every? #(and (vector? %) (seq %) (= (count %) (count (set %)))
                        (every? (fn [root] (and (nonempty-string? root)
                                                (not (re-find #"[\t\r\n]" root)))) %))
                  (vals roots)))
      (throw (ex-info "Invalid generated bundled artifact recipe" {}))))
  generation)

(defn- canonical-data [value]
  ;; Tagged values avoid collisions between keyword/string keys and containers.
  ;; Only these recipe data types are admitted; EDN printer settings cannot
  ;; influence the cohort. Map order is normalized, vector order is retained.
  (cond
    (map? value) ["map" (->> value
                             (map (fn [[k v]] [(canonical-data k) (canonical-data v)]))
                             (sort-by #(json/write-str (first %))) vec)]
    (vector? value) ["vector" (mapv canonical-data value)]
    (keyword? value) ["keyword" (namespace value) (name value)]
    (string? value) ["string" value]
    (nil? value) ["nil"]
    (boolean? value) ["boolean" value]
    (integer? value) ["integer" (str value)]
    :else (throw (ex-info "Unsupported generated cohort value" {:class (str (class value))}))))

(defn generated-cohort
  "Hash the versioned generation recipe, kernel producer and FULL manifest rows.
   Canonical tagged JSON normalizes maps, input paths and resource row order;
   root order remains significant. UTF-8 bytes include a domain prefix and LF.
   This binds claimed provenance to bytes; it grants no authentication or proof."
  [generation kernel-producer resources]
  (let [value {:generation (update generation :inputs #(vec (sort-by :path %)))
               :producer kernel-producer
               :resources (vec (sort-by (juxt :role :resource) resources))}
        canonical (str "ansatz-generated-bundle/2\n" (json/write-str (canonical-data value)) "\n")]
    (str "generated-bundle-sha256:" (sha256 (.getBytes canonical StandardCharsets/UTF_8)))))

(defn- companion-producer [generation role]
  (let [path (get companion-dumpers role)
        input (first (filter #(= path (:path %)) (:inputs generation)))]
    {:lean (:lean generation) :dumper (select-keys input [:path :sha256])}))

(defn- validate-manifest! [manifest]
  (let [resources (:resources manifest)
        generated? (= "ansatz-bundle/2" (:bundle/schema manifest))]
    (when-not (and (if generated?
                     (and (= :generated (:bundle/status manifest))
                          (= :recorded (:bundle/co-generation manifest))
                          (= :kernel-exports-and-companions (:producer/scope manifest)))
                     (and (= "ansatz-bundle/1" (:bundle/schema manifest))
                          (= :legacy-inventory (:bundle/status manifest))
                          (= :unrecorded (:bundle/co-generation manifest))
                          (= :kernel-exports-only (:producer/scope manifest))))
                   (nonempty-string? (:artifact/cohort manifest))
                   (producer? (:producer manifest))
                   (vector? resources) (= 6 (count resources))
                   (= (into kernel-roles metadata-roles) (set (map :role resources)))
                   (= 6 (count (set (map :resource resources)))))
      (throw (ex-info "Invalid bundled artifact manifest" {:schema (:bundle/schema manifest)})))
    (when generated? (validate-generation! (:generation manifest) (:producer manifest)))
    (doseq [{:keys [resource role sha256 producer] :as row} resources]
      (when-not (= (get role-resources role) resource)
        (throw (ex-info "Invalid bundled artifact role/resource mapping"
                        {:role role :resource resource :expected (get role-resources role)})))
      (when-not (and (nonempty-string? resource) (not (re-find #"[\t\r\n]" resource))
                     (string? sha256) (re-matches #"[0-9a-f]{64}" sha256)
                     (if generated?
                       (and (= #{:role :resource :sha256 :provenance/status :producer} (set (keys row)))
                            (= :generated (:provenance/status row))
                            (= producer (if (kernel-roles role) (:producer manifest)
                                            (companion-producer (:generation manifest) role))))
                       (if (kernel-roles role)
                         (and (= :header-recorded (:provenance/status row))
                              (= (:producer manifest) producer))
                         (and (= :unrecorded (:provenance/status row))
                              (not (contains? row :producer))))))
        (throw (ex-info "Invalid bundled artifact resource metadata" {:resource resource :role role}))))
    (let [expected (if generated?
                     (generated-cohort (:generation manifest) (:producer manifest) resources)
                     (inventory-cohort resources))]
      (when-not (= expected (:artifact/cohort manifest))
        (throw (ex-info "Bundled inventory cohort mismatch"
                        {:expected expected :found (:artifact/cohort manifest)}))))
    manifest))

(defn generated-manifest
  "Construct a schema-2 manifest from a pinned generation recipe, exact kernel
   producer and six {:role :resource :sha256} rows. Derive companion provenance
   from actual dumper inputs. Validates metadata only; verify! checks staged bytes
   and companion syntax. Generation and kernel acceptance remain separate gates."
  [generation kernel-producer resources]
  (validate-generation! generation kernel-producer)
  (when-not (and (vector? resources)
                 (every? #(and (map? %) (= #{:role :resource :sha256} (set (keys %)))) resources))
    (throw (ex-info "Generated bundle requires resource identity rows" {})))
  (let [rows (mapv (fn [row]
                     (assoc row :provenance/status :generated
                            :producer (if (kernel-roles (:role row)) kernel-producer
                                          (companion-producer generation (:role row))))) resources)
        manifest {:bundle/schema "ansatz-bundle/2" :bundle/status :generated
                  :bundle/co-generation :recorded :producer/scope :kernel-exports-and-companions
                  :producer kernel-producer :generation generation :resources rows
                  :artifact/cohort (generated-cohort generation kernel-producer rows)}]
    (validate-manifest! manifest)))

(defn- required-subset? [found expected]
  (if (map? expected)
    (and (map? found)
         (every? (fn [[key value]]
                   (and (contains? found key) (required-subset? (get found key) value))) expected))
    (= found expected)))

(defn- check-requirements! [manifest requirements]
  (when-not (map? requirements)
    (throw (ex-info "Bundle requirements must be a map" {})))
  (doseq [[key expected] requirements]
    (when-not (contains? #{:producer :artifact/cohort :bundle/co-generation} key)
      (throw (ex-info "Unknown bundled artifact requirement" {:requirement key})))
    (let [found (get manifest key)]
      (when-not (if (= :producer key) (required-subset? found expected) (= found expected))
        (throw (ex-info "Bundled artifacts do not match requirements"
                        {:requirement key :expected expected :found found})))))
  manifest)

(defn- capture!
  [{:keys [manifest read-resource requirements]
    :or {read-resource classpath-bytes requirements {}}}]
  (let [manifest (validate-manifest!
                  (or manifest
                      (edn/read-string (String. ^bytes (required-bytes read-resource manifest-resource)
                                                StandardCharsets/UTF_8))))]
    (check-requirements! manifest requirements)
    (let [resources
          (into {}
                (map (fn [{:keys [resource role producer] expected-hash :sha256}]
                       (let [payload (aclone ^bytes (required-bytes read-resource resource))
                             found-hash (sha256 payload)]
                         (when-not (= expected-hash found-hash)
                           (throw (ex-info "Bundled resource checksum mismatch"
                                           {:resource resource :expected expected-hash :found found-hash})))
                         (when (kernel-roles role)
                           (let [header (with-open [in (GZIPInputStream. (ByteArrayInputStream. payload))
                                                    reader (io/reader in :encoding "UTF-8")]
                                          (json/read-str (or (.readLine ^java.io.BufferedReader reader) "") :key-fn keyword))]
                             (when-not (= {:meta producer} header)
                               (throw (ex-info "Bundled kernel export header mismatch"
                                               {:resource resource :expected producer :found (:meta header)})))))
                         [resource payload])))
                (:resources manifest))]
      (let [companions (when (= "ansatz-bundle/2" (:bundle/schema manifest))
                         (metadata/validate-resources!
                          (into {} (map (fn [role] [role (get resources (get role-resources role))])) metadata-roles)))]
        {:manifest manifest :resources resources :companions companions}))))

(defn verify!
  "Validate all bundled resource hashes and exact kernel-export header records.
   Schema 2 additionally validates the pinned recipe and strict companion syntax.
   Return manifest metadata only. No proof checking, authentication, extraction,
   or global state changes occur. Call before activation.

   Options: :manifest (map, else read ansatz/bundle.edn), :read-resource (resource
   name -> byte-array or nil; defaults to classpath-bytes), :requirements (map).
   Requirements support exact :artifact/cohort and :bundle/co-generation, plus
   a nested :producer subset. Top-level producer identifies kernel export headers;
   schema-2 companion rows identify their Lean dumper inputs separately. Schema 1
   retains unrecorded metadata history. Neither profile establishes kernel validity
   or complete frontend compatibility."
  ([] (verify! {}))
  ([options] (:manifest (capture! options))))

(def ^:dynamic ^:private *verified-snapshot* nil)

(defn with-verified
  "Capture and verify all resource bytes before (f manifest), scoped dynamically.
   Nested calls reuse the captured snapshot, including its original byte arrays;
   nested :requirements are checked against that manifest. Nested :read-resource
   is ignored; a different explicit :manifest is rejected. Options match verify!.
   Independent top-level calls always capture again; no process-wide cache.
   This scopes resource consistency only and grants no checking authority."
  ([f] (with-verified {} f))
  ([options f]
   (if *verified-snapshot*
     (let [manifest (:manifest *verified-snapshot*)]
       (when (and (contains? options :manifest) (not= (:manifest options) manifest))
         (throw (ex-info "Nested bundled snapshot has a different manifest" {})))
       (check-requirements! manifest (get options :requirements {}))
       (f manifest))
     (binding [*verified-snapshot* (capture! options)]
       (f (:manifest *verified-snapshot*))))))

(defn verified-bytes
  "Return a defensive copy of a declared resource's captured verified bytes.
   Within with-verified, never reopen resources. Outside it, capture/verify the
   current bundle for this call. Unknown resource names are rejected."
  [resource]
  (if *verified-snapshot*
    (if-let [payload (get-in *verified-snapshot* [:resources resource])]
      (aclone ^bytes payload)
      (throw (ex-info "Resource is not declared by bundled inventory" {:resource resource})))
    (with-verified (fn [_] (verified-bytes resource)))))

(defn verified-companion-rows
  "Return immutable strict companion rows from the captured schema-2 snapshot.
   Returns nil for schema 1, whose metadata history has a separate legacy policy."
  [role]
  (when-not (metadata-roles role)
    (throw (ex-info "Unknown bundled companion role" {:role role})))
  (with-verified (fn [_] (get-in *verified-snapshot* [:companions role]))))

(defn consumption-report
  "Report selected schema-2 attribute rows whose native semantics the current
   consumer cannot represent. Structural verify! deliberately permits these
   rows for lossless staging. No metadata installation or proof checking occurs.
   Options match verify!; an active verified snapshot is reused."
  ([] (consumption-report {}))
  ([options]
   (with-verified options
     (fn [manifest]
       (let [unsupported (filterv metadata/unsupported-attribute?
                                  (get-in *verified-snapshot* [:companions :attrs]))]
         {:artifact/cohort (:artifact/cohort manifest)
          :consumable? (empty? unsupported) :unsupported-attrs unsupported})))))

(defn assert-consumable!
  "Reject schema-2 selected unfold-thms, inverse simp, or pre-phase simp rows
   before activation. The complete selected corpus is gated, including rows for
   lazy supplemental preludes. Schema 1 retains its existing consumer policy.
   Returns the verified manifest; options match verify!."
  ([] (assert-consumable! {}))
  ([options]
   (with-verified options
     (fn [manifest]
       (let [report (consumption-report)]
         (when-not (:consumable? report)
           (throw (ex-info "Bundled metadata contains unsupported consumer semantics" report)))
         manifest)))))
