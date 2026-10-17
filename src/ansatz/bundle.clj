(ns ansatz.bundle
  "Integrity and compatibility checks for bundled resources. The legacy inventory
   records kernel export headers; metadata provenance and common generation are
   unrecorded. Returned metadata grants no checking authority or authentication."
  (:require [clojure.data.json :as json]
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

(defn- validate-manifest! [manifest]
  (let [resources (:resources manifest)]
    (when-not (and (= "ansatz-bundle/1" (:bundle/schema manifest))
                   (= :legacy-inventory (:bundle/status manifest))
                   (= :unrecorded (:bundle/co-generation manifest))
                   (= :kernel-exports-only (:producer/scope manifest))
                   (nonempty-string? (:artifact/cohort manifest))
                   (producer? (:producer manifest))
                   (vector? resources) (= 6 (count resources))
                   (= (into kernel-roles metadata-roles) (set (map :role resources)))
                   (= 6 (count (set (map :resource resources)))))
      (throw (ex-info "Invalid bundled artifact manifest" {:schema (:bundle/schema manifest)})))
    (doseq [{:keys [resource role sha256 producer] :as row} resources]
      (when-not (= (get role-resources role) resource)
        (throw (ex-info "Invalid bundled artifact role/resource mapping"
                        {:role role :resource resource :expected (get role-resources role)})))
      (when-not (and (nonempty-string? resource) (not (re-find #"[\t\r\n]" resource))
                     (string? sha256) (re-matches #"[0-9a-f]{64}" sha256)
                     (if (kernel-roles role)
                       (and (= :header-recorded (:provenance/status row))
                            (= (:producer manifest) producer))
                       (and (= :unrecorded (:provenance/status row))
                            (not (contains? row :producer)))))
        (throw (ex-info "Invalid bundled artifact resource metadata" {:resource resource :role role}))))
    (let [expected (inventory-cohort resources)]
      (when-not (= expected (:artifact/cohort manifest))
        (throw (ex-info "Bundled inventory cohort mismatch"
                        {:expected expected :found (:artifact/cohort manifest)}))))
    manifest))

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
    {:manifest manifest
     :resources
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
           (:resources manifest))}))

(defn verify!
  "Validate all bundled resource hashes and exact kernel-export header records.
   Return manifest metadata only. No proof checking, authentication, extraction,
   or global state changes occur. Call before activation.

   Options: :manifest (map, else read ansatz/bundle.edn), :read-resource (resource
   name -> byte-array or nil; defaults to classpath-bytes), :requirements (map).
   Requirements support exact :artifact/cohort and :bundle/co-generation, plus
   a nested :producer subset. Producer requirements apply ONLY to kernel export
   headers; metadata producer history is unrecorded, so this legacy inventory
   cannot establish frontend compatibility or a co-generated release."
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
