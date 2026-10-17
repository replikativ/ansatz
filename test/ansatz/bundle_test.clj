(ns ansatz.bundle-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.data.json :as json]
            [ansatz.bundle :as bundle])
  (:import [java.io ByteArrayOutputStream]
           [java.nio.charset StandardCharsets]
           [java.security MessageDigest]
           [java.util.zip GZIPOutputStream]))

(defn- sha256 [^bytes payload]
  (apply str (map #(format "%02x" (bit-and 255 %))
                  (.digest (MessageDigest/getInstance "SHA-256") payload))))

(defn- gzip [text]
  (let [out (ByteArrayOutputStream.)]
    (with-open [gzip (GZIPOutputStream. out)]
      (.write gzip (.getBytes ^String text StandardCharsets/UTF_8)))
    (.toByteArray out)))

(defn- fixture []
  (let [producer {:exporter {:name "lean4export" :version "3.1.0"}
                  :format {:version "3.1.0"}
                  :lean {:githash "legacy-kernel-commit" :version "4.29.0-rc2"}}
        roles [:init :lex :sizeof :attrs :matchers :instances]
        resources (into {} (map (fn [role]
                                  [(get bundle/role-resources role)
                                   (gzip (if (contains? #{:init :lex :sizeof} role)
                                           (str (json/write-str {:meta producer}) "\n")
                                           "legacy metadata\n"))]) roles))
        rows (mapv (fn [role]
                     (let [resource (get bundle/role-resources role)
                           kernel? (contains? #{:init :lex :sizeof} role)]
                       (cond-> {:resource resource :role role :sha256 (sha256 (get resources resource))
                                :provenance/status (if kernel? :header-recorded :unrecorded)}
                         kernel? (assoc :producer producer)))) roles)
        manifest {:bundle/schema "ansatz-bundle/1" :bundle/status :legacy-inventory
                  :bundle/co-generation :unrecorded :artifact/cohort (bundle/inventory-cohort rows)
                  :producer/scope :kernel-exports-only :producer producer :resources rows}]
    {:manifest manifest :resources resources}))

(deftest actual-legacy-inventory-is-readable-without-claiming-co-generation
  (let [manifest (bundle/verify!)]
    (is (= :legacy-inventory (:bundle/status manifest)))
    (is (= :unrecorded (:bundle/co-generation manifest)))
    (is (= :kernel-exports-only (:producer/scope manifest)))
    (is (= "4.29.0-rc2" (get-in manifest [:producer :lean :version])))
    (is (= "83e54b65b65d1d3ce31d99d820a7bd5f3e219295"
           (get-in manifest [:producer :lean :githash])))
    (is (= #{:init :lex :sizeof :attrs :matchers :instances} (set (map :role (:resources manifest)))))
    (is (= bundle/role-resources (into {} (map (juxt :role :resource)) (:resources manifest))))
    (doseq [row (:resources manifest) :when (contains? #{:attrs :matchers :instances} (:role row))]
      (is (= :unrecorded (:provenance/status row)))
      (is (not (contains? row :producer))))))

(deftest requirements-distinguish-legacy-producer-from-frontend-release
  (let [{:keys [manifest resources]} (fixture)
        options {:manifest manifest :read-resource resources}]
    (is (= manifest (bundle/verify! (assoc options :requirements
                                           {:producer {:lean {:version "4.29.0-rc2"}}
                                            :artifact/cohort (:artifact/cohort manifest)}))))
    (doseq [requirements [{:producer {:lean {:version "4.33.1"}}}
                          {:producer {:lean {:githash "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"}}}
                          {:artifact/cohort "frontend-release"}
                          {:bundle/co-generation :recorded}]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"do not match requirements"
                            (bundle/verify! (assoc options :requirements requirements)))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unknown bundled artifact requirement"
                          (bundle/verify! (assoc options :requirements {:verified true})))))
  (testing "the actual bundled inventory does not match the hosted frontend producer"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"do not match requirements"
                          (bundle/verify! {:requirements {:producer {:lean {:version "4.33.1"}}}})))))

(deftest checksum-and-missing-resource-fail-before-caller-activation
  (let [{:keys [manifest resources]} (fixture)
        resource (get-in manifest [:resources 0 :resource])
        corrupted (aclone ^bytes (get resources resource))
        last-index (dec (alength corrupted))]
    (aset-byte corrupted last-index (unchecked-byte (bit-xor 1 (aget corrupted last-index))))
    (doseq [[reader message] [[(dissoc resources resource) #"missing or is not bytes"]
                              [(assoc resources resource corrupted) #"checksum mismatch"]]]
      (let [activated? (atom false)]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo message
                              (do (bundle/verify! {:manifest manifest :read-resource reader})
                                  (reset! activated? true))))
        (is (false? @activated?))))))

(deftest header-is-checked-independently-of-the-compressed-hash
  (let [{:keys [manifest resources]} (fixture)
        resource (get-in manifest [:resources 0 :resource])
        wrong-producer (assoc-in (:producer manifest) [:lean :version] "4.33.1")
        payload (gzip (str (json/write-str {:meta wrong-producer}) "\n"))
        manifest (assoc-in manifest [:resources 0 :sha256] (sha256 payload))
        manifest (assoc manifest :artifact/cohort (bundle/inventory-cohort (:resources manifest)))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"header mismatch"
                          (bundle/verify! {:manifest manifest :read-resource (assoc resources resource payload)})))))

(deftest invalid-manifest-fails-before-reading-artifacts
  (let [{:keys [manifest]} (fixture)]
    (doseq [bad [(assoc manifest :bundle/schema "unknown")
                 (assoc manifest :bundle/co-generation :recorded)
                 (assoc manifest :producer/scope :all-resources)
                 (assoc-in manifest [:resources 0 :sha256] "not-sha256")
                 (assoc-in manifest [:resources 1 :resource] (get-in manifest [:resources 0 :resource]))
                 (assoc-in manifest [:resources 0 :resource] "test/tab\tresource.gz")
                 (assoc-in manifest [:resources 3 :producer] (:producer manifest))
                 (update manifest :resources pop)]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid bundled artifact"
                            (bundle/verify! {:manifest bad
                                             :read-resource (fn [_] (throw (AssertionError. "must validate first")))}))))))

(deftest self-consistent-alternate-paths-and-swapped-roles-fail-before-artifact-reads
  (let [{:keys [manifest]} (fixture)
        alternate (update manifest :resources
                          (fn [rows] (mapv #(update % :resource (fn [path] (str "alternate/" path))) rows)))
        swapped (-> manifest
                    (assoc-in [:resources 0 :role] :lex)
                    (assoc-in [:resources 1 :role] :init))]
    (doseq [candidate [alternate swapped]]
      ;; Recompute the cohort: internal hash consistency does not authorize
      ;; paths or role assignments different from the consumer contract.
      (let [candidate (assoc candidate :artifact/cohort (bundle/inventory-cohort (:resources candidate)))
            reads (atom [])]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"role/resource mapping"
                              (bundle/verify! {:manifest candidate
                                               :read-resource (fn [resource]
                                                                (swap! reads conj resource)
                                                                (throw (AssertionError. "must reject before reading artifacts")))})))
        (is (empty? @reads))))))

(deftest injectable-reader-can-supply-the-manifest-and-all-payloads
  (let [{:keys [manifest resources]} (fixture)
        resources (assoc resources bundle/manifest-resource
                         (.getBytes (pr-str manifest) StandardCharsets/UTF_8))
        reads (atom [])]
    (is (= manifest (bundle/verify! {:read-resource (fn [resource]
                                                      (swap! reads conj resource)
                                                      (get resources resource))})))
    (is (= 7 (count @reads)))
    (is (= bundle/manifest-resource (first @reads)))
    (is (= (set (map :resource (:resources manifest))) (set (rest @reads))))))

(deftest inventory-cohort-is-order-independent-and-bound-to-content-identities
  (testing "canonical UTF-8/LF/tab recipe has a language-independent reference digest"
    (is (= "legacy-inventory-sha256:967cf123221d522566b278326ce21d0e23e4526d65644553e82192f35e8c0310"
           (bundle/inventory-cohort [{:role :init :resource "test/z.gz" :sha256 (apply str (repeat 64 "1"))}
                                     {:role :attrs :resource "test/a.gz" :sha256 (apply str (repeat 64 "0"))}]))))
  (let [{:keys [manifest resources]} (fixture)
        rows (:resources manifest)
        changed (assoc-in manifest [:resources 0 :sha256] (apply str (repeat 64 "0")))]
    (is (= (:artifact/cohort manifest) (bundle/inventory-cohort (reverse rows))))
    (is (= manifest (bundle/verify! {:manifest manifest :read-resource resources})))
    (is (not= (:artifact/cohort manifest) (bundle/inventory-cohort (:resources changed))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"inventory cohort mismatch"
                          (bundle/verify! {:manifest changed
                                           :read-resource (fn [_] (throw (AssertionError. "must validate cohort first")))})))
    (let [changed (assoc changed :artifact/cohort (bundle/inventory-cohort (:resources changed)))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"do not match requirements"
                            (bundle/verify! {:manifest changed :read-resource resources
                                             :requirements {:artifact/cohort (:artifact/cohort manifest)}}))))))

(deftest scoped-verified-bytes-reuse-one-complete-snapshot
  (let [{:keys [manifest resources]} (fixture)
        manifest-bytes (.getBytes (pr-str manifest) StandardCharsets/UTF_8)
        underlying (atom (assoc resources bundle/manifest-resource manifest-bytes))
        reads (atom [])
        reader (fn [resource] (swap! reads conj resource) (get @underlying resource))
        resource (get-in manifest [:resources 0 :resource])]
    (bundle/with-verified {:read-resource reader}
      (fn [actual]
        (is (= manifest actual))
        (is (= 7 (count @reads)) "all resources verified before entering callback")
        (reset! underlying {})
        (is (= (seq (get resources resource)) (seq (bundle/verified-bytes resource))))
        (bundle/with-verified
          {:read-resource (fn [_] (throw (AssertionError. "nested scope must not reopen")))
           :requirements {:artifact/cohort (:artifact/cohort manifest)}}
          (fn [nested]
            (is (= actual nested))
            (is (= (seq (get resources resource)) (seq (bundle/verified-bytes resource))))))
        (is (= 7 (count @reads)))))
    (testing "an independent top-level call captures again instead of using stale cache"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"missing or is not bytes"
                            (bundle/with-verified {:read-resource reader}
                              (fn [_] (throw (AssertionError. "must not activate")))))))
    (is (= 8 (count @reads)))))

(deftest scoped-capture-is-protected-from-byte-array-mutation
  (let [{:keys [manifest resources]} (fixture)
        resource (get-in manifest [:resources 0 :resource])
        source ^bytes (get resources resource)
        original-first-byte (aget source 0)]
    (bundle/with-verified {:manifest manifest :read-resource resources}
      (fn [_]
        ;; A caller-supplied reader can retain aliases to its own arrays.
        (aset-byte source 0 (unchecked-byte (bit-xor 1 original-first-byte)))
        (let [returned ^bytes (bundle/verified-bytes resource)]
          (is (= original-first-byte (aget returned 0)))
          (aset-byte returned 0 (unchecked-byte (bit-xor 1 original-first-byte))))
        (is (= original-first-byte (aget ^bytes (bundle/verified-bytes resource) 0)))))))

(deftest verified-scope-fails-before-callback-and-rejects-undeclared-resources
  (let [{:keys [manifest resources]} (fixture)
        resource (get-in manifest [:resources 0 :resource])
        activated? (atom false)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"missing or is not bytes"
                          (bundle/with-verified {:manifest manifest :read-resource (dissoc resources resource)}
                            (fn [_] (reset! activated? true)))))
    (is (false? @activated?))
    (bundle/with-verified {:manifest manifest :read-resource resources}
      (fn [_]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not declared"
                              (bundle/verified-bytes "outside/inventory.gz")))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"do not match requirements"
                              (bundle/with-verified {:requirements {:producer {:lean {:version "4.33.1"}}}}
                                (fn [_] (throw (AssertionError. "must reject requirements"))))))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"different manifest"
                              (bundle/with-verified {:manifest (assoc manifest :artifact/cohort "other")}
                                (fn [_] (throw (AssertionError. "must reject replacement"))))))))))
