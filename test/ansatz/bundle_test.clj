(ns ansatz.bundle-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.data.json :as json]
            [ansatz.bundle-metadata :as metadata]
            [ansatz.bundle :as bundle]
            [ansatz.attrs :as attrs])
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

(deftest actual-generated-bundle-records-pinned-co-generation
  (let [manifest (bundle/verify!)]
    (is (= :generated (:bundle/status manifest)))
    (is (= :recorded (:bundle/co-generation manifest)))
    (is (= :kernel-exports-and-companions (:producer/scope manifest)))
    (is (= "4.33.1" (get-in manifest [:producer :lean :version])))
    (is (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
           (get-in manifest [:producer :lean :githash])))
    (is (= #{:init :lex :sizeof :attrs :matchers :instances} (set (map :role (:resources manifest)))))
    (is (= bundle/role-resources (into {} (map (juxt :role :resource)) (:resources manifest))))
    (doseq [row (:resources manifest) :when (contains? #{:attrs :matchers :instances} (:role row))]
      (is (= :generated (:provenance/status row)))
      (is (= "4.33.1" (get-in row [:producer :lean :version]))))))

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
  (testing "the shipped bundle matches its recorded Lean producer"
    (is (= :recorded (:bundle/co-generation
                      (bundle/verify! {:requirements {:producer {:lean {:version "4.33.1"}}
                                                      :bundle/co-generation :recorded}}))))))

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

(defn generated-fixture []
  ;; Header-only kernel exports exercise the inventory boundary, not replay or
  ;; kernel validity. Companion payloads exercise the real strict parser.
  (let [lean {:version "4.33.1" :githash "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"}
        producer {:exporter {:name "lean4export" :version "3.1.0"}
                  :format {:version "3.1.0"} :lean lean}
        generation {:profile "ansatz-bundle-generator/1" :lean lean
                    :exporter {:commit (apply str (repeat 40 "a"))
                               :binary-sha256 (apply str (repeat 64 "b"))
                               :source-sha256 (apply str (repeat 64 "c"))
                               :toolchain "leanprover/lean4:v4.33.1"}
                    :inputs (mapv (fn [path] {:path path :sha256 (apply str (repeat 64 "d"))})
                                  ["scripts/dump_attrs.lean" "scripts/dump_matchers.lean"
                                   "scripts/dump_instances.lean" "scripts/generate-bundle.py"])
                    :roots {:init ["Nat.add" "Nat.mul"] :lex ["Prod.lex" "Prod.Lex.right'"]
                            :sizeof ["List._sizeOf_inst"]}
                    :metadata-profile "ansatz-global-companions/1"}
        texts {:attrs (str (json/write-str {:kind "simp" :name "Nat.add_zero" :prio 1000
                                            :post true :inv false}) "\n")
               :matchers (str (json/write-str {:name "fixture.match_1" :numParams 0 :numDiscrs 1
                                               :uElimPos nil :discrs [nil] :overlaps []
                                               :alts [{:numFields 0 :numOverlaps 0 :unitThunk true}]}) "\n")
               :instances "Inhabited\tinstInhabitedNat\t1000\n"}
        resources (into {} (map (fn [[role path]]
                                  [path (gzip (get texts role (str (json/write-str {:meta producer}) "\n")))])
                                bundle/role-resources))
        rows (mapv (fn [[role path]] {:role role :resource path :sha256 (sha256 (get resources path))})
                   bundle/role-resources)
        manifest (bundle/generated-manifest generation producer rows)]
    {:manifest manifest :resources resources :generation generation :producer producer :rows rows}))

(deftest generated-profile-records-dumper-provenance-and-verifies-bytes
  (let [{:keys [manifest resources generation producer]} (generated-fixture)]
    (is (= "ansatz-bundle/2" (:bundle/schema manifest)))
    (is (= :generated (:bundle/status manifest)))
    (is (= :recorded (:bundle/co-generation manifest)))
    (is (= generation (:generation manifest)))
    (is (= manifest (bundle/verify! {:manifest manifest :read-resource resources
                                     :requirements {:producer {:lean (:lean generation)}
                                                    :bundle/co-generation :recorded}})))
    (doseq [row (:resources manifest)]
      (is (= :generated (:provenance/status row)))
      (if (contains? #{:init :lex :sizeof} (:role row))
        (is (= producer (:producer row)))
        (do
          (is (= (:lean generation) (get-in row [:producer :lean])))
          (is (some #{(get-in row [:producer :dumper])} (:inputs generation)))
          (is (not (contains? (:producer row) :exporter))))))))

(deftest generated-cohort-binds-recipe-and-code-with-order-independent-inventories
  (let [{:keys [manifest generation producer]} (generated-fixture)
        rows (:resources manifest)
        cohort (:artifact/cohort manifest)]
    (is (= cohort (bundle/generated-cohort (update generation :inputs #(vec (reverse %)))
                                           (into (sorted-map) producer) (vec (reverse rows)))))
    (doseq [changed [(update-in generation [:roots :init] #(vec (reverse %)))
                     (assoc-in generation [:exporter :binary-sha256] (apply str (repeat 64 "1")))
                     (assoc-in generation [:exporter :source-sha256] (apply str (repeat 64 "2")))
                     (assoc-in generation [:inputs 0 :sha256] (apply str (repeat 64 "3")))]]
      (is (not= cohort (bundle/generated-cohort changed producer rows))))
    (is (not= cohort (bundle/generated-cohort generation producer
                                              (assoc-in rows [0 :sha256] (apply str (repeat 64 "4"))))))
    (is (not= cohort (bundle/generated-cohort generation (assoc-in producer [:format :version] "changed") rows)))))

(deftest generated-recipes-reject-incomplete-or-incompatible-provenance
  (let [{:keys [generation producer rows]} (generated-fixture)]
    (doseq [bad [(assoc-in generation [:lean :version] "4.29.0-rc2")
                 (assoc-in generation [:lean :githash] (apply str (repeat 40 "0")))
                 (assoc-in generation [:exporter :commit] "unrecorded")
                 (assoc-in generation [:exporter :binary-sha256] "bad")
                 (assoc-in generation [:exporter :source-sha256] "bad")
                 (assoc-in generation [:exporter :toolchain] "leanprover/lean4:v4.33.0")
                 (assoc generation :metadata-profile "unknown")
                 (update generation :inputs #(vec (rest %)))
                 (update generation :inputs conj (first (:inputs generation)))
                 (assoc-in generation [:inputs 0 :path] "../scripts/dump_attrs.lean")
                 (assoc-in generation [:inputs 0 :path] "/scripts/dump_attrs.lean")
                 (assoc-in generation [:inputs 0 :path] "scripts\\dump_attrs.lean")
                 (assoc-in generation [:roots :lex] [])
                 (assoc-in generation [:roots :init] ["Nat.add" "Nat.add"])]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"recipe"
                            (bundle/generated-manifest bad producer rows))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (bundle/generated-manifest generation (assoc-in producer [:lean :version] "wrong") rows)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (bundle/generated-manifest generation producer (assoc-in rows [0 :resource] "elsewhere.gz"))))))

(deftest forged-generated-provenance-fails-before-resource-reads
  (let [{:keys [manifest]} (generated-fixture)
        index (first (keep-indexed #(when (= :attrs (:role %2)) %1) (:resources manifest)))]
    (doseq [bad [(assoc-in manifest [:resources index :producer] (:producer manifest))
                 (assoc-in manifest [:resources index :producer :dumper :sha256] (apply str (repeat 64 "0")))
                 (assoc-in manifest [:resources index :producer :dumper :path] "scripts/dump_instances.lean")
                 (assoc-in manifest [:resources index :provenance/status] :unrecorded)]]
      (let [bad (assoc bad :artifact/cohort (bundle/generated-cohort (:generation bad) (:producer bad) (:resources bad)))]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"resource metadata"
                              (bundle/verify! {:manifest bad
                                               :read-resource (fn [_] (throw (AssertionError. "must validate provenance first")))})))))))

(deftest generated-metadata-validation-runs-after-all-artifact-integrity-checks
  (let [{:keys [manifest resources generation producer rows]} (generated-fixture)
        parsed (atom 0)]
    (with-redefs [metadata/validate-resources! (fn [payloads]
                                                 (swap! parsed inc)
                                                 (is (= #{:attrs :matchers :instances} (set (keys payloads)))))]
      (let [missing (get bundle/role-resources :sizeof)]
        (is (thrown? clojure.lang.ExceptionInfo
                     (bundle/verify! {:manifest manifest :read-resource (dissoc resources missing)})))
        (is (zero? @parsed)))
      (bundle/verify! {:manifest manifest :read-resource resources})
      (is (= 1 @parsed)))
    (testing "valid hashes cannot disguise malformed companion syntax"
      (let [path (get bundle/role-resources :instances)
            payload (gzip "Inhabited\tinstInhabitedNat\tnot-a-priority\n")
            rows (mapv #(if (= :instances (:role %)) (assoc % :sha256 (sha256 payload)) %) rows)
            manifest (bundle/generated-manifest generation producer rows)]
        (is (thrown? clojure.lang.ExceptionInfo
                     (bundle/verify! {:manifest manifest :read-resource (assoc resources path payload)})))))))

(deftest generated-cohort-and-recipe-are-preflight-gates
  (let [{:keys [manifest generation producer rows]} (generated-fixture)]
    (doseq [bad [(assoc manifest :artifact/cohort "generated-bundle-sha256:tampered")
                 (assoc-in manifest [:generation :roots :init] ["Nat.sub"])
                 (assoc-in manifest [:generation :exporter :binary-sha256]
                           (apply str (repeat 64 "0")))]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cohort mismatch"
                            (bundle/verify! {:manifest bad
                                             :read-resource (fn [_] (throw (AssertionError. "must validate cohort first")))}))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"identity rows"
                          (bundle/generated-manifest generation producer
                                                     (assoc-in rows [0 :producer] producer)))))
  (testing "schema 1 keeps its separate legacy metadata policy"
    (let [{:keys [manifest resources]} (fixture)]
      (with-redefs [metadata/validate-resources! (fn [_] (throw (AssertionError. "legacy metadata must not use generated profile")))]
        (is (= manifest (bundle/verify! {:manifest manifest :read-resource resources})))))))

(defn generated-fixture-with-attrs [attr-rows]
  (let [{:keys [generation producer rows resources]} (generated-fixture)
        path (:attrs bundle/role-resources)
        payload (gzip (apply str (map #(str (json/write-str %) "\n") attr-rows)))
        rows (mapv #(if (= :attrs (:role %)) (assoc % :sha256 (sha256 payload)) %) rows)]
    {:manifest (bundle/generated-manifest generation producer rows)
     :resources (assoc resources path payload)}))

(deftest generated-unsupported-metadata-is-staged-but-not-consumed
  (doseq [row [{:kind "simp" :name "Fixture.inv" :prio 1000 :post true :inv true}
               {:kind "simp" :name "Fixture.pre" :prio 1000 :post false :inv false}]]
    (let [{:keys [manifest resources]} (generated-fixture-with-attrs [row])
          options {:manifest manifest :read-resource resources}]
      (is (= manifest (bundle/verify! options)))
      (is (= [row] (:unsupported-attrs (bundle/consumption-report options))))
      (is (false? (:consumable? (bundle/consumption-report options))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unsupported consumer semantics"
                            (bundle/assert-consumable! options)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unsupported consumer semantics"
                            (bundle/with-verified options (fn [_] (attrs/bundled-attrs))))))))

(deftest generated-supported-attributes-use-json-decoded-names
  (let [n "Fixture.\"quoted\\λ"
        target "Fixture.\\target\""
        rows [{:kind "simp" :name n :prio 47 :post true :inv false}
              {:kind "csimp" :name "Fixture.f" :target target}
              {:kind "unfold" :name "Fixture.g"}
              {:kind "unfold-thms" :name "Fixture.h" :theorems ["Fixture.h.eq_1"]}]
        {:keys [manifest resources]} (generated-fixture-with-attrs rows)
        options {:manifest manifest :read-resource resources}]
    (is (= manifest (bundle/assert-consumable! options)))
    (is (true? (:consumable? (bundle/consumption-report options))))
    (bundle/with-verified options
      (fn [_]
        (is (= rows (bundle/verified-companion-rows :attrs)))
        (is (= [["simp" n nil 47] ["csimp" "Fixture.f" target nil]
                ["unfold" "Fixture.g" nil nil]
                ["unfold-thms" "Fixture.h" ["Fixture.h.eq_1"] nil]]
               (attrs/bundled-attrs)))))))
