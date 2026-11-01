(ns prototype.restore-consumer-test
  "Bounded compatibility authentication tests. Inventory hashes in the pure shape
   tests are explicit models; selected-class checks use genuine current Java
   bytes. These tests do not claim a full archived frontend/checkpoint restore."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.java.io :as io]
            [clojure.edn :as edn]
            [prototype.checkpoint-wire :as wire]
            [prototype.globals-consumer-profile :as profile]
            [prototype.globals-consumer-factory :as factory]
            [prototype.restore-consumer :as restore]
            [prototype.machine :as m]
            [clojure.data.json :as json])
  (:import [java.io ByteArrayOutputStream DataOutputStream ByteArrayInputStream DataInputStream Closeable]))

(def recipe-source (slurp (io/resource "fixtures/producer50f-catalogue-recipe.edn")))
(def recipe (edn/read-string recipe-source))
(def producer
  {:factory-id factory/shared-linear-factory-id
   :implementation-sha256 profile/producer-implementation-sha256
   :catalogue-recipe recipe :kernel-policy factory/kernel-policy
   :trusted-roots (vec (concat factory/assembly-roots [factory/shared-linear-target factory/exporter]))})
(def model-hash (apply str (repeat 64 "a")))
(def inventory
  (vec (concat
        (for [row (:build-inventory recipe)
              :when (not (contains? profile/excluded-producer-sources (:id row)))]
          (if-let [sha (get (assoc profile/program-substitutions "prototype/mutable.clj" profile/mutable-sha256)
                            (:id row))]
            (assoc row :sha256 sha) row))
        (for [[id kind] (sort-by key profile/added-inputs)]
          {:id id :kind kind :sha256 (if (= id "src-java/ansatz/runtime/GlobalsOverlay.java")
                                       profile/globals-source-sha256 model-hash)}))))
(defn changed [rows id f] (mapv #(if (= id (:id %)) (f %) %) rows))
(defn valid! [rows] (profile/validate-inventory! recipe rows (profile/consumer-identity rows)))

(deftest exact-producer-provenance-remains-distinct
  (is (= recipe (profile/producer-recipe! producer recipe-source)))
  (is (not= profile/producer-implementation-sha256 (profile/consumer-identity inventory)))
  (doseq [source [(str recipe-source "\n") "{}" nil]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"producer recipe bytes"
                          (profile/producer-recipe! producer source))))
  (doseq [p [(assoc producer :implementation-sha256 model-hash)
             (assoc producer :factory-id factory/factory-id)
             (update producer :catalogue-recipe assoc :schema "invented")]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Producer preparation identity"
                          (profile/producer-recipe! p recipe-source)))))

(deftest complete-closed-consumer-shape
  (is (identical? inventory (valid! inventory)))
  (is (= (profile/consumer-identity inventory) (profile/consumer-identity (vec (reverse inventory)))))
  (is (not-any? #(contains? profile/excluded-producer-sources (:id %)) inventory))
  (doseq [id ["ansatz/runtime/GlobalsOverlay$Hint.class"
              "ansatz/runtime/HeapOverlay$1$1.class"
              "prototype/TypedLongMemo.class"
              "prototype/resident_import.clj" "prototype/restore_consumer.clj"]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected-input inventory drift"
                          (valid! (vec (remove #(= id (:id %)) inventory))))))
  (doseq [row [{:id "unreviewed/extra.clj" :kind :host-source :sha256 model-hash}
               {:id "prototype/full_init_checkpoint_factory.clj" :kind :host-source :sha256 model-hash}]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected-input inventory drift"
                          (valid! (conj inventory row)))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"role drift"
                        (valid! (changed inventory "ansatz/runtime/GlobalsOverlay$Hint.class" #(assoc % :kind :host-source)))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid consumer inventory"
                        (valid! (conj inventory (first inventory))))))

(deftest no-unlisted-source-or-build-substitutions
  (doseq [id ["prototype/raw_interop.clj" "prototype/machine.cljc"
              "prototype/checkpoint_wire.clj" "ansatz/kernel/TypeChecker.class"]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved consumer substitution"
                          (valid! (changed inventory id #(assoc % :sha256 model-hash))))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"mutable consumer"
                        (valid! (changed inventory "prototype/mutable.clj" #(assoc % :sha256 model-hash)))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"globals overlay source"
                        (valid! (changed inventory "src-java/ansatz/runtime/GlobalsOverlay.java" #(assoc % :sha256 model-hash)))))
  (doseq [id (keys profile/program-substitutions)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"program sizing implementation"
                          (valid! (changed inventory id #(assoc % :sha256 model-hash))))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"digest mismatch"
                        (profile/validate-inventory! recipe inventory profile/producer-implementation-sha256))))

(deftest real-selected-class-and-resource-verification
  (doseq [id ["ansatz/runtime/GlobalsOverlay.class" "ansatz/runtime/GlobalsOverlay$Hint.class"
              "ansatz/runtime/HeapOverlay.class" "ansatz/runtime/HeapOverlay$1.class"
              "ansatz/runtime/HeapOverlay$1$1.class" "prototype/TypedLongMemo.class"]]
    (let [url (io/resource id)
          sha (with-open [input (io/input-stream url)] (wire/sha256 (.readAllBytes input)))
          row {:id id :kind :runtime-class :sha256 sha}]
      (is (= :selected-class (profile/input-role row)))
      (is (true? (profile/authenticate-input! row (fn [_] (throw (AssertionError. "Class must not use source resolver"))))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Selected consumer class drift"
                            (profile/authenticate-input! (assoc row :sha256 model-hash) identity)))))
  (let [id "prototype/mutable.clj" row {:id id :kind :host-source :sha256 profile/runtime-ops-mutable-sha256}]
    (is (true? (profile/authenticate-input! row identity)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Selected consumer resource drift"
                          (profile/authenticate-input! (assoc row :sha256 model-hash) identity))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"resource unavailable"
                        (profile/authenticate-input! {:id "unavailable/source.clj" :kind :host-source :sha256 model-hash} identity))))

(deftest provenance-scripts-are-pinned-files-without-classpath-expansion
  (is (= 5 (count profile/provenance-scripts)))
  (doseq [id profile/provenance-scripts]
    (let [path (io/file "../.." id)
          row {:id id :kind :host-source :sha256 (wire/file-sha256 path)}
          resolve-source (fn [requested] (is (= id requested)) path)]
      (is (nil? (io/resource id)))
      (is (= :provenance-source (profile/input-role row)))
      (is (true? (profile/authenticate-input! row resolve-source)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"provenance script drift"
                            (profile/authenticate-input! (assoc row :sha256 model-hash) resolve-source)))))
  (is (= :selected-resource
         (profile/input-role {:id "experiments/lean-ir/scripts/unapproved.clj" :kind :host-source}))))

(deftest arbitrary-or-forged-factories-are-not-capabilities
  (doseq [value [(fn [_] {}) {} nil
                 (prototype.globals_consumer_factory.Factory.)]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"authenticated closed globals consumer factory"
                          (factory/descriptor value)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"authenticated closed globals consumer factory"
                          (factory/invoke! value {})))))

(deftest policy-roots-and-unknown-options-are-not-upgrades
  (doseq [[p pattern] [[(assoc producer :kernel-policy {}) #"kernel policy"]
                       [(update producer :trusted-roots pop) #"helper roots"]
                       [(assoc producer :factory-id factory/factory-id) #"producer profile"]]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo pattern
                          (factory/make-factory {:producer-preparation p})))))

(deftest mandatory-independent-consumer-attestation
  (let [opts {:producer-preparation producer :producer-recipe-source recipe-source
              :producer-resolve-artifact identity :store-root "unused-model-store"
              :consumer-inventory inventory
              :expected-consumer-implementation-sha256 (profile/consumer-identity inventory)
              :loaded-consumer-implementation-sha256 profile/producer-implementation-sha256
              :consumer-resolve-source identity}]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"fresh loaded-consumer attestation"
                          (profile/authenticate! opts))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"factory options"
                        (profile/authenticate! {:unexpected true}))))

;; Explicit read-only white-box calls to preserved validation/cleanup boundaries.
;; No Var is redefined and no authenticated factory capability is fabricated.
(defn private-call [name & args]
  (apply @(ns-resolve 'prototype.restore-consumer name) args))
(def zero-counts {:functions 0 :heap 0 :globals 0 :imported-declarations 0})
(defn stream-rows [counts]
  [[:header {:format restore/format-id :counts counts :authority-present? false :authority-keys #{}}]
   [:authority {}] [:state {}] [:end counts]])
(defn parse-rows [rows counts]
  (let [bytes (ByteArrayOutputStream.)]
    (with-open [output (DataOutputStream. bytes)]
      (doseq [row rows] (wire/write-frame! output row)))
    (with-open [input (DataInputStream. (ByteArrayInputStream. (.toByteArray bytes)))]
      (private-call 'parse-data input counts))))

(deftest preserved-parser-negative-boundaries
  ;; A syntactically empty stream can parse, but is not a valid world/factory
  ;; restore and receives no source/kernel authority.
  (is (= {} (get-in (parse-rows (stream-rows zero-counts) zero-counts) [:world :functions])))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Stream header mismatch"
                        (parse-rows (assoc-in (stream-rows zero-counts) [0 1 :format] "invented") zero-counts)))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"trailer mismatch"
                        (parse-rows (assoc-in (stream-rows zero-counts) [3 1 :heap] 1) zero-counts)))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Trailing checkpoint data"
                        (parse-rows (conj (stream-rows zero-counts) [:end zero-counts]) zero-counts)))
  (let [counts (assoc zero-counts :functions 2)
        f {:params [] :body [:return [:imm 42]]}
        name ["str" ["anonymous"] "model"]
        rows (into [(first (stream-rows counts)) [:function name #{:prepared} f]
                    [:function name #{:prepared} f]] (rest (stream-rows counts)))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Duplicate/unauthorized function"
                          (parse-rows rows counts))))
  (let [counts (assoc zero-counts :functions 1)
        rows (into [(first (stream-rows counts))
                    [:function ["anonymous"] #{:imported} {:params [] :body [:return [:imm 42]]}]]
                   (rest (stream-rows counts)))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Undeclared function authority"
                          (parse-rows rows counts)))))

(deftest producer-consumer-and-binding-envelopes-are-independent
  (let [consumer (profile/consumer-identity inventory)
        signature {:params [] :return-type "object"}
        result {:producer-preparation producer :consumer-implementation-sha256 consumer
                :compatibility-profile profile/profile-id :catalogue {}
                :bindings {"model" {:signature signature :handler identity}}}
        manifest {:binding-signatures {"model" signature}}]
    (is (identical? result (private-call 'factory-result! result producer consumer profile/profile-id manifest)))
    (doseq [changed [(assoc result :producer-preparation (assoc producer :implementation-sha256 model-hash))
                     (assoc result :consumer-implementation-sha256 profile/producer-implementation-sha256)
                     (assoc result :compatibility-profile "unreviewed")
                     (assoc-in result [:bindings "model" :signature :return-type] "uint32")
                     (update result :bindings dissoc "model")]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"identity/signature mismatch"
                            (private-call 'factory-result! changed producer consumer profile/profile-id manifest))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid consumer factory result"
                          (private-call 'factory-result! (assoc result :implementation-sha256 profile/producer-implementation-sha256)
                                        producer consumer profile/profile-id manifest)))))

(deftest preserved-executable-authority-is-identity-sensitive
  (let [name ["str" ["anonymous"] "model"]
        f {:params [] :body [:return [:imm 42]]}
        other (into {} f) ; distinct object, equal body
        world {:functions {name f}}]
    (is (true? (private-call 'authorization! world {name f} {} {} [name])))
    (is (not (identical? f other)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Prepared executable identity drift"
                          (private-call 'authorization! world {name other} {} {} [name])))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unclassified executable authority"
                          (private-call 'authorization! world {} {} {} [])))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Counterfeit imported row"
                          (private-call 'authorization!
                                        (assoc world :eval-const-authorizations
                                               {:imported-declarations {name {:name name :ir {}}}})
                                        {name f} {:declarations {}} {} [name])))))

(def resource-descriptor "fixtures/module-data-canary.verified.json")
(def resource-sha "13a03fd9dd2346a535f7c064e1c0f4c5ed514a5a58b1625c8fbdefeb11e24a67")
(defn resource-recipe []
  (let [d (json/read-str (slurp resource-descriptor) :key-fn keyword)]
    {:id "canary" :descriptor-sha256 resource-sha :source-sha256 (:sourceSha256 d)
     :index-sha256 (:indexSha256 d) :source-bytes (:sourceBytes d) :index-bytes (:indexBytes d)
     :base 41 :size (:nodes d)}))
(defn resource-locations [_]
  {:descriptor-path resource-descriptor :source-path "fixtures/module-data-canary.jsonl"})

(deftest genuine-store-reopening-and-private-index-cursor
  (let [recipe (resource-recipe)
        source (private-call 'reopen! recipe resource-locations)]
    (try
      (is (= 41 (:base source)))
      (is (false? @(:closed source)))
      (let [index ^java.io.RandomAccessFile (:index source)]
        (.seek index 7)
        (is (= (:index-sha256 recipe) (private-call 'private-index-sha256 index)))
        (is (= 7 (.getFilePointer index))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Resource descriptor recipe drift"
                            (private-call 'reopen! (assoc recipe :source-sha256 model-hash) resource-locations)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"descriptor hash mismatch"
                            (private-call 'reopen! (assoc recipe :descriptor-sha256 model-hash) resource-locations)))
      (finally (.close ^Closeable source)))
    (is (true? @(:closed source)))))

(deftest resource-lease-closes-all-on-failure-exactly-once
  (let [source (private-call 'reopen! (resource-recipe) resource-locations)
        calls (atom []) first-error (ex-info "first cleanup" {}) second-error (ex-info "second cleanup" {})
        failing (fn [k error] (reify Closeable (close [_] (swap! calls conj k) (throw error))))
        owned (atom [(failing :first first-error) source (failing :second second-error)])
        lease (prototype.restore_consumer.ResourceLease. owned)
        failure (try (.close ^Closeable lease) nil (catch Throwable error error))]
    (is (identical? first-error failure))
    (is (= [:first :second] @calls))
    (is (= [second-error] (vec (.getSuppressed ^Throwable failure))))
    (is (true? @(:closed source)))
    (is (nil? @owned))
    (.close ^Closeable lease)
    (is (= [:first :second] @calls))))

(def reconstruction-baseline-ids
  ["prototype/imported_kernel.clj" "prototype/kernel_bridge.clj" "prototype/test_runner.clj"])
(def reconstruction-inventory
  (conj (reduce (fn [rows id] (changed rows id #(assoc % :sha256 model-hash)))
                inventory reconstruction-baseline-ids)
        {:id "prototype/resident_init_prefix.clj" :kind :host-source :sha256 model-hash}))
(defn reconstruction-valid! [rows]
  (profile/validate-reconstruction-inventory! recipe rows (profile/consumer-identity rows)))

(deftest reconstruction-is-a-distinct-closed-inventory
  (is (= 255 (count inventory)))
  (is (= 256 (count reconstruction-inventory)))
  (is (not= profile/profile-id profile/reconstruction-profile-id))
  (is (identical? reconstruction-inventory (reconstruction-valid! reconstruction-inventory)))
  ;; The old API keeps its original ID set and baseline hash contract.
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected-input inventory drift"
                        (valid! reconstruction-inventory)))
  (doseq [id reconstruction-baseline-ids]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved consumer substitution"
                          (valid! (changed inventory id #(assoc % :sha256 model-hash))))))
  ;; The new contract never relaxes unrelated baseline or pinned substitutions.
  (doseq [id ["prototype/raw_interop.clj" "prototype/machine.cljc"
              "prototype/checkpoint_wire.clj" "ansatz/kernel/TypeChecker.class"]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved consumer substitution"
                          (reconstruction-valid! (changed reconstruction-inventory id #(assoc % :sha256 model-hash))))))
  (doseq [id (map :id reconstruction-inventory)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected-input inventory drift"
                          (reconstruction-valid! (vec (remove #(= id (:id %)) reconstruction-inventory))))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected-input inventory drift"
                        (reconstruction-valid! (conj reconstruction-inventory
                                                     {:id "unreviewed/extra.clj" :kind :host-source :sha256 model-hash}))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"role drift"
                        (reconstruction-valid! (changed reconstruction-inventory "prototype/resident_init_prefix.clj"
                                                        #(assoc % :kind :host-resource)))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"digest mismatch"
                        (profile/validate-reconstruction-inventory!
                         recipe reconstruction-inventory (profile/consumer-identity inventory)))))

(deftest closed-authentication-rejects-before-resource-acquisition
  (let [calls (atom [])
        resolver (fn [id] (swap! calls conj id) (throw (AssertionError. "Must reject before resource lookup")))
        options (fn [rows]
                  {:producer-preparation producer :producer-recipe-source recipe-source
                   :producer-resolve-artifact resolver :store-root "unused-model-store"
                   :consumer-inventory rows
                   :expected-consumer-implementation-sha256 (profile/consumer-identity rows)
                   :loaded-consumer-implementation-sha256 (profile/consumer-identity rows)
                   :consumer-resolve-source resolver})]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected-input inventory drift"
                          (profile/authenticate! (options reconstruction-inventory))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved consumer substitution"
                          (profile/authenticate-reconstruction!
                           (options (changed reconstruction-inventory "prototype/machine.cljc"
                                             #(assoc % :sha256 model-hash))))))
    (doseq [authenticate [profile/authenticate! profile/authenticate-reconstruction! profile/authenticate-runtime-ops-reconstruction!
                          profile/authenticate-heap-net-dirty-reconstruction! profile/authenticate-source-graph-reconstruction!]
            extra [{:compatibility-profile "invented"} {:substitutions #{"anything"}} {:authenticator identity}]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"factory options"
                            (authenticate (merge (options reconstruction-inventory) extra)))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"fresh loaded-consumer attestation"
                          (profile/authenticate-reconstruction!
                           (assoc (options reconstruction-inventory)
                                  :loaded-consumer-implementation-sha256 profile/producer-implementation-sha256))))
    (is (empty? @calls))))

(deftest restore-captures-known-profile-and-requires-exact-returned-profile
  ;; Read-only model checks at the same pre-resource descriptor gate used by
  ;; restore!. No opaque factory is fabricated and no guest owner is allocated.
  (let [consumer (profile/consumer-identity reconstruction-inventory)
        description {:producer-preparation producer :consumer-implementation-sha256 consumer}
        result (assoc description :catalogue {} :bindings {})
        manifest {:binding-signatures {}}
        known [profile/profile-id profile/reconstruction-profile-id profile/runtime-ops-reconstruction-profile-id
               profile/heap-net-dirty-reconstruction-profile-id profile/source-graph-reconstruction-profile-id]]
    (is (= 20 (count (for [id known other known :when (not= id other)] [id other]))))
    (doseq [id known]
      (is (= id (private-call 'factory-profile! (assoc description :compatibility-profile id) producer consumer)))
      (is (= id (:compatibility-profile
                 (private-call 'factory-result! (assoc result :compatibility-profile id) producer consumer id manifest))))
      (doseq [other (remove #{id} ["unknown" nil profile/profile-id profile/reconstruction-profile-id
                                   profile/runtime-ops-reconstruction-profile-id
                                   profile/heap-net-dirty-reconstruction-profile-id profile/source-graph-reconstruction-profile-id])]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"identity/signature mismatch"
                              (private-call 'factory-result! (assoc result :compatibility-profile other)
                                            producer consumer id manifest)))))
    (doseq [id ["unknown" nil]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"capability identity mismatch"
                            (private-call 'factory-profile! (assoc description :compatibility-profile id) producer consumer))))))

(def runtime-ops-inventory
  (changed reconstruction-inventory "prototype/mutable.clj"
           #(assoc % :sha256 profile/runtime-ops-mutable-sha256)))
(defn runtime-ops-valid! [rows]
  (profile/validate-runtime-ops-reconstruction-inventory! recipe rows (profile/consumer-identity rows)))

(deftest runtime-ops-reconstruction-preserves-both-original-closed-contracts
  (is (= 256 (count runtime-ops-inventory)))
  (is (= 3 (count (set [profile/profile-id profile/reconstruction-profile-id
                        profile/runtime-ops-reconstruction-profile-id]))))
  (is (not= profile/mutable-sha256 profile/runtime-ops-mutable-sha256))
  (is (identical? inventory (valid! inventory)))
  (is (identical? reconstruction-inventory (reconstruction-valid! reconstruction-inventory)))
  (is (identical? runtime-ops-inventory (runtime-ops-valid! runtime-ops-inventory)))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved mutable consumer"
                        (reconstruction-valid! runtime-ops-inventory)))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved mutable consumer"
                        (runtime-ops-valid! reconstruction-inventory)))
  (doseq [sha [profile/mutable-sha256 model-hash]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved mutable consumer"
                          (runtime-ops-valid! (changed runtime-ops-inventory "prototype/mutable.clj"
                                                       #(assoc % :sha256 sha))))))
  (doseq [id ["prototype/raw_interop.clj" "prototype/machine.cljc"
              "prototype/checkpoint_wire.clj" "ansatz/kernel/TypeChecker.class"]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved consumer substitution"
                          (runtime-ops-valid! (changed runtime-ops-inventory id #(assoc % :sha256 model-hash))))))
  (doseq [id (map :id runtime-ops-inventory)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected-input inventory drift"
                          (runtime-ops-valid! (vec (remove #(= id (:id %)) runtime-ops-inventory))))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected-input inventory drift"
                        (runtime-ops-valid! (conj runtime-ops-inventory
                                                  {:id "unreviewed/extra.clj" :kind :host-source :sha256 model-hash})))))

(deftest runtime-ops-authentication-is-closed-before-resource-acquisition
  (let [calls (atom [])
        resolver (fn [id] (swap! calls conj id) (throw (AssertionError. "Must reject before resource lookup")))
        options {:producer-preparation producer :producer-recipe-source recipe-source
                 :producer-resolve-artifact resolver :store-root "unused-model-store"
                 :consumer-inventory runtime-ops-inventory
                 :expected-consumer-implementation-sha256 (profile/consumer-identity runtime-ops-inventory)
                 :loaded-consumer-implementation-sha256 (profile/consumer-identity runtime-ops-inventory)
                 :consumer-resolve-source resolver}]
    (doseq [extra [{:compatibility-profile "invented"} {:substitutions #{"anything"}} {:authenticator identity}]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"factory options"
                            (profile/authenticate-runtime-ops-reconstruction! (merge options extra)))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"fresh loaded-consumer attestation"
                          (profile/authenticate-runtime-ops-reconstruction!
                           (assoc options :loaded-consumer-implementation-sha256 profile/producer-implementation-sha256))))
    (let [rows (changed runtime-ops-inventory "prototype/mutable.clj" #(assoc % :sha256 model-hash))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved mutable consumer"
                            (profile/authenticate-runtime-ops-reconstruction!
                             (assoc options :consumer-inventory rows
                                    :expected-consumer-implementation-sha256 (profile/consumer-identity rows)
                                    :loaded-consumer-implementation-sha256 (profile/consumer-identity rows))))))
    (is (empty? @calls))))

(def heap-source-id "src-java/ansatz/runtime/HeapOverlay.java")
(def heap-class-ids ["ansatz/runtime/HeapOverlay.class" "ansatz/runtime/HeapOverlay$1.class"
                     "ansatz/runtime/HeapOverlay$1$1.class"])
(def heap-net-dirty-inventory
  (changed runtime-ops-inventory heap-source-id #(assoc % :sha256 profile/heap-net-dirty-source-sha256)))
(defn heap-net-dirty-valid! [rows]
  (profile/validate-heap-net-dirty-reconstruction-inventory! recipe rows (profile/consumer-identity rows)))

(deftest heap-net-dirty-is-a-fourth-closed-source-contract
  (is (= 4 (count (set [profile/profile-id profile/reconstruction-profile-id
                        profile/runtime-ops-reconstruction-profile-id profile/heap-net-dirty-reconstruction-profile-id]))))
  (is (= 256 (count heap-net-dirty-inventory)))
  (is (identical? heap-net-dirty-inventory (heap-net-dirty-valid! heap-net-dirty-inventory)))
  ;; Each old API still rejects the new Heap source under its OWN old shape.
  (doseq [[validate rows] [[valid! inventory] [reconstruction-valid! reconstruction-inventory]
                           [runtime-ops-valid! runtime-ops-inventory]]]
    (is (identical? rows (validate rows)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved consumer substitution"
                          (validate (changed rows heap-source-id #(assoc % :sha256 profile/heap-net-dirty-source-sha256))))))
  (let [old-sha (:sha256 (first (filter #(= heap-source-id (:id %)) (:build-inventory recipe))))
        nearby (str (subs profile/heap-net-dirty-source-sha256 0 63) "b")]
    (doseq [sha [old-sha nearby model-hash]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved net-dirty heap overlay source"
                            (heap-net-dirty-valid! (changed heap-net-dirty-inventory heap-source-id #(assoc % :sha256 sha)))))))
  (doseq [id ["prototype/raw_interop.clj" "prototype/machine.cljc" "ansatz/kernel/TypeChecker.class"]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved consumer substitution"
                          (heap-net-dirty-valid! (changed heap-net-dirty-inventory id #(assoc % :sha256 model-hash))))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved mutable consumer"
                        (heap-net-dirty-valid! (changed heap-net-dirty-inventory "prototype/mutable.clj"
                                                        #(assoc % :sha256 profile/mutable-sha256)))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected-input inventory drift"
                        (heap-net-dirty-valid! (conj heap-net-dirty-inventory
                                                     {:id "unreviewed/extra.clj" :kind :host-source :sha256 model-hash})))))

(deftest heap-net-dirty-inventory-uses-actual-changed-source-and-loaded-class-bytes
  ;; The remaining baseline rows are the explicit model above. These four rows
  ;; use genuine current bytes; this is NOT whole-consumer loaded-code attestation.
  (let [path (io/file "../.." heap-source-id)
        actual-sha (wire/file-sha256 path)
        rows (changed runtime-ops-inventory heap-source-id #(assoc % :sha256 actual-sha))
        rows (reduce (fn [rows id]
                       (with-open [input (io/input-stream (io/resource id))]
                         (changed rows id #(assoc % :sha256 (wire/sha256 (.readAllBytes input)))))) rows heap-class-ids)]
    (is (= profile/heap-net-dirty-source-sha256 actual-sha))
    (is (identical? rows (heap-net-dirty-valid! rows)))
    (doseq [row (filter #(contains? (set (conj heap-class-ids heap-source-id)) (:id %)) rows)]
      (is (true? (profile/authenticate-input! row (fn [id] (is (= heap-source-id id)) path))))
      (is (thrown? clojure.lang.ExceptionInfo
                   (profile/authenticate-input! (assoc row :sha256 model-hash) (constantly path)))))))

(deftest heap-net-dirty-authentication-keeps-fresh-attestation-and-closed-options
  (let [calls (atom [])
        resolver (fn [id] (swap! calls conj id) (throw (AssertionError. "Must reject before resource lookup")))
        options {:producer-preparation producer :producer-recipe-source recipe-source
                 :producer-resolve-artifact resolver :store-root "unused-model-store"
                 :consumer-inventory heap-net-dirty-inventory
                 :expected-consumer-implementation-sha256 (profile/consumer-identity heap-net-dirty-inventory)
                 :loaded-consumer-implementation-sha256 (profile/consumer-identity heap-net-dirty-inventory)
                 :consumer-resolve-source resolver}]
    (doseq [extra [{:compatibility-profile "invented"} {:substitutions #{heap-source-id}} {:authenticator identity}]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"factory options"
                            (profile/authenticate-heap-net-dirty-reconstruction! (merge options extra)))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"fresh loaded-consumer attestation"
                          (profile/authenticate-heap-net-dirty-reconstruction!
                           (assoc options :loaded-consumer-implementation-sha256 profile/producer-implementation-sha256))))
    (let [rows (changed heap-net-dirty-inventory heap-source-id #(assoc % :sha256 model-hash))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved net-dirty heap overlay source"
                            (profile/authenticate-heap-net-dirty-reconstruction!
                             (assoc options :consumer-inventory rows
                                    :expected-consumer-implementation-sha256 (profile/consumer-identity rows)
                                    :loaded-consumer-implementation-sha256 (profile/consumer-identity rows))))))
    (is (empty? @calls))))

;; The fifth contract below is an explicit shape model. The graph runtime has a
;; separately frozen source-import/planner pair; a future whole selected-consumer
;; capture must authenticate actual resources and freshly loaded code together.
(def source-import-id "prototype/source_import.clj")
(def source-graph-plan-id "prototype/source_graph_plan.clj")
(def source-graph-inventory
  (conj (changed heap-net-dirty-inventory source-import-id
                 #(assoc % :sha256 profile/source-graph-import-sha256))
        {:id source-graph-plan-id :kind :host-source :sha256 profile/source-graph-plan-sha256}))
(defn source-graph-valid! [rows]
  (profile/validate-source-graph-reconstruction-inventory! recipe rows (profile/consumer-identity rows)))
(def closed-profile-cases
  [[profile/profile-id valid! inventory]
   [profile/reconstruction-profile-id reconstruction-valid! reconstruction-inventory]
   [profile/runtime-ops-reconstruction-profile-id runtime-ops-valid! runtime-ops-inventory]
   [profile/heap-net-dirty-reconstruction-profile-id heap-net-dirty-valid! heap-net-dirty-inventory]
   [profile/source-graph-reconstruction-profile-id source-graph-valid! source-graph-inventory]])

(deftest five-closed-inventories-reject-all-twenty-ordered-profile-mismatches
  (is (= 5 (count (set (map first closed-profile-cases)))))
  (is (= [255 256 256 256 257] (mapv #(count (nth % 2)) closed-profile-cases)))
  (is (= 20 (count (for [[id] closed-profile-cases [other] closed-profile-cases :when (not= id other)] [id other]))))
  (doseq [[id validate rows] closed-profile-cases]
    (is (identical? rows (validate rows)) (str id " accepts its own modeled inventory"))
    (doseq [[other _ other-rows] closed-profile-cases :when (not= id other)]
      ;; Each validator receives the digest of the supplied inventory. Rejection
      ;; therefore tests the closed contract rather than a stale digest alone.
      (is (thrown? clojure.lang.ExceptionInfo (validate other-rows)) (str id " rejects " other)))))

(deftest fifth-source-pins-do-not-relax-the-four-old-contracts
  (doseq [[id validate rows] (butlast closed-profile-cases)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved consumer substitution"
                          (validate (changed rows source-import-id #(assoc % :sha256 profile/source-graph-import-sha256)))) id)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected-input inventory drift"
                          (validate (conj rows {:id source-graph-plan-id :kind :host-source
                                                :sha256 profile/source-graph-plan-sha256}))) id))
  (let [old-import (:sha256 (first (filter #(= source-import-id (:id %)) (:build-inventory recipe))))]
    (doseq [[id shas] [[source-import-id [old-import model-hash
                                          (str (subs profile/source-graph-import-sha256 0 63) "0")]]
                       [source-graph-plan-id [model-hash
                                              (str (subs profile/source-graph-plan-sha256 0 63) "0")]]]
            sha shas]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved source graph consumer source"
                            (source-graph-valid! (changed source-graph-inventory id #(assoc % :sha256 sha)))))))
  (doseq [id ["prototype/raw_interop.clj" "prototype/machine.cljc" "ansatz/kernel/TypeChecker.class"]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved consumer substitution"
                          (source-graph-valid! (changed source-graph-inventory id #(assoc % :sha256 model-hash))))))
  (doseq [[id sha pattern] [["prototype/mutable.clj" profile/mutable-sha256 #"Unapproved mutable consumer"]
                            [heap-source-id model-hash #"Unapproved net-dirty heap overlay source"]
                            ["src-java/ansatz/runtime/GlobalsOverlay.java" model-hash #"globals overlay source"]]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo pattern
                          (source-graph-valid! (changed source-graph-inventory id #(assoc % :sha256 sha))))))
  (doseq [id (keys profile/program-substitutions)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"program sizing implementation"
                          (source-graph-valid! (changed source-graph-inventory id #(assoc % :sha256 model-hash)))))))

(deftest fifth-inventory-remains-exact-in-count-roles-and-digest
  (doseq [id (map :id source-graph-inventory)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected-input inventory drift"
                          (source-graph-valid! (vec (remove #(= id (:id %)) source-graph-inventory))))))
  (doseq [id [source-import-id source-graph-plan-id]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"role drift"
                          (source-graph-valid! (changed source-graph-inventory id #(assoc % :kind :host-resource))))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected-input inventory drift"
                        (source-graph-valid! (conj source-graph-inventory {:id "unreviewed/extra.clj" :kind :host-source :sha256 model-hash}))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid consumer inventory"
                        (source-graph-valid! (conj source-graph-inventory (last source-graph-inventory)))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"digest mismatch"
                        (profile/validate-source-graph-reconstruction-inventory!
                         recipe source-graph-inventory (profile/consumer-identity heap-net-dirty-inventory)))))

(deftest fifth-authentication-keeps-attestation-and-no-caller-authority-options
  (let [calls (atom [])
        resolver (fn [id] (swap! calls conj id) (throw (AssertionError. "Must reject before resource lookup")))
        options {:producer-preparation producer :producer-recipe-source recipe-source
                 :producer-resolve-artifact resolver :store-root "unused-model-store"
                 :consumer-inventory source-graph-inventory
                 :expected-consumer-implementation-sha256 (profile/consumer-identity source-graph-inventory)
                 :loaded-consumer-implementation-sha256 (profile/consumer-identity source-graph-inventory)
                 :consumer-resolve-source resolver}]
    ;; Exercise both public entry points, including factory→fifth authenticator
    ;; routing, without fabricating a successful opaque factory or guest owners.
    (doseq [authenticate [profile/authenticate-source-graph-reconstruction!
                          factory/make-source-graph-reconstruction-factory]]
      (doseq [extra [{:compatibility-profile profile/source-graph-reconstruction-profile-id}
                     {:substitutions #{source-import-id}} {:authenticator identity}
                     {:source-graph-import-sha256 model-hash} {:loader identity} {:import-receipt {}}]]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"factory options"
                              (authenticate (merge options extra)))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"fresh loaded-consumer attestation"
                            (authenticate
                             (assoc options :loaded-consumer-implementation-sha256 profile/producer-implementation-sha256))))
      (doseq [id [source-import-id source-graph-plan-id]]
        (let [rows (changed source-graph-inventory id #(assoc % :sha256 model-hash))
              sha (profile/consumer-identity rows)]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved source graph consumer source"
                                (authenticate
                                 (assoc options :consumer-inventory rows
                                        :expected-consumer-implementation-sha256 sha
                                        :loaded-consumer-implementation-sha256 sha)))))))
    (is (empty? @calls))))

;; Sixth inventory remains a model. Its exact frontend pin is supplied only
;; after the runtime owner's independent protocol regression freeze. No modeled
;; inventory or factory rejection claims a genuine loaded consumer or graph IO.
(def graph-frontend-id "prototype/frontend.clj")
(def graph-frontend-inventory
  (changed source-graph-inventory graph-frontend-id
           #(assoc % :sha256 profile/source-graph-frontend-sha256)))
(defn graph-frontend-valid! [rows]
  (profile/validate-source-graph-frontend-reconstruction-inventory!
   recipe rows (profile/consumer-identity rows)))
(def six-profile-cases
  (conj closed-profile-cases
        [profile/source-graph-frontend-reconstruction-profile-id graph-frontend-valid! graph-frontend-inventory]))

(deftest six-closed-inventories-reject-all-thirty-ordered-profile-mismatches
  (is (= 6 (count (set (map first six-profile-cases)))))
  (is (= [255 256 256 256 257 257] (mapv #(count (nth % 2)) six-profile-cases)))
  (is (= 30 (count (for [[id] six-profile-cases [other] six-profile-cases :when (not= id other)] [id other]))))
  (doseq [[id validate rows] six-profile-cases]
    (is (identical? rows (validate rows)) (str id " accepts its exact modeled inventory"))
    (doseq [[other _ other-rows] six-profile-cases :when (not= id other)]
      (is (thrown? clojure.lang.ExceptionInfo (validate other-rows)) (str id " rejects " other)))))

(deftest sixth-frontend-pin-does-not-relax-five-prior-source-contracts
  (doseq [[id validate rows] closed-profile-cases]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved consumer substitution"
                          (validate (changed rows graph-frontend-id
                                             #(assoc % :sha256 profile/source-graph-frontend-sha256)))) id))
  (let [baseline (:sha256 (first (filter #(= graph-frontend-id (:id %)) (:build-inventory recipe))))
        pin profile/source-graph-frontend-sha256
        nearby (str (if (= \0 (first pin)) "1" "0") (subs pin 1))]
    (doseq [sha [baseline model-hash nearby]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved source graph frontend consumer source"
                            (graph-frontend-valid! (changed graph-frontend-inventory graph-frontend-id #(assoc % :sha256 sha)))))))
  (doseq [id [source-import-id source-graph-plan-id]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved source graph consumer source"
                          (graph-frontend-valid! (changed graph-frontend-inventory id #(assoc % :sha256 model-hash))))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved net-dirty heap overlay source"
                        (graph-frontend-valid! (changed graph-frontend-inventory heap-source-id #(assoc % :sha256 model-hash)))))
  (doseq [id ["prototype/raw_interop.clj" "prototype/machine.cljc" "ansatz/kernel/TypeChecker.class"]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved consumer substitution"
                          (graph-frontend-valid! (changed graph-frontend-inventory id #(assoc % :sha256 model-hash)))))))

(deftest sixth-inventory-count-roles-and-digest-remain-exact
  (doseq [id (map :id graph-frontend-inventory)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected-input inventory drift"
                          (graph-frontend-valid! (vec (remove #(= id (:id %)) graph-frontend-inventory))))))
  (doseq [id [graph-frontend-id source-import-id source-graph-plan-id]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"role drift"
                          (graph-frontend-valid! (changed graph-frontend-inventory id #(assoc % :kind :host-resource))))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected-input inventory drift"
                        (graph-frontend-valid! (conj graph-frontend-inventory {:id "unreviewed/extra.clj" :kind :host-source :sha256 model-hash}))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid consumer inventory"
                        (graph-frontend-valid! (conj graph-frontend-inventory (last graph-frontend-inventory)))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"digest mismatch"
                        (profile/validate-source-graph-frontend-reconstruction-inventory!
                         recipe graph-frontend-inventory (profile/consumer-identity source-graph-inventory)))))

(deftest sixth-factory-and-authenticator-reject-caller-authority-before-resource-lookup
  (let [calls (atom [])
        resolver (fn [id] (swap! calls conj id) (throw (AssertionError. "Must reject before resource lookup")))
        options {:producer-preparation producer :producer-recipe-source recipe-source
                 :producer-resolve-artifact resolver :store-root "unused-model-store"
                 :consumer-inventory graph-frontend-inventory
                 :expected-consumer-implementation-sha256 (profile/consumer-identity graph-frontend-inventory)
                 :loaded-consumer-implementation-sha256 (profile/consumer-identity graph-frontend-inventory)
                 :consumer-resolve-source resolver}]
    (doseq [authenticate [profile/authenticate-source-graph-frontend-reconstruction!
                          factory/make-source-graph-frontend-reconstruction-factory]]
      (doseq [extra [{:compatibility-profile profile/source-graph-frontend-reconstruction-profile-id}
                     {:substitutions #{graph-frontend-id}} {:authenticator identity}
                     {:frontend-sha256 model-hash} {:loader identity} {:import-receipt {}}]]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"factory options" (authenticate (merge options extra)))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"fresh loaded-consumer attestation"
                            (authenticate (assoc options :loaded-consumer-implementation-sha256 profile/producer-implementation-sha256))))
      (doseq [[id pattern] [[graph-frontend-id #"Unapproved source graph frontend consumer source"]
                            [source-import-id #"Unapproved source graph consumer source"]
                            [source-graph-plan-id #"Unapproved source graph consumer source"]
                            [heap-source-id #"Unapproved net-dirty heap overlay source"]]]
        (let [rows (changed graph-frontend-inventory id #(assoc % :sha256 model-hash)) sha (profile/consumer-identity rows)]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo pattern
                                (authenticate (assoc options :consumer-inventory rows
                                                     :expected-consumer-implementation-sha256 sha
                                                     :loaded-consumer-implementation-sha256 sha)))))))
    (is (empty? @calls))))

(deftest six-returned-profile-identities-reject-all-thirty-ordered-mismatches
  (let [consumer (profile/consumer-identity reconstruction-inventory)
        description {:producer-preparation producer :consumer-implementation-sha256 consumer}
        result (assoc description :catalogue {} :bindings {}) manifest {:binding-signatures {}}
        known (mapv first six-profile-cases)]
    (is (= 30 (count (for [id known other known :when (not= id other)] [id other]))))
    (doseq [id known]
      (is (= id (private-call 'factory-profile! (assoc description :compatibility-profile id) producer consumer)))
      (is (= id (:compatibility-profile
                 (private-call 'factory-result! (assoc result :compatibility-profile id) producer consumer id manifest))))
      (doseq [other (remove #{id} known)]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"identity/signature mismatch"
                              (private-call 'factory-result! (assoc result :compatibility-profile other)
                                            producer consumer id manifest)))))))

;; Seventh profile models three fixed new resources and exact reviewed
;; substitutions. Pure shape checks do not attest any loaded source or restore.
(def hosted-application-inventory
  (vec (concat
        (map (fn [row]
               (if-let [pin (get profile/hosted-application-substitutions (:id row))]
                 (assoc row :sha256 pin) row)) graph-frontend-inventory)
        (for [[id kind] (sort-by key profile/hosted-application-added-inputs)]
          {:id id :kind kind :sha256 model-hash}))))
(defn hosted-application-valid! [rows]
  (profile/validate-hosted-application-inventory! recipe rows (profile/consumer-identity rows)))

(deftest seventh-fixed-domain-preserves-all-six-earlier-contracts
  (is (= 260 (count hosted-application-inventory)))
  (is (identical? hosted-application-inventory (hosted-application-valid! hosted-application-inventory)))
  (doseq [[id validate rows] six-profile-cases]
    (is (identical? rows (validate rows)) id)
    (is (thrown? clojure.lang.ExceptionInfo (validate hosted-application-inventory)) id)
    (is (thrown? clojure.lang.ExceptionInfo (hosted-application-valid! rows)) id))
  (doseq [id (map :id hosted-application-inventory)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected-input inventory drift"
                          (hosted-application-valid! (vec (remove #(= id (:id %)) hosted-application-inventory))))))
  (doseq [id (keys profile/hosted-application-added-inputs)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"role drift"
                          (hosted-application-valid! (changed hosted-application-inventory id #(assoc % :kind :host-resource)))))))

(deftest seventh-reviewed-substitutions-are-not-caller-extensible
  (doseq [[id pin] profile/hosted-application-substitutions]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"hosted application source substitution"
                          (hosted-application-valid! (changed hosted-application-inventory id #(assoc % :sha256 model-hash))))))
  (doseq [id ["prototype/machine.cljc" "prototype/checkpoint_wire.clj" "ansatz/kernel/Reducer.class"]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved consumer substitution"
                          (hosted-application-valid! (changed hosted-application-inventory id #(assoc % :sha256 model-hash))))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected-input inventory drift"
                        (hosted-application-valid! (conj hosted-application-inventory
                                                         {:id "unreviewed/extra.clj" :kind :host-source :sha256 model-hash}))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"digest mismatch"
                        (profile/validate-hosted-application-inventory! recipe hosted-application-inventory
                                                                        (profile/consumer-identity graph-frontend-inventory)))))

(deftest seventh-factory-rejects-caller-authority-before-resource-lookup
  (let [calls (atom []) resolver (fn [id] (swap! calls conj id) (throw (AssertionError. "Unexpected lookup")))
        digest (profile/consumer-identity hosted-application-inventory)
        options {:producer-preparation producer :producer-recipe-source recipe-source
                 :producer-resolve-artifact resolver :store-root "unused-model-store"
                 :consumer-inventory hosted-application-inventory
                 :expected-consumer-implementation-sha256 digest :loaded-consumer-implementation-sha256 digest
                 :consumer-resolve-source resolver}]
    (doseq [authenticate [profile/authenticate-hosted-application! factory/make-hosted-application-factory]]
      (doseq [extra [{:substitutions profile/hosted-application-substitutions}
                     {:compatibility-profile profile/hosted-application-profile-id}
                     {:loader identity} {:kernel-policy {}}]]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"factory options" (authenticate (merge options extra)))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"fresh loaded-consumer attestation"
                            (authenticate (assoc options :loaded-consumer-implementation-sha256 model-hash))))
      (let [rows (changed hosted-application-inventory "prototype/raw_interop.clj" #(assoc % :sha256 model-hash))
            digest (profile/consumer-identity rows)]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"hosted application source substitution"
                              (authenticate (assoc options :consumer-inventory rows
                                                   :expected-consumer-implementation-sha256 digest
                                                   :loaded-consumer-implementation-sha256 digest))))))
    (is (empty? @calls))))

(deftest seventh-restore-capability-remains-distinct-from-all-six-priors
  (let [consumer (profile/consumer-identity hosted-application-inventory)
        description {:producer-preparation producer :consumer-implementation-sha256 consumer}
        result (assoc description :catalogue {} :bindings {}) manifest {:binding-signatures {}}
        known (conj (mapv first six-profile-cases) profile/hosted-application-profile-id)]
    (is (= 42 (count (for [id known other known :when (not= id other)] [id other]))))
    (doseq [id known]
      (is (= id (private-call 'factory-profile! (assoc description :compatibility-profile id) producer consumer)))
      (is (= id (:compatibility-profile
                 (private-call 'factory-result! (assoc result :compatibility-profile id) producer consumer id manifest))))
      (doseq [other (remove #{id} known)]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"identity/signature mismatch"
                              (private-call 'factory-result! (assoc result :compatibility-profile other)
                                            producer consumer id manifest)))))))

(deftest seventh-kernel-source-and-class-cohort-rejects-old-corrected-mixing
  (let [old (into {} (map (juxt :id :sha256)) graph-frontend-inventory)]
    (doseq [id ["src-java/ansatz/kernel/Expr.java" "src-java/ansatz/kernel/ExprStore.java"
                "src-java/ansatz/kernel/TypeChecker.java" "ansatz/kernel/Expr.class"
                "ansatz/kernel/TypeChecker.class"]]
      ;; Even a caller that recomputes the whole digest cannot mix one old
      ;; source/class row into the reviewed corrected kernel cohort.
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"hosted application source substitution"
                            (hosted-application-valid! (changed hosted-application-inventory id
                                                                #(assoc % :sha256 (get old id))))))
      (doseq [[label validate rows] six-profile-cases]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved consumer substitution"
                              (validate (changed rows id #(assoc % :sha256 (get profile/hosted-application-substitutions id))))) label)))))

(deftest producer-provenance-and-actual-corrected-class-resources-are-independent
  ;; Producer byte hashes here are models; loaded class resources are actual.
  ;; Original archived class bytes are opaque provenance, never executed here.
  (let [directory (java.nio.file.Files/createTempDirectory "ansatz-producer-class-proof-"
                                                           (make-array java.nio.file.attribute.FileAttribute 0))
        bytes (fn [s] (.getBytes ^String s java.nio.charset.StandardCharsets/UTF_8))
        actual (fn [id] (with-open [input (io/input-stream (io/resource id))] (.readAllBytes input)))
        content {"ansatz/kernel/Expr.class" (bytes "modeled original Expr bytes")
                 "ansatz/kernel/TypeChecker.class" (bytes "modeled original TypeChecker bytes")
                 "ansatz/kernel/Name.class" (actual "ansatz/kernel/Name.class")
                 "producer/model.clj" (bytes "(ns original.producer)")}
        paths (into {} (map-indexed (fn [i [id value]]
                                      (let [path (.resolve directory (str i ".bin"))]
                                        (java.nio.file.Files/write path ^bytes value (make-array java.nio.file.OpenOption 0))
                                        [id path])) content))
        rows (mapv (fn [[id value]] {:id id :kind (if (.endsWith ^String id ".class") :kernel-class :host-source)
                                     :sha256 (wire/sha256 value)}) content)
        recipe {:build-inventory rows}
        preparation {:implementation-sha256 (#'factory/build-identity rows)}
        reads (atom []) resolver (fn [id] (swap! reads conj id) (.toFile ^java.nio.file.Path (get paths id)))]
    (try
      (doseq [id ["ansatz/kernel/Expr.class" "ansatz/kernel/TypeChecker.class"]]
        (is (= (get profile/hosted-application-substitutions id) (wire/sha256 (actual id)))))
      (is (nil? (#'factory/authenticate-hosted-application-build! recipe preparation resolver)))
      (is (= (set (keys content)) (set @reads)))
      ;; The legacy policy still requires the producer's actual class bytes;
      ;; it does not consult arbitrary resolved disk files for loaded identity.
      (reset! reads [])
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Loaded kernel class resource drift"
                            (#'factory/authenticate-build! recipe preparation resolver)))
      (is (empty? @reads))
      ;; A valid corrected loaded class cannot hide corrupted archived bytes.
      (java.nio.file.Files/write (get paths "ansatz/kernel/Expr.class") (bytes "tampered")
                                 (make-array java.nio.file.OpenOption 0))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Archived producer kernel class drift"
                            (#'factory/authenticate-hosted-application-build! recipe preparation resolver)))
      (java.nio.file.Files/write (get paths "ansatz/kernel/Expr.class") (get content "ansatz/kernel/Expr.class")
                                 (make-array java.nio.file.OpenOption 0))
      ;; A non-overridden class must still match its original row against the
      ;; real selected class resource, even when its archive file hashes agree.
      (let [wrong (bytes "different original Name bytes")
            rows (changed rows "ansatz/kernel/Name.class" #(assoc % :sha256 (wire/sha256 wrong)))
            recipe {:build-inventory rows} preparation {:implementation-sha256 (#'factory/build-identity rows)}]
        (java.nio.file.Files/write (get paths "ansatz/kernel/Name.class") wrong (make-array java.nio.file.OpenOption 0))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Loaded hosted application kernel class resource drift"
                              (#'factory/authenticate-hosted-application-build! recipe preparation resolver))))
      (reset! reads [])
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Factory build identity mismatch"
                            (#'factory/authenticate-hosted-application-build!
                             recipe (assoc preparation :implementation-sha256 model-hash) resolver)))
      (is (empty? @reads))
      (finally
        (doseq [path (vals paths)] (java.nio.file.Files/delete path))
        (java.nio.file.Files/delete directory)))))

;; /2 changes only the authenticated guest encoder member. The fixture still
;; models selected resource bytes; it confers no loaded-code/restore authority.
(def hosted-application-control-inventory
  (mapv (fn [row]
          (if-let [pin (get profile/hosted-application-control-substitutions (:id row))]
            (assoc row :sha256 pin) row)) hosted-application-inventory))
(defn hosted-application-control-valid! [rows]
  (profile/validate-hosted-application-control-inventory!
   recipe rows (profile/consumer-identity rows)))

(deftest encoder-control-revision-preserves-all-seven-closed-policies
  (let [rows hosted-application-control-inventory
        prior (conj (vec six-profile-cases)
                    [profile/hosted-application-profile-id hosted-application-valid!
                     hosted-application-inventory])]
    (is (= 260 (count rows)))
    (is (= (mapv #(dissoc % :sha256) hosted-application-inventory)
           (mapv #(dissoc % :sha256) rows)))
    (let [old-by-id (into {} (map (juxt :id identity)) hosted-application-inventory)]
      (is (= ["prototype/guest_encoding.clj"]
             (mapv :id (filter #(not= % (get old-by-id (:id %))) rows)))))
    (is (identical? rows (hosted-application-control-valid! rows)))
    (doseq [[id validate old] prior]
      (is (identical? old (validate old)) id)
      (is (thrown? clojure.lang.ExceptionInfo (validate rows)) id)
      (is (thrown? clojure.lang.ExceptionInfo (hosted-application-control-valid! old)) id))
    (doseq [id (map :id rows)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected-input inventory drift"
                            (hosted-application-control-valid! (vec (remove #(= id (:id %)) rows))))))
    (is (= profile/hosted-application-substitutions
           (dissoc profile/hosted-application-control-substitutions "prototype/guest_encoding.clj")))
    (doseq [id (map :id rows)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"role drift"
                            (hosted-application-control-valid! (changed rows id #(update % :kind (fn [kind] (if (= kind :host-resource) :host-source :host-resource))))))))
    (doseq [[id _] profile/hosted-application-control-substitutions]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"hosted application source substitution"
                            (hosted-application-control-valid! (changed rows id #(assoc % :sha256 model-hash)))))))
  (doseq [id ["prototype/machine.cljc" "ansatz/kernel/Reducer.class"]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unapproved consumer substitution"
                          (hosted-application-control-valid!
                           (changed hosted-application-control-inventory id #(assoc % :sha256 model-hash)))))))

(deftest encoder-control-factory-rejects-forged-options-and-attestation
  (let [calls (atom []) resolver (fn [id] (swap! calls conj id) (throw (AssertionError. "Unexpected lookup")))
        digest (profile/consumer-identity hosted-application-control-inventory)
        options {:producer-preparation producer :producer-recipe-source recipe-source
                 :producer-resolve-artifact resolver :store-root "unused-model-store"
                 :consumer-inventory hosted-application-control-inventory
                 :expected-consumer-implementation-sha256 digest :loaded-consumer-implementation-sha256 digest
                 :consumer-resolve-source resolver}]
    (doseq [authenticate [profile/authenticate-hosted-application-control!
                          factory/make-hosted-application-control-factory]]
      (doseq [extra [{:substitutions profile/hosted-application-control-substitutions}
                     {:compatibility-profile profile/hosted-application-control-profile-id}
                     {:hosted-application-revision :v2} {:loader identity}]]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"factory options"
                              (authenticate (merge options extra)))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"fresh loaded-consumer attestation"
                            (authenticate (assoc options :loaded-consumer-implementation-sha256 model-hash))))
      (let [old hosted-application-inventory old-digest (profile/consumer-identity old)]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"hosted application source substitution"
                              (authenticate (assoc options :consumer-inventory old
                                                   :expected-consumer-implementation-sha256 old-digest
                                                   :loaded-consumer-implementation-sha256 old-digest))))))
    (is (empty? @calls))))

(deftest encoder-control-restore-capability-distinguishes-all-eight-policies
  (let [consumer (profile/consumer-identity hosted-application-control-inventory)
        description {:producer-preparation producer :consumer-implementation-sha256 consumer}
        result (assoc description :catalogue {} :bindings {}) manifest {:binding-signatures {}}
        known (conj (mapv first six-profile-cases) profile/hosted-application-profile-id
                    profile/hosted-application-control-profile-id)]
    (doseq [id known]
      (is (= id (private-call 'factory-profile! (assoc description :compatibility-profile id) producer consumer)))
      (doseq [other known]
        (if (= id other)
          (is (= id (:compatibility-profile
                     (private-call 'factory-result! (assoc result :compatibility-profile other)
                                   producer consumer id manifest))))
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"identity/signature mismatch"
                                (private-call 'factory-result! (assoc result :compatibility-profile other)
                                              producer consumer id manifest))))))))

(deftest encoder-control-authenticator-routes-exact-inventory-and-profile
  ;; Model the resource boundary explicitly; actual source/class checking is
  ;; covered separately. Both authenticators must check every selected member.
  (doseq [[id authenticate rows]
          [[profile/hosted-application-profile-id profile/authenticate-hosted-application!
            hosted-application-inventory]
           [profile/hosted-application-control-profile-id profile/authenticate-hosted-application-control!
            hosted-application-control-inventory]]]
    (let [checked (atom []) digest (profile/consumer-identity rows)
          resolver (fn [_] (throw (AssertionError. "Unexpected producer lookup")))
          options {:producer-preparation producer :producer-recipe-source recipe-source
                   :producer-resolve-artifact resolver :store-root "unused-model-store"
                   :consumer-inventory rows :expected-consumer-implementation-sha256 digest
                   :loaded-consumer-implementation-sha256 digest :consumer-resolve-source resolver}]
      (with-redefs [io/resource (constantly nil)
                    profile/authenticate-input! (fn [row supplied]
                                                  (is (identical? resolver supplied))
                                                  (swap! checked conj row) true)]
        (is (= {:producer-preparation producer :consumer-implementation-sha256 digest
                :compatibility-profile id} (authenticate options))))
      (is (= rows @checked)))))
