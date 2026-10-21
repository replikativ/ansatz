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
           (if (= "prototype/mutable.clj" (:id row)) (assoc row :sha256 profile/mutable-sha256) row))
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
  (let [id "prototype/mutable.clj" row {:id id :kind :host-source :sha256 profile/mutable-sha256}]
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
    (is (identical? result (private-call 'factory-result! result producer consumer manifest)))
    (doseq [changed [(assoc result :producer-preparation (assoc producer :implementation-sha256 model-hash))
                     (assoc result :consumer-implementation-sha256 profile/producer-implementation-sha256)
                     (assoc result :compatibility-profile "unreviewed")
                     (assoc-in result [:bindings "model" :signature :return-type] "uint32")
                     (update result :bindings dissoc "model")]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"identity/signature mismatch"
                           (private-call 'factory-result! changed producer consumer manifest))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid consumer factory result"
                         (private-call 'factory-result! (assoc result :implementation-sha256 profile/producer-implementation-sha256)
                                       producer consumer manifest)))))

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
