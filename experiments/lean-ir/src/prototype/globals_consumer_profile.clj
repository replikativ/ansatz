(ns prototype.globals-consumer-profile
  "Closed producer50f -> globals-boundary consumer compatibility contract.
   The producer recipe stays immutable. The consumer inventory describes selected
   available project resources, not a claim that every namespace was executed.
   An external digest and fresh-process loaded-code attestation are mandatory."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [prototype.checkpoint-wire :as wire])
  (:import [java.nio.charset StandardCharsets]))

(def profile-id "ansatz-producer50f-globals-overlay-consumer/2")
(def reconstruction-profile-id "ansatz-producer50f-reconstruction-consumer/1")
(def runtime-ops-reconstruction-profile-id "ansatz-producer50f-runtime-ops-reconstruction-consumer/1")
(def runtime-ops-mutable-sha256 "d9661df032553e12efeaef20965089ed0dd2e9832e63e974714ed3f8ecf700ee")
(def ^:private reconstruction-substitutions
  #{"prototype/imported_kernel.clj" "prototype/kernel_bridge.clj" "prototype/test_runner.clj"})
(def producer-implementation-sha256 "50f0b30693b1d696dd60790a0bb09aeeeba58baf2b2fdabe13e17f0103bf2849")
(def producer-recipe-sha256 "9a1d53dce65909c15330ee4fa7289804e727927b30f504ed010680a0c1971e70")
(def mutable-sha256 "64e2ecdaec7708d3041b9260af41ed32d2d8cdeb87ee268e0ddeb2928d569188")
(def globals-source-sha256 "440cc5132b27cd5b65f58240d7620ac21ecfb01f3959a3c89d619e5aa16fe9bb")
(def program-substitutions
  {"prototype/slot_count.clj" "fc679048c071613ed1c7c0b6d4a28a0bae15a138452657ab6f37cfad2eddea7e"
   "prototype/program_install.clj" "c69df77e5b85a7894759bcdce715aaf0b0eac1cb24ea57e22660ce1f3d56a9b4"})
(def excluded-producer-sources
  #{"prototype/finalizer_checkpoint.clj" "prototype/full_init_checkpoint_factory.clj"})
(def added-inputs
  {"prototype/restore_consumer.clj" :host-source
   "prototype/globals_consumer_factory.clj" :host-source
   "prototype/globals_consumer_profile.clj" :host-source
   "prototype/compact_import_check.clj" :host-source
   "prototype/compact_kernel_projection.clj" :host-source
   "prototype/resident_source.clj" :host-source
   "prototype/resident_import.clj" :host-source
   "java/prototype/TypedLongMemo.java" :host-source
   "src-java/ansatz/runtime/GlobalsOverlay.java" :host-source
   "ansatz/runtime/GlobalsOverlay.class" :runtime-class
   "ansatz/runtime/GlobalsOverlay$Hint.class" :runtime-class
   "ansatz/runtime/HeapOverlay.class" :runtime-class
   "ansatz/runtime/HeapOverlay$1.class" :runtime-class
   "ansatz/runtime/HeapOverlay$1$1.class" :runtime-class
   "prototype/TypedLongMemo.class" :runtime-class})
(def option-keys
  #{:producer-preparation :producer-recipe-source :producer-resolve-artifact :store-root
    :consumer-inventory :expected-consumer-implementation-sha256
    :loaded-consumer-implementation-sha256 :consumer-resolve-source})
(defn- exact! [value keys label]
  (wire/check (and (map? value) (= keys (set (clojure.core/keys value)))) (str "Invalid " label)))
(defn consumer-identity
  "Content digest only; neither loaded-code attestation nor checking authority."
  [inventory]
  (wire/check (and (vector? inventory) (seq inventory) (<= (count inventory) 1000)
                   (= (count inventory) (count (set (map :id inventory))))) "Invalid consumer inventory")
  (doseq [row inventory]
    (exact! row #{:id :kind :sha256} "consumer inventory row")
    (wire/check (and (string? (:id row)) (re-matches #"[A-Za-z0-9_./$-]+" (:id row))
                     (not (some #{".."} (str/split (:id row) #"/")))
                     (contains? #{:host-source :host-resource :kernel-class :runtime-class} (:kind row))
                     (wire/hash? (:sha256 row))) "Invalid consumer input identity"))
  (wire/sha256 (.getBytes (str "ansatz-restored-runtime-consumer/1\n"
                              (apply str (for [{:keys [id kind sha256]} (sort-by :id inventory)]
                                           (str id "\t" (name kind) "\t" sha256 "\n"))))
                          StandardCharsets/UTF_8)))
(defn producer-recipe!
  "Authenticate exact captured original recipe bytes; never reopen a recipe path."
  [preparation source]
  (exact! preparation #{:factory-id :implementation-sha256 :catalogue-recipe :kernel-policy :trusted-roots}
          "producer preparation")
  (wire/check (and (string? source)
                   (<= (count source) wire/max-row-bytes)
                   (= producer-recipe-sha256 (wire/sha256 (.getBytes ^String source StandardCharsets/UTF_8))))
              "Unapproved producer recipe bytes")
  (let [recipe (edn/read-string source)]
    (wire/check (and (= producer-implementation-sha256 (:implementation-sha256 preparation))
                     (= "ansatz-full-init-source-bound-precheck/2" (:factory-id preparation))
                     (= "full-init-checkpoint-preparation/2" (:schema recipe))
                     (wire/same-data? recipe (:catalogue-recipe preparation)))
                "Producer preparation identity drift")
    recipe))
(defn- validate-inventory*
  "Check the closed delta before ANY consumer resource is trusted. New API hashes
   are pinned by the externally accepted consumer digest, avoiding a self-hash cycle."
  [reconstruction? runtime-ops? recipe inventory expected]
  (wire/check (and (wire/hash? expected) (= expected (consumer-identity inventory)))
              "Consumer implementation digest mismatch")
  (let [original (:build-inventory recipe)
        by-id (into {} (map (juxt :id identity)) inventory)
        baseline (remove #(contains? excluded-producer-sources (:id %)) original)
        required (merge (into {} (map (juxt :id :kind)) baseline) added-inputs
                        (when reconstruction? {"prototype/resident_init_prefix.clj" :host-source}))]
    (wire/check (= (set (keys required)) (set (keys by-id))) "Consumer selected-input inventory drift")
    (doseq [[id kind] required]
      (wire/check (= kind (get-in by-id [id :kind])) "Consumer input role drift"))
    (doseq [{:keys [id sha256]} baseline
            :when (and (not= id "prototype/mutable.clj") (not (contains? program-substitutions id))
                       (not (and reconstruction? (contains? reconstruction-substitutions id))))]
      (wire/check (= sha256 (get-in by-id [id :sha256])) "Unapproved consumer substitution"))
    (doseq [[id sha256] program-substitutions]
      (wire/check (= sha256 (get-in by-id [id :sha256])) "Unapproved program sizing implementation"))
    (wire/check (= (if runtime-ops? runtime-ops-mutable-sha256 mutable-sha256)
                   (get-in by-id ["prototype/mutable.clj" :sha256]))
                "Unapproved mutable consumer implementation")
    (wire/check (= globals-source-sha256 (get-in by-id ["src-java/ansatz/runtime/GlobalsOverlay.java" :sha256]))
                "Unapproved globals overlay source")
    inventory))
(defn validate-inventory!
  "Validate the original closed globals inventory without reconstruction deltas."
  [recipe inventory expected]
  (validate-inventory* false false recipe inventory expected))
(defn validate-reconstruction-inventory!
  "Validate the closed reconstruction delta. The external digest pins exact bytes
   of the three reviewed baseline substitutions and added resident prefix source."
  [recipe inventory expected]
  (validate-inventory* true false recipe inventory expected))
(defn validate-runtime-ops-reconstruction-inventory!
  "Validate the closed reconstruction inventory with the separately pinned ops-table
   mutable implementation. Original globals/reconstruction contracts remain exact."
  [recipe inventory expected]
  (validate-inventory* true true recipe inventory expected))
(def provenance-scripts
  #{"experiments/lean-ir/scripts/full-init-assembly-probe.clj"
    "experiments/lean-ir/scripts/prepare-ir-witness.clj"
    "experiments/lean-ir/scripts/prepare-shared-names-linear-witness.clj"
    "experiments/lean-ir/scripts/prepare-shared-names-witness.clj"
    "experiments/lean-ir/scripts/typed-witness-next.clj"})
(defn input-role [{:keys [id kind]}]
  (cond
    (contains? #{:kernel-class :runtime-class} kind) :selected-class
    (or (str/starts-with? id "src-java/") (= id "java/prototype/TypedLongMemo.java")) :java-source
    (contains? provenance-scripts id) :provenance-source
    :else :selected-resource))
(defn- stream-sha256 [input]
  (let [digest (java.security.MessageDigest/getInstance "SHA-256") bytes (byte-array 65536)]
    (loop [] (let [n (.read ^java.io.InputStream input bytes)]
               (when (pos? n) (.update digest bytes 0 n) (recur))))
    (.formatHex (java.util.HexFormat/of) (.digest digest))))
(defn authenticate-input!
  "Verify selected resources/classes and separately pinned provenance files.
   Java sources and the exact build scripts are not required on the classpath;
   the matching actual Java outer/nested classes have their own rows."
  [row resolve-source]
  (let [{:keys [id sha256]} row]
    (case (input-role row)
      :java-source
      (wire/check (= sha256 (wire/file-sha256 (resolve-source id))) "Consumer Java source drift")
      :provenance-source
      (wire/check (= sha256 (wire/file-sha256 (resolve-source id))) "Consumer provenance script drift")
      :selected-resource
      (let [url (io/resource id)]
        (wire/check url "Selected consumer resource unavailable")
        (with-open [input (io/input-stream url)]
          (wire/check (= sha256 (stream-sha256 input)) "Selected consumer resource drift")))
      :selected-class
      (let [class-name (subs (str/replace id "/" ".") 0 (- (count id) 6))
            class (Class/forName class-name false (clojure.lang.RT/baseLoader))]
        (with-open [input (.getResourceAsStream class (str "/" id))]
          (wire/check input "Selected consumer class unavailable")
          (wire/check (= sha256 (stream-sha256 input)) "Selected consumer class drift"))))
    true))
(defn- authenticate*
  "Host-only verification. The external loaded-consumer attestation must come
   from a fresh trusted launcher which checks classpath/source selection and
   rejects project __init.class AOT shadows before loading namespaces, and which
   prohibits reload/redefs. This API cannot infer that
   fact from disk/resource hashes. No source leases or guest owners are acquired."
  [reconstruction? runtime-ops? {:keys [producer-preparation producer-recipe-source consumer-inventory
           expected-consumer-implementation-sha256 loaded-consumer-implementation-sha256
           producer-resolve-artifact consumer-resolve-source store-root] :as options}]
  (exact! options option-keys "globals consumer factory options")
  (wire/check (and (fn? producer-resolve-artifact) (fn? consumer-resolve-source)
                   (string? store-root) (seq store-root)
                   (= expected-consumer-implementation-sha256 loaded-consumer-implementation-sha256))
              "Explicit producer/consumer resolvers and fresh loaded-consumer attestation required")
  (let [recipe (producer-recipe! producer-preparation producer-recipe-source)]
    (validate-inventory* reconstruction? runtime-ops? recipe consumer-inventory expected-consumer-implementation-sha256)
    (doseq [id excluded-producer-sources]
      (wire/check (and (nil? (io/resource id))
                       (nil? (io/resource (str (subs id 0 (- (count id) 4)) "__init.class"))))
                  "Producer-only legacy source or AOT is available on consumer classpath"))
    (doseq [row consumer-inventory] (authenticate-input! row consumer-resolve-source))
    {:producer-preparation producer-preparation
     :consumer-implementation-sha256 expected-consumer-implementation-sha256
     :compatibility-profile (cond runtime-ops? runtime-ops-reconstruction-profile-id
                                  reconstruction? reconstruction-profile-id
                                  :else profile-id)}))

(defn authenticate!
  "Authenticate the original closed globals consumer and fresh loaded-code attestation."
  [options]
  (authenticate* false false options))
(defn authenticate-reconstruction!
  "Authenticate the separately named closed reconstruction consumer. Same exact
   options and fresh-process loaded-code attestation as authenticate!."
  [options]
  (authenticate* true false options))

(defn authenticate-runtime-ops-reconstruction!
  "Authenticate the separately named ops-table reconstruction consumer. Same closed
   options and mandatory fresh-process loaded-code attestation as authenticate!."
  [options]
  (authenticate* true true options))
