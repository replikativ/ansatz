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

(def coherent-frontend-profile-id "ansatz-producer50f-coherent-frontend-consumer/1")
(def profile-id "ansatz-producer50f-globals-overlay-consumer/2")
(def reconstruction-profile-id "ansatz-producer50f-reconstruction-consumer/1")
(def runtime-ops-reconstruction-profile-id "ansatz-producer50f-runtime-ops-reconstruction-consumer/1")
(def heap-net-dirty-reconstruction-profile-id "ansatz-producer50f-heap-net-dirty-reconstruction-consumer/1")
(def source-graph-reconstruction-profile-id "ansatz-producer50f-source-graph-reconstruction-consumer/1")
(def source-graph-frontend-reconstruction-profile-id "ansatz-producer50f-source-graph-frontend-reconstruction-consumer/1")
(def hosted-application-profile-id "ansatz-producer50f-hosted-application-consumer/1")
(def hosted-application-control-profile-id "ansatz-producer50f-hosted-application-consumer/2")
;; New fixed member domain. The externally accepted inventory pins exact bytes
;; of added sources, just as for the existing added factory/profile resources.
(def hosted-application-added-inputs
  {"prototype/binding_dependencies.clj" :host-source
   "prototype/source_inductive_preparation.clj" :host-source
   "prototype/typed_eio.clj" :host-source})
;; Reviewed substitutions of original producer members. Older profiles retain
;; their old bytes; the resident prefix and test runner were already explicit
;; reconstruction additions/substitutions pinned by the external whole digest.
(def hosted-application-substitutions
  {"prototype/kernel_host.clj" "f27e6703d6e1982b2cab2604dff1fa4560698a6f484c1031fdf790a32cff6b6a"
   "prototype/raw_interop.clj" "fa37ecfb46c8cc7f7cbe44c9505a922bba269781082e050fa1f9bf778329e5fc"
   "prototype/resident_frontend.clj" "3d78b84820e3a1709b5bc3b10aa4ff68e3fb3a4de2b482793d5a0732c4223040"
   "src-java/ansatz/kernel/Expr.java" "e3dd622b8030643ec9030512e2485cdc388371216a69484e83821b91f53a7b36"
   "src-java/ansatz/kernel/ExprStore.java" "4f8769fa1588c5a141adbc1a411a5005981da38b69b991dc018250fb54f95960"
   "src-java/ansatz/kernel/TypeChecker.java" "c89eac2d36aa8032856023d51dd66618d4820190deba511eac5fdb6b32cd18ba"
   "ansatz/kernel/Expr.class" "2282f4f346cf4ac50a3dbcc59c85ef83241caceca83a185b6d1970f84b07df8f"
   "ansatz/kernel/TypeChecker.class" "3df16726bdfca973861b0e4f53787b9da53ad3ebc73e314f3900351820bc9677"})
(def hosted-application-control-substitutions
  (assoc hosted-application-substitutions
         "prototype/guest_encoding.clj" "88279ee0dc6447ebfe5676fba6227ab9a2fd6e950a150c707f649bb15640a265"))
(defn- application-substitutions [revision]
  (case revision
    nil {}
    :v1 hosted-application-substitutions
    :v2 hosted-application-control-substitutions
    (throw (ex-info "Unknown hosted application revision" {}))))
(defn- application-profile [revision]
  (case revision
    :v1 hosted-application-profile-id
    :v2 hosted-application-control-profile-id
    (throw (ex-info "Unknown hosted application revision" {}))))
;; Exact independently reviewed frontend protocol checkpoint/session fix.
(def source-graph-frontend-sha256 "58e385c7d06b269981be47ee9c976d66a446a29d6b18ed3f8d319595d1901c79")
(def source-graph-import-sha256 "c329a591447aa37d40030f382eaeec21ca1e94d06367c5919f5248ad4668436f")
(def source-graph-plan-sha256 "8a8d9a59002ecd5b440af478589874cbd7b7cf46fad8e834b13349b3971540ee")
(def heap-net-dirty-source-sha256 "e89abd25eaa1815be7fc2a5136ee06e9a6b9d784958652ae6acbde9c4617c75a")
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
  [reconstruction? runtime-ops? heap-net-dirty? source-graph? graph-frontend? hosted-application-revision recipe inventory expected]
  (wire/check (and (wire/hash? expected) (= expected (consumer-identity inventory)))
              "Consumer implementation digest mismatch")
  (let [substitutions (application-substitutions hosted-application-revision)
        original (:build-inventory recipe)
        by-id (into {} (map (juxt :id identity)) inventory)
        baseline (remove #(contains? excluded-producer-sources (:id %)) original)
        required (merge (into {} (map (juxt :id :kind)) baseline) added-inputs
                        (when reconstruction? {"prototype/resident_init_prefix.clj" :host-source})
                        (when source-graph? {"prototype/source_graph_plan.clj" :host-source})
                        (when hosted-application-revision hosted-application-added-inputs))]
    (wire/check (= (set (keys required)) (set (keys by-id))) "Consumer selected-input inventory drift")
    (doseq [[id kind] required]
      (wire/check (= kind (get-in by-id [id :kind])) "Consumer input role drift"))
    (doseq [{:keys [id sha256]} baseline
            :when (and (not= id "prototype/mutable.clj") (not (contains? program-substitutions id))
                       (not (and heap-net-dirty? (= id "src-java/ansatz/runtime/HeapOverlay.java")))
                       (not (and source-graph? (= id "prototype/source_import.clj")))
                       (not (and graph-frontend? (= id "prototype/frontend.clj")))
                       (not (and hosted-application-revision (contains? substitutions id)))
                       (not (and reconstruction? (contains? reconstruction-substitutions id))))]
      (wire/check (= sha256 (get-in by-id [id :sha256])) "Unapproved consumer substitution"))
    (when hosted-application-revision
      (doseq [[id sha256] substitutions]
        (wire/check (= sha256 (get-in by-id [id :sha256]))
                    "Unapproved hosted application source substitution")))
    (doseq [[id sha256] program-substitutions]
      (wire/check (= sha256 (get-in by-id [id :sha256])) "Unapproved program sizing implementation"))
    (wire/check (= (if runtime-ops? runtime-ops-mutable-sha256 mutable-sha256)
                   (get-in by-id ["prototype/mutable.clj" :sha256]))
                "Unapproved mutable consumer implementation")
    (wire/check (= globals-source-sha256 (get-in by-id ["src-java/ansatz/runtime/GlobalsOverlay.java" :sha256]))
                "Unapproved globals overlay source")
    (when heap-net-dirty?
      (wire/check (= heap-net-dirty-source-sha256
                     (get-in by-id ["src-java/ansatz/runtime/HeapOverlay.java" :sha256]))
                  "Unapproved net-dirty heap overlay source"))
    (when source-graph?
      (doseq [[id sha256] {"prototype/source_import.clj" source-graph-import-sha256
                           "prototype/source_graph_plan.clj" source-graph-plan-sha256}]
        (wire/check (= sha256 (get-in by-id [id :sha256]))
                    "Unapproved source graph consumer source")))
    (when graph-frontend?
      (wire/check (and (wire/hash? source-graph-frontend-sha256)
                       (= source-graph-frontend-sha256 (get-in by-id ["prototype/frontend.clj" :sha256])))
                  "Unapproved source graph frontend consumer source"))
    inventory))
(defn validate-inventory!
  "Validate the original closed globals inventory without reconstruction deltas."
  [recipe inventory expected]
  (validate-inventory* false false false false false nil recipe inventory expected))
(defn validate-reconstruction-inventory!
  "Validate the closed reconstruction delta. The external digest pins exact bytes
   of the three reviewed baseline substitutions and added resident prefix source."
  [recipe inventory expected]
  (validate-inventory* true false false false false nil recipe inventory expected))
(defn validate-runtime-ops-reconstruction-inventory!
  "Validate the closed reconstruction inventory with the separately pinned ops-table
   mutable implementation. Original globals/reconstruction contracts remain exact."
  [recipe inventory expected]
  (validate-inventory* true true false false false nil recipe inventory expected))
(defn validate-heap-net-dirty-reconstruction-inventory!
  "Validate only the separately named net-dirty heap consumer: exact reviewed heap
   source plus the existing ops/reconstruction deltas. No caller substitutions."
  [recipe inventory expected]
  (validate-inventory* true true true false false nil recipe inventory expected))
(defn validate-source-graph-reconstruction-inventory!
  "Validate the fifth closed graph consumer: exact source-import/planner bytes,
   alongside the unchanged fourth heap/ops/reconstruction prerequisites."
  [recipe inventory expected]
  (validate-inventory* true true true true false nil recipe inventory expected))
(defn validate-source-graph-frontend-reconstruction-inventory!
  "Validate the sixth fixed graph frontend protocol consumer. Inherits the exact
   fifth257 input roles/pins and permits only its independently frozen frontend."
  [recipe inventory expected]
  (validate-inventory* true true true true true nil recipe inventory expected))
(defn validate-hosted-application-inventory!
  "Validate only the seventh fixed member domain: sixth graph prerequisites,
   three explicit application sources and reviewed helper/disposal substitutions.
   All six earlier contracts keep their exact inventories and pins."
  [recipe inventory expected]
  (validate-inventory* true true true true true :v1 recipe inventory expected))

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
  [reconstruction? runtime-ops? heap-net-dirty? source-graph? graph-frontend? hosted-application-revision {:keys [producer-preparation producer-recipe-source consumer-inventory
                                                                                                                  expected-consumer-implementation-sha256 loaded-consumer-implementation-sha256
                                                                                                                  producer-resolve-artifact consumer-resolve-source store-root] :as options}]
  (exact! options option-keys "globals consumer factory options")
  (wire/check (and (fn? producer-resolve-artifact) (fn? consumer-resolve-source)
                   (string? store-root) (seq store-root)
                   (= expected-consumer-implementation-sha256 loaded-consumer-implementation-sha256))
              "Explicit producer/consumer resolvers and fresh loaded-consumer attestation required")
  (let [recipe (producer-recipe! producer-preparation producer-recipe-source)]
    (validate-inventory* reconstruction? runtime-ops? heap-net-dirty? source-graph? graph-frontend? hosted-application-revision recipe consumer-inventory expected-consumer-implementation-sha256)
    (doseq [id excluded-producer-sources]
      (wire/check (and (nil? (io/resource id))
                       (nil? (io/resource (str (subs id 0 (- (count id) 4)) "__init.class"))))
                  "Producer-only legacy source or AOT is available on consumer classpath"))
    (doseq [row consumer-inventory] (authenticate-input! row consumer-resolve-source))
    {:producer-preparation producer-preparation
     :consumer-implementation-sha256 expected-consumer-implementation-sha256
     :compatibility-profile (cond hosted-application-revision (application-profile hosted-application-revision)
                                  graph-frontend? source-graph-frontend-reconstruction-profile-id
                                  source-graph? source-graph-reconstruction-profile-id
                                  heap-net-dirty? heap-net-dirty-reconstruction-profile-id
                                  runtime-ops? runtime-ops-reconstruction-profile-id
                                  reconstruction? reconstruction-profile-id
                                  :else profile-id)}))

(defn authenticate!
  "Authenticate the original closed globals consumer and fresh loaded-code attestation."
  [options]
  (authenticate* false false false false false nil options))
(defn authenticate-reconstruction!
  "Authenticate the separately named closed reconstruction consumer. Same exact
   options and fresh-process loaded-code attestation as authenticate!."
  [options]
  (authenticate* true false false false false nil options))

(defn authenticate-runtime-ops-reconstruction!
  "Authenticate the separately named ops-table reconstruction consumer. Same closed
   options and mandatory fresh-process loaded-code attestation as authenticate!."
  [options]
  (authenticate* true true false false false nil options))

(defn authenticate-heap-net-dirty-reconstruction!
  "Authenticate the distinct net-dirty heap consumer, with the unchanged closed
   option set and mandatory fresh-process external loaded-code attestation."
  [options]
  (authenticate* true true true false false nil options))

(defn authenticate-source-graph-reconstruction!
  "Authenticate only the fifth fixed graph consumer. Same exact option set and
   mandatory fresh-process loaded-code attestation; no graph authority is issued."
  [options]
  (authenticate* true true true true false nil options))

(defn authenticate-source-graph-frontend-reconstruction!
  "Authenticate only the sixth fixed frontend-protocol graph consumer, retaining
   the exact options and fresh-process loaded-code attestation requirements."
  [options]
  (authenticate* true true true true true nil options))

(defn authenticate-hosted-application!
  "Authenticate the seventh fixed application consumer with the same closed
   options and mandatory fresh-process loaded-code attestation."
  [options]
  (authenticate* true true true true true :v1 options))

(defn validate-hosted-application-control-inventory!
  "Validate the separately named /2 control-preserving encoder consumer. The
   /1 inventory and all older policies remain unchanged; no caller overrides."
  [recipe inventory expected]
  (validate-inventory* true true true true true :v2 recipe inventory expected))

(defn authenticate-hosted-application-control!
  "Authenticate only the fixed /2 encoder consumer with the same exact options
   and mandatory fresh-process loaded-code attestation as /1."
  [options]
  (authenticate* true true true true true :v2 options))
