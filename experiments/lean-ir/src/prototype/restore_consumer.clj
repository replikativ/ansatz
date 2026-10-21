(ns prototype.restore-consumer
  "Restore-only compatibility consumer of unchanged checkpoint wire/manifest data.
   Producer preparation and loaded consumer implementation are separate identities.
   An external manifest pin authorizes restoration, never Java kernel validity."
  (:require [clojure.java.io :as io]
            [clojure.data.json :as json]
            [clojure.set :as set]
            [prototype.checkpoint-wire :as wire]
            [prototype.machine :as m]
            [prototype.module-store :as store]
            [prototype.native-heap :as native-heap]
            [prototype.eval-const :as eval]
            [prototype.import-ir :as ir]
            [prototype.runtime-abi :as abi]
            [prototype.raw-interop :as raw]
            [prototype.globals-consumer-factory :as factory]
            [prototype.globals-consumer-profile :as compatibility])
  (:import [java.io DataInputStream DataOutputStream BufferedInputStream BufferedOutputStream]
           [java.nio.file Files StandardCopyOption StandardOpenOption]
           [java.nio.channels FileChannel]
           [java.security MessageDigest DigestInputStream DigestOutputStream]))

(def format-id "ansatz-hosted-finalizer-checkpoint/1")
(def pinned-build {:lean-version "4.33.1" :lean-commit "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
                   :target "x86_64-unknown-linux-gnu" :word-bits 64})
(def max-counts {:functions 2000000 :heap 5000000 :globals 1000000 :imported-declarations 1000000})
(def state-keys
  #{:status :result :body :locals :joins :frames :next-id :events :stats
    :initialized-modules :initializing? :initialization-scope :heartbeat-allocation-offset
    :environment :runtime-build :runtime-build-overrides :sharecommon-profile
    :entropy :stdio-runtime :task-runtime :kernel-environments :source-modules :source-regions :source-import-prefixes})
(def inactive #{:body :locals :joins :frames :result})
(def authority-keys #{:functions :imported-declarations :imported-catalogue-manifests})
(def node-keys
  #{:kind :tag :fields :rc :function :layout :scalar-bytes :bytes :values :integer :text :utf8-bytes
    :native-object-bytes :native-source-id :native-capacity :native-byte-size :native-utf8-length :element-bytes
    :thunk-state :task-state :task-kind :queued? :sync? :priority :keep-alive? :cancelled? :thread-key :mutex-state})
(def node-kinds #{:ctor :closure :array :ref :task :byte-array :float-array :thunk :promise :string :mpz :scalar-array :mutex})
(defn- natural? [x] (and (integer? x) (<= 0 x Long/MAX_VALUE)))
(defn- keys! [value allowed label]
  (wire/check (and (map? value) (set/subset? (set (keys value)) allowed)) (str "Unsupported " label " fields")))
(defn- exact! [value expected label]
  (wire/check (and (map? value) (= expected (set (keys value)))) (str "Invalid " label " fields")))
(defn- counts [world]
  {:functions (count (:functions world)) :heap (count (:heap world)) :globals (count (:globals world))
   :imported-declarations (count (get-in world [:eval-const-authorizations :imported-declarations]))})
(defn- counts! [value]
  (exact! value (set (keys max-counts)) "counts")
  (doseq [[k n] value] (wire/check (and (natural? n) (<= n (get max-counts k))) "Checkpoint count exceeds profile limit")))
(defn- end-id [base size]
  (wire/check (and (natural? base) (natural? size) (pos? size) (<= base (- Long/MAX_VALUE size))) "Invalid native range")
  (+ base size))
(defn- ranges! [recipes next-id heap]
  (wire/check (natural? next-id) "Invalid next-id")
  (wire/check (= (count recipes) (count (set (map :id recipes)))) "Duplicate resource IDs")
  (let [ranges (sort-by first (map (fn [{:keys [base size]}] [base (end-id base size)]) recipes))]
    (doseq [[[a b] [c d]] (partition 2 1 ranges)] (wire/check (<= b c) "Overlapping native ranges"))
    (doseq [[a b] ranges] (wire/check (<= b next-id) "Native range exceeds next-id"))
    (doseq [id (keys heap)]
      (wire/check (and (natural? id) (< id next-id)) "Invalid overlay ID")
      (wire/check (not-any? (fn [[a b]] (<= a id (dec b))) ranges) "Overlay shadows native source"))
    ranges))
(defn- live-id? [world ranges id]
  (and (natural? id) (or (contains? (:heap world) id) (some (fn [[a b]] (<= a id (dec b))) ranges))))
(defn- values! [root world ranges live?]
  ;; Iterative whitelist/reference walk, including metadata. Native range checks
  ;; never enumerate backing nodes. Inactive registers may retain dead Ref IDs.
  (loop [pending [root]]
    (when (seq pending)
      (let [x (peek pending) pending (pop pending)
            pending (if-let [md (meta x)] (conj pending md) pending)]
        (cond
          (m/ref? x) (do (wire/check (and (natural? (:id x)) (or (not live?) (live-id? world ranges (:id x)))) "Dangling guest reference")
                         (recur pending))
          (map? x) (recur (reduce-kv (fn [out k v] (conj out k v)) pending x))
          (coll? x) (recur (into pending x))
          :else (recur pending))))))
(defn- quiescent! [world]
  (when-let [tasks (:task-runtime world)]
    (keys! tasks #{:queue :active :heartbeats} "task runtime")
    (wire/check (and (vector? (:queue tasks)) (empty? (:queue tasks))
                     (vector? (:active tasks)) (empty? (:active tasks))) "Unfinished task scheduler")
    (when-let [h (:heartbeats tasks)]
      (exact! h #{:thread :mark :counts} "heartbeat")
      (wire/check (and (= :main (:thread h)) (natural? (:mark h)) (map? (:counts h))) "Unsupported heartbeat state")))
  (when-let [stdio (:stdio-runtime world)]
    (keys! stdio #{:defaults :threads} "stdio runtime")
    (wire/check (and (map? (:defaults stdio))
                     (or (not (contains? stdio :threads)) (map? (:threads stdio))))
                "Unsupported stdio state")
    (doseq [streams (cons (:defaults stdio) (vals (:threads stdio)))]
      (keys! streams #{:stdin :stdout :stderr} "stdio streams")
      (doseq [ref (vals streams)] (wire/check (m/ref? ref) "Non-guest stdio handle"))))
  (when-let [entropy (:entropy world)]
    (exact! entropy #{:bytes :position} "entropy")
    (wire/check (and (vector? (:bytes entropy)) (natural? (:position entropy))
                     (<= (:position entropy) (count (:bytes entropy)))
                     (every? #(and (integer? %) (<= 0 % 255)) (:bytes entropy))) "Unsupported entropy state")))
(defn- node! [world id node]
  (keys! node node-keys "heap node")
  (wire/check (and (contains? node-kinds (:kind node)) (natural? (:rc node)) (vector? (:fields node))) "Unsupported heap node")
  (case (:kind node)
    :closure (wire/check (contains? (:functions world) (:function node)) "Unlinked heap closure")
    :task (wire/check (and (or (= :ready (:task-state node))
                              (and (nil? (:task-state node)) (= 1 (count (:fields node)))))
                          (= 1 (count (:fields node))) (not (:queued? node))) "Unfinished task object")
    :thunk (wire/check (and (contains? #{:ready :pending} (:thunk-state node)) (= 1 (count (:fields node)))) "In-flight thunk")
    :mutex (wire/check (and (= :unlocked (:mutex-state node)) (empty? (:fields node))) "Unsupported mutex state")
    :promise (let [task (m/node world (first (:fields node)))]
               (wire/check (and (= 1 (count (:fields node))) (= :task (:kind task))
                                (= :ready (:task-state task))) "Unfinished promise"))
    nil))
(defn- state-of [world] (apply dissoc world [:functions :heap :globals :native-imports :eval-const-authorizations]))
(defn- world! [world recipes roots]
  ;; These containers are partitioned/reconstructed by the wire format rather
  ;; than emitted as values. v1 must not silently discard even empty metadata.
  (doseq [[path value] [[[:functions] (:functions world)]
                       [[:heap] (:heap world)] [[:globals] (:globals world)]
                       [[:native-imports] (:native-imports world)]
                       [[:eval-const-authorizations] (:eval-const-authorizations world)]
                       [[:eval-const-authorizations :functions]
                        (get-in world [:eval-const-authorizations :functions])]
                       [[:eval-const-authorizations :imported-declarations]
                        (get-in world [:eval-const-authorizations :imported-declarations])]]]
    (wire/check (nil? (meta value)) (str "Metadata on partitioned checkpoint container: " path)))
  (keys! (state-of world) state-keys "world")
  (wire/check (and (= :done (:status world)) (empty? (:frames world)) (nil? (:host-request world))
                   (not (:initializing? world)) (not (:initialization-scope world))) "Only idle completed finalizer state is supported")
  (doseq [k [:functions :heap :globals]] (wire/check (map? (get world k)) "Missing world table"))
  (counts! (counts world))
  (doseq [key [:kernel-environments :source-modules :source-regions :source-import-prefixes]]
    (wire/check (empty? (get world key)) "Checked authority/source publications are outside pre-check profile"))
  (keys! (or (:eval-const-authorizations world) {}) authority-keys "executable authority")
  (let [ranges (ranges! recipes (:next-id world) (:heap world))]
    (quiescent! world)
    (doseq [[name f] (:functions world)]
      (wire/check (and (vector? name) (map? f) (vector? (:params f)) (vector? (:body f))) "Invalid executable")
      (wire/wire-value [name f]) (values! [name f] world ranges true))
    (doseq [[id node] (:heap world)] (node! world id node) (wire/wire-value node) (values! node world ranges true))
    (doseq [[name entry] (:globals world)]
      (exact! entry #{:status :value} "global") (wire/check (= :ready (:status entry)) "Incomplete global initializer")
      (wire/wire-value [name entry]) (values! [name entry] world ranges true))
    (let [state (state-of world)]
      (wire/wire-value state)
      (values! (apply dissoc state inactive) world ranges true)
      (values! (select-keys state inactive) world ranges false))
    (exact! roots #{:io-result} "application roots")
    (let [value (:io-result roots) node (when (m/ref? value) (m/node world value))
          environment (first (:fields node))]
      (wire/check (and (= value (:result world)) (= :ctor (:kind node)) (= 0 (:tag node))
                       (= 1 (count (:fields node))) (m/ref? environment)) "Expected owned successful finalizer IO.Result")
      (m/node world environment)))
  world)

(defn readiness
  "Bounded diagnostics, never serialization permission. Does not walk function bodies."
  [event]
  (let [w (:state event)]
    {:event-status (:status event) :world-status (:status w) :world-keys (set (keys w))
     :counts (counts w) :authority-keys (set (keys (:eval-const-authorizations w)))
     :kernel-associations (count (:kernel-environments w))
     :task-runtime-keys (set (keys (:task-runtime w)))
     :task-queue-count (count (get-in w [:task-runtime :queue])) :task-active-count (count (get-in w [:task-runtime :active]))
     :stdio-keys (set (keys (:stdio-runtime w))) :entropy-keys (set (keys (:entropy w)))
     :node-shapes (reduce (fn [out node] (update out (:kind node) (fnil set/union #{}) (set (keys node)))) {} (vals (:heap w)))
     :task-states (frequencies (map #(select-keys % [:kind :task-state :thunk-state :queued?])
                                  (filter #(contains? #{:task :thunk :promise} (:kind %)) (vals (:heap w)))))
     :native-ranges (mapv (fn [s] {:base (:base s) :size (:size s) :digest (:digest s)}) (:native-imports w))}))

(defn- preparation! [preparation]
  (exact! preparation #{:factory-id :implementation-sha256 :catalogue-recipe :kernel-policy :trusted-roots} "preparation")
  (wire/check (and (string? (:factory-id preparation)) (seq (:factory-id preparation))
                   (wire/hash? (:implementation-sha256 preparation)) (map? (:catalogue-recipe preparation))
                   (map? (:kernel-policy preparation)) (vector? (:trusted-roots preparation))
                   (seq (:trusted-roots preparation))) "Incomplete explicit preparation identity")
  (wire/wire-value preparation))
(defn- read-descriptor [path sha]
  (let [bytes (wire/read-file-bytes path wire/max-row-bytes)]
    (wire/check (and (wire/hash? sha) (= sha (wire/sha256 bytes))) "Resource descriptor hash mismatch")
    (json/read-str (wire/utf8-string bytes) :key-fn keyword)))
(defn- read-row [catalogue name]
  (if-let [read! (:read-declaration catalogue)] (read! name) (get-in catalogue [:declarations name])))
(defn- authorization! [world prepared-functions catalogue bindings trusted-roots]
  ;; Rebuild imported additions from canonical authenticated rows, without
  ;; running them. Synthetic global wrappers come from the ordinary linker.
  (let [a (or (:eval-const-authorizations world) {}) imported (or (:functions a) {}) rows (or (:imported-declarations a) {})]
    (keys! a authority-keys "executable authority")
    (doseq [[name function] prepared-functions]
      (wire/check (identical? function (get-in world [:functions name])) "Prepared executable identity drift"))
    (doseq [[name function] imported]
      (wire/check (identical? function (get-in world [:functions name])) "Imported executable identity drift"))
    (wire/check (= (set (keys (:functions world))) (set/union (set (keys prepared-functions)) (set (keys imported))))
                "Unclassified executable authority")
    (when (contains? a :imported-catalogue-manifests)
      (wire/check (wire/same-data? (:manifests catalogue) (:imported-catalogue-manifests a)) "Imported manifest drift"))
    (doseq [[name row] rows]
      (wire/check (and (= name (:name row)) (wire/same-data? row (read-row catalogue name))) "Counterfeit imported row"))
    (let [lower #(if (contains? bindings (some-> % :ir :extern abi/symbol-for))
                   (raw/lower bindings %) (abi/lower-deferred-catalogue catalogue %))
          rebuilt (ir/load-closure catalogue (vec (keys rows)) lower {:existing-functions prepared-functions})]
      (doseq [[name function] imported]
        (wire/check (wire/same-data? function (get rebuilt name)) "Imported executable differs from authenticated lowering")))
    (eval/validate-executables! world prepared-functions trusted-roots)
    true))

(defn- frame-kind! [row kind length]
  (wire/check (and (vector? row) (= length (count row)) (= kind (first row))) "Unexpected/truncated checkpoint row") row)
(defn- parse-data [input expected-counts]
  (let [names (java.util.HashMap.) next! #(wire/share-name-prefixes names (wire/read-frame! input))
        header (second (frame-kind! (next!) :header 2))]
    (exact! header #{:format :counts :authority-present? :authority-keys} "stream header")
    (wire/check (and (= format-id (:format header)) (= expected-counts (:counts header))
                     (boolean? (:authority-present? header)) (set? (:authority-keys header))
                     (set/subset? (:authority-keys header) authority-keys)) "Stream header mismatch")
    (let [functions (loop [n (:functions expected-counts) functions (transient {}) prepared (transient {}) imported (transient {})]
                      (if (zero? n) {:functions (persistent! functions) :prepared (persistent! prepared) :imported (persistent! imported)}
                        (let [[_ name flags f] (frame-kind! (next!) :function 4)]
                          (wire/check (and (set? flags) (seq flags) (set/subset? flags #{:prepared :imported})
                                           (not (contains? functions name))) "Duplicate/unauthorized function row")
                          (recur (dec n) (assoc! functions name f)
                                 (if (contains? flags :prepared) (assoc! prepared name f) prepared)
                                 (if (contains? flags :imported) (assoc! imported name f) imported)))))
          table (fn [kind n]
                  (loop [n n out (transient {})]
                    (if (zero? n) (persistent! out)
                      (let [[_ k v] (frame-kind! (next!) kind 3)]
                        (wire/check (not (contains? out k)) "Duplicate checkpoint table entry")
                        (recur (dec n) (assoc! out k v))))))
          heap (table :heap (:heap expected-counts)) globals (table :global (:globals expected-counts))
          declarations (table :imported-declaration (:imported-declarations expected-counts))
          authority (second (frame-kind! (next!) :authority 2))
          _ (keys! authority #{:imported-catalogue-manifests} "authority metadata")
          state (second (frame-kind! (next!) :state 2))
          _ (keys! state state-keys "serialized state")
          _ (wire/check (= expected-counts (second (frame-kind! (next!) :end 2))) "Checkpoint trailer mismatch")
          _ (wire/check (= -1 (.read input)) "Trailing checkpoint data")
          _ (wire/check (= (contains? authority :imported-catalogue-manifests)
                            (contains? (:authority-keys header) :imported-catalogue-manifests)) "Authority manifest presence mismatch")
          _ (wire/check (or (contains? (:authority-keys header) :functions) (empty? (:imported functions))) "Undeclared function authority")
          _ (wire/check (or (contains? (:authority-keys header) :imported-declarations) (empty? declarations)) "Undeclared imported rows")
          a (cond-> authority
              (contains? (:authority-keys header) :functions) (assoc :functions (:imported functions))
              (contains? (:authority-keys header) :imported-declarations) (assoc :imported-declarations declarations))
          world (cond-> (assoc state :functions (:functions functions) :heap heap :globals globals)
                  (:authority-present? header) (assoc :eval-const-authorizations a))]
      (wire/check (or (:authority-present? header) (empty? (:authority-keys header))) "Unexpected absent authority ledger")
      (.clear names)
      {:world world :prepared-functions (:prepared functions)})))

(deftype ResourceLease [sources]
  java.io.Closeable
  (close [_]
    (let [[opened _] (swap-vals! sources (constantly nil)) failures (atom [])]
      (doseq [source opened]
        (try (.close ^java.io.Closeable source) (catch Throwable e (swap! failures conj e))))
      (when-let [e (first @failures)]
        (doseq [other (rest @failures) :when (not (identical? e other))] (.addSuppressed ^Throwable e other))
        (throw e)))))
(defn- private-index-sha256 [^java.io.RandomAccessFile index]
  ;; Hash the returned Store's already pinned private inode, not its mutable
  ;; descriptor path. Restore the cursor even when verification fails.
  (locking index
    (let [position (.getFilePointer index) digest (MessageDigest/getInstance "SHA-256")
          buffer (byte-array 65536)]
      (try
        (.seek index 0)
        (loop [] (let [n (.read index buffer)]
                   (when (pos? n) (.update digest buffer 0 n) (recur))))
        (.formatHex (java.util.HexFormat/of) (.digest digest))
        (finally (.seek index position))))))
(defn- reopened-source! [source recipe descriptor]
  ;; open-verified currently hashes the descriptor path before parsing it again.
  ;; Its returned object must agree with OUR captured authenticated descriptor;
  ;; never infer agreement from the input filename or declared digest alone.
  (wire/check (and (= "prototype.module_store.Store" (.getName (class source)))
                   (false? @(:closed source))
                   (= (:base recipe) (:base source)) (= (:size recipe) (:size source))
                   (= (:source-sha256 recipe) (:digest source))
                   (= (:manifest descriptor) (:manifest source))
                   (= (:source-bytes recipe) (:maximum-bytes source)
                      (.size ^java.nio.channels.FileChannel (:channel source)))
                   (= (:index-bytes recipe) (.length ^java.io.RandomAccessFile (:index source)))
                   (= (:index-sha256 recipe) (private-index-sha256 (:index source))))
              "Reopened Store differs from authenticated checkpoint resource")
  source)
(defn- reopen! [recipe resolver]
  (exact! recipe #{:id :descriptor-sha256 :source-sha256 :index-sha256 :source-bytes :index-bytes :base :size} "resource recipe")
  (let [locations (resolver (:id recipe))
        _ (exact! locations #{:descriptor-path :source-path} "resolved resource location")
        d (read-descriptor (:descriptor-path locations) (:descriptor-sha256 recipe))]
    (wire/check (and (= (:source-sha256 recipe) (:sourceSha256 d)) (= (:index-sha256 recipe) (:indexSha256 d))
                     (= (:source-bytes recipe) (:sourceBytes d)) (= (:index-bytes recipe) (:indexBytes d))
                     (= (:size recipe) (:nodes d))) "Resource descriptor recipe drift")
    ;; Reservation world counter changes are discarded, not applied to snapshot.
    (let [source (:source (store/open-verified (assoc (m/world {}) :status :done :next-id (:base recipe))
                                             (:descriptor-path locations) (:descriptor-sha256 recipe)
                                             {:source-path (:source-path locations) :cache-size 1024}))]
      ;; This source has not yet reached the loader lease. Acquire/validate it
      ;; locally and close it exactly once on any identity rejection.
      (try (reopened-source! source recipe d)
           (catch Throwable error
             (try (.close ^java.io.Closeable source)
                  (catch Throwable cleanup
                    (when-not (identical? error cleanup) (.addSuppressed error cleanup))))
             (throw error))))))
(defn- factory-profile! [description producer consumer]
  (let [profile (:compatibility-profile description)]
    (wire/check (and (wire/same-data? producer (:producer-preparation description))
                     (= consumer (:consumer-implementation-sha256 description))
                     (contains? #{compatibility/profile-id compatibility/reconstruction-profile-id
                                  compatibility/runtime-ops-reconstruction-profile-id
                                  compatibility/heap-net-dirty-reconstruction-profile-id} profile))
                "Restore consumer capability identity mismatch")
    profile))
(defn- factory-result! [produced producer consumer compatibility-profile manifest]
  (exact! produced #{:producer-preparation :consumer-implementation-sha256 :compatibility-profile
                     :catalogue :bindings} "consumer factory result")
  (wire/check (and (wire/same-data? (:producer-preparation produced) producer)
                   (= (:consumer-implementation-sha256 produced) consumer)
                   (= compatibility-profile (:compatibility-profile produced))
                   (= (:binding-signatures manifest)
                      (into {} (map (fn [[symbol binding]] [symbol (:signature binding)])) (:bindings produced))))
              "Consumer factory identity/signature mismatch")
  produced)
(defn restore!
  "Restore privately, reopen verified resources at saved bases, canonicalize ONLY
   recorded prepared/imported identities and invoke the authenticated closed factory.
   Factory gets canonical function objects and explicit pinned recipe; it must not
   execute guest code/initializers or substitute code. Returns world/session/IO
   owner plus explicit shared resource lease. Kernel checking remains mandatory."
  [manifest-path {:keys [expected-manifest-sha256 producer-preparation consumer-implementation-sha256
                         factory resolve-resource backend fuel]
                  :as options}]
  (wire/worker
    (fn []
      (exact! options #{:expected-manifest-sha256 :producer-preparation :consumer-implementation-sha256
                        :factory :resolve-resource :backend :fuel} "restore consumer options")
      (preparation! producer-preparation)
      (let [compatibility-profile (factory-profile! (factory/descriptor factory)
                                                    producer-preparation consumer-implementation-sha256)
            _ (wire/check (and (wire/hash? expected-manifest-sha256) (wire/hash? consumer-implementation-sha256)
                       (fn? resolve-resource) (= :mutable backend)
                       (integer? fuel) (pos? fuel) (<= fuel Long/MAX_VALUE))
                  "Explicit restore consumer authority/resolver/mutable budget required")
            file (.getAbsoluteFile (io/file manifest-path))
            bytes (wire/read-file-bytes file wire/max-row-bytes)
            _ (wire/check (= expected-manifest-sha256 (wire/sha256 bytes)) "Expected external manifest digest mismatch")
            manifest (wire/decode bytes)
            _ (exact! manifest #{:format :build :preparation :resources :roots :counts :binding-signatures :data} "manifest")
            _ (wire/check (and (= format-id (:format manifest)) (= pinned-build (:build manifest))
                               (wire/same-data? producer-preparation (:preparation manifest))) "Checkpoint build/preparation mismatch")
            _ (counts! (:counts manifest))
            _ (exact! (:data manifest) #{:file :sha256 :bytes} "data descriptor")
            filename (get-in manifest [:data :file])
            _ (wire/check (and (string? filename) (= filename (.getName (io/file filename)))
                               (wire/hash? (get-in manifest [:data :sha256]))
                               (natural? (get-in manifest [:data :bytes]))
                               (vector? (:resources manifest)) (<= (count (:resources manifest)) 16)) "Invalid data/resource descriptor")
            data-file (io/file (.getParentFile file) filename)
            _ (wire/check (= (.length data-file) (get-in manifest [:data :bytes])) "Data size mismatch")
            md (MessageDigest/getInstance "SHA-256")
            parsed (with-open [input (DataInputStream. (DigestInputStream. (BufferedInputStream. (io/input-stream data-file)) md))]
                     (parse-data input (:counts manifest)))
            _ (wire/check (= (.formatHex (java.util.HexFormat/of) (.digest md)) (get-in manifest [:data :sha256])) "Data digest mismatch")
            owned (atom []) lease (ResourceLease. owned)]
        (try
          (doseq [recipe (:resources manifest)] (swap! owned conj (reopen! recipe resolve-resource)))
          (let [world (assoc (:world parsed) :native-imports @owned)
                _ (world! world (:resources manifest) (:roots manifest))
                produced (factory/invoke! factory {:preparation producer-preparation :world world
                                           :functions (:functions world) :prepared-functions (:prepared-functions parsed)
                                           :resources @owned})
                _ (factory-result! produced producer-preparation consumer-implementation-sha256 compatibility-profile manifest)
                _ (authorization! world (:prepared-functions parsed) (:catalogue produced) (:bindings produced) (:trusted-roots producer-preparation))
                session (raw/open-functions (:functions world) (:bindings produced) {:backend backend :fuel fuel})]
            {:status :restored-precheck :world world :session session :io-result (get-in manifest [:roots :io-result])
             :roots (:roots manifest) :catalogue (:catalogue produced) :resource-lease lease
             :trusted-functions (:prepared-functions parsed) :trusted-bindings (:bindings produced)
             :producer-preparation producer-preparation :consumer-implementation-sha256 consumer-implementation-sha256
             :compatibility-profile compatibility-profile
             :manifest-sha256 expected-manifest-sha256 :strictly-checked? false})
          (catch Throwable e
            (try (.close ^java.io.Closeable lease) (catch Throwable close-error
                                                     (when-not (identical? e close-error) (.addSuppressed e close-error))))
            (throw e)))))))
