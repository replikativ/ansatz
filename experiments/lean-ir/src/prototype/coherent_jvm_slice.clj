(ns prototype.coherent-jvm-slice
  "Finite fresh mutable-frontend/JVM-application orchestration. Actual live
   associations and independently captured configuration remain authority.
   Returned owners enter private escrow before any observer or assertion."
  (:require [clojure.data.json :as json]
            [prototype.checkpoint-wire :as wire]
            [prototype.coherent-consumer-profile :as profile]
            [prototype.coherent-stage-guards :as guards]
            [prototype.globals-consumer-factory :as factory]
            [prototype.restore-consumer :as restore]
            [prototype.coherent-source-preparation :as source]
            [prototype.coherent-helper-value :as helper]
            [prototype.coherent-owner-ledger :as owners]
            [prototype.resident-preparation :as preparation]
            [prototype.resident-frontend :as resident]
            [prototype.resident-init-prefix :as prefix]
            [prototype.raw-interop :as raw]
            [prototype.typed-extern :as extern]
            [prototype.interop-codec :as codec]
            [prototype.lazy-runtime :as lazy]
            [ansatz.kernel.name :as name]))

(defonce ^:private state (atom nil))
(defonce ^:private ownership (atom {:phase :ready}))
(defn checkpoint "Borrow private canonical owners and failures; never serialize." []
  {:controller @state :ownership @ownership})
(defn boundary-measurements
  "Bounded completed diagnostics, containing no guest owners. Nested spans are
   inclusive; never add them to their parent phases. Missing spans did not finish."
  [] (vec (:boundaries @state)))
(defn- require! [condition message] (wire/check condition message))
(defn- read-input [approved id limit]
  (let [rows (filter #(= id (:id %)) (get-in approved [:manifest :direct-inputs]))]
    (require! (= 1 (count rows)) "Exactly one authenticated direct input required")
    (let [bytes (wire/read-file-bytes ((:resolve-input approved) id) limit)]
      (require! (= (:sha256 (first rows)) (wire/sha256 bytes)) "Captured direct input drift")
      bytes)))
(defn- factory-options [approved]
  (let [producer (wire/decode (read-input approved "producer/preparation" (* 4 1024 1024)))
        recipe (wire/utf8-string (read-input approved "producer/recipe" (* 4 1024 1024)))
        index ((:resolve-input approved) "producer/declaration-index")]
    {:producer-preparation producer :producer-recipe-source recipe
     :producer-resolve-artifact (fn [id] ((:resolve-input approved) (str "producer/" (if (keyword? id) (name id) id))))
     :store-root (-> index .getParentFile .getParentFile .getPath)
     :consumer-inventory (:inventory approved)
     :expected-consumer-implementation-sha256 (:implementation-sha256 approved)
     :loaded-consumer-implementation-sha256 (:implementation-sha256 approved)
     :consumer-resolve-source (fn [id] (if (some #(= id (:id %)) (:inventory approved))
                                       ((:resolve-consumer-source approved) id) ((:resolve-input approved) id)))
     :consumer-contract-source (:contract-source approved)
     :expected-consumer-contract-sha256 (:contract-sha256 approved)}))

(defn construct!
  "Host-only exact authenticated construction. No restore/Source/guest/checking."
  [approved]
  (require! (compare-and-set! state nil {:phase :constructing :bootstrap approved}) "Finite JVM slice is one-shot")
  (try
    (let [options (factory-options approved)
          capability (factory/make-coherent-jvm-application-factory options)
          _ (swap! state assoc :factory capability :options options)
          contract (factory/coherent-contract capability) description (factory/descriptor capability)
          _ (swap! state assoc :approved-contract contract)
          application (get-in contract [:contract :composition :application])
          _ (require! (= profile/jvm-profile-id (:compatibility-profile description) (:compatibility-profile approved))
                      "Bootstrap/actual Factory application profile mismatch")
          _ (require! (= (:execution approved) (get-in application [:execution-roles :frontend])) "Frontend execution policy mismatch")
          _ (source/validate-approved-composition! capability)
          rows (filter #(= "prototype/coherent_jvm_slice.clj" (:id %)) (get-in contract [:contract :composition :controllers]))]
      (require! (and (= 1 (count rows)) (= ["prototype.coherent-jvm-slice/construct!" "prototype.coherent-jvm-slice/run!"]
                                          (:entrypoints (first rows)))) "Exact finite controller entrypoints required")
      (swap! state assoc :phase :constructed :application application :phases [] :corpus [] :effects [])
      (merge (:execution approved)
             {:status :constructed :consumer-contract-sha256 (:sha256 contract)
              :consumer-implementation-sha256 (:consumer-implementation-sha256 description)
              :compatibility-profile (:compatibility-profile description)
              :native-resources-acquired false :guest-executed false :strictly-checked? false}))
    (catch Throwable failure (swap! state assoc :phase :failed :failure failure) (throw failure))))

(defn- own-context! [context prefix]
  (swap! ownership update :contexts (fnil conj []) {:context context :prefix prefix :closed? false})
  (require! (<= (count (:contexts @ownership)) 128) "Finite Context owner bound exceeded")
  context)
(defn- owned-call!
  "Capture every returned owner before validation/metrics. An exception leaves
   unknown partial state unsafe; no automatic retry or lease cleanup."
  [key invoke capture]
  (require! (not (:unsafe-partial? @ownership)) "Earlier owner operation unresolved")
  (swap! ownership assoc :unsafe-partial? true :active-operation key)
  (println (json/write-str {:operation key :status :running})) (flush)
  (let [result (invoke)]
    (swap! ownership assoc :returned-operation {:key key :result result})
    (capture result)
    (swap! ownership #(-> % (assoc :unsafe-partial? false) (dissoc :active-operation :returned-operation)))
    result))

(defn- configuration [prepared]
  {:catalogue (:catalogue prepared) :trusted-functions (:trusted-functions prepared)
   :trusted-bindings (get-in prepared [:support :session :bindings])
   :kernel-helpers (get-in prepared [:support :kernel-helpers])
   :frontend-configuration (:frontend-configuration prepared)})

(defn reopen-application
  "Public-boundary adapter. Configuration is the ORIGINAL independent registry,
   never reconstructed from loaded executable/binding maps. No owner retain.
   The finite controller passes ONE explicit cache to all A/B branches."
  ([context independent execution]
   (reopen-application context independent execution
                       (or (:cache (raw/session-options (:session (resident/snapshot context)))) (lazy/code-cache))))
  ([context independent execution cache]
   (let [before (resident/snapshot context)
         _ (require! (and (= :mutable (get-in before [:session :backend]))
                          (= execution (get-in profile/execution-roles [:application]))
                          (instance? clojure.lang.Atom cache) (map? @cache))
                     "Only the approved mutable-to-JVM application transition/cache is supported")
         session (raw/open-functions (get-in before [:world :functions]) (get-in before [:session :bindings])
                                     (assoc execution :cache cache))]
     (resident/adopt-prepared (assoc before :session session) independent))))

(defn- measurement [f]
  (let [bean ^com.sun.management.ThreadMXBean (java.lang.management.ManagementFactory/getThreadMXBean)
        tid (.getId (Thread/currentThread))
        supported? (and (.isCurrentThreadCpuTimeSupported bean) (.isThreadCpuTimeEnabled bean)
                        (.isThreadAllocatedMemorySupported bean) (.isThreadAllocatedMemoryEnabled bean))
        cpu (when supported? (.getCurrentThreadCpuTime bean))
        bytes (when supported? (.getThreadAllocatedBytes bean tid)) wall (System/nanoTime)
        result (f)
        end-wall (System/nanoTime)
        end-cpu (when supported? (.getCurrentThreadCpuTime bean))
        end-bytes (when supported? (.getThreadAllocatedBytes bean tid))]
    [result {:wall-ns (- end-wall wall)
             :cpu-ns (when supported? (- end-cpu cpu))
             :allocated-bytes (when supported? (- end-bytes bytes))}]))
(defn- boundary!
  "Completed inclusive span. CPU/allocation cover this caller thread only.
   Owner-returning operations must escrow their result INSIDE f. No guest or
   owner values enter this bounded diagnostic record. Nested spans overlap."
  [operation f]
  (let [[result metrics] (measurement f)]
    ;; Pure owner-ledger models can call cleanup without constructing a run.
    ;; Diagnostics must not manufacture controller state or consume its claim.
    (when (some? @state)
      (swap! state update :boundaries
             (fn [rows]
               (let [rows (or rows [])]
                 (require! (< (count rows) 512) "Finite boundary observation bound exceeded")
                 (conj rows {:operation operation :call (:active-call @state)
                             :thread (.getName (Thread/currentThread))
                             :scope :caller-thread :inclusive true :metrics metrics})))))
    result))
(defn- phase! [stage measured]
  (let [index (count (:phases @state))]
    (require! (= stage (nth profile/jvm-stages index nil)) "Finite stage duplicate/order mismatch")
    (let [summary (assoc measured :stage stage)]
      (swap! state update :phases conj summary)
      (println (json/write-str {:stage stage :status :passed :measurement measured})) (flush))))
(defn- perform! [stage f]
  (println (json/write-str {:stage stage :status :running})) (flush)
  (let [[result measured] (measurement f)] (phase! stage measured) result))

(defn- restore-and-prepare! []
  (println (json/write-str {:stage :fresh-init :operation :restore :status :running})) (flush)
  (let [{:keys [bootstrap factory options]} @state
        [restored restore-time]
        (measurement
          #(owned-call! :restore
             (fn [] (restore/restore! ((:resolve-input bootstrap) "checkpoint/manifest")
                      {:expected-manifest-sha256 (:sha256 (first (filter (fn [r] (= "checkpoint/manifest" (:id r)))
                                                                        (get-in bootstrap [:manifest :direct-inputs]))))
                       :producer-preparation (:producer-preparation options)
                       :consumer-implementation-sha256 (:implementation-sha256 bootstrap) :factory factory
                       :backend :mutable :fuel (get-in bootstrap [:execution :fuel])
                       :resolve-resource (fn [id] {:descriptor-path ((:resolve-input bootstrap) (str "resource/" id "/descriptor"))
                                                   :source-path ((:resolve-input bootstrap) (str "resource/" id "/source"))})}))
             (fn [r] (swap! state assoc :restored r))))
        _ (require! (= 1 (get-in restored [:session :compile-threshold])) "Archive session threshold differs from frontend role")
        restored (assoc restored :session (raw/open-functions (get-in restored [:world :functions])
                                                             (:trusted-bindings restored) (:execution bootstrap)))
        _ (swap! state assoc :restored restored :phase :checking)
        _ (do (println (json/write-str {:stage :fresh-init :operation :strict-init :status :running})) (flush))
        [checked check-time]
        (measurement
          #(let [branch (boundary! :bootstrap-support
                          (fn []
                            (println (json/write-str {:operation :bootstrap-support :status :running})) (flush)
                            (let [branch (source/prepare-bootstrap-support factory restored (:resolve-input bootstrap))]
                              (swap! state assoc :bootstrap-support branch) branch)))
                 checked (boundary! :strict-admission
                           (fn []
                             (println (json/write-str {:operation :strict-admission :status :running})) (flush)
                             (let [checked (source/check-restored! {:factory factory :restored (:candidate branch) :support (:support branch)})]
                               (swap! state assoc :checked checked) checked)))]
             checked))]
    (phase! :fresh-init {:measurement :separate-segments :segments [{:phase :restore :metrics restore-time}
                                                                  {:phase :strict-init :metrics check-time}]})
    (println (json/write-str {:stage :graph-helpers :operation :source-preparation :status :running})) (flush)
    (let [[summary measured] (measurement #(source/prepare! {:factory factory :checked checked
                                                           :support (get-in @state [:bootstrap-support :support])
                                                           :resolve-artifact (:resolve-input bootstrap)}))
          escrow (source/checkpoint)
          _ (swap! state assoc :preparation escrow)
          disposition (guards/preparation-phase! summary escrow source/pure-value-target)
          evidence (:evidence escrow)]
      (require! (and (= :helper-value-required disposition) (map? (:panic-preparation evidence))
                     (map? (:ordinary-preparation evidence)) (map? (:eio-builder-preparation evidence))
                     (map? (:cases-on-preparation evidence))) "Required actual preparation evidence missing")
      (phase! :graph-helpers (assoc measured :measurement :shared-preparation-span
                                 :shared-with [:panic :ordinary-helpers :typed-eio :cases-on :seal]))
      (doseq [stage [:panic :ordinary-helpers :typed-eio :cases-on :seal]]
        (phase! stage {:measurement :shared-preparation-span :measured-at :graph-helpers}))
      (perform! :helper-value
        #(let [summary (helper/initialize!) escrow (helper/checkpoint)]
           (swap! state assoc :helper escrow)
           (when (= :failed (:phase escrow)) (throw (:failure escrow)))
           (guards/helper-value-facts! summary)
           (swap! state assoc :prepared (:prepared escrow) :phase :prepared))))))

(defn- prepare-prefix! []
  (let [{:keys [prepared checked restored application]} @state
        original (configuration prepared) callback (:callback application)
        symbol (:symbol callback)
        _ (source/validate-prefix-native-bindings! (get-in prepared [:original-support :session :bindings])
                                                   (:prefix-native-bindings prepared) (:trusted-bindings original))
        _ (require! (and (empty? (:application-extern-symbols original)) (not (contains? (:trusted-bindings original) symbol)))
                    "Callback must be a new explicitly authorized symbol")
        allow (assoc original :application-extern-symbols #{symbol})
        _ (owners/claim-execution! ownership (:resource-lease restored) checked prepared)
        _ (swap! ownership assoc :native-source (get-in prepared [:support :source]))
        base (owners/adopt! ownership #(preparation/open-checked prepared allow))
        _ (own-context! base nil)
        binding (extern/binding
                  (assoc (select-keys callback [:signature :arguments :result])
                         :fn (fn [text]
                               (require! (and (string? text) (<= (count text) 4096)) "Callback requires bounded immutable text")
                               (require! (empty? (:effects @state)) "Callback invocation cannot repeat")
                               (swap! state update :effects conj text)
                               (count (.getBytes ^String text java.nio.charset.StandardCharsets/UTF_8)))))
        _ (swap! state assoc :callback-binding binding)
        configured (owned-call! :authorize-callback #(resident/with-externs base {symbol binding}) #(own-context! % nil))
        independent (update allow :trusted-bindings assoc symbol binding)
        authorized (owned-call! :adopt-authorized #(resident/adopt-prepared (resident/snapshot configured) independent) #(own-context! % nil))
        result (owned-call! :prepare-init-prefix
                 #(prefix/prepare-init-prefix authorized checked
                    {:configuration independent :native-bindings (assoc (:prefix-native-bindings prepared) symbol binding)})
                 (fn [result]
                   (swap! state assoc :prefix-result result :independent independent)
                   (own-context! (:context result) (:prefix result))))]
    (require! (empty? (:effects @state)) "Loading/preparation executed the callback")
    (swap! state assoc :pristine-context (:context result))
    result))

(defn- close-tracked-context! [index]
  (let [{:keys [context prefix closed?]} (nth (:contexts @ownership) index)]
    (when-not closed?
      (boundary! :context-retirement
        (fn []
          (if prefix
            (owners/release-prefix! ownership [:context index] {:context context :prefix prefix}
              ;; Include the owner-ledger escrow before collecting diagnostics.
              prefix/release-prefix resident/close! true boundary!)
            (owners/operation! ownership [:context-close index] #(resident/close! context)))))
      (swap! ownership assoc-in [:contexts index :closed?] true))))
(defn dispose!
  "Close known owners exactly once before Source. Unknown partial work retains
   its canonical checkpoint and lease; destructive failure is never retried."
  []
  (when-not (= :already-disposed (owners/begin-disposal! ownership))
    (doseq [index (reverse (range (count (:contexts @ownership))))] (close-tracked-context! index))
    (require! (every? :closed? (:contexts @ownership)) "Source lease still has Context borrowers")
    (when-let [lease (:lease @ownership)]
      (owners/operation! ownership :source-lease-close #(.close ^java.io.Closeable lease)
        (fn [_] (when-let [native-source (:native-source @ownership)]
                  (require! (true? @(:closed native-source)) "Source lease did not close after all borrowers retired")))))
    (swap! ownership assoc :disposal-phase :disposed))
  {:disposal-phase :disposed})

(defn- close-value! [context]
  (let [indices (keep-indexed (fn [i row] (when (identical? context (:context row)) i)) (:contexts @ownership))]
    (require! (= 1 (count indices)) "Only a uniquely escrowed Context can close")
    (close-tracked-context! (first indices))))
(defn- kernel-name [wire]
  (case (first wire)
    "anonymous" (name/anonymous)
    "str" (name/mk-str (kernel-name (second wire)) (nth wire 2))
    "num" (name/mk-num (kernel-name (second wire)) (nth wire 2))))
(defn- load-version! [row version first?]
  (let [{:keys [bootstrap pristine-context application prefix-result]} @state
        input-id (get row (if (= version :a) :source-a-id :source-b-id))
        bytes (read-input bootstrap input-id (get-in application [:selection-limits :max-source-bytes]))
        before (resident/snapshot pristine-context)
        effects-before (:effects @state)
        roots (cond-> [(:entry row) (:worker row) (get-in row [:fallback :entry])]
                first? (conj (get-in application [:callback :entry])))
        loaded (owned-call! [(:id row) version :load]
                 #(resident/load-source pristine-context
                    {:text (wire/utf8-string bytes) :file-name (str (:id row) ".lean")
                     :module-name (kernel-name (:module row)) :roots (mapv kernel-name (distinct roots)) :initialization :defer})
                 (fn [r]
                   (swap! state assoc-in [:versions (:id row) version] r)
                   (own-context! (:context r) (:prefix prefix-result))))
        _ (require! (:success loaded) "Actual hosted file elaboration/admission failed")
        after (resident/snapshot (:context loaded))
        before-units (get-in before [:world :eval-const-authorizations :units])
        after-units (get-in after [:world :eval-const-authorizations :units])
        added (remove #(contains? before-units %) (keys after-units))]
    (require! (and (<= (count after-units) 64) (= 1 (count added))) "Expected one actually admitted source unit")
    (let [digest (first added) plan (get-in after-units [digest :manifest :initializationPlan])]
      (require! (and (map? plan) (vector? (:actions plan)) (empty? (:actions plan)))
                "Deferred source has required initialization; explicit prerequisite unresolved")
      (require! (= effects-before (:effects @state)) "Hosted loading executed application callback")
      (swap! state update-in [:versions (:id row) version] assoc :source-sha256 (wire/sha256 bytes) :unit-digest digest))
    (require! (identical? before (resident/snapshot pristine-context)) "Pristine source baseline changed")
    loaded))

(defn- select-version! [row version]
  (let [{:keys [independent application prefix-result]} @state
        loaded (get-in @state [:versions (:id row) version :context])
        selection ((requiring-resolve 'prototype.coherent-jvm-selection/select)
                    (resident/snapshot loaded) independent (:worker row) (:selection-limits application))]
    (require! (and (:compiler-options selection) (wire/hash? (:region-key selection)) (wire/hash? (:source-key selection)))
              "Actual admitted worker is outside the reviewed optimizing profile")
    (let [jvm (owned-call! [(:id row) version :reopen]
                #(reopen-application loaded independent (get-in application [:execution-roles :application]) (:application-cache @state))
                #(own-context! % (:prefix prefix-result)))
          selected (owned-call! [(:id row) version :select]
                     #(resident/with-compiler-options jvm (:compiler-options selection))
                     #(own-context! % (:prefix prefix-result)))]
      (require! (identical? (:application-cache @state) (get-in (resident/snapshot selected) [:session :cache]))
                "A/B branch lost the ONE explicit shared application cache")
      (swap! state update-in [:versions (:id row) version] assoc :selected selected :selection selection)
      (close-value! jvm)
      (when (= :b version)
        (let [a (get-in @state [:versions (:id row) :a]) b (get-in @state [:versions (:id row) :b])]
          (require! (and (not= (:source-sha256 a) (:source-sha256 b)) (not= (:unit-digest a) (:unit-digest b))
                         (not= (get-in a [:selection :source-key]) (:source-key selection))
                         (not= (get-in a [:selection :region-key]) (:region-key selection)))
                    "Changed B must bind different source, unit and compiler semantic keys")))
      selected)))

(defn- route-observer [compile]
  (fn [& args]
    (when-let [artifact (apply compile args)]
      (if-not (= :typed-tail (get-in artifact [:specialization :kind])) artifact
        (let [id (count (:artifacts @state))]
          (require! (< id 64) "Finite compiled artifact bound exceeded")
          (swap! state update :artifacts (fnil conj []) artifact)
          (reduce (fn [out hook]
                    (if-let [execute (get artifact hook)]
                      (assoc out hook
                             (fn [& args]
                               (let [route (apply execute args)
                                     event {:artifact id :kind :typed-tail :function (get-in artifact [:specialization :name])
                                            :hook hook :route route :call (:active-call @state)}]
                                 (swap! state update :route-events (fnil conj []) event)
                                 (require! (<= (count (:route-events @state)) 512) "Finite route observation bound exceeded")
                                 route))) out)) artifact [:execute! :execute-budget!]))))))

(defn- invoke! [context file entry args signature expected selected-worker label]
  (swap! state assoc :active-call label)
  (let [start (count (:route-events @state))
        called (boundary! :resident-call
                 #(owned-call! [:call label] (fn [] (resident/call context file (kernel-name entry) args signature))
                    (fn [returned] (own-context! (:context returned) (get-in @state [:prefix-result :prefix])))))
        events (subvec (vec (:route-events @state)) start)
        selected (filterv #(and (= selected-worker (:function %)) (= :specialized (:route %))) events)
        result (:value called)]
    (require! (= expected result) "Actual boxed call result differs from pinned expectation")
    (if selected-worker
      (require! (seq selected) "Actual compiled artifact did not execute a specialized worker")
      (require! (empty? events) "Fallback control unexpectedly entered the selected compiler"))
    (let [summary {:value result :carrier (.getName (class result))
                   :artifacts (vec (distinct (map :artifact selected)))}]
      (close-value! (:context called))
      (swap! state dissoc :active-call)
      summary)))

(defn- call-version! [row version role]
  (let [{:keys [selected file]} (get-in @state [:versions (:id row) version])]
    (mapv (fn [index call]
            (invoke! selected file (:entry row) (:args call) (:signature row)
                     (get call (if (= version :a) :expected-a :expected-b)) (:worker row) [(:id row) role index]))
          (range) (:calls row))))

(defn- callback! []
  (let [row (first (get-in @state [:application :corpus])) callback (get-in @state [:application :callback])
        {:keys [selected file]} (get-in @state [:versions (:id row) :a])]
    (require! (empty? (:effects @state)) "Callback executed during loading or ordinary calls")
    (invoke! selected file (:entry callback) [(:input callback)] {:arguments [:string] :result :nat}
             (:expected callback) nil :callback)
    (require! (= [(:input callback)] (:effects @state)) "Callback did not execute exactly once with the pinned immutable input")))

(defn- wrong-image! [row]
  (let [a (get-in @state [:versions (:id row) :a]) b (get-in @state [:versions (:id row) :b])
        encoded (atom 0) encode codec/encode-boxed]
    (require! (not (:unsafe-partial? @ownership)) "Earlier owner operation unresolved")
    (swap! ownership assoc :unsafe-partial? true :active-operation :wrong-image-control)
    (let [error (with-redefs [codec/encode-boxed (fn [& args] (swap! encoded inc) (apply encode args))]
                  (try
                    (let [returned (resident/call (:selected b) (:file a) (kernel-name (:entry row))
                                                   (:args (first (:calls row))) (:signature row))]
                      ;; Even an unexpected success is an owner before it is a
                      ;; failed negative assertion. Never discard its Context.
                      (swap! ownership assoc :returned-operation {:key :wrong-image-control :result returned})
                      (own-context! (:context returned) (get-in @state [:prefix-result :prefix]))
                      nil)
                    (catch clojure.lang.ExceptionInfo e e)))]
      (require! (and error (= "Resident file handle belongs to a different context generation" (.getMessage ^Throwable error))
                     (zero? @encoded)) "Wrong-image handle did not reject before encoding")
      ;; The exact stock target check runs BEFORE encoding/guest invocation.
      ;; Only this known pure rejection discharges the negative operation.
      (swap! ownership #(-> % (assoc :unsafe-partial? false) (dissoc :active-operation))))))

(defn- applications!
  ([] (applications! :all))
  ([mode]
  (let [_ (require! (contains? #{:all :prepare :finish} mode) "Unknown finite application segment")
        _ (when (contains? #{:all :prepare} mode) (swap! state assoc :application-cache (lazy/code-cache)))
        rows (get-in @state [:application :corpus]) compile-var (requiring-resolve 'prototype.typed-tail-execution/compile-entry)
        compile @compile-var]
    (with-redefs-fn {compile-var (route-observer compile)}
      (fn []
        (when (contains? #{:all :prepare} mode)
          (perform! :load-a #(doseq [[index row] (map-indexed vector rows)] (load-version! row :a (zero? index))))
          (perform! :select-a #(doseq [row rows] (select-version! row :a))))
        (when (contains? #{:all :finish} mode)
        (perform! :call-a
          #(doseq [row rows]
             (let [results (call-version! row :a :a)
                   {:keys [context selected file]} (get-in @state [:versions (:id row) :a]) f (:fallback row)]
               (swap! state assoc-in [:versions (:id row) :a :results] results)
               (require! (= :jvm (get-in (resident/snapshot selected) [:session :backend])) "Fallback control must run on selected JVM session")
               (invoke! selected file (:entry f) (:args f) (:signature f) (:expected f) nil [(:id row) :fallback])
               (close-value! context))))
        (perform! :callback callback!)
        (perform! :load-b #(doseq [[index row] (map-indexed vector rows)] (load-version! row :b (zero? index))))
        (perform! :select-b #(doseq [row rows] (select-version! row :b)))
        (perform! :call-b-a
          #(doseq [row rows]
             (let [b-results (call-version! row :b :b) a (get-in @state [:versions (:id row) :a])
                   fresh (owned-call! [(:id row) :reselect-old-a]
                           (fn [] (resident/with-compiler-options (:selected a) (get-in a [:selection :compiler-options])))
                           (fn [c] (own-context! c (get-in @state [:prefix-result :prefix]))))
                   _ (swap! state assoc-in [:versions (:id row) :a :selected] fresh)
                   a-again (call-version! row :a :a-again)
                   cache (lazy/summary (get-in (resident/snapshot fresh) [:session :program]))]
               (wrong-image! row)
               (require! (= (mapv :artifacts (:results a)) (mapv :artifacts a-again)) "Old A did not reuse its actual cached compiled artifact")
               (require! (pos? (:cache-hits cache)) "Fresh old-A program did not hit the shared code cache")
               (swap! state update :corpus conj
                      {:id (:id row) :source-a-sha256 (:source-sha256 a)
                       :source-b-sha256 (get-in @state [:versions (:id row) :b :source-sha256])
                       :unit-a (:unit-digest a) :unit-b (get-in @state [:versions (:id row) :b :unit-digest])
                       :region-a (get-in a [:selection :region-key]) :region-b (get-in @state [:versions (:id row) :b :selection :region-key])
                       :a (:results a) :b b-results :a-again a-again :wrong-image-rejected true :cache cache}))))))))))

(defn- fail-run! [failure]
  (swap! state assoc :phase :failed :failure failure :checking-checkpoint (source/checking-checkpoint)
         :preparation-checkpoint (source/checkpoint) :helper-checkpoint (helper/checkpoint))
  (if (and (:lease @ownership) (not (:unsafe-partial? @ownership)) (nil? (:disposal-phase @ownership)))
    (try (dispose!) (catch Throwable cleanup
                      (when-not (identical? failure cleanup) (.addSuppressed ^Throwable failure cleanup))))
    (swap! state assoc :disposal-phase :unresolved))
  (throw failure))

(defn initialize!
  "Developer staging only: construct/restore/check and retain the actual Init
   prefix owners once. Returns bounded diagnostics, never owners or a full-run
   receipt. This is not an additional authenticated bootstrap entrypoint.
   Use continue! or dispose! explicitly; no effects are automatically retried."
  [approved]
  (construct! approved)
  (try
    (restore-and-prepare!)
    (perform! :init-prefix prepare-prefix!)
    (let [stages (mapv :stage (:phases @state))]
      (require! (= (subvec profile/jvm-stages 0 9) stages) "Incomplete retained Init preparation")
      (swap! state assoc :phase :initialized)
      {:status :development-initialized :stages stages
       :consumer-contract-sha256 (get-in @state [:approved-contract :sha256])
       :consumer-implementation-sha256 (:implementation-sha256 approved)
       :compatibility-profile profile/jvm-profile-id})
    (catch Throwable failure (fail-run! failure))))

(defn prepare-applications!
  "Developer staging only: load/select A once and retain its actual owners.
   Neither this diagnostic result nor initialize! is a bootstrap entrypoint."
  []
  (let [before @state]
    (require! (and (= :initialized (:phase before))
                   (not (:unsafe-partial? @ownership)) (nil? (:disposal-phase @ownership))
                   (compare-and-set! state before (assoc before :phase :preparing-applications)))
              "Application preparation requires one live initialized stage"))
  (try
    (applications! :prepare)
    (let [stages (mapv :stage (:phases @state))]
      (require! (= (subvec profile/jvm-stages 0 11) stages) "Incomplete retained A preparation")
      (swap! state assoc :phase :applications-ready :sample-batches 0)
      {:status :development-applications-ready :stages stages})
    (catch Throwable failure (fail-run! failure))))

(defn- with-route-observation [f]
  (let [compile-var (requiring-resolve 'prototype.typed-tail-execution/compile-entry)]
    (with-redefs-fn {compile-var (route-observer @compile-var)} f)))

(defn sample-a!
  "Explicit developer repetition of reviewed A cases, not a general purity test.
   One corpus row, at most four batches; no caller arguments or callback entry.
   Return only scalar call summaries and leave the finite gate stages untouched.
   Serialize developer operations; a partial failure is terminal."
  []
  (let [before @state ledger @ownership rows (get-in before [:application :corpus])
        batch (:sample-batches before)]
    ;; Reserve64 ledger slots for the remaining finite program. Refuse before
    ;; any invocation, including if other developer work consumed owner slots.
    (require! (and (= :applications-ready (:phase before)) (= 1 (count rows))
                   (integer? batch) (<= 0 batch 3)
                   (<= (+ (count (:contexts ledger)) (count (:calls (first rows))) 64) 128)
                   (not (:unsafe-partial? ledger)) (nil? (:disposal-phase ledger))
                   (compare-and-set! state before (assoc before :phase :sampling :sample-batches (inc batch))))
              "A sampling requires one live prepared row and remaining batch/owner budget")
    (try
      (let [effects (:effects before)
            results (with-route-observation
                      #(mapv (fn [row] {:id (:id row)
                                        :calls (call-version! row :a [:sample (inc batch)])}) rows))]
        (require! (= effects (:effects @state)) "Reviewed sampling cases executed an unexpected callback")
        (swap! state assoc :phase :applications-ready)
        {:status :development-sampled :batch (inc batch) :results results})
      (catch Throwable failure (fail-run! failure)))))

(defn continue!
  "Claim one retained initialized developer stage, run the existing finite A/B/A
   program and dispose. Only all seventeen completed stages return :passed.
   Reject duplicate/out-of-order claims before cleanup or any guest operation."
  []
  (let [before @state mode (if (= :applications-ready (:phase before)) :finish :all)]
    (require! (and (contains? #{:initialized :applications-ready} (:phase before))
                   (not (:unsafe-partial? @ownership)) (nil? (:disposal-phase @ownership))
                   (compare-and-set! state before (assoc before :phase :continuing)))
              "Finite JVM continuation requires one live initialized stage")
  (try
    (if (= :finish mode) (applications! :finish) (applications!))
    (perform! :dispose dispose!)
    (let [approved (:bootstrap @state)
          stages (mapv :stage (:phases @state)) application (:application @state)
          result (merge (:execution approved)
                        {:status :passed :disposal-phase :disposed :stages stages
                         :consumer-contract-sha256 (get-in @state [:approved-contract :sha256])
                         :consumer-implementation-sha256 (:implementation-sha256 approved)
                         :compatibility-profile profile/jvm-profile-id
                         :application-execution (get-in application [:execution-roles :application])
                         :measurements {:corpus (:corpus @state) :callback {:loading-effects 0 :invocation-effects (count (:effects @state))}
                                        :phases (:phases @state)}})]
      (require! (= profile/jvm-stages stages) "Incomplete finite JVM application stage evidence")
      (swap! state assoc :phase :passed :result result) result)
    (catch Throwable failure (fail-run! failure)))))

(defn run!
  "Construct/restore/check once, then finite genuine file A/B/A and disposal.
   This controller grants no trust from receipts and retries no guest effects."
  [approved]
  (initialize! approved)
  (continue!))
