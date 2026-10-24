(ns prototype.project-loader
  "Experimental orchestration: pristine rebuilds, captured text, actual typed graph
   nodes and one accumulated World lineage. Requires NativeBase public APIs at
   integration; no Project-wide fuel, cancellation or initializer permission."
  (:require [clojure.string :as str]
            [prototype.project-discovery :as discovery]
            [prototype.resident-frontend :as resident]
            [prototype.resident-init-prefix :as graph])
  (:import [ansatz.kernel Name]
           [java.nio.file Path]
           [java.nio.charset StandardCharsets]
           [java.util WeakHashMap IdentityHashMap]))

(deftype ProjectVersion [])
(deftype ProjectLoad [])
(deftype ProjectFailure [])
(defonce ^:private versions (WeakHashMap.))
(defonce ^:private loads (WeakHashMap.))
(defonce ^:private failures (WeakHashMap.))
(defn- fail [message data] (throw (ex-info message data)))
(defn- exact! [x keys label]
  (when-not (and (map? x) (= (count x) (count keys)) (every? #(contains? x %) keys))
    (fail (str "Project loader requires closed " label) {})))
(defn- positive! [n]
  (when-not (and (integer? n) (<= 1 n Long/MAX_VALUE))
    (fail "Project loader requires positive Long limits" {})))
(defn- issued! [registry kind value label]
  (when-not (.isInstance ^Class kind value) (fail (str "Expected issued " label) {}))
  (or (locking registry (.get ^WeakHashMap registry value))
      (fail (str "Unknown " label) {})))
(defn- version! [project]
  (let [data @(issued! versions ProjectVersion project "Project version")]
    (when (= :closed (:phase data)) (fail "Project version is closed" {})) data))
(defn- load-state! [load] (issued! loads ProjectLoad load "Project load"))
(defn- utf8! [s remaining]
  (when-not (and (string? s) (<= (count s) remaining))
    (fail "Project Name exceeds byte bound" {}))
  (let [encoded (.getBytes ^String s StandardCharsets/UTF_8) n (alength encoded)]
    (when-not (and (<= n remaining) (= s (String. encoded StandardCharsets/UTF_8)))
      (fail "Project Name exceeds UTF-8 bound" {})) n))

(defn- module! [wire limits]
  (loop [part wire segments () bytes 0 nodes 0]
    (when (>= nodes (:max-name-nodes limits)) (fail "Project module Name exceeds spine bound" {}))
    (when-not (vector? part) (fail "Project module requires structured Name" {}))
    (if (and (= 1 (count part)) (= "anonymous" (first part)))
      (do (when-not (seq segments) (fail "Project module is anonymous" {}))
          {:segments (vec segments) :bytes bytes})
      (do
        (when-not (and (= 3 (count part)) (= "str" (first part)))
          (fail "Project module requires string segments" {}))
        (let [s (nth part 2) n (utf8! s (- (:max-name-bytes limits) bytes))]
          ;; Closing » silently truncates the actual pinned parser, even with
          ;; hasErrors=false. CR/LF exclusion is our narrower loader policy.
          (when (or (empty? s) (re-find #"[.\\/\u0000\r\n»]" s))
            (fail "Project module segment cannot be rendered by this loader" {}))
          (recur (nth part 1) (conj segments s) (+ bytes n) (inc nodes)))))))
(defn- wire [segments] (reduce #(vector "str" %1 %2) ["anonymous"] segments))
(defn- java-module [segments] (reduce #(Name/mkStr %1 %2) Name/ANONYMOUS_NAME segments))
(defn- java-name! [value limits]
  (when-not (instance? Name value) (fail "Project exports require explicit Java Names" {}))
  (loop [^Name part value nodes 0 bytes 0]
    (when (>= nodes (:max-name-nodes limits)) (fail "Project export Name exceeds spine bound" {}))
    (when-not (instance? Name part) (fail "Project export Name has no anonymous terminator" {}))
    (case (int (.-tag part))
      0 (do (when (zero? nodes) (fail "Project export Name is anonymous" {})) bytes)
      1 (recur (.-prefix part) (inc nodes)
               (+ bytes (utf8! (.-str part) (- (:max-name-bytes limits) bytes))))
      2 (do (when-not (and (<= 0 (.-num part) 4294967295)
                           (<= 10 (- (:max-name-bytes limits) bytes)))
              (fail "Project export numeric Name exceeds profile" {}))
            (recur (.-prefix part) (inc nodes) (+ bytes 10)))
      (fail "Project export Name has another tag" {}))))

(defn- render! [modules limits header-limits max-bytes]
  (when-not (and (vector? modules) (seq modules) (<= (count modules) (:max-roots limits)))
    (fail "Project requires bounded nonempty source roots" {}))
  (let [{:keys [names size]}
        (reduce (fn [{:keys [names size bytes]} name]
                  (let [{:keys [segments] n :bytes} (module! name limits)
                        next-bytes (+ bytes n)
                        line (+ 8 n (* 4 (count segments)) (dec (count segments)))
                        remaining (- (min max-bytes (:max-source-bytes header-limits)) size)]
                    (when (or (> next-bytes (:max-total-name-bytes limits)) (> line remaining))
                      (fail "Project import view exceeds byte bounds" {}))
                    {:names (conj names segments) :size (+ size line) :bytes next-bytes}))
                {:names [] :size 0 :bytes 0} modules)
        text (apply str (map #(str "import " (str/join "." (map (fn [s] (str "«" s "»")) %)) "\n") names))]
    {:text text :byte-count size :modules names}))

(def ^:private discovery-limit-keys
  [:max-roots :max-native-modules :max-modules :max-depth :max-edges :max-source-bytes
   :max-header-output-bytes :max-name-nodes :max-name-bytes :max-total-name-bytes])
(def ^:private header-limit-keys
  [:max-source-bytes :max-file-name-bytes :max-output-bytes :max-json-depth :max-imports
   :max-diagnostics :max-name-nodes :max-name-bytes :max-total-name-bytes])
(defn- bounds! [limits]
  (exact! limits [:discovery :header :max-exports :max-export-name-bytes :max-view-bytes
                  :max-owned-contexts :max-operations] "limits")
  (doseq [[k keys] [[:discovery discovery-limit-keys] [:header header-limit-keys]]]
    (exact! (get limits k) keys "nested bounds")
    (doseq [key keys] (positive! (get-in limits [k key]))))
  (doseq [k [:max-exports :max-export-name-bytes :max-view-bytes :max-owned-contexts :max-operations]]
    (positive! (get limits k)))
  (when (< (:max-owned-contexts limits) 3) (fail "Project requires room for baseline/current/returned Contexts" {}))
  (when-not (<= 2 (get-in limits [:header :max-imports]) 1026)
    (fail "Project header import limit must be 2..1026" {})))
(defn- policies! [policies]
  (exact! policies [:discovery-budgets :publication-budgets :import-options :native-options] "policies")
  (doseq [k [:discovery-budgets :publication-budgets]]
    (exact! (get policies k) [:helper-fuel :attempt-fuel] "proof budgets")
    (doseq [n (vals (get policies k))] (positive! n)))
  (doseq [k [:import-options :native-options]]
    (exact! (get policies k) [:kernel-policy :budgets] "child options")
    (let [policy (get-in policies [k :kernel-policy])]
      (when-not (and (map? policy) (<= (count policy) 4)
                     (every? (fn [key] (or (= :allow-axioms? key) (= :allow-unsafe? key)
                                          (= :allow-compiler-markers? key) (= :fuel key))) (keys policy)))
        (fail "Project kernel policy forbids caller certificates/options" {}))
      (doseq [flag [:allow-axioms? :allow-unsafe? :allow-compiler-markers?]
              :when (contains? policy flag)]
        (when-not (boolean? (get policy flag)) (fail "Project kernel flags require Boolean values" {})))
      (when (contains? policy :fuel) (positive! (:fuel policy))))
    (exact! (get-in policies [k :budgets]) [:outer-fuel :helper-fuel :attempt-fuel] "child budgets")
    (doseq [n (vals (get-in policies [k :budgets]))] (positive! n))))
(defn- provider! [provider]
  (exact! provider [:roots :max-bytes] "provider")
  (when-not (and (vector? (:roots provider)) (<= 1 (count (:roots provider)) 256)
                 (integer? (:max-bytes provider)) (<= 1 (:max-bytes provider) 67108864))
    (fail "Project requires a bounded canonical provider" {}))
  (doseq [p (:roots provider)]
    (when-not (and (instance? Path p) (.isAbsolute ^Path p) (= p (.normalize ^Path p))
                   (<= 1 (.getNameCount ^Path p) 256) (<= (count (str p)) 16384))
      (fail "Project provider requires bounded absolute normalized Paths" {}))))

(defn open-project
  "Fork a retained PRISTINE prepublication native Context. Exact host options are
   validated here; existing runtime APIs validate prefix/profile/readiness at use.
   Neither this wrapper nor its descriptors certify a native base. Shared Source
   resources remain caller-owned. No native/guest operation executes here."
  [context {:keys [configuration prefix profile native-readiness provider native-modules limits policies] :as options}]
  (exact! options [:configuration :prefix :profile :native-readiness :provider :native-modules :limits :policies] "configuration")
  (bounds! limits) (policies! policies) (provider! provider)
  (when-not (and (map? configuration) (vector? native-modules)
                 (<= (count native-modules) (get-in limits [:discovery :max-native-modules])))
    (fail "Project requires bounded native module data and independent configuration" {}))
  (reduce (fn [used name]
            (let [n (:bytes (module! name (:discovery limits)))]
              (when (> n (- (get-in limits [:discovery :max-total-name-bytes]) used))
                (fail "Project native Name data exceeds aggregate bound" {}))
              (+ used n))) 0 native-modules)
  (let [entry (resident/snapshot context) owned (atom [])]
    (when (seq (get-in entry [:world :source-modules]))
      (fail "Project baseline must precede source publications; native reset does not clear them" {}))
    (try
      (let [baseline (resident/fork context) _ (swap! owned conj baseline)
            current (resident/fork context) _ (swap! owned conj current)
            data (assoc options :baseline baseline :context current :phase :open
                        :captures {} :nodes {} :files {} :exports {} :roots [] :order [])
            project (ProjectVersion.)]
        (locking versions (.put versions project (atom data))) project)
      (catch Throwable cause
        (throw (ex-info "Project construction failed" {:project-entry entry :project-owned-contexts @owned} cause))))))

(defn- progress [s]
  {:phase (:phase s) :module-index (:index s 0) :module-count (count (:order s))
   :operations (:operations s 0) :child-progress (:child-progress s)})
(defn- reserve-context! [state]
  (when (>= (count (:owned @state)) (get-in @state [:version :limits :max-owned-contexts]))
    (fail "Project owned Context count exceeds bound" {})))
(defn- own-context! [state context]
  (swap! state update :owned conj context) context)
(defn- retire-context! [state context]
  (when-not (or (identical? context (:baseline @state)) (identical? context (:context @state)))
    (when-not (some #(identical? context %) (:owned @state))
      (fail "Project cannot close a borrowed Context" {}))
    (swap! state assoc :closing-context context)
    (resident/close! context)
    (swap! state #(-> % (update :owned (fn [contexts] (filterv (fn [c] (not (identical? c context))) contexts)))
                       (update :closed-context-count (fnil inc 0)) (dissoc :closing-context)))))
(defn- failed! [state cause]
  (let [before @state
        ;; Active child remains private: its public API has no latest packet or
        ;; disposal accessor. Never label last-complete Context as latest child.
        diagnostic (dissoc before :child :failure)
        ;; Synchronous load-file callers never receive the load key. The opaque
        ;; failure token keeps private child evidence alive without exposing a
        ;; continuation. Its registry value holds neither token nor exception.
        token (ProjectFailure.)
        _ (locking failures (.put failures token (dissoc before :failure)))
        wrapped (ex-info (or (.getMessage cause) "Project load failed")
                  (merge (ex-data cause) {:project-load-state diagnostic :project-load-terminal? true
                                         :project-failure-diagnostic token}) cause)]
    (swap! state assoc :phase :failed :failure wrapped) (throw wrapped)))

(defn- exports! [records limits]
  (when-not (and (vector? records) (<= (count records) (get-in limits [:discovery :max-modules])))
    (fail "Project exports require bounded module records" {}))
  (let [result
        (reduce (fn [{:keys [entries root-count bytes]} record]
                  (exact! record [:module :roots] "export record")
                  (let [module (:segments (module! (:module record) (:discovery limits))) roots (:roots record)]
                    (when-not (and (vector? roots) (<= (count roots) (- (:max-exports limits) root-count)))
                      (fail "Project export root count exceeds bound" {}))
                    (let [next-bytes (reduce (fn [used name]
                                               (let [n (java-name! name (:header limits))]
                                                 (when (> n (- (:max-export-name-bytes limits) used))
                                                   (fail "Project aggregate export Name bytes exceeded" {}))
                                                 (+ used n))) bytes roots)]
                      (when (or (contains? entries module) (not= (count roots) (count (set roots))))
                        (fail "Project exports contain duplicate modules or roots" {}))
                      {:entries (assoc entries module roots) :root-count (+ root-count (count roots)) :bytes next-bytes})))
                {:entries {} :root-count 0 :bytes 0} records)]
    (:entries result)))
(defn- preflight-graph! [discovered rendered limits]
  (let [g (:graph discovered)]
    (doseq [root (:roots g)]
      (when-not (contains? (:nodes g) root) (fail "Project load requires captured SOURCE roots" {})))
    (doseq [[_ node] (:nodes g)]
      (module! (wire (get-in node [:capture :module])) (:discovery limits))
      (doseq [request (subvec (get-in node [:header :requestedImports]) 2)]
        (let [dep (:segments (module! (:module request) (:discovery limits)))]
          (when (contains? (:native-modules g) dep)
            (fail "Project load does not support explicit native imports, including explicit Init" {})))))
    (when-not (= (:roots g) (:modules rendered)) (fail "Project root rendering changed module identity" {}))))

(defn prepare-load
  "Capture once on a fork of pristine baseline, thread discovery's actual packet
   and adopt it ONCE. REQUEST exactly {:roots wire-Names :exports [{:module wire
   :roots vector-of-explicit-Java-Names}]}. Empty export vectors are explicit.
   No cache/old Node reattachment, prefix-restart, cancel or filesystem reread."
  [project request]
  (locking project
    (let [source-version (version! project)
          version (select-keys source-version [:configuration :prefix :profile :native-readiness :provider :native-modules :limits :policies])
          state (atom {:phase :entry :version version :owned [] :operations 0 :index 0 :busy? false})]
      (try
        (exact! request [:roots :exports] "load request")
        (let [{:keys [configuration provider native-modules limits policies]} version
              exports (exports! (:exports request) limits)
              rendered (render! (:roots request) (:discovery limits) (:header limits) (:max-view-bytes limits))
              _ (reserve-context! state) baseline (resident/fork (:baseline source-version))
              _ (own-context! state baseline) _ (swap! state assoc :baseline baseline)
              _ (reserve-context! state) scratch (resident/fork (:baseline source-version))
              _ (own-context! state scratch) entry (resident/snapshot scratch)
              _ (swap! state assoc :entry entry :phase :discovery)
              discovered (discovery/discover-project entry
                           {:roots (:roots request) :native-modules native-modules :provider provider}
                           {:configuration configuration :header-limits (:header limits)
                            :limits (:discovery limits) :budgets (:discovery-budgets policies)})
              _ (swap! state assoc :discovery-result discovered :phase :preflight)
              _ (preflight-graph! discovered rendered limits)
              _ (when-not (= (set (keys exports)) (set (keys (get-in discovered [:graph :nodes]))))
                  (fail "Project exports must explicitly cover exactly the captured source modules" {}))
              _ (reserve-context! state)
              context (resident/adopt-prepared (:packet discovered) configuration)
              _ (own-context! state context)
              _ (swap! state assoc :context context :exports exports :rendered rendered
                       :discovered-graph (:graph discovered) :discovery-progress (:progress discovered)
                       :order (get-in discovered [:graph :order]) :nodes {} :files {} :phase :module-base)
              _ (resident/snapshot context)
              _ (retire-context! state scratch)
              _ (swap! state dissoc :entry :discovery-result)
              control (ProjectLoad.)]
          (locking loads (.put loads control state))
          {:control control :progress (progress @state)})
        (catch Throwable cause (failed! state cause))))))

(defn- module-request [state module]
  (let [capture (get-in state [:discovered-graph :nodes module :capture])]
    {:text (:text capture) :file-name (str (:path capture)) :module-name (java-module module)
     :roots (get-in state [:exports module]) :initialization :defer}))
(defn- parent-nodes [s module]
  ;; Use the actual RAW ordinary imports, not discovery's scheduling dedup.
  (mapv (fn [request]
          (let [parent (:segments (module! (:module request) (get-in s [:version :limits :discovery])))]
            (or (get-in s [:nodes parent])
                (fail "Project parent has no issued node in this operation lineage" {:module parent}))))
        (subvec (get-in s [:discovered-graph :nodes module :header :requestedImports]) 2)))
(defn- start-child! [state mode purpose request roots]
  (let [{:keys [version context]} @state
        {:keys [prefix profile native-readiness policies]} version
        _ (swap! state assoc :phase :child-prepare :child-mode mode :child-purpose purpose :child-request request)
        child (if (= :native mode)
                (graph/prepare-native-init-base context request prefix profile native-readiness (:native-options policies))
                (graph/prepare-source-graph-import context request prefix profile roots (:import-options policies)))]
    (swap! state assoc :child (:control child) :child-progress (:progress child) :phase :child-running)))
(defn- one-operation! [state wall-ms]
  (case (:phase @state)
    :module-base
    (let [s @state module (nth (:order s) (:index s))
          request (module-request s module) parents (parent-nodes s module)]
      (swap! state assoc :module module :module-request request :parents parents)
      (cond
        (seq parents) (start-child! state :graph :module request parents)
        (zero? (:index s)) (swap! state assoc :phase :publish)
        :else (start-child! state :native :module request [])))

    :child-running
    (let [{:keys [child child-mode]} @state
          limits {:max-operations 1 :wall-ms wall-ms}
          result (if (= :native child-mode)
                   (graph/advance-native-init-base! child limits)
                   (graph/advance-source-graph-import! child limits))]
      (swap! state assoc :child-progress (:progress result))
      (when (= :io-completed (get-in result [:progress :phase]))
        (swap! state assoc :phase :child-finish)))

    :child-finish
    (let [{:keys [child child-mode child-purpose]} @state
          previous (:context @state)
          _ (reserve-context! state)
          result (if (= :native child-mode)
                   (graph/finish-native-init-base! child)
                   (graph/finish-source-graph-import! child))
          ;; Save the whole returned Context/result before snapshot or checks.
          _ (swap! state assoc :last-child-result result :context (:context result))
          _ (own-context! state (:context result))]
      (when (= :final child-purpose)
        (when-not (= (get-in @state [:rendered :byte-count]) (get-in result [:header :headerEndByte]))
          (fail "Project generated import header was not fully consumed" {})))
      (resident/snapshot (:context result))
      (retire-context! state previous)
      (swap! state #(-> % (dissoc :child :last-child-result)
                         (assoc :last-child-header (:header result)
                                :phase (if (= :final child-purpose) :complete :publish)))))

    :publish
    (let [{:keys [version context module module-request parents index order]} @state
          _ (reserve-context! state)
          _ (swap! state assoc :phase :publication-started)
          result (graph/publish-source-graph-node context module-request (:prefix version) (:profile version) parents
                   {:proof-budgets (get-in version [:policies :publication-budgets])})
          _ (swap! state assoc :last-publication result :context (:context result))
          _ (own-context! state (:context result))]
      (when-not (and (:success result) (:graph-node result) (:file result)
                     (= (wire module) (get-in result [:graph-publication :module])))
        (fail "Project publication did not return its actual node/file/module" {}))
      (resident/snapshot (:context result))
      (swap! state #(-> % (assoc-in [:nodes module] (:graph-node result))
                         (assoc-in [:files module] (:file result))
                         (assoc :index (inc index) :phase (if (= (inc index) (count order)) :final-view :module-base))))
      (retire-context! state context)
      (swap! state dissoc :last-publication :module-request :parents))

    :final-view
    (let [s @state request {:text (get-in s [:rendered :text]) :file-name "<project-import-view>"
                            :module-name (Name/mkStr Name/ANONYMOUS_NAME "_ProjectImportView")
                            :roots [] :initialization :defer}
          roots (mapv #(or (get-in s [:nodes %]) (fail "Project final root has no issued node" {}))
                      (get-in s [:discovered-graph :roots]))]
      (start-child! state :graph :final request roots))

    (fail "Project load has no advanceable stage" {})))

(defn advance-load!
  "Drive one private native/graph child at a time. Limits are exactly positive
   :max-operations/:wall-ms, optionally scalar :observe!. No preemption inside
   compilation/checking/FS/host work and no cancellation API. Failures terminal."
  [control {:keys [max-operations wall-ms observe!] :as limits}]
  (let [state (load-state! control)]
    (locking control
      (when-let [failure (:failure @state)] (throw failure))
      (when (:busy? @state) (fail "Project load is busy" {}))
      (when (contains? #{:complete :finished} (:phase @state))
        (fail "Project load is not advanceable" {}))
      (when-not (and (map? limits) (<= 2 (count limits) 3)
                     (contains? limits :max-operations) (contains? limits :wall-ms)
                     (every? (fn [key] (or (= :max-operations key) (= :wall-ms key) (= :observe! key))) (keys limits))
                     (or (nil? observe!) (fn? observe!)))
        (fail "Project load requires bounded slice options" {}))
      (positive! max-operations) (positive! wall-ms)
      (swap! state assoc :busy? true)
      (try
        (let [started (System/nanoTime)]
          (loop [n 0]
            (when (and (< n max-operations) (not= :complete (:phase @state))
                       (< (/ (- (System/nanoTime) started) 1000000.0) wall-ms))
              (when (>= (:operations @state) (get-in @state [:version :limits :max-operations]))
                (fail "Project operation count exceeds bound" {}))
              (swap! state update :operations inc)
              (one-operation! state wall-ms)
              (when observe! (observe! (progress @state)))
              (recur (inc n)))))
        {:progress (progress @state)}
        (catch Throwable cause (failed! state cause))
        (finally (swap! state assoc :busy? false))))))

(defn- close-other-contexts! [state retained]
  (let [seen (IdentityHashMap.)]
    (doseq [context (:owned @state)]
      (when-not (or (.containsKey seen context) (some #(identical? % context) retained))
        (.put seen context true)
        (swap! state assoc :closing-context context)
        (resident/close! context)
        (swap! state update :closed-context-count (fnil inc 0))))))
(defn finish-load!
  "Issue a persistent Project version only after complete final checked import.
   Underlying successful suboperations remain real on a later Project failure;
   this is not a rollback or receipt deactivation promise. Consume success once."
  [control]
  (let [state (load-state! control)]
    (locking control
      (when-let [failure (:failure @state)] (throw failure))
      (when (:busy? @state) (fail "Project load is busy" {}))
      (when-not (= :complete (:phase @state)) (fail "Project load has no complete result" {}))
      (try
        (let [{:keys [version context baseline discovered-graph exports nodes files order]} @state
              captures (into {} (map (fn [[module node]] [module (:capture node)])) (:nodes discovered-graph))
              data (assoc version :baseline baseline :context context :phase :open
                                  :captures captures :nodes nodes :files files :exports exports
                                  :roots (:roots discovered-graph) :order order)
              project (ProjectVersion.)
              result {:project project :files files
                      :modules {:roots (:roots data) :order order :count (count order)}
                      :progress (assoc (progress @state) :phase :finished)}]
          (close-other-contexts! state [baseline context])
          ;; Complete all fallible construction/cleanup before issuance. Values
          ;; never retain their own registry keys or a previous Project version.
          (locking versions (.put versions project (atom data)))
          (reset! state {:phase :finished :operations (:operations @state)})
          result)
        (catch Throwable cause (failed! state cause))))))

(defn load-file
  "Convenience one-source-root driver. Request identifies a module through its
   provider, not a module inferred from a canonical filename. :exports explicitly
   covers every discovered source, including [] for intentionally unexported ones.
   Slice is cooperative and every failure retains its exact diagnostic evidence."
  [project {:keys [module exports] :as request} slice]
  (exact! request [:module :exports] "load-file request")
  (let [{:keys [control]} (prepare-load project {:roots [module] :exports exports})]
    (loop []
      (let [result (advance-load! control slice)]
        (if (= :complete (get-in result [:progress :phase]))
          (finish-load! control) (recur))))))

(defn- invoke* [operation project module name values signature]
  (locking project
    (let [data (version! project)
          segments (:segments (module! module (get-in data [:limits :discovery])))
          _ (java-name! name (get-in data [:limits :header]))
          file (or (get-in data [:files segments]) (fail "Project module has no stored FileHandle" {}))
          _ (when-not (some #(= name %) (get-in data [:exports segments]))
              (fail "Project function was not an explicit export" {}))
          owned (atom [])]
      (try
        (let [baseline (resident/fork (:baseline data)) _ (swap! owned conj baseline)
              scratch (resident/fork (:context data)) _ (swap! owned conj scratch)
              called (case operation
                       :invoke (resident/call scratch file name values signature)
                       :invoke-io (resident/call-io scratch file name values signature))
              _ (swap! owned conj (:context called))
              next-data (assoc data :baseline baseline :context (:context called))
              next-project (ProjectVersion.) result {:project next-project :value (:value called)}]
          (resident/close! scratch)
          (locking versions (.put versions next-project (atom next-data))) result)
        (catch Throwable cause
          (throw (ex-info (or (.getMessage cause) "Project invocation failed")
                   (merge (ex-data cause) {:project-operation operation :project-owned-contexts @owned}) cause)))))))

(defn invoke
  "Call an explicit stored file/export through resident/call. Return a NEW version
   with separate baseline/current Context wrappers. Does not mutate or close the
   caller version. No inferred ABI, eval-string or automatic initialization."
  [project module name values signature]
  (invoke* :invoke project module name values signature))

(defn invoke-io
  "Call an explicit stored IO export through resident/call-io. VALUES and argument
   codecs describe only explicit Lean arguments; the resident facade supplies
   the erased world and decodes [:io result]. Success returns a NEW Project/value.
   Failures retain canonical world/session, owned result and operation Contexts;
   they do not retry, roll back effects or clean up diagnostic owners.
   This delegates existing IO execution; it grants no additional capabilities,
   initialization permission or application extern admission."
  [project module name values signature]
  (invoke* :invoke-io project module name values signature))

(defn close-project!
  "Close only this version's private Context wrappers once. Borrowed Source/Store
   and separately forked older/newer versions remain owned by their callers."
  [project]
  (let [state (issued! versions ProjectVersion project "Project version")]
    (locking project
      (when-not (= :closed (:phase @state))
        (let [{:keys [baseline context]} @state]
          (resident/close! context)
          (when-not (identical? baseline context) (resident/close! baseline))
          (reset! state {:phase :closed})))))
  nil)
