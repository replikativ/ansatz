(ns prototype.frontend
  "Hosted pinned file-helper orchestration over an explicit prepared raw session.
   This API neither imports modules nor bootstraps the frontend. Input references
   are BORROWED; each owned helper argument is retained before transfer. Returned
   :environment is owned, including when command diagnostics report failure.
   Code installation never runs pending module initialization."
  (:require [clojure.data.json :as json]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]
            [prototype.interop-codec :as codec]
            [prototype.eval-const :as eval]
            [prototype.runtime-prim :as prim]
            [prototype.runtime-abi :as abi]))

(defn- helper [part] ["str" ["str" ["anonymous"] "RuntimeCompileShim"] part])
(def header-target (helper "inspectFileHeader"))
(def compile-target (helper "compileImportedFileState"))
(def ^:private profile {:target "x86_64-unknown-linux-gnu" :wordBits 64})
(defn- fail [message data] (throw (ex-info message data)))
(defn- name! [value]
  (loop [n value]
    (when-not (vector? n) (fail "Invalid frontend structured Name" {}))
    (case (first n)
      "anonymous" (when-not (= 1 (count n)) (fail "Invalid frontend anonymous Name" {}))
      "str" (do (when-not (and (= 3 (count n)) (string? (nth n 2)))
                  (fail "Invalid frontend string Name segment" {})) (recur (second n)))
      "num" (do (when-not (and (= 3 (count n))
                               (or (and (integer? (nth n 2)) (<= 0 (nth n 2)))
                                   (and (string? (nth n 2)) (re-matches #"0|[1-9][0-9]*" (nth n 2)))))
                  (fail "Invalid frontend numeric Name segment" {})) (recur (second n)))
      (fail "Invalid frontend structured Name" {}))) value)
(defn- imports! [imports]
  (when-not (vector? imports) (fail "Invalid frontend import list" {}))
  (doseq [i imports]
    (when-not (and (map? i) (every? #(boolean? (get i %)) [:importAll :isExported :isMeta]))
      (fail "Invalid frontend import flags" {}))
    (name! (:module i))) imports)
(defn- envelope! [text schema producer file-name]
  (let [e (json/read-str text :key-fn keyword)]
    (when-not (and (= schema (:schema e)) (= producer (:producer e))
                   (= (get prim/pinned-build "lean_get_githash") (:leanCommit e))
                   (= profile (:runtimeProfile e)) (= file-name (:fileName e))
                   (boolean? (:moduleSystem e)) (vector? (:diagnostics e))
                   (every? map? (:diagnostics e)))
      (fail "Invalid frontend producer/profile/envelope" {}))
    (imports! (:requestedImports e)) e))
(defn- reference! [world value label]
  (when-not (m/ref? value) (fail "Expected frontend guest reference" {:argument label}))
  (m/node world value) value)
(defn- ctor! [world value tag fields]
  (let [node (when (m/ref? value) (m/node world value))]
    (when-not (and (= :ctor (:kind node)) (= tag (:tag node)) (= fields (count (:fields node)))
                   (nil? (:layout node)) (empty? (:scalar-bytes node)))
      (fail "Invalid frontend result layout" {:tag tag :fields fields})) node))
(defn- io-ok! [world value]
  ;; Decode errors through the public codec; it preserves the owned error/result
  ;; for caller inspection. No released error reference is put in an exception.
  (let [node (when (m/ref? value) (m/node world value))]
    (when (= 1 (:tag node)) (codec/decode world [:io :unit] value))
    (first (:fields (ctor! world value 0 1)))))

(defn- checked-result [result f]
  (try (f)
       (catch Throwable cause
         ;; The pre-cleanup immutable result snapshot still owns the entire IO
         ;; result, so callers can inspect/release it if transport validation or
         ;; pure installation fails. Guest effects already performed stay visible.
         (let [data (ex-data cause)
               newer? (some? (:checkpoint data))]
           (throw (ex-info (or (.getMessage cause) "Hosted frontend result failed")
                           (cond-> (merge data
                                          {:checkpoint (or (:checkpoint data) (:state result))
                                           :session (or (:checkpoint-session data) (:session data) (:session result))
                                     ;; This wrapper is owned only in this separately
                                     ;; retained snapshot, before result cleanup.
                                           :frontend-result {:checkpoint (:state result)
                                                             :session (:session result)
                                                             :raw-result (:value result)}})
                             (not newer?) (assoc :raw-result (:value result))) cause))))))

(defn inspect-file-header
  "Run the actual guest header parser. Text/file-name accept host immutable
   strings or borrowed guest String references. Return :header and updated raw
   :session/:world; erroneous headers authorize no imports."
  ([session world text file-name] (inspect-file-header session world text file-name {}))
  ([session world text file-name options]
   (let [file-name-host (codec/decode world :string file-name)
         _ (codec/decode world :string text)
         world (-> world (m/retain text 1) (m/retain file-name 1))
         result (raw/call session world (or (:header-target options) header-target) [text file-name m/erased])]
     (checked-result result (fn []
                              (let [world (:state result) wrapper (:value result)
                                    value (codec/decode world :string (io-ok! world wrapper))
                                    world (assoc (m/release world wrapper 1) :result 0)
                                    header (envelope! value "lean-file-header/1" "RuntimeCompileShim.inspectFileHeader" file-name-host)]
                                (when-not (and (boolean? (:hasErrors header))
                                               (integer? (:headerEndByte header)) (<= 0 (:headerEndByte header))
                                               (or (not (:hasErrors header)) (empty? (:requestedImports header))))
                                  (fail "Invalid frontend header result" {}))
                                {:session (:session result) :world world :header header}))))))

(defn- install-decoded-file
  "Install one decoded compiler packet with real owner checkpoints. The final
   installed World is a separate candidate until its matching session opens."
  [base roots configuration]
  (let [entry-world (:world base) entry-session (:session base)
        active (atom entry-session)
        coherent (volatile! {:world entry-world :session entry-session})
        last-call (volatile! nil) installed-result (volatile! nil) unpaired (volatile! nil)
        matches? (fn [world session]
                   (and (map? world) (map? session) (map? (:functions world))
                        (map? (:functions session)) (= (:functions world) (:functions session))))
        record! (fn [world session phase]
                  (if (matches? world session)
                    (vreset! coherent {:world world :session session :phase phase})
                    (do (vreset! unpaired {:world world :session session :phase phase})
                        (fail "Frontend installation checkpoint has no matching raw session" {})))
                  world)
        checkpoint! (fn [world] (record! world @active :owner-checkpoint))
        invoke (fn [world target args]
                 (record! world @active :helper-entry)
                 (let [called (raw/call @active world target args)]
                   ;; Preserve the ACTUAL envelope before any validation or
                   ;; adoption; all host owner checkpoints share this ledger.
                   (vreset! last-call {:target target :arguments args :returned called})
                   (reset! active (:session called))
                   (record! (:state called) (:session called) :helper-returned)
                   [(:state called) (:value called)]))]
    (try
      (let [bindings (:bindings entry-session)
            custom (get-in configuration [:install-options :lower-extern])
            lower (fn [row]
                    (if (contains? bindings (abi/symbol-for (get-in row [:ir :extern])))
                      (raw/lower bindings row) (when custom (custom row))))
            installed (eval/install-file-bundle {:invoke invoke :checkpoint! checkpoint!}
                        entry-world (:environment base) roots (get-in base [:envelope :bundle])
                        (assoc (:install-options configuration) :initialize? false :lower-extern lower
                          :witness (or (get-in configuration [:install-options :witness]) (helper "exportEvalConstWitness"))
                          :trusted-functions (:functions entry-session)))
            ;; Installation may add functions. Do NOT pair this candidate with
            ;; the preceding raw session if constructing its new session fails.
            _ (vreset! installed-result installed)
            world (:world installed)
            session @active
            next-session (raw/open-functions (:functions world) bindings
                           (assoc (select-keys session [:backend :fuel :compile-threshold])
                             :cache (or (get-in session [:program :cache]) (:cache session))))
            _ (reset! active next-session)
            _ (record! world next-session :session-reopened)]
        (assoc base :world world :session next-session
          :boxed-entrypoints (:boxed-entrypoints installed)
          :pending-local-initializers (:pending-local-initializers installed)
          :handle {:module-name (get-in base [:envelope :mainModule]) :file-name (:file-name base)
                   :boxed-entrypoints (:boxed-entrypoints installed) :unit-digest (:unit-digest installed)}))
      (catch Throwable cause
        (let [data (ex-data cause)
              child-world (:checkpoint data)
              child-session (or (:checkpoint-session data) (:session data) @active)
              latest (if (and child-world (matches? child-world child-session))
                       {:world child-world :session child-session} @coherent)]
          (throw (ex-info (or (.getMessage cause) "Frontend file installation failed")
                   (assoc data :checkpoint (:world latest) :checkpoint-session (:session latest)
                     :session (:session latest) :frontend-installation-entry base
                     :frontend-installation-last-call @last-call
                     :frontend-installation-installed-candidate @installed-result
                     :frontend-installation-unpaired-checkpoint @unpaired
                     :frontend-installation-child-failure data) cause)))))))

(defn finish-compilation-refs
  "Finish an independently completed raw compileImportedFileState invocation.
   RESULT must carry the actual done world/value and its matching session. The
   original :file-name and borrowed :roots are required. This runs only result
   decoding and strict bundle installation; it never resumes guest execution or
   retries a handler. Returned Environment is owned. Failure preserves the
   original owned IO result separately from any later helper checkpoint."
  ([result arguments] (finish-compilation-refs result arguments {}))
  ([result {:keys [file-name roots]} configuration]
   (when-not (and (map? (:state result)) (map? (:session result))
                  (map? (get-in result [:state :functions]))
                  (= :done (get-in result [:state :status]))
                  (= (:value result) (get-in result [:state :result]))
                  (identical? (get-in result [:state :functions]) (get-in result [:session :functions])))
     (fail "Expected completed frontend raw result with matching session" {}))
   (when (get-in configuration [:install-options :initialize?])
     (fail "Frontend installation requires separate explicit initialization" {}))
   (let [file-name-host (codec/decode (:state result) :string file-name)
         _ (reference! (:state result) roots :roots)
         decoded (volatile! nil)]
     (checked-result result (fn []
                            (try
                              (let [world (:state result) wrapper (:value result)
                                    pair (io-ok! world wrapper)
                                    [returned-env envelope-string] (:fields (ctor! world pair 0 2))
                                    _ (reference! world returned-env :returned-environment)
                                    envelope-text (codec/decode world :string envelope-string)
         ;; The pair owns the Environment. Save that owner BEFORE dropping pair
         ;; and IO wrapper, even on a diagnostic/failure result.
                                    world (m/retain world returned-env 1)
                                    _ (vreset! decoded {:checkpoint world :environment returned-env
                                                       :environment-state :owned :wrapper-state :owned})
                                    world (assoc (m/release world wrapper 1) :result 0)
                                    _ (vreset! decoded {:checkpoint world :environment returned-env
                                                       :environment-state :owned :wrapper-state :released})
                                    envelope (envelope! envelope-text "lean-file-compilation/1"
                                                        "RuntimeCompileShim.compileImportedFileState" file-name-host)
                                    _ (name! (:mainModule envelope))
                                    _ (when-not (and (boolean? (:success envelope))
                                                     (contains? #{"header" "imports" "module-name" "commands" "exports" "complete"} (:stage envelope))
                                                     (contains? #{"input" "prepared" "after-commands"} (:environmentState envelope))
                                                     (if (:success envelope)
                                                       (and (= "complete" (:stage envelope)) (string? (:bundle envelope)))
                                                       (nil? (:bundle envelope))))
                                        (fail "Invalid frontend compilation result" {}))
                                    base {:session (:session result) :world world :environment returned-env
                                          :success (:success envelope) :diagnostics (:diagnostics envelope)
                                          :envelope envelope :boxed-entrypoints {} :handle nil}]
                                (if-not (:success envelope) base
                                        (dissoc (install-decoded-file (assoc base :file-name file-name-host) roots configuration)
                                                :file-name)))
                              (catch Throwable cause
                                (if-let [owner @decoded]
                                  (let [data (ex-data cause)]
                                    (throw (ex-info (or (.getMessage cause) "Frontend result decoding failed")
                                             (merge {:checkpoint (:checkpoint owner)
                                                     :checkpoint-session (:session result)}
                                                    data {:frontend-decoder-ownership owner}) cause)))
                                  (throw cause)))))))))

(defn compile-file-refs
  "Compile against the supplied imported :environment, with borrowed guest
   :module-name (Name), :roots (Array Name), and :options (Options) references.
   :text/:file-name may be host strings or guest String refs. The helper owns
   retained copies of every argument. Failed envelopes retain actual partial
   environment and diagnostics, and install no final bundle. :install-options
   follow eval/install-bundle except :initialize? true is forbidden here."
  ([session world arguments] (compile-file-refs session world arguments {}))
  ([session world {:keys [environment text file-name module-name roots options]} configuration]
   (when (get-in configuration [:install-options :initialize?])
     (fail "Frontend installation requires separate explicit initialization" {}))
   (doseq [[label value] [[:environment environment] [:roots roots] [:options options]]]
     (reference! world value label))
   (if (m/ref? module-name) (m/node world module-name)
     ;; Name.anonymous is the valid nullary immediate zero.
       (codec/decode world :unit module-name))
   (let [file-name-host (codec/decode world :string file-name)
         _ (codec/decode world :string text)
         arguments [environment text file-name module-name roots options]
         world (reduce #(m/retain %1 %2 1) world arguments)
         result (raw/call session world (or (:compile-target configuration) compile-target) (conj arguments m/erased))]
     (finish-compilation-refs result {:file-name file-name :roots roots} configuration))))

(defn compile-file
  "Structured-name convenience layer. :module-name is a Java Name and :roots a
   vector of Java Names; no dotted-string guessing. Configuration must provide
   :encode-name and :encode-names callbacks with guest-encoding's signature
   [world invoke value options] -> [world owned-guest-value]. :encoder-options
   are passed unchanged. Options remain an explicit borrowed guest reference."
  ([session world arguments] (compile-file session world arguments {}))
  ([session world arguments {:keys [encode-name encode-names encoder-options] :as configuration}]
   (when-not (and (fn? encode-name) (fn? encode-names) (vector? (:roots arguments)))
     (fail "Structured frontend compilation requires explicit Name encoders and vector roots" {}))
   (let [active-session (atom session)
         progress (volatile! world)
         temporaries (volatile! [])
         invoke (fn [world target args]
                  (let [result (raw/call @active-session world target args)]
                    (reset! active-session (:session result))
                    (vreset! progress (:state result))
                    [(:state result) (:value result)]))]
     (try
       (let [[world module] (encode-name world invoke (:module-name arguments) encoder-options)
             _ (vreset! progress world)
             _ (vswap! temporaries conj module)
             [world roots] (encode-names world invoke (:roots arguments) encoder-options)
             _ (vreset! progress world)
             _ (vswap! temporaries conj roots)
             result (compile-file-refs @active-session world
                                       (assoc arguments :module-name module :roots roots) configuration)]
         ;; Each successful encoder produced a named owner even if a subsequent
         ;; encoder fails. Only the successful path discharges these temporaries.
         (update result :world #(-> % (m/release module 1) (m/release roots 1))))
       (catch Throwable cause
         (let [data (ex-data cause)]
           (throw (ex-info (or (.getMessage cause) "Structured frontend compilation failed")
                           (merge {:checkpoint @progress :checkpoint-session @active-session}
                                  data
                                  {:session (or (:checkpoint-session data) (:session data) @active-session)
                                   :frontend-temporary-owners @temporaries}) cause))))))))
