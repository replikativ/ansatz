(ns general-command-receipt-v1
  "Observed original parse/elaboration receipts. No body-language recognizer,
   automatic unwind, generic module import, or execution-success inference."
  (:require [java-ir-baseline :as j] [sequential-frontend-probe :as sp]
            [generated-command-receipt-v1 :as finite]
            [artifact-checked-declaration-adapter-v4 :as adapter]
            [artifact-declaration-authority-v4 :as authority]
            [ansatz.research.ir.node-decoder-v1 :as decoder]
            [ansatz.research.ir.source-setup :as source])
  (:import [java.util WeakHashMap LinkedHashMap IdentityHashMap ArrayDeque]))
(deftype SourceCaptures [])
(deftype CommandRun [])
(deftype CommandReceipt [])
(defonce ^:private providers (WeakHashMap.))
(defonce ^:private runs (WeakHashMap.))
(defonce ^:private receipts (WeakHashMap.))
(defonce ^:private busy (WeakHashMap.))
(def ^:private entry-label "ObservedFrontendCommand.processCommandObserved._boxed")
(def ^:private header-contract
  {:entry [entry-label "113a457b6e4cf7826300e2e19c0dcdd627139a4faf4c3f4bae4701cb4e58b8cd"]
   :caller ["ObservedFrontendCommand.processCommandObserved" "17983ef01b12b3e0ba4b896fa62950541f48cb64e5d8dcca46bededeacc9dcb8"]
   :gate ["ObservedFrontendCommand.beforeElaboration" "bf96d5878e30e9e49eaf2b451742599e044afaaaea7f16423a9653fe6f49ecb9"]
   :parser-errors ["Lean.MessageLog.hasErrors._boxed" nil]})
(defn- need [ok message] (when-not ok (throw (ex-info message {:profile :general-command-v1}))))
(defn- issued [registry token]
  (locking registry (or (.get ^WeakHashMap registry token) (throw (ex-info "Actual issued generic token required" {})))))
(defn- put! [registry token holder] (locking registry (.put ^WeakHashMap registry token holder)) token)
(defn- field [x k] (#'finite/field x k))
(defn- ctx [holder] (#'finite/ctx @holder))
(defn- engine [holder] (#'finite/engine @holder))
(defn- live! [holder] (#'finite/live! holder))
(defn- observe! [holder key argument] (#'finite/observe! holder key argument))
(defn- decode-limits []
  {:deadline-nanos (+ (System/nanoTime) 10000000000)
   :max-nodes (min 100000 (:max-nodes decoder/defaults))
   :max-output (min 200000 (:max-output decoder/defaults))
   :max-depth (min 1000 (:max-depth decoder/defaults))
   :max-chars (min 2000000 (:max-chars decoder/defaults))})
(defn source-captures
  "TRUSTED SOURCE ADAPTER constructor, not map/Boolean verification. Root must
   authenticate the companion overlay, exact Headers, source/layout/protected
   policy and opaque gate receipt implementation before constructing these hooks."
  [receipt {:keys [headers] :as hooks}]
  (doseq [key [:check! :before-command! :before-call! :after-taken! :inspect-observation!
               :check-gate! :check-observed-result!]]
    (need (fn? (get hooks key)) "Complete actual source/gate observer required"))
  (need (= #{:entry :caller :gate :parser-errors} (set (keys headers))) "Four actual source Headers required")
  ;; Mint once per actual captured file/provider and reuse across its commands.
  ;; Marker is neither an opaque registry key nor a caller-supplied flag.
  (put! providers (SourceCaptures.) {:receipt receipt :hooks (into {} hooks) :headers (into {} headers) :file-marker (Object.)}))
(defn- authenticate-header! [driver receipt header]
  (let [name (j/lean-name-data (j/request-value header "name"))
        entry (source/lookup-entry receipt name)]
    (need entry "Header not in this actual authenticated source receipt")
    (source/authenticate-canonical-header! (:source driver) (:row entry) (:sha256 entry) header)
    (#'finite/exact-header! {:frontend {:driver driver} :source (:source driver)} header)
    header))
(defn- ir-map! [decls limit]
  (need (<= (count decls) limit) "Cumulative local IR row budget exceeded")
  (reduce (fn [out row]
            (need (and (map? row) (= 1 (count row))) "Malformed decoded local IR declaration")
            (let [[kind raw] (first row) name (get raw "f")]
              (need (and (contains? #{"fdecl" "extern"} kind) (vector? name)
                         (not (contains? out name))) "Duplicate/unsupported local IR declaration")
              (assoc out name {:kind kind :declaration raw}))) {} decls))
(defn- gate-site! [holder request]
  (let [e (engine holder) s @holder call (field request "call") active (field e "active")
        prepared (field e "activePrepared") program (:program (ctx holder))
        _ (need (and (identical? (get-in s [:headers :caller]) (field active "header"))
                     (identical? active (field prepared "caller"))
                     (identical? active (aget ^objects (field program "functions") (int (field active "id"))))
                     (identical? prepared (aget ^objects (field program "preparedBodies") (int (field active "id"))))
                     (identical? request (j/host-request (ctx holder) e))
                     (identical? (field request "owner") (field e "runtimeIdentity"))
                     (identical? (get-in s [:headers :gate]) (field (field call "function") "header"))
                     (identical? (field call "next") (field e "pc"))
                     (= 41 (field call "dest")) (false? (field call "facade"))) "Gate is not the actual companion FAP continuation")
        queue (ArrayDeque.) seen (IdentityHashMap.) matches (atom [])]
    (.push queue (field prepared "body"))
    (while (not (.isEmpty queue))
      (let [body (.pop queue)]
        (when-not (.containsKey seen body)
          (.put seen body true) (need (<= (.size seen) 4096) "Companion prepared-site bound")
          (let [expr (field body "expr")]
            (when (and (= 0 (field body "op")) expr (= 3 (field expr "op"))
                       (identical? (field expr "target") (field call "function")))
              (swap! matches conj body)))
          (doseq [key ["next" "body"] :let [child (field body key)] :when child] (.push queue child))
          (when-let [alternatives (field body "alternatives")]
            (doseq [child alternatives :when child] (.push queue child))))))
    (need (= 1 (count @matches)) "Companion gate site is not unique")
    (let [site (first @matches) next (field site "next") next-expr (field next "expr")]
      (need (and (= 41 (field site "a"))
                 (= [1 4 24 25 26 0] (vec (field (field site "expr") "args")))
                 (identical? next (field call "next")) (= 42 (field next "a"))
                 (= 3 (field next-expr "op"))
                 (= "Lean.Elab.Frontend.elabCommandAtFrontend" (field (field next-expr "target") "label"))
                 (= [24 1 2 0] (vec (field next-expr "args")))) "Companion gate/next-body differs from authenticated compiled layout"))))
(defn- begin-gate! [holder request]
  (let [s (live! holder) c (ctx holder) e (engine holder) args (vec (j/request-value request "arguments"))]
    (need (nil? (:gate s)) "Repeated/spurious parser gate")
    (need (and (= ["object" "object" "tobject" "object" "object" "void"] (vec (j/request-value request "paramTypes")))
               (= [true true true true true false] (vec (j/request-value request "borrowed")))
               (= "tagged" (j/request-value request "resultType")) (= 6 (count args))
               (instance? Long (peek args)) (zero? (peek args))) "Observed gate ABI/world differs")
    (gate-site! holder request)
    (need (and (identical? (first args) (get-in s [:capture :input]))
               (identical? (second args) (get-in s [:initial :state]))) "Gate InputContext/beforeState is not this actual command snapshot")
    (doseq [i (range 5)] (#'finite/retain! holder [:gate :operand i] (nth args i)))
    (let [log (nth args 4) argument (#'finite/retain! holder [:gate :helper-argument] log)
          argument-slot (.get ^LinkedHashMap (:owners @holder) [:gate :helper-argument])
          token-slot (object-array 1) result-slot (#'finite/new-slot! holder [:gate :parser-errors])
          gate {:request request :arguments (subvec args 0 5) :token-slot token-slot
                :result-slot result-slot :stage :helper-pending}
          descriptor (j/host-owned-argument c argument)]
      (swap! holder assoc :gate gate)
      (aset ^objects argument-slot 1 :start-pending)
      (let [token (j/start-host-guest! c e request (get-in s [:headers :parser-errors]) [descriptor])]
        (aset token-slot 0 token) (aset ^objects argument-slot 1 :transferred)
        (swap! holder assoc-in [:gate :stage] :helper-running)))))
(defn- finish-gate! [holder]
  (let [s (live! holder) c (ctx holder) e (engine holder) gate (:gate s)
        token (aget ^objects (:token-slot gate) 0) slot ^objects (:result-slot gate)]
    (need (and token (identical? token (j/host-guest-result c e))
               (identical? (get-in s [:headers :parser-errors]) (j/request-value token "helperHeader"))
               (identical? (:request gate) (j/request-value token "outerRequest"))
               (= 1 (count (j/request-value token "arguments")))
               (identical? (nth (:arguments gate) 4) (first (j/request-value token "arguments")))) "Actual parser-error helper token differs")
    (aset slot 1 :take-pending)
    (let [result (j/take-host-guest-result! c e (:request gate) token)]
      (aset slot 0 result) (aset slot 1 :owned)
      (need (and (instance? Long result) (zero? result)) "Parser errors prevent successful command/file")
      (let [receipt (observe! holder :check-gate! {:engine e :source (:source s) :request (:request gate)
                         :arguments (:arguments gate) :initial-observation (:initial s) :capture (:capture s)
                         :parse-error-token token})]
        (need receipt "Source policy did not return its actual opaque gate receipt")
        (swap! holder assoc-in [:gate :receipt] receipt)
        (swap! holder assoc-in [:gate :stage] :reply-pending)
        (j/resume-host! c e (:request gate) (long 0))
        (swap! holder assoc-in [:gate :stage] :replied)))))
(defn- drain! [holder slot]
  (loop []
    (let [s (live! holder) f (:frontend s) c (ctx holder) e (engine holder) phase (j/phase c e)
          request (when (= "host-call" phase) (j/host-request c e))
          header (when request (field (field request "call") "function"))]
      (sp/check-time! f) (#'finite/entry-live! s (:operation s))
      (cond
        (= "complete" phase) (do (aset ^objects slot 1 :take-pending) (j/take-result! c e))
        (= "code-call" phase) (do (sp/charge! f :turns 1) (sp/charge! f :code-requests 1)
                                   ((sp/host-helper "service-code!") (:driver f)) (recur))
        (= "running" phase) (let [left (- (get-in f [:limits :instructions]) (:instructions @(:used f)))
                                     before (j/instructions c e)]
                                 (need (pos? left) "Command instruction budget exhausted") (sp/charge! f :turns 1)
                                 (j/advance! c e (min (:quantum s) left))
                                 (sp/charge! f :instructions (- (j/instructions (ctx holder) e) before)) (recur))
        (and request (identical? (get-in s [:headers :gate]) (field header "header")))
        (do (begin-gate! holder request) (recur))
        (and (= "host-guest-result" phase) (= :helper-running (get-in s [:gate :stage]))
             (identical? (aget ^objects (get-in s [:gate :token-slot]) 0) (j/host-guest-result c e)))
        (do (finish-gate! holder) (recur))
        (and (contains? #{"host-call" "host-guest-result"} phase) (:runtime-step! f))
        (do (sp/charge! f :turns 1) ((:runtime-step! f) f) (recur))
        :else (throw (ex-info "Unsupported observed-command runtime boundary; preserve exact operation" {:phase phase :stage (:stage s)}))))))
(defn open-command!
  [frontend strict-driver captures {:keys [layout-directory quantum row-limit]
                                    :or {quantum 1000 row-limit 2048}}]
  (need (and (integer? quantum) (<= 100 quantum 10000) (integer? row-limit) (<= 1 row-limit 2048)) "Explicit bounded generic policy required")
  (let [{:keys [receipt hooks headers file-marker]} (issued providers captures) driver (:driver frontend)
        _ (source/guard-source! receipt (:source driver))
        _ (doseq [[role h] headers
                  :let [[label sha] (get header-contract role)]]
            (need (and (= (sp/typed-name label) (j/lean-name-data (j/request-value h "name")))
                       (or (nil? sha) (= sha (j/request-value h "originalSha256")))) "Companion/helper role differs from pinned source")
            (authenticate-header! driver receipt h))
        token (CommandRun.) holder (atom {:status :open :thread (Thread/currentThread) :stage :open
              :frontend frontend :strict-driver strict-driver :source (:source driver) :receipt receipt :hooks hooks :headers headers :file-marker file-marker
              :layout (#'authority/read-layout! layout-directory) :owners (LinkedHashMap.) :quantum quantum :row-limit row-limit
              :controller-headers {entry-label (:entry headers)}
              :controller-drain drain! :controller-decode-limits decode-limits})]
    (live! holder)
    (need (= "idle" (j/phase (ctx holder) (engine holder))) "Observed command opens only at idle boundary")
    (put! runs token holder)))
(defn- final-version! [holder observation]
  (let [s @holder session (get-in s [:strict-driver :adapter]) version (peek @(:versions session))
        actual (#'authority/environment-view! (:driver (:frontend s)) (:layout s) (:environment observation))
        expected (#'authority/kernel-view! (:driver (:frontend s)) (:layout s) (aget ^objects (:kernel-root version) 0))]
    (need (and (identical? (:constant-map actual) (aget ^objects (:constant-map version) 0))
               (identical? (:const2mod-map actual) (:const2mod-map expected))
               (every? true? (map identical? (rest (:header-fields actual)) (rest (:header-fields expected)))))
          "Final frontend Env is not the actual last replied checked version") version))
(defn run-command! [run]
  (let [holder (issued runs run) s (live! holder) f (:frontend s) d (:driver f) session (get-in s [:strict-driver :adapter]) e (engine holder)]
    (need (= :open (:status s)) "Observed command can start only once")
    (locking busy (need (not (.containsKey busy e)) "Observed command already owns this engine") (.put busy e true))
    (swap! holder assoc :status :running :stage :capture)
    (try
      (let [capture (observe! holder :before-command! {:engine e :source (:source s) :frontend f
                       :input (sp/owned f :input) :state-ref (sp/owned f :state-ref)})
            _ (need (and (identical? e (:engine capture)) (identical? (:source s) (:source capture))
                         (identical? (sp/owned f :input) (:input capture)) (identical? (sp/owned f :state-ref) (:state-ref capture))) "Source capture lacks actual roots")
            _ (swap! holder assoc :capture capture :stage :baseline)
            command-index (get-in capture [:description :command-index])
            _ (need (and (integer? command-index) (<= 0 command-index 127)) "Actual captured command index exceeds generic policy")
            initial (#'finite/snapshot! holder :before)
            _ (swap! holder assoc :initial initial)
            _ (when (empty? @(:versions session)) (adapter/establish-base! session (:environment initial)))
            prior (:id (peek @(:versions session)))
            baseline (ir-map! (#'finite/decode! holder (#'finite/call-borrowed! holder :baseline "Lean.IR.getDecls" [(:environment initial)])) (:row-limit s))
            _ (swap! holder assoc :prior-version prior :baseline baseline :stage :process-command)
            _ (sp/charge! f :commands 1)
            result (#'finite/call-borrowed! holder :process entry-label
                                          [(sp/owned f :input) (sp/owned f :state-ref) 0])
            _ (need (= :replied (get-in @holder [:gate :stage])) "No actual approved parser gate")
            _ (swap! holder assoc :stage :observed)
            after (#'finite/snapshot! holder :after)
            gate (:gate @holder)
            view (observe! holder :check-observed-result! {:engine e :source (:source s) :result result
                      :gate-receipt (:receipt gate) :arguments (:arguments gate) :initial-observation initial
                      :final-observation after :capture capture})
            _ (need (and (contains? #{:command :eoi :exit :import} (:kind view))
                         (every? true? (map identical? (:arguments gate)
                                             (map view [:input :before-state :syntax :parser-state :parser-messages])))) "Actual companion observation differs from its gate")
            errors (#'finite/call-borrowed! holder :elaboration-errors "Lean.MessageLog.hasErrors" [(:elaboration-messages view)])
            _ (need (and (instance? Long errors) (zero? errors)) "Elaboration/compiler diagnostics contain errors")
            history (adapter/complete-command-history! session prior)
            version (final-version! holder after)
            post (ir-map! (#'finite/decode! holder (#'finite/call-borrowed! holder :post "Lean.IR.getDecls" [(:environment after)])) (:row-limit s))
            _ (doseq [[name row] baseline] (need (= row (get post name)) "Original compiler changed a historical local IR row"))
            delta (apply dissoc post (keys baseline))
            _ (when (not= :command (:kind view))
                (need (and (empty? history) (empty? delta)) "Terminal source transaction changed checked versions or IR"))
            _ (need (not= :import (:kind view)) "Late import is not completed-file EOF")
            source-policy (when (= :observed-classic-prelude-command-v1 (get-in capture [:description :profile]))
                            {:profile :observed-classic-prelude-command-v1 :kind (:kind view)
                             :requirements-policy :no-local-initializers-exports-externs-redirects-v1})
            _ (swap! holder assoc :stage :cleanup :observation view :version version :version-marker (Object.)
                           :delta delta :history history :post-ir post :source-policy source-policy :command-index command-index)
            _ (#'finite/clean-temporaries! holder)
            _ (#'adapter/validate-versions! session)
            description (#'finite/frozen-host (:description capture))
            summary {:schema "observed-original-command/1" :kind (:kind view) :source-description description
                     :start-pos (:start-pos view) :end-pos (:end-pos view) :prior-version prior :version (:id version)
                     :publications history :new-ir-names (vec (keys delta)) :new-ir-rows (count delta)
                     :execution :not-prepared :initialization :requires-separate-policy}
            _ (#'finite/frozen-host summary)
            receipt (CommandReceipt.)]
        (swap! holder assoc :status :sealed :stage :sealed :summary summary :base-program (:program (ctx holder)))
        (put! receipts receipt holder)
        {:status :sealed :receipt receipt :summary summary})
      (catch Throwable error
        (let [message (or (.getMessage error) (.getName (class error)))]
          (swap! holder assoc :status :failed :failure {:class (.getName (class error)) :message (subs message 0 (min 900 (count message)))})
          {:status :failed :run run :stage (:stage @holder) :failure (:failure @holder)})))))
(defn owner-packet [run]
  (let [s @(issued runs run)] (select-keys s [:status :stage :operation :gate :owners :failure])))
(defn with-command!
  "Internal trusted batch adapter lease. Never accept caller-supplied rows or a
   public summary in its place. No bare Env is a portable checking certificate."
  ([receipt callback] (with-command! receipt nil callback))
  ([receipt scope-binding callback]
   (let [holder (issued receipts receipt) s (live! holder) d (get-in s [:frontend :driver])
         session (get-in s [:strict-driver :adapter])
         binding {:engine (:engine d) :source (:source d) :adapter session :current-ctx (:current-ctx d)}]
     (need (and (= :sealed (:status s)) (= "idle" (j/phase (ctx holder) (engine holder)))) "Actual successful unretired idle command required")
     (need (or (nil? scope-binding)
               (and (map? scope-binding) (= (set (keys binding)) (set (keys scope-binding)))
                    (every? (fn [[key value]] (identical? value (get binding key))) scope-binding)))
           "Foreign generated-code scope binding")
     (#'adapter/validate-versions! session)
     (need (identical? (:version s) (peek @(:versions session))) "Checked version advanced after command")
     (let [before (#'finite/hook-stamp (engine holder))
           view {:driver d :engine (:engine d) :source (:source d) :source-receipt (:receipt s)
                             :file-marker (:file-marker s) :command-index (:command-index s)
                             :adapter session :version-id (get-in s [:version :id]) :version-marker (:version-marker s)
                             :base-program (:base-program s) :before-ir (:baseline s) :after-ir (:post-ir s)
                             :delta (:delta s) :source-policy (:source-policy s) :summary (:summary s)}]
       (try (callback view)
         (finally
           (live! holder) (#'adapter/validate-versions! session)
           (let [after (#'finite/hook-stamp (engine holder))]
             (need (and (identical? (:version s) (peek @(:versions session)))
                        (= "idle" (j/phase (ctx holder) (engine holder)))
                        (= (:counts before) (:counts after)) (= (:flags before) (:flags after))
                        (every? true? (map identical? (rest (:identities before)) (rest (:identities after)))))
                   "Batch metadata callback advanced guest state or changed checked version"))))))))
(defn receipt-summary [receipt] (with-command! receipt :summary))
(defn retire! [run]
  (let [holder (issued runs run) s (live! holder) e (engine holder)]
    (need (and (= :sealed (:status s)) (= "idle" (j/phase (ctx holder) (engine holder)))) "Retire only a healthy completed command")
    (swap! holder assoc :stage :retiring)
    (try
      (#'finite/release-slot! holder [:after :env])
      (live! holder) (#'adapter/validate-versions! (get-in s [:strict-driver :adapter]))
      (need (identical? (:version s) (peek @(:versions (get-in s [:strict-driver :adapter]))))
            "Command retirement changed checked history outside its receipt")
      (locking busy (.remove busy e))
      (reset! holder {:status :retired :stage :retired :summary (:summary s)})
      {:status :retired}
      (catch Throwable error (swap! holder assoc :status :failed :stage :retirement-failed) (throw error)))))
