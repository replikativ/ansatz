(ns artifact-checked-declaration-adapter-v4
  "Artifact-relative safe declaration checking; no active association forks."
  (:require [java-ir-baseline :as j]
            [clojure.set]
            [ansatz.research.ir.kernel-projection :as projection]
            [prototype.kernel-bridge :as bridge]
            [prototype.kernel-projection-snapshot :as snapshot]
            [prototype.imported-kernel :as imported]
            [java-composite-artifact-base-v1 :as base])
  (:import [ansatz.kernel Env ConstantInfo] [java.util LinkedHashMap]))
(defn- reject [message] (throw (ex-info message {:profile :artifact-checked-declaration-v4})))
(defn- need [condition message] (when-not condition (reject message)))
(defn- private-value [value field]
  (let [f (doto (.getDeclaredField (class value) field) (.setAccessible true))] (.get f value)))
(defn- invoke1 [target method value]
  (let [m (doto (.getDeclaredMethod (class target) method (into-array Class [Object])) (.setAccessible true))]
    (.invoke m target (object-array [value]))))
(defn- ctor [session value tag fields]
  (let [node (invoke1 (:engine session) "constructorNode" value)
        fs ^objects (.get ^java.lang.reflect.Field (:fields (:basis session)) node)
        bytes ^bytes (.get ^java.lang.reflect.Field (:scalars (:basis session)) node)]
    (need (and (nil? (private-value node "closure")) (= tag (.getInt ^java.lang.reflect.Field (:tag (:basis session)) node))
               (= fields (alength fs)) (zero? (alength bytes))) "Unexpected ordinary constructor layout")
    node))
(defn- fields [session value] (.get ^java.lang.reflect.Field (:fields (:basis session)) value))
(def ^:private declaration-kinds
  {0 {:kind :axiom :declaration-projection :axiom-declaration :value-projection :axiom-val
      :publication "postCheckSafeAxiom"}
   1 {:kind :definition :declaration-projection :declaration :value-projection :definition-val
      :publication "postCheckSafeDefinition"}
   2 {:kind :theorem :declaration-projection :theorem-declaration :value-projection :theorem-val
      :publication "postCheckTheorem"}
   5 {:kind :mutual-definition :declaration-projection :mutual-declaration
      :publication "postCheckMutualDefinitions"}})
(defn- descriptor! [session value]
  (let [node (invoke1 (:engine session) "constructorNode" value)
        tag (.getInt ^java.lang.reflect.Field (:tag (:basis session)) node)
        descriptor (get declaration-kinds tag)]
    (need descriptor "Unsupported declaration/constant kind")
    (ctor session value tag 1)
    descriptor))
(defn- group-payloads! [session list-root]
  (loop [value list-root out [] seen #{}]
    (if (and (instance? Long value) (zero? value)) out
      (do
        (need (< (count out) 256) "Mutual group exceeds member bound")
        (need (not (contains? seen value)) "Cyclic mutual definition list")
        (ctor session value 1 2)
        (let [fs ^objects (fields session value)]
          (recur (aget fs 1) (conj out (aget fs 0)) (conj seen value)))))))
(defn- generated-admission! [session request]
  (let [n (find-ns 'general-command-receipt-v1) guard (when n (ns-resolve n 'assert-generated-admission!))]
    (need guard "Generated mutual group requires an actual active observed source command")
    (guard session request)))
(defn- tagged-bool [value]
  (need (and (instance? Long value) (contains? #{0 1} value)) "Expected exact boxed Bool") value)
(defn- request-header [request] (private-value (private-value request "call") "function"))
(defn- actual-header [request] (private-value (request-header request) "header"))
(defn- source-live! [session]
  (need (identical? (:thread session) (Thread/currentThread)) "Adapter session is thread confined")
  ;; Independent accepted source/resource lease authority; never a :verified map flag.
  ((get-in session [:authority :check-source!]) (:engine session) (:source session)))
(defn- readonly-witness! [session witness kernel]
  (need (and (map? witness) (identical? kernel (:kernel-root witness))
             (identical? (:source session) (:source-binding witness))
             (= (get-in session [:authority :layout-receipt-sha256]) (:layout-receipt-sha256 witness)))
        "Read-only witness lacks the actual root/source/compiled-layout receipt")
  witness)
(defn- diagnostics! [session kernel root-token]
  (let [w (readonly-witness! session ((get-in session [:authority :diagnostics-disabled!]) (:engine session) kernel root-token) kernel)]
    (need (= 0 (:enabled w)) "Kernel diagnostics enabled/unsupported")))
(defn- failure! [session inv failure]
  ;; Bounded scalars only; neither raw ex-data aliases nor exception cause survive.
  (let [message (try (or (.getMessage ^Throwable failure) (.getName (class failure)))
                     (catch Throwable _ "Adapter failure"))
        receipt {:stage (:stage @inv) :message (subs message 0 (min 900 (count message)))
                 :class (.getName (class failure))}]
    (swap! inv assoc :failure receipt) (reset! (:phase session) :failed)
    {:status :failed :failure receipt}))
(defn- validate-local-view! [session entry]
  (base/with-version! (:matched-base session) (:env entry)
    (fn [^Env env]
      (let [projected (reduce (fn [out segment]
                                (snapshot/validate-segment-values segment)
                                (doseq [[name ^ConstantInfo ci] (:projected segment)]
                                  (need (not (contains? out name)) "Overlapping local snapshot segments")
                                  (need (identical? ci (.lookupLocal env name)) "Local snapshot CI is not the actual Env member"))
                                (into out (:projected segment))) {} (:segments entry))
            locals (vec (.allConstants env)) names (mapv #(.name ^ConstantInfo %) locals)]
        (need (and (= (count names) (count (set names)) (count (:payloads entry)))
                   (= (set names) (set (keys (:payloads entry))) (set (keys projected)))
                   (empty? (clojure.set/intersection (set names) (base/domain-names (:matched-base session)))))
              "Private local overlay domain differs from the checked version")
        (doseq [^ConstantInfo ci locals]
          (need (and (identical? ci (get projected (.name ci)))
                     (identical? ci (.lookupLocal env (.name ci))))
                "Private local overlay CI identity changed"))))))
(defn- validate-candidate! [session inv]
  (when-let [candidate (:candidate @inv)] (validate-local-view! session candidate)))
(defn- slot [value status] (object-array [value status]))
(defn- slot-value [slot] (aget ^objects slot 0))
(defn- slot-state [slot] (aget ^objects slot 1))
(defn- state! [slot state] (aset ^objects slot 1 state))
(defn- owner! [inv key] (or (.get ^LinkedHashMap (:owners @inv) key) (reject "Missing occurrence slot")))
(defn- add-owner! [inv key value]
  (need (nil? (.get ^LinkedHashMap (:owners @inv) key)) "Duplicate owner occurrence slot")
  (let [s (slot value :owned)] (.put ^LinkedHashMap (:owners @inv) key s) s))
(defn- retain-into! [session inv key value]
  ;; Allocate/record the occurrence before retain. Rejection leaves :unclaimed.
  (let [s (slot value :unclaimed)]
    (need (nil? (.putIfAbsent ^LinkedHashMap (:owners @inv) key s)) "Duplicate retained occurrence")
    (j/retain! (:basis session) (:engine session) value) (state! s :owned) s))
(defn- validate-versions! [session]
  (base/guard! (:matched-base session))
  (doseq [entry @(:versions session)]
    (need (and (identical? (:source session) (:source entry)) (true? (:quot entry))
               (identical? (:matched-base session) (:base-token entry))
               (= :trusted-artifact (:base-basis entry))
               (= :association-owned (aget ^objects (:kernel-root entry) 1))
               (= :association-owned (aget ^objects (:constant-map entry) 1))) "Association source/quot/owner disposition differs")
    (invoke1 (:engine session) "constructorNode" (aget ^objects (:kernel-root entry) 0))
    (invoke1 (:engine session) "constructorNode" (aget ^objects (:constant-map entry) 0))
    (validate-local-view! session entry)))
(defn- open-session-with-ceiling
  "Authority callbacks validate exact actual input/output helper-token bundles.
   Version storage is private to this transaction; no arbitrary Env association API."
  [ceiling basis engine setup source authority matched-base {:keys [allow-axioms? allow-theorems? allow-definitions? fuel projection-limits max-declarations] :as options}]
  (need (and (boolean? allow-axioms?) (boolean? allow-theorems?) (boolean? allow-definitions?)
             (or allow-axioms? allow-theorems? allow-definitions?)) "Explicit finite declaration permissions required")
  (need (and (integer? fuel) (<= 1 fuel Long/MAX_VALUE) (fn? projection-limits)
             (integer? max-declarations) (<= 1 max-declarations ceiling)) "Explicit bounded checker/version policy required")
  (doseq [key [:check-source! :begin-request! :artifact-environment! :checked-environment!
               :checked-constants! :diagnostics-disabled! :finish-request! :close!]]
    (need (fn? (get authority key)) "Independent source/layout/request witness authority required"))
  (need (and (string? (:layout-receipt-sha256 authority))
             (re-matches #"[0-9a-f]{64}" (:layout-receipt-sha256 authority))) "Compiled layout receipt required")
  (base/assert-session! matched-base engine source (:finalized-run authority))
  (base/guard! matched-base)
  (let [session {:thread (Thread/currentThread) :basis basis :engine engine :setup setup :source source :authority authority
                 :matched-base matched-base
                 :options options :invocation (atom nil) :versions (atom []) :published-count (atom 0)
                 :base-operation (atom nil) :events (atom [])
                 :last-request (atom nil) :phase (atom :idle)}]
    (source-live! session) session))
(defn open-session
  "Existing finite profile: explicit permissions and at most sixteen admissions."
  [basis engine setup source authority matched-base options]
  (open-session-with-ceiling 16 basis engine setup source authority matched-base options))
(defn open-general-session
  "General command profile, same admitted declaration kinds and ownership rules;
   explicitly bounded to at most512 admissions. This adds no block constructor."
  [basis engine setup source authority matched-base options]
  (need (fn? (:artifact-baseline! authority)) "Actual idle artifact baseline authority required")
  (open-session-with-ceiling 512 basis engine setup source authority matched-base options))
(defn establish-base!
  "Establish genuine version0 before zero-publication commands. ENVIRONMENT is
   borrowed from the actual owned frontend snapshot, not a serialized map."
  [session environment]
  (source-live! session) (base/guard! (:matched-base session))
  (need (and (= :idle @(:phase session)) (nil? @(:invocation session))
             (empty? @(:versions session)) (zero? @(:published-count session))
             (nil? @(:base-operation session))
             (= "idle" (j/phase (:basis session) (:engine session)))) "Base establishment is once-only before commands")
  (need (fn? (get-in session [:authority :artifact-baseline!])) "No actual idle baseline witness authority")
  (let [root-slot (slot nil :pending) map-slot (slot nil :pending)
        operation {:environment environment :kernel-root root-slot :constant-map map-slot :stage :witness-pending}]
    (reset! (:base-operation session) operation)
    (try
      (let [witness ((get-in session [:authority :artifact-baseline!]) (:engine session) environment)
            kernel (:kernel-root witness) constant-map (:constant-map witness)
            _ (readonly-witness! session witness kernel)
            _ (need (and (identical? environment (:guest-environment witness)) (true? (:quot witness))
                         (= :authenticated-idle-finalized-artifact-baseline (:origin witness))) "Actual idle base witness differs")]
        (doseq [[owner value] [[root-slot kernel] [map-slot constant-map]]]
          (aset ^objects owner 0 value) (state! owner :retain-pending)
          (j/retain! (:basis session) (:engine session) value) (state! owner :owned))
        (let [entry (base/with-env! (:matched-base session)
                      (fn [^Env env]
                        (need (and (empty? (.allConstants env)) (.isQuotEnabled env)) "Guarded base local view is not empty/quotient-enabled")
                        {:id 0 :parent nil :kernel-root root-slot :constant-map map-slot :quot true
                         :env env :segments [] :payloads {} :source (:source session)
                         :origin (:origin witness) :base-basis :trusted-artifact :base-token (:matched-base session)}))
              versions [entry]]
          (state! root-slot :association-owned) (state! map-slot :association-owned)
          (reset! (:versions session) versions)
          (reset! (:base-operation session) (assoc operation :stage :established))
          (validate-versions! session) {:status :base-established :version-id 0}))
      (catch Throwable failure
        (swap! (:base-operation session) assoc :stage :failed
               :failure {:class (.getName (class failure)) :message (.getMessage failure)})
        (reset! (:phase session) :failed) (throw failure)))))
(defn- event! [session phase invocation entry]
  (let [events (:events session)]
    (need (< (count @events) (* 8 (get-in session [:options :max-declarations]))) "Publication event budget exhausted")
    (swap! events conj {:phase phase :request (:outer @invocation)
                        :version-id (:id entry) :parent-id (:parent entry)
                        :constant (get-in @invocation [:candidate :constant])})))
(defn begin!
  "Capture a distinct actual unclaimed ELAB request. Multiple requests may occur
   inside one original processCommand call; only retirement requires engine IDLE."
  [session request]
  (need (and (contains? #{:idle :replied} @(:phase session)) (nil? @(:invocation session))
             (not (identical? request @(:last-request session)))) "Reentrant/replayed admission request")
  (need (< @(:published-count session) (get-in session [:options :max-declarations])) "Published declaration-version budget exhausted")
  (source-live! session) (validate-versions! session)
  (let [ctx (:basis session) engine (:engine session) [_ elab-header] (:outer-headers (:setup session))
        args (vec (.arguments request))]
    (need (identical? request (j/host-request ctx engine)) "Not the current unclaimed request")
    (need (identical? elab-header (actual-header request)) "Only exact authenticated ELAB Header is authorized")
    (need (and (= "lean_elab_add_decl" (.symbol request))
               (= ["object" "usize" "usize" "tobject" "tobject"] (vec (.paramTypes request)))
               (= [false false false true true] (vec (.borrowed request)))
               (= "object" (.resultType request)) (= 5 (count args))) "Native checked ABI mismatch")
    (let [[env heartbeats depth declaration cancel] args]
      (need (and (integer? heartbeats) (zero? heartbeats) (integer? depth) (zero? depth)) "Nonzero native limits unsupported")
      (need (and (instance? Long cancel) (= 0 cancel)) "Cancellation token unsupported")
      (let [descriptor (descriptor! session declaration)
            _ (need (true? (get-in session [:options (case (:kind descriptor) :axiom :allow-axioms? :theorem :allow-theorems? :definition :allow-definitions? :mutual-definition :allow-definitions?)]))
                    "Declaration kind is not enabled")
            _ (when (= :mutual-definition (:kind descriptor))
                (generated-admission! session request)
                (need (seq (group-payloads! session (aget ^objects (fields session declaration) 0))) "Empty mutual definition group")
                (need (get-in session [:setup :helper-headers "KernelBridgeShim.postCheckMutualDefinitions._boxed"])
                      "Mutual publisher absent from exact source policy"))
            inv (atom {:outer request :input-env env :declaration declaration
                       :descriptor descriptor :payload (aget ^objects (fields session declaration) 0)
                       :owners (LinkedHashMap.) :stage :root0 :operation nil :candidate nil :tokens {}
                       :outer-env-transferred? false :failure nil})]
        ((get-in session [:authority :begin-request!]) engine request)
        (reset! (:invocation session) inv) (reset! (:phase session) :active)
        (try (retain-into! session inv :declaration-anchor declaration) inv
             (catch Throwable failure (failure! session inv failure)))))))
(defn- launch-helper! [session inv helper args result-key next-stage]
  (let [basis (:basis session) engine (:engine session) outer (:outer @inv)
        result-slot (slot nil :pending)
        token-cell (object-array 1)
        op {:kind :helper :token token-cell :result-slot result-slot :result-key result-key :next-stage next-stage}
        descriptors (mapv (fn [arg]
                            (if (= arg :outer-env)
                              (j/host-transferred-argument basis outer 0)
                              (let [s (owner! inv arg)]
                                (need (= :owned (slot-state s)) "Input occurrence not owned")
                                (j/host-owned-argument basis (slot-value s))))) args)
        header (get-in session [:setup :helper-headers (str "KernelBridgeShim." helper "._boxed")])]
    (when (= helper "postCheckMutualDefinitions") (generated-admission! session (:outer @inv)))
    (need header "Helper absent from exact source policy")
    (.put ^LinkedHashMap (:owners @inv) result-key result-slot)
    (swap! inv assoc :operation op)
    (let [token (j/start-host-guest! basis engine outer header descriptors)]
      (aset ^objects token-cell 0 token)
      (doseq [arg args]
        (if (= arg :outer-env) (swap! inv assoc :outer-env-transferred? true)
            (state! (owner! inv arg) :transferred))))
    :running))
(defn- witness! [session inv helper env key next-stage]
  (let [input-key (keyword (str (name key) "-input"))]
    (retain-into! session inv input-key env)
    (launch-helper! session inv helper [input-key] key next-stage)))
(defn- receive! [session inv]
  (let [op (:operation @inv) token (aget ^objects (:token op) 0)]
    (need token "Operation publication failed; automatic retry forbidden")
    (need (identical? token (j/host-guest-result (:basis session) (:engine session))) "Unexpected helper result token")
    (let [value (j/take-host-guest-result! (:basis session) (:engine session) (:outer @inv) token)]
      ;; Record transferred result before inspecting it or allocating later stages.
      (aset ^objects (:result-slot op) 0 value) (state! (:result-slot op) :owned)
      (when (= :helper (:kind op)) (swap! inv assoc-in [:tokens (:result-key op)] token))
      (when (= :release (:kind op))
        (need (and (instance? Long value) (= 0 value)) "Release operation returned non-Unit")
        (let [s (owner! inv (:released-key op))] (aset ^objects s 0 nil) (state! s :released))
        (state! (:result-slot op) :consumed))
      (swap! inv assoc :operation nil :stage (:next-stage op)))))
(defn- bundle [inv suffix]
  (let [tokens (:tokens @inv)]
    {:root (get tokens (keyword (str "K" suffix))) :map (get tokens (keyword (str "M" suffix)))
     :quot (get tokens (keyword (str "quot" suffix))) :empty (get tokens :empty0) :publish (get tokens :reply)}))
(defn- retain-seed-version! [session inv witness]
  (base/with-env! (:matched-base session)
    (fn [^Env env]
      (let [k (owner! inv :K0) m (owner! inv :M0)
            entry {:id 0 :parent nil :kernel-root k :constant-map m :quot true
                   :env env :segments [] :payloads {} :source (:source session)
                   :origin (:origin witness) :base-basis :trusted-artifact
                   :base-token (:matched-base session)}]
        (need (and (= :owned (slot-state k)) (= :owned (slot-state m))
                   (empty? @(:versions session)) (empty? (.allConstants env))
                   (.isQuotEnabled env)) "Seed differs from the guarded artifact base")
        (state! k :association-owned) (state! m :association-owned)
        (reset! (:versions session) [entry]) entry))))
(defn- resolve-base! [session inv]
  (let [s @inv k (slot-value (owner! inv :K0)) m (slot-value (owner! inv :M0)) tokens (bundle inv "0")
        first? (empty? @(:versions session))
        _ (need (and (= :owned (slot-state (owner! inv :K0))) (= :owned (slot-state (owner! inv :M0))))
                "Base root/map witnesses do not own their returned occurrences")
        witness (readonly-witness! session
                  (if first?
                    ((get-in session [:authority :artifact-environment!]) (:engine session) (:input-env s) k m tokens)
                    ((get-in session [:authority :checked-environment!]) (:engine session) (:input-env s) k m tokens :input)) k)
        _ (need (and (identical? (:input-env s) (:guest-environment witness))
                     (identical? m (:constant-map witness)) (true? (:quot witness))) "Actual artifact base witness differs")
        _ (diagnostics! session k (:root tokens))
        version (if first? (retain-seed-version! session inv witness)
                  (let [matches (filter #(identical? m (slot-value (:constant-map %))) @(:versions session))]
                    (need (= 1 (count matches)) "Actual checked map has no unique retained version") (first matches)))]
    (need (and (= :association-owned (slot-state (:constant-map version)))
               (= :association-owned (slot-state (:kernel-root version)))) "Accepted version anchors retired")
    (need (= 0 (tagged-bool (slot-value (owner! inv :empty0)))) "Imported artifact unexpectedly reported empty")
    (swap! inv assoc :base version) version))
(defn- check-java! [session inv]
  (validate-versions! session)
  (need (< @(:published-count session) (get-in session [:options :max-declarations])) "Version budget exhausted before checking")
  (let [version (resolve-base! session inv) environment (:env version)
        mutual? (= :mutual-definition (get-in @inv [:descriptor :kind]))]
    (when mutual? (generated-admission! session (:outer @inv)))
    (base/with-version! (:matched-base session) environment
      (fn [^Env environment]
        (let [scope (projection/open-projector (:basis session) (:engine session) ((get-in session [:options :projection-limits])))]
          (try
            (let [projected (:value (bridge/project-with-stats (:world scope)
                                       (get-in @inv [:descriptor :declaration-projection]) (:declaration @inv) (:projector scope)))
                  constants (if mutual? projected [projected])
                  names (mapv #(.name ^ConstantInfo %) constants)
                  payloads (if mutual? (group-payloads! session (:payload @inv)) [(:payload @inv)])
                  _ (need (and (<= 1 (count constants) 256) (= (count constants) (count payloads) (count (set names)))
                               (<= (+ (count constants) (count (:payloads version))) (get-in session [:options :max-declarations])))
                          "Declaration group exceeds exact local domain/member bounds")
                  _ (doseq [name names] (need (nil? (.lookup environment name)) "Declaration shadows a base or local name"))
                  result (case (get-in @inv [:descriptor :kind])
                           :axiom (bridge/admit-axiom (:world scope) environment (:declaration @inv) (get-in session [:options :fuel]) (:projector scope))
                           :definition (bridge/admit-definition (:world scope) environment (:declaration @inv) (get-in session [:options :fuel]) (:projector scope))
                           :theorem (bridge/admit-theorem (:world scope) environment (:declaration @inv) (get-in session [:options :fuel]) (:projector scope))
                           :mutual-definition (bridge/admit-mutual-definitions (:world scope) environment (:declaration @inv)
                                                                           (get-in session [:options :fuel]) (:projector scope)))
                  ^Env child (:env result) checked (if mutual? (:constants result) [(:constant result)])]
              (need (and (= (count constants) (count checked))
                         (every? true? (map identical? constants checked)) (.sameExternalView child environment)
                         (.isQuotEnabled child) (= (+ (count constants) (count (:payloads version))) (count (.allConstants child))))
                    "Checked child differs from its atomic original local delta")
              (doseq [^ConstantInfo ci constants] (need (identical? ci (.lookupLocal child (.name ci))) "Checked member is not the actual child CI"))
              (let [group (zipmap names constants) segment (snapshot/snapshot-segment group)
                    additions (into {} (map (fn [name payload]
                                               [name (cond-> {:kind (if mutual? :definition (get-in @inv [:descriptor :kind])) :payload payload}
                                                       mutual? (assoc :value-projection :definition-val-general))]) names payloads))
                    candidate {:env child :constant (when-not mutual? (first constants)) :constants constants
                               :segments (conj (:segments version) segment) :payloads (merge (:payloads version) additions)}]
                (validate-local-view! session candidate)
                (swap! inv assoc :candidate candidate :stage :publish)
                (event! session :checked inv {:id (inc @(:published-count session)) :parent (:id version)})))
            (finally ((:close! scope))))))))
  (validate-versions! session) (validate-candidate! session inv))
(defn- validate-local-info! [session scope candidate ^Env checked info name]
  (let [descriptor (descriptor! session info) payload (aget ^objects (fields session info) 0)
        expected (get (:payloads candidate) name)
        ^ConstantInfo projected (:value (bridge/project-with-stats (:world scope)
                                          (or (:value-projection expected) (:value-projection descriptor)) payload (:projector scope)))
        actual (.lookup checked name)]
    (need (and expected (= name (.name projected)) (= (:kind descriptor) (:kind expected))
               (identical? payload (:payload expected)) actual
               (= (imported/checking-shape actual) (imported/checking-shape projected)))
          "Readback changed a local name/kind/payload/checking shape")))
(defn- validate-readback! [session inv]
  (let [s @inv k0 (slot-value (owner! inv :K0)) m0 (slot-value (owner! inv :M0))
        k1 (slot-value (owner! inv :K1)) m1 (slot-value (owner! inv :M1)) tokens (bundle inv "1")
        candidate (:candidate s) ^Env checked (:env candidate)
        witness (readonly-witness! session
                  ((get-in session [:authority :checked-environment!]) (:engine session) (:output-env s) k1 m1 tokens :published) k1)
        readback (slot-value (owner! inv :readback))
        array-witness ((get-in session [:authority :checked-constants!]) (:engine session) (:output-env s) (get-in s [:tokens :readback]) readback)
        array (invoke1 (:engine session) "array" readback) n (.arraySize array)
        artifact (:matched-base session) domain (base/domain-names artifact) local-names (set (keys (:payloads candidate)))]
    (need (and (identical? m1 (:constant-map witness)) (true? (:quot witness))
               (identical? readback (:array array-witness)) (identical? (:source session) (:source-binding array-witness))
               (= (get-in session [:authority :layout-receipt-sha256]) (:layout-receipt-sha256 array-witness))) "Output/readback witness differs")
    (need (and (not (identical? k0 k1)) (not (identical? m0 m1))) "Publication reused an anchored input root/map")
    (need (not-any? #(identical? m1 (slot-value (:constant-map %))) @(:versions session)) "Publication reused a prior map")
    (need (and (empty? (clojure.set/intersection domain local-names))
               (= n (+ (base/base-count artifact) (count local-names)))
               (<= (count local-names) (get-in session [:options :max-declarations]))) "Checked readback domain/count differs")
    (diagnostics! session k1 (:root tokens))
    (base/with-version! artifact checked
      (fn [^Env checked]
        (let [scope (projection/open-projector (:basis session) (:engine session) ((get-in session [:options :projection-limits])))]
          (try
            (let [seen (atom #{})]
              (dotimes [i n]
                (let [info (aget ^objects (fields session array) i)
                      summary (imported/project-constant-name-kind (:world scope) info
                                {:max-nodes 256 :max-chars 4096} (:carrier-ops scope))
                      name (:name summary)]
                  (need (not (contains? @seen name)) "Readback contains a duplicate typed Name")
                  (if (contains? domain name)
                    (base/validate-base-info! artifact (:world scope) (:carrier-ops scope) info)
                    (validate-local-info! session scope candidate checked info name))
                  (swap! seen conj name)))
              (need (= @seen (clojure.set/union domain local-names)) "Readback omitted or added constants"))
            (finally ((:close! scope))))))))
  (validate-versions! session) (validate-candidate! session inv))
(defn- commit! [session inv]
  (validate-readback! session inv) (source-live! session)
  (validate-versions! session) (validate-candidate! session inv)
  (let [s @inv candidate (:candidate s) next-count (inc @(:published-count session))
        entry {:id next-count :parent (get-in s [:base :id]) :kernel-root (owner! inv :K1) :constant-map (owner! inv :M1) :quot true
               :env (:env candidate) :segments (:segments candidate) :payloads (:payloads candidate) :source (:source session)
               :origin :strict-checked-original-declaration-publication
               :base-basis :trusted-artifact :base-token (:matched-base session)}
        versions (conj @(:versions session) entry)
        cleanup (vec (for [entry (.entrySet ^LinkedHashMap (:owners s))
                           :let [key (.getKey entry) value (.getValue entry)]
                           :when (and (= :owned (slot-state value)) (not= :reply key))] key))]
    ;; K1/M1 are not temporary cleanup owners. Seed K0/M0 are already association-owned.
    (event! session :published inv entry)
    (state! (:kernel-root entry) :association-owned) (state! (:constant-map entry) :association-owned)
    (reset! (:versions session) versions) (reset! (:published-count session) next-count)
    (event! session :committed inv entry)
    (swap! inv assoc :cleanup (vec (remove #{:K1 :M1} cleanup)) :cleanup-index 0 :stage :cleanup)))
(defn- cleanup-next! [session inv]
  (let [s @inv i (:cleanup-index s) keys (:cleanup s)]
    (if (= i (count keys))
      (do (event! session :cleanup-finished inv (peek @(:versions session)))
          (swap! inv assoc :stage :reply))
      (let [key (nth keys i) value (owner! inv key)
            _ (need (= :owned (slot-state value)) "Retirement occurrence was already transferred")
            token-cell (object-array 1) unit-slot (slot nil :pending)
            op {:kind :release :token token-cell :result-slot unit-slot :released-key key :next-stage :cleanup}
            descriptor (j/host-owned-argument (:basis session) (slot-value value))]
        (swap! inv assoc :operation op :cleanup-index (inc i))
        (let [token (j/start-host-release! (:basis session) (:engine session) (:outer s) descriptor 1)]
          (aset ^objects token-cell 0 token) (state! value :transferred))))))
(defn- reply! [session inv]
  (source-live! session) (validate-candidate! session inv)
  (let [reply-slot (owner! inv :reply) value (slot-value reply-slot)]
    (need (= :owned (slot-state reply-slot)) "Reply occurrence was already transferred")
    ;; A throwing resume may already have claimed its reply. Preserve the exact
    ;; uncertainty instead of reporting an automatically releasable owned slot.
    (state! reply-slot :resume-pending)
    (j/resume-host! (:basis session) (:engine session) (:outer @inv) value)
    (state! reply-slot :transferred)
    (event! session :reply-transferred inv (peek @(:versions session)))
    ;; HostCompletion now owns reply even if subsequent cleanup pauses or fails.
    ((get-in session [:authority :finish-request!]) (:engine session) (:outer @inv))
    (reset! (:last-request session) (:outer @inv))
    (reset! (:phase session) :replied) (reset! (:invocation session) nil)))
(defn publication-watermark [session]
  "Chronological issued-publication cursor, independent of selected guest Env."
  (let [n @(:published-count session)]
    (need (and (integer? n) (<= 0 n (get-in session [:options :max-declarations]))
               (= (inc n) (count @(:versions session)))) "Retained publication ledger/counter differs") n))
(defn version-ancestry [session selected-id]
  (let [versions @(:versions session) by-id (into {} (map (juxt :id identity) versions))]
    (loop [id selected-id out []]
      (need (and (integer? id) (<= 0 id) (< (count out) (count versions))) "Invalid retained version ancestry")
      (let [entry (get by-id id)]
        (need entry "Missing retained version ancestor")
        (if (zero? id)
          (do (need (nil? (:parent entry)) "Baseline version has a parent") (vec (reverse (conj out id))))
          (do (need (and (integer? (:parent entry)) (<= 0 (:parent entry)) (< (:parent entry) id))
                    "Publication parent is not an earlier retained version")
              (recur (:parent entry) (conj out id))))))))
(defn complete-command-history!
  "Validate EVERY completed publication in a chronological interval, including
   speculative sibling branches. Selected guest Env is resolved separately from
   its actual map; no event is discarded or relabeled as selected by this API."
  ([session watermark] (complete-command-history! session watermark watermark))
  ([session watermark initial-selected-id]
  (source-live! session) (validate-versions! session)
  (need (and (contains? #{:idle :replied} @(:phase session)) (nil? @(:invocation session))
             (= "idle" (j/phase (:basis session) (:engine session)))
             (nil? (private-value (:engine session) "hostCompletion"))
             (nil? (private-value (:engine session) "hostGuestRecord"))
             (nil? (private-value (:engine session) "runtimeAction"))) "Command still owns pending native completion work")
  (let [versions @(:versions session) end (publication-watermark session)
        by-id (into {} (map (juxt :id identity) versions))
        _ (need (= (mapv :id versions) (vec (range (inc end)))) "Publication IDs are not the complete retained ledger")
        _ (need (and (integer? watermark) (<= 0 watermark end)
                     (integer? initial-selected-id) (<= 0 initial-selected-id watermark)
                     (contains? by-id initial-selected-id)) "Missing retained initial command version/watermark")
        added (vec (filter #(< watermark (:id %)) versions))
        requests (java.util.IdentityHashMap.)
        phases [:checked :published :committed :cleanup-finished :reply-transferred]]
    (doseq [entry versions] (version-ancestry session (:id entry)))
    (doseq [entry added]
      (let [events (vec (filter #(= (:id entry) (:version-id %)) @(:events session)))
            required (filterv #(not= :reply-finished (:phase %)) events)
            finished (filterv #(= :reply-finished (:phase %)) events)
            request (:request (first required))]
        (need (and request (= phases (mapv :phase required)) (<= (count finished) 1)
                   (= (mapv :phase events) (into phases (repeat (count finished) :reply-finished)))
                   (every? #(= (:parent entry) (:parent-id %)) events)
                   (every? #(identical? request (:request %)) events)
                   (not (.containsKey requests request))
                   (true? (private-value (private-value request "call") "replyClaimed")))
              "Version lacks exact checked/published/committed/cleanup/reply completion")
        (.put requests request true)
        (when (empty? finished) (event! session :reply-finished (atom {:outer request}) entry))))
    (mapv #(select-keys % [:id :parent]) added))))
(defn poll!
  "One nonrecursive adapter transition. Driver owns advance/Code/other Host servicing.
   A failed receipt remains owned and cannot be retried, forked or silently unwound."
  [session]
  (if (not= :active @(:phase session)) {:status @(:phase session)}
    (let [inv @(:invocation session) phase (j/phase (:basis session) (:engine session))]
      (try
        (source-live! session) (validate-versions! session) (validate-candidate! session inv)
        (cond
          (= phase "failed") (reject "Guest operation failed")
          (= phase "host-guest-result") (do (receive! session inv) {:status :progress})
          (:operation @inv) {:status (case phase "code-call" :needs-code "host-call" :needs-host "waiting" :waiting :running)
                            :operation (aget ^objects (get-in @inv [:operation :token]) 0)}
          :else
          (do
            (need (identical? (:outer @inv) (j/host-request (:basis session) (:engine session))) "Outer request was not restored")
            (case (:stage @inv)
              :root0 (witness! session inv "checkedKernelRoot" (:input-env @inv) :K0 :map0)
              :map0 (do (invoke1 (:engine session) "constructorNode" (slot-value (owner! inv :K0)))
                        (witness! session inv "checkedConstantMapRoot" (:input-env @inv) :M0 :quot0))
              :quot0 (do (invoke1 (:engine session) "constructorNode" (slot-value (owner! inv :M0)))
                         (witness! session inv "checkedQuotInit" (:input-env @inv) :quot0 :empty0))
              :empty0 (do (need (= 1 (tagged-bool (slot-value (owner! inv :quot0)))) "Expected the original initialized quotient base")
                          (witness! session inv "checkedEnvironmentIsEmpty" (:input-env @inv) :empty0 :check))
              :check (check-java! session inv)
              :publish (do (when (= :mutual-definition (get-in @inv [:descriptor :kind]))
                             (generated-admission! session (:outer @inv)))
                           (retain-into! session inv :publication-declaration (:declaration @inv))
                           (launch-helper! session inv (get-in @inv [:descriptor :publication]) [:outer-env :publication-declaration] :reply :published))
              :published (let [r (slot-value (owner! inv :reply))]
                           (ctor session r 1 1)
                           (swap! inv assoc :output-env (aget ^objects (fields session r) 0) :stage :root1))
              :root1 (witness! session inv "checkedKernelRoot" (:output-env @inv) :K1 :map1)
              :map1 (do (invoke1 (:engine session) "constructorNode" (slot-value (owner! inv :K1)))
                        (witness! session inv "checkedConstantMapRoot" (:output-env @inv) :M1 :quot1))
              :quot1 (do (invoke1 (:engine session) "constructorNode" (slot-value (owner! inv :M1)))
                         (witness! session inv "checkedQuotInit" (:output-env @inv) :quot1 :readback))
              :readback (do (need (= 1 (tagged-bool (slot-value (owner! inv :quot1)))) "Published quotient state changed")
                           (witness! session inv "checkedConstants" (:output-env @inv) :readback :commit))
              :commit (commit! session inv)
              :cleanup (cleanup-next! session inv)
              :reply (reply! session inv)
              (reject "Unknown adapter stage"))
            {:status (if (= :active @(:phase session)) :progress @(:phase session))}))
        (catch Throwable failure (failure! session inv failure))))))

(defn fork-session! [_]
  (reject "Adapter session fork unsupported: association/receipt remapping is not implemented; do not call raw eagerFork"))
(defn owner-packet [session]
  "Borrowed guest-owner diagnostics; no Java Env/CI values escape through this view."
  {:phase @(:phase session) :published @(:published-count session)
   :base-operation @(:base-operation session)
   :events (mapv #(select-keys % [:phase :version-id :parent-id :request]) @(:events session))
   :versions (mapv #(select-keys % [:id :parent :kernel-root :constant-map :quot]) @(:versions session))
   :invocation (when-let [inv @(:invocation session)]
                 {:stage (:stage @inv) :operation (:operation @inv) :outer (:outer @inv)
                  :owners (:owners @inv) :failure (:failure @inv)})})
(defn take-retirement-owners!
  "Remove all association authority before transferring every K/M occurrence to
   root resumable release. Includes the seed and every old version, with aliases."
  [session]
  (source-live! session)
  (need (and (contains? #{:idle :replied} @(:phase session)) (nil? @(:invocation session))
             (= "idle" (j/phase (:basis session) (:engine session)))) "Retirement requires an idle command boundary")
  (validate-versions! session)
  (let [slots (vec (mapcat #(vector (:kernel-root %) (:constant-map %)) @(:versions session)))
        packet (mapv (fn [slot] (need (= :association-owned (slot-state slot)) "Anchor already transferred") (slot-value slot)) slots)]
    ((get-in session [:authority :close!]))
    (base/revoke! (:matched-base session))
    (reset! (:versions session) []) (reset! (:last-request session) nil)
    (reset! (:base-operation session) nil) (reset! (:events session) [])
    (doseq [slot slots] (state! slot :external-retirement))
    (reset! (:phase session) :retired) packet))
