(ns artifact-declaration-authority-v4
  "Artifact-relative helper/source authority only; no Java Env, checking or base issuance."
  (:require [clojure.data.json :as json] [clojure.java.io :as io]
            [java-ir-baseline :as j] [ansatz.research.ir.catalogue :as cat]
            [ansatz.research.ir.source-setup :as source]
            [java-prelude-finalizer-lineage-v1 :as finalized])
  (:import [java.util IdentityHashMap] [java.lang.reflect InvocationTargetException]))
(def lean-pin "819816b2e0a3bf405af45ae5c7af2491d8f5bee6")
(def index-pin "74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e")
(def original-pin "2b8f1995d4036ce93f7d8eb424456394d07ab7a674f85af259d1958034ff0837")
(def layout-pin "ea407573867ed696e4591b94e507a8bcfed58a1434b33f2145f1671901a32df6")
(def receipt-pin "2b2057d4df5588a668b77b7631d55bd38c494b2c9a0fea4abab55c5aef7e989a")
(def elab-pin "dd730795db2582181bc71a1e280793fb8790a3d68f51fad13ea6bbad12df737e")
(def shim-source-pin "8d4fa0f2c8cd8b38ae1637945521a584c2f90de0a3820a1ef8b812d993f7ec03")
(def shim-stream-pin "93a58e710315bb140f3799695aeeaaa687f6fd9cca1f3acc1f06660059de8a0b")
(def helper-pins
  {"79720d8bc92af9a7c4ba0873eb9b506e06c9adcda0532665dac0dbbdd0711e65" :root
   "81105c0aced7b1338ae0a6b91ebfec7bb0cb310f5ec34ad65d3859eebe7536b7" :map
   "4ebc3cb55b5d6740d1592f146dfd123ffd5dca7d6d17bdb904187d9fe386711d" :quot
   "b8e6207f0cf1c123cb43fb057cf585d734cc21c88123e980953a8d0d214c9fbf" :empty
   "5ce56dbb8300eeed780eeac1fd41519fe8fad49b6ec7d469dea7844c28ce328f" :publish-axiom
   "52a0a1806c39f6d73e845131d725a56e3e06097df412dcf9241fde218ffc41e4" :publish-theorem
   "c60b8d00d76b49cfff180d19b49347dbb4db49ef7710f349bfa368dc9eb17e08" :publish-definition
   "abd01742636f91481a888ec089678e9bc1ff4bc40441d7085885f0e097da4152" :constants})
(defn- reject [message data] (throw (ex-info message (assoc data :profile :artifact-declaration-authority-v4))))
(defn- need [condition message] (when-not condition (reject message {})))
(defn- field [object name]
  (let [f (doto (.getDeclaredField (class object) name) (.setAccessible true))] (.get f object)))
(defn- guard [engine method value]
  (let [m (doto (.getDeclaredMethod (class engine) method (into-array Class [Object])) (.setAccessible true))]
    (try (.invoke m engine (object-array [value]))
         (catch InvocationTargetException error (throw (.getCause error))))))
(defn- sha [bytes]
  (apply str (map #(format "%02x" (bit-and 255 %))
                 (.digest (java.security.MessageDigest/getInstance "SHA-256") bytes))))
(defn- live-driver! [driver receipt]
  (let [ctx @(:current-ctx driver) engine (:engine driver) src (:source driver)]
    (need (and engine src (identical? (:class ctx) (class engine))) "Actual driver engine/source required")
    (doseq [key ["closed" "disposed" "untrackedFailure" "advancing"]]
      (need (false? (field engine key)) "Engine cannot lend authority after lifecycle/progress failure"))
    (need (not= "failed" (j/phase ctx engine)) "Failed engine cannot lend authority")
    (need (identical? (:program ctx) (field engine "program")) "Driver/current Program differ")
    (let [token (cat/source-token (:catalogue driver))]
      (need (= index-pin (:source-index-sha256 token)) "Driver catalogue source differs"))
    (source/guard-source! receipt src)
    (need (= "captured-base-plus-ordered-source-overlays/4"
             (get (source/code-profile receipt) "schema")) "Actual composite v4 code receipt required")
    ctx))
(defn- actual-header! [driver header]
  (need header "Actual registered Header required")
  (let [program (:program @(:current-ctx driver))
        method (.getMethod (class program) "functionId" (into-array Class [(class header)]))]
    ;; Program.functionId(Header) requires exact registered Header identity.
    (try (.invoke method program (object-array [header]))
         (catch InvocationTargetException error (throw (.getCause error))))))
(defn- constructor! [driver value kind layout]
  (let [ctx @(:current-ctx driver) engine (:engine driver)
        _ (need (and value (identical? (:node-class ctx) (class value))) "Not the exact engine Node class")
        _ (guard engine "constructorNode" value)
        _ (need (nil? (field value "closure")) "Closure is not an ordinary layout")
        fs ^objects (.get ^java.lang.reflect.Field (:fields ctx) value)
        bytes ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) value)
        expected (get-in layout ["layouts" kind])]
    (need (and expected (= (get expected "tag") (.getInt ^java.lang.reflect.Field (:tag ctx) value))
               (= (get expected "object-fields") (alength fs))
               (contains? (set (get expected "allowed-physical-scalar-bytes")) (alength bytes)))
          "Compiled constructor layout mismatch")
    {:node value :fields fs :bytes bytes}))
(defn- scalar [view offset width]
  (reduce (fn [n i] (bit-or n (bit-shift-left (long (Byte/toUnsignedInt (aget ^bytes (:bytes view) (+ offset i)))) (* 8 i)))) 0 (range width)))
(defn- kernel-view! [driver layout kernel]
  (let [k (constructor! driver kernel "kernel-environment" layout)
        d (constructor! driver (aget ^objects (:fields k) 1) "diagnostics" layout)
        h (constructor! driver (aget ^objects (:fields k) 5) "header" layout)]
    (need (= 1 (scalar k 0 1)) "Artifact kernel quotient must remain enabled")
    (need (= 0 (scalar d 0 1)) "Enabled kernel diagnostics unsupported")
    (need (and (= 0 (scalar h 0 4)) (= 0 (scalar h 4 1))) "Kernel trust/module flags outside finalized private profile")
    (guard (:engine driver) "constructorNode" (aget ^objects (:fields k) 0))
    {:kernel-root kernel :constant-map (aget ^objects (:fields k) 0) :diagnostics (:node d) :header (:node h)
     :header-fields (vec (:fields h)) :const2mod-map (aget ^objects (:fields k) 2)
     :extensions (aget ^objects (:fields k) 3) :ir-base-exts (aget ^objects (:fields k) 4)}))
(defn- environment-view! [driver layout environment]
  (let [e (constructor! driver environment "source-environment" layout)
        _ (need (= 0 (scalar e 0 1)) "Exporting Environment outside finalized private scope")
        task (guard (:engine driver) "readyTaskNode" (aget ^objects (:fields e) 2))
        kernel (aget ^objects (.get ^java.lang.reflect.Field (:fields @(:current-ctx driver)) task) 0)]
    (assoc (kernel-view! driver layout kernel) :guest-environment environment)))
(defn- outer! [driver request]
  (need request "Actual checked outer request required")
  (let [source (:source driver) header (field (field (field request "call") "function") "header")
        _ (actual-header! driver header)]
    (need (identical? (field request "owner") (field (:engine driver) "runtimeIdentity")) "Foreign outer request")
    (need (and header (identical? source (j/request-value header "source"))
               (= elab-pin (j/request-value header "originalSha256"))
               (= "lean_elab_add_decl" (.symbol request))
               (= ["object" "usize" "usize" "tobject" "tobject"] (vec (.paramTypes request)))
               (= [false false false true true] (vec (.borrowed request)))
               (= "object" (.resultType request))) "Outer source/Header/ABI is not the actual checked ELAB seam")
    request))
(defn- read-layout! [directory]
  (let [read! (fn [name pin]
                (let [path (.toPath (io/file directory name)) n (java.nio.file.Files/size path)]
                  (need (<= n 65536) "Layout file exceeds bound")
                  (let [bytes (java.nio.file.Files/readAllBytes path)]
                    (need (= pin (sha bytes)) "Layout evidence hash differs")
                    (json/read-str (String. bytes java.nio.charset.StandardCharsets/UTF_8)))))
        receipt (read! "fresh-layout-receipt.json" receipt-pin)
        data (read! "fresh-layout-evidence.json" layout-pin)]
    (need (= [lean-pin index-pin layout-pin original-pin]
             (mapv #(get receipt %) ["lean-commit" "source-index-sha256" "evidence-sha256" "original-row-sha256"]))
          "Layout source pins differ") data))
(defn- publication-kind! [driver request]
  (let [declaration (nth (vec (.arguments request)) 3)
        node (guard (:engine driver) "constructorNode" declaration)
        ctx @(:current-ctx driver)
        tag (.getInt ^java.lang.reflect.Field (:tag ctx) node)]
    (need (and (nil? (field node "closure"))
               (= 1 (alength ^objects (.get ^java.lang.reflect.Field (:fields ctx) node)))
               (zero? (alength ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) node))))
          "Unsupported publication Declaration carrier")
    (case tag 0 :publish-axiom 1 :publish-definition 2 :publish-theorem
      (reject "Unsupported publication Declaration kind" {}))))
(defn- helper-abi! [driver header kind]
  (actual-header! driver header)
  (need (and (identical? (:source driver) (j/request-value header "source"))
             (= "fdecl" (j/request-value header "kind"))
             (= (if (contains? #{:publish-axiom :publish-theorem :publish-definition} kind) ["object" "tobject"] ["object"])
                (vec (j/request-value header "paramTypes")))
             (= (if (contains? #{:publish-axiom :publish-theorem :publish-definition} kind) [false false] [false]) (vec (j/request-value header "borrowed")))
             (= (if (contains? #{:quot :empty} kind) "tagged" "object") (j/request-value header "resultType")))
        "Shim helper ABI/source differs"))
(defn- observe-result! [state]
  (let [driver (:driver state) engine (:engine driver) ctx @(:current-ctx driver)]
    (when-let [token (j/host-guest-result ctx engine)]
      (need (and (identical? (field token "owner") (field engine "runtimeIdentity"))
                 (not (.resultTaken token))) "Foreign/taken protocol result")
      (let [outer (outer! driver (.outerRequest token))]
        (need (identical? outer @(:request state)) "Protocol result belongs to another request")
        (if (.isRelease token)
          (need (nil? (.helperHeader token)) "Release unexpectedly has helper Header")
          (let [observations ^IdentityHashMap (:observations state)]
            (when-not (.containsKey observations token)
              (need (< (.size observations) 16) "Per-request helper history exceeds bound")
              (need (.resultOwned token) "Helper has no unclaimed owned result")
              (let [header (.helperHeader token) kind (get helper-pins (j/request-value header "originalSha256"))
                    args (vec (.arguments token))]
                (need kind "Unrecognized helper source hash") (helper-abi! driver header kind)
                (need (= (if (contains? #{:publish-axiom :publish-theorem :publish-definition} kind) 2 1) (count args)) "Helper argument count differs")
                (when (contains? #{:publish-axiom :publish-theorem :publish-definition} kind)
                  (need (= kind (publication-kind! driver outer)) "Publisher kind differs from the actual outer Declaration")
                  (let [outer-args (vec (.arguments outer))]
                    (need (and (identical? (first args) (first outer-args))
                               (identical? (second args) (nth outer-args 3)))
                          "Publication is not the exact outer Env/declaration")))
                (.put observations token {:kind kind :header header :outer outer :args args :value (.result token)})))))))))
(declare imported-profile!)
(defn- prefix! [state]
  ;; The real Run retains all original occurrences. This authority never takes
  ;; them and cannot outlive its retirement. No public witness map substitutes.
  (let [actual (finalized/inspect! (:finalized-run state)) driver (:driver state)]
    (need (and (identical? (:engine driver) (:engine actual))
               (identical? (:source driver) (:source actual))
               (identical? (:code-receipt state) (:code-receipt actual))
               (= :actual-original-finalizer-only (:basis actual))
               (= 1 (:quot actual)) (= 0 (:empty actual))) "Foreign or unsealed finalizer Run")
    (doseq [key [:environment :kernel-root :constant-map :constants]]
      (need (identical? (get (:prefix state) key) (get actual key)) "Protected finalizer occurrence changed"))
    (let [view (kernel-view! driver (:layout state) (:kernel-root actual))
          current (environment-view! driver (:layout state) (:environment actual))]
      (need (and (identical? (:constant-map actual) (:constant-map view))
                 (identical? (:kernel-root actual) (:kernel-root current))) "Protected finalizer Env/root/map contents changed")
      (imported-profile! state view))
    actual))
(defn- imported-profile! [state view]
  ;; Header mainModule may change when the original frontend opens a file.
  ;; Imported arrays/regions/module lookup/IR data remain the actual finalized
  ;; objects. Scalar trust/isModule/diagnostics checks are in kernel-view!.
  (let [expected (:prefix-view state) actual-fields (:header-fields view)]
    (need (identical? (:const2mod-map expected) (:const2mod-map view))
          "Finalized imported const2ModIdx identity changed")
    (need (every? (fn [i] (identical? (nth (:header-fields expected) i) (nth actual-fields i)))
                  (range 1 7)) "Finalized import/module/header profile changed")
    view))
(defn- state! [holder engine src]
  (let [state @holder]
    (need state "Artifact declaration authority is closed")
    (need (and (identical? engine (:engine (:driver state))) (identical? src (:source (:driver state))))
          "Foreign authority engine/source")
    (need (identical? (:thread state) (Thread/currentThread)) "Authority is thread confined")
    (live-driver! (:driver state) (:code-receipt state))
    (prefix! state)
    (observe-result! state) state))
(defn- taken! [state token kind environment]
  (let [observation (.get ^IdentityHashMap (:observations state) token)]
    (need (and token observation (.resultTaken token)
               (= kind (:kind observation))
               (identical? @(:request state) (:outer observation))
               (identical? environment (first (:args observation))))
          "Missing exact taken helper token for this request/stage")
    observation))
(defn- ordinary! [driver value tag count]
  (let [ctx @(:current-ctx driver) node (guard (:engine driver) "constructorNode" value)]
    (need (and (nil? (field node "closure"))
               (= tag (.getInt ^java.lang.reflect.Field (:tag ctx) node))
               (= count (alength ^objects (.get ^java.lang.reflect.Field (:fields ctx) node)))
               (zero? (alength ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) node))))
          "Unexpected publication result layout") node))
(defn- observed! [state environment kernel constant-map bundle mode]
  (let [driver (:driver state) engine (:engine driver) request @(:request state)
        _ (need (identical? request (j/host-request @(:current-ctx driver) engine)) "Outer request is not restored")
        _ (need (not (field (field request "call") "replyClaimed")) "Outer request is claimed")
        root-op (taken! state (:root bundle) :root environment)
        map-op (taken! state (:map bundle) :map environment)
        quot-op (taken! state (:quot bundle) :quot environment)
        view (imported-profile! state (kernel-view! driver (:layout state) kernel))
        current (environment-view! driver (:layout state) environment)]
    (case mode
      :input (need (identical? environment (first (vec (.arguments request)))) "Input witness is not actual outer Env")
      :published
      (let [publish (.get ^IdentityHashMap (:observations state) (:publish bundle))
            _ (need (and publish (= (publication-kind! driver request) (:kind publish))
                         (identical? request (:outer publish)) (.resultTaken (:publish bundle))) "No actual taken publication result")
            wrapper (ordinary! driver (:value publish) 1 1)
            output (aget ^objects (.get ^java.lang.reflect.Field (:fields @(:current-ctx driver)) wrapper) 0)]
        (need (identical? environment output) "Published Env is not the authentic helper result"))
      (reject "Unknown environment witness stage" {}))
    (need (and (identical? kernel (:value root-op)) (identical? constant-map (:value map-op))
               (identical? kernel (:kernel-root current)) (identical? constant-map (:constant-map view))
               (instance? Long (:value quot-op)) (= 1 (:value quot-op))) "Actual root/map/quot witnesses differ")
    {:kernel-root kernel :constant-map constant-map :guest-environment environment :quot true
     :source-binding (:source driver) :layout-receipt-sha256 receipt-pin :observation-seal (Object.)
     :origin mode}))
(defn open-authority
  "New v4 helper/source authority, derived from actual live finalizer Run owners.
   No bootstrap/fresh-empty fallback, Java Env, base admission or owner transfer.
   Keep Run owners live until close; all callbacks retain exact v3 protocol checks."
  [driver {:keys [code-receipt finalized-run layout-directory]}]
  (live-driver! driver code-receipt)
  (let [data (read-layout! layout-directory)
        prefix (finalized/inspect! finalized-run)
        _ (need (and (identical? (:engine driver) (:engine prefix))
                     (identical? (:source driver) (:source prefix))
                     (identical? code-receipt (:code-receipt prefix))
                     (= :actual-original-finalizer-only (:basis prefix))
                     (= 1 (:quot prefix)) (= 0 (:empty prefix))) "Actual matching finalized Run required")
        initial (kernel-view! driver data (:kernel-root prefix))
        env-view (environment-view! driver data (:environment prefix))
        _ (need (and (identical? (:constant-map prefix) (:constant-map initial))
                     (identical? (:kernel-root prefix) (:kernel-root env-view))) "Finalizer Run root/map/Env changed")
        holder (atom {:driver driver :layout data :thread (Thread/currentThread)
                      :code-receipt code-receipt :finalized-run finalized-run :prefix prefix :prefix-view initial
                      :seed-pending? (atom true) :request (atom nil) :observations (IdentityHashMap.)})
        get-state (fn [engine] (state! holder engine (:source (:driver @holder))))]
    {:layout-receipt-sha256 receipt-pin
     :finalized-run finalized-run ; descriptive identity for actual session cross-binding, never issuance
     :check-source! (fn [engine source] (state! holder engine source) nil)
     :begin-request!
     (fn [engine request]
       (let [state (get-state engine) driver (:driver state)]
         (need (and (nil? @(:request state)) (zero? (.size ^IdentityHashMap (:observations state)))) "Previous request history is live")
         (outer! driver request)
         (need (and (identical? request (j/host-request @(:current-ctx driver) engine))
                    (not (field (field request "call") "replyClaimed"))) "Not the current unclaimed request")
         (reset! (:request state) request) nil))
     :artifact-environment!
     (fn [engine environment kernel constant-map bundle]
       (let [state (get-state engine)
             _ (need @(:seed-pending? state) "Artifact prefix can seed only one accepted version")
             witness (observed! state environment kernel constant-map bundle :input)
             prefix (prefix! state)]
         (need (and (identical? constant-map (:constant-map prefix)) (= 1 (:quot prefix)))
               "Actual first input map/quot differs from protected finalizer prefix")
         ;; Caller already holds the new K/M occurrences; Run still owns its
         ;; separate anchors. A later failure is terminal, never a second seed.
         (reset! (:seed-pending? state) false)
         (assoc witness :origin :authenticated-finalized-artifact-prefix)))
     :checked-environment!
     (fn [engine environment kernel constant-map bundle mode]
       (let [state (get-state engine)]
         (need (not @(:seed-pending? state)) "No accepted artifact prefix seed yet")
         (observed! state environment kernel constant-map bundle mode)))
     :checked-constants!
     (fn [engine environment token array]
       (let [state (get-state engine) observation (taken! state token :constants environment)]
         (need (identical? array (:value observation)) "Readback is not the exact taken checkedConstants result")
         (guard engine "array" array)
         {:guest-environment environment :array array :source-binding (:source (:driver state))
          :layout-receipt-sha256 receipt-pin}))
     :diagnostics-disabled!
     (fn [engine kernel root-token]
       (let [state (get-state engine) o (.get ^IdentityHashMap (:observations state) root-token)]
         (need (and o (= :root (:kind o)) (.resultTaken root-token)
                    (identical? @(:request state) (:outer o)) (identical? kernel (:value o))) "No exact taken root token for diagnostics")
         (imported-profile! state (kernel-view! (:driver state) (:layout state) kernel))
         {:kernel-root kernel :source-binding (:source (:driver state)) :layout-receipt-sha256 receipt-pin :enabled 0}))
     :finish-request!
     (fn [engine request]
       (let [state (get-state engine)]
         (need (and (identical? request @(:request state)) (field (field request "call") "replyClaimed")
                    (nil? (j/host-guest-result @(:current-ctx (:driver state)) engine))) "Request has unfinished helper or reply")
         (.clear ^IdentityHashMap (:observations state)) (reset! (:request state) nil) nil))
     :close!
     (fn []
       (when-let [state @holder]
         (reset! holder nil) (.clear ^IdentityHashMap (:observations state)) (reset! (:request state) nil)) nil)}))
