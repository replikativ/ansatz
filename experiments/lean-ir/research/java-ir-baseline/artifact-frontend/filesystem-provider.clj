(ns filesystem-nat-source-provider-v2
  "Independent trusted-host witnesses for a bounded filesystem identity sequence.
   Hooks only read actual guest roots. They never advance or change ownership."
  (:require [java-ir-baseline :as j] [sequential-frontend-probe :as sp]
            [ansatz.research.ir.source-setup :as source]
            [heartbeat-lab-options-proof :as options-proof]
            [generated-command-receipt-v1 :as receipt]
            [filesystem-nat-source-profile-v2 :as profile]
            [prototype.kernel-bridge :as bridge]
            [ansatz.research.ir.kernel-projection :as projection]
            [artifact-declaration-authority-v4 :as authority])
  (:import [ansatz.kernel Name] [java.util IdentityHashMap] [java.lang.reflect InvocationTargetException]))
(def prefix "prelude\nimport Init.Prelude\n")
(def compiler-ref-sha "f05b997ed0394268a8f82e605292f26c205d16aa607b41ad715651fb914fbd06")
(def compiler-target-sha "ad6e9f84c4966aa59095a186cc6ed81f8a81dfdb24983e3109061b3345bcb461")
(defn- need [ok message] (when-not ok (throw (ex-info message {:profile :filesystem-nat-source-provider-v2}))))
(defn- field [x n] (.get (doto (.getDeclaredField (class x) n) (.setAccessible true)) x))
(defn- invoke-guard [e method x]
  (try (.invoke (doto (.getDeclaredMethod (class e) method (into-array Class [Object])) (.setAccessible true)) e (object-array [x]))
       (catch InvocationTargetException cause (throw (.getCause cause)))))
(defn- sha [^String text]
  (apply str (map #(format "%02x" (bit-and 255 %))
                 (.digest (java.security.MessageDigest/getInstance "SHA-256") (.getBytes text "UTF-8")))))
(defn- ctor [s x tag n bytes]
  (invoke-guard (sp/engine s) "constructorNode" x)
  (need (and (nil? (field x "closure")) (= tag (.getInt ^java.lang.reflect.Field (:tag (sp/ctx s)) x))
             (= n (alength ^objects (sp/fields s x))) (= bytes (alength ^bytes (sp/scalars s x)))) "Compiled source witness layout differs")
  (sp/fields s x))
(defn- array-values [s x]
  (invoke-guard (sp/engine s) "array" x)
  (let [n (j/request-value x "arraySize") fs ^objects (sp/fields s x)]
    (need (<= 0 n (alength fs) 16384) "Source array bound")
    (mapv #(aget fs %) (range n))))
(defn- frozen-data [s root]
  (let [seen (IdentityHashMap.) work (atom 0) chars (atom 0)]
    (letfn [(walk [x depth]
              (need (and (< (swap! work inc) 4096) (< depth 64)) "Source data witness bound")
              (cond
                (instance? Long x) [:long x]
                (instance? java.math.BigInteger x) (do (need (<= (.bitLength ^java.math.BigInteger x) 4096) "Source Nat bit bound") [:integer (str x)])
                (string? x) (do (need (<= (swap! chars + (count x)) 65536) "Source text bound") [:string x])
                :else
                (do
                  (need (identical? (:node-class (sp/ctx s)) (class x)) "Unknown mutable source witness carrier")
                  (if (.containsKey seen x) [:ref (.get seen x)]
                    (let [id (.size seen) _ (.put seen x id)
                          _ (need (and (not (field x "ref")) (not (field x "readyTask")) (nil? (field x "closure"))) "Source witness contains mutable/effectful object")
                          fs (if (field x "array") (array-values s x)
                               (do (invoke-guard (sp/engine s) "constructorNode" x) (vec (sp/fields s x))))]
                      [:node id (.getInt ^java.lang.reflect.Field (:tag (sp/ctx s)) x)
                       (mapv #(Byte/toUnsignedInt %) (sp/scalars s x)) (mapv #(walk % (inc depth)) fs)])))))]
      (walk root 0))))
(defn- scope-view [s command]
  (let [cf (ctor s command 0 11 0) scopes (ctor s (aget ^objects cf 2) 1 2 0)
        _ (need (= 0 (aget ^objects scopes 1)) "Exactly one base command scope required")
        scope (aget ^objects scopes 0) sf (ctor s scope 0 10 3)]
    (need (and (= "" (aget ^objects sf 0)) (= 0 (aget ^objects sf 2))
               (every? #(= 0 (aget ^objects sf %)) [3 4 7 8 9])
               (every? empty? (map #(array-values s (aget ^objects sf %)) [5 6]))
               (= [0 0 0] (mapv #(Byte/toUnsignedInt %) (sp/scalars s scope)))
               (= 0 (aget ^objects cf 5))) "Namespace/binders/attributes/computability/meta/depth source profile differs")
    {:options (aget ^objects sf 1) :environment (aget ^objects cf 0)}))
(defn- current-view [s]
  (let [ref (invoke-guard (sp/engine s) "reference" (sp/owned s :state-ref))
        state (aget ^objects (sp/fields s ref) 0) fs (ctor s state 0 4 0)]
    (assoc (scope-view s (aget ^objects fs 0)) :state state)))
(def main-module-getter-sha "f41d108aa00cd0b72502bf665567579a6ca95d8b62fd3557a4405ce1d43d69c6")
(def layout-directory "../../target/java-kernel-shim-overlay-v1")
(defn- actual-main-module [s layout environment]
  ;; Reuse the authenticated original mkEmptyEnvironment layout checker. Header
  ;; field0 is mainModule; all ordinary constructor/task/scalar guards run here.
  (first (:header-fields (#'authority/environment-view! (:driver s) layout environment))))
(defn- prove-main-module! [s captured authenticate! header-for layout-directory]
  (let [module (:module captured)
        _ (need (and (<= (count module) 256) (<= (reduce + (map count module)) 4096)) "Module Name proof bound")
        label "Lean.Environment.mainModule._boxed" header (header-for label)
        _ (authenticate! header)
        _ (need (= main-module-getter-sha (j/request-value header "originalSha256")) "Module getter is not pinned original boxed getter")
        layout (#'authority/read-layout! layout-directory)
        environment (:environment (current-view s))
        key [:filesystem-main-module-proof (Object.)]
        env-key [key :environment] name-key [key :name]
        ;; Boxed getter consumes the retained facade, never the frontend Env's
        ;; borrowed anchor. sp/:in-flight preserves arguments if the call pauses.
        _ (sp/retain-as! s env-key environment)
        name (sp/hold! s name-key (sp/call! s label [(sp/take-owner! s env-key)]))
        scope (projection/open-projector (sp/ctx s) (sp/engine s)
                {:max-nodes 1024 :deadline-nanos (+ (System/nanoTime) 5000000000)})
        actual (try (bridge/project-name-bounded (:world scope) name
                      {:max-nodes 257 :max-chars 4096} (:carrier-ops scope))
                    (finally ((:close! scope))))
        expected (reduce (fn [prefix segment] (Name/mkStr prefix segment)) Name/ANONYMOUS_NAME module)
        _ (need (= expected actual) "Actual original Environment.mainModule differs from captured module")
        _ (need (identical? name (actual-main-module s layout environment)) "Getter result differs from actual protected Header mainModule")
        frozen-name (frozen-data s name)]
    ;; Only successful projection/comparison releases proof ownership. Failure
    ;; preserves name-key in frontend owners for the existing retirement packet.
    ;; After release, current/initial frontend Env anchors this exact Name.
    (sp/drop! s name-key)
    {:layout layout :name name :frozen-name frozen-name}))
(defn make-captures!
  "Run actual getter-based options proof and witness actual guest source/compiler
   roots for one indexed definition or the EOF transaction. Captured host metadata grants no authority."
  ([child frontend captured-source command-index]
   (make-captures! child frontend captured-source command-index {:layout-directory layout-directory}))
  ([child frontend captured-source command-index {:keys [layout-directory]}]
  (need (and (string? layout-directory) (seq layout-directory)) "Explicit compiled layout directory required")
  (let [captured (profile/captured-profile captured-source)]
    (need (and (integer? command-index) (<= 0 command-index) (<= command-index (:command-count captured))) "Command index outside captured source")
  (let [_ (source/guard-source! (:code-receipt child) (get-in frontend [:driver :source]))
        proof (options-proof/check-prepared! frontend)
        _ (need (and (= :lab-options-proved (:status proof)) (identical? frontend (:session proof))) "Original option proof did not return this frontend session")
        s frontend d (:driver s) e (sp/engine s) src (:source d) code (:code-receipt child)
        expected (:text captured) filename (:filename captured)
        command (if (= command-index (:command-count captured)) (:eof captured) (nth (:commands captured) command-index))
        end (:byte-count captured) command-start (:start command) next-start (:next-start command)
        previous-start (:previous-start command)
        input (sp/owned s :input) input-fields (ctor s input 0 4 0)
        state-ref (sp/owned s :state-ref) old-owner-key (:state-owner-key (first @(:observations s)))
        old-owner (sp/owned s old-owner-key) options (:options (current-view s)) frozen-options (frozen-data s options)
        _ (need (= [expected filename end] [(aget ^objects input-fields 0) (aget ^objects input-fields 1) (aget ^objects input-fields 3)]) "Actual input bytes/name/end differ from known source")
        file-map (aget ^objects input-fields 2) file-fields (ctor s file-map 0 2 0)
        ;; Pinned FileMap.ofString always pushes the terminal position, including
        ;; a second occurrence when the final character is a newline.
        starts (conj (into [0] (keep-indexed (fn [i b] (when (= 10 (bit-and 255 b)) (inc i))) (.getBytes ^String expected "UTF-8"))) end)
        _ (need (and (= expected (aget ^objects file-fields 0)) (= starts (array-values s (aget ^objects file-fields 1)))) "Actual FileMap differs from input")
        header-for (fn [label] ((sp/host-helper "ensure-header!") d (sp/typed-name label)))
        authenticate! (fn [header]
                        (let [name (j/lean-name-data (j/request-value header "name"))
                              row (or (source/lookup-entry code name) ((sp/host-helper "original-row!") d name))]
                          (need row "Call is outside accepted source")
                          (source/authenticate-canonical-header! src (:row row) (:sha256 row) header)))
        module-proof (prove-main-module! s captured authenticate! header-for layout-directory)
        ref-header (header-for "Lean.compileDeclsRef") _ (authenticate! ref-header)
        _ (need (= compiler-ref-sha (j/request-value ref-header "originalSha256")) "Compiler ref source differs")
        ref-id (j/function-id (sp/ctx s) "Lean.compileDeclsRef")
        compiler-ref (aget ^objects (field e "constants") ref-id)
        _ (invoke-guard e "reference" compiler-ref)
        compiler (aget ^objects (sp/fields s compiler-ref) 0) function (field compiler "closure")
        target (when function (field function "header"))
        _ (need (and target (= compiler-target-sha (j/request-value target "originalSha256"))
                     (identical? target (header-for "Lean.Compiler.LCNF.main._boxed"))
                     (zero? (alength ^objects (sp/fields s compiler)))) "Compiler callback is not original zero-capture LCNF main")
        _ (authenticate! target)
        accepts (doto (.getDeclaredMethod (class e) "acceptsClosure" (into-array Class [(:node-class (sp/ctx s))])) (.setAccessible true))
        check! (fn [_]
                 (source/guard-source! code src)
                 (need (and (identical? e (sp/engine s)) (identical? src (:source d))
                            (identical? input (sp/owned s :input)) (identical? state-ref (sp/owned s :state-ref))
                            (identical? old-owner (sp/owned s old-owner-key))) "Source owner lease changed")
                 (ctor s old-owner 0 4 0)
                 ;; Lean's ST.Ref.take deliberately stores nullptr until put.
                 ;; During execution the live value can belong to a guest frame;
                 ;; inspect only protected immutable roots here. Current scope
                 ;; and environment contents are witnessed at stable boundaries.
                 (invoke-guard (sp/engine s) "reference" state-ref)
                 (need (= (:frozen-name module-proof) (frozen-data s (:name module-proof))) "Protected module Name changed")
                 (need (= frozen-options (frozen-data s options)) "Protected options changed")
                 (let [f (ctor s input 0 4 0)]
                   (need (and (= expected (aget ^objects f 0)) (= filename (aget ^objects f 1))
                              (= end (aget ^objects f 3)) (identical? file-map (aget ^objects f 2))) "InputContext changed"))
                 (let [ff (ctor s file-map 0 2 0)]
                   (need (and (= expected (aget ^objects ff 0)) (= starts (array-values s (aget ^objects ff 1)))) "FileMap changed"))
                 (let [ready ^booleans (field e "constantReady") retired ^booleans (field e "constantRetired")
                       provenance (.get ^java.util.Map (field e "preparedGlobalSources") (int ref-id))]
                   (need (and (aget ready ref-id) (not (aget retired ref-id))
                              (identical? compiler-ref (aget ^objects (field e "constants") ref-id))
                              provenance (identical? src (field provenance "binding"))
                              (identical? compiler (aget ^objects (sp/fields s compiler-ref) 0))
                              (identical? target (field (field compiler "closure") "header"))) "Actual compiler reference/callback lease changed"))
                 (.invoke ^java.lang.reflect.Method accepts e (object-array [compiler]))
                 nil)
        observation! (fn [{:keys [observation stage]}]
                       (check! nil)
                       (let [state (:state observation) fs (ctor s state 0 4 0)
                             ps (aget ^objects fs 1) pf (ctor s ps 0 1 2)
                             view (scope-view s (:command-state observation))
                             pos (aget ^objects pf 0) commands (array-values s (aget ^objects fs 3))]
                         (need (and (identical? (:environment view) (:environment observation))
                                    (identical? options (:options view)) (= frozen-options (frozen-data s options))
                                    (= [0 0] (mapv #(Byte/toUnsignedInt %) (sp/scalars s ps))))
                               "Actual command state/scope/options/parser changed outside selected profile")
                         (need (identical? (:name module-proof) (actual-main-module s (:layout module-proof) (:environment observation))) "Observed environment mainModule differs")
                         (case stage
                           :baseline (need (and (= command-start pos) (= previous-start (aget ^objects fs 2)) (= command-index (count commands))) "Initial source parser position differs")
                           :observed (need (and (= next-start pos) (= command-start (aget ^objects fs 2)) (= (inc command-index) (count commands))) "Completed source span/command count differs")
                           (throw (ex-info "Unknown compiler observation stage" {:stage stage}))))) ]
    (check! nil)
    (receipt/source-captures
      {:check! check!
       :before-command! (fn [request]
                          (check! nil)
                          (need (identical? (:name module-proof)
                                  (actual-main-module s (:layout module-proof) (:environment (current-view s))))
                                "Initial environment mainModule differs")
                          (need (and (identical? input (:input request)) (identical? state-ref (:state-ref request))
                                     (identical? e (:engine request)) (identical? src (:source request))
                                     (identical? options (:options (current-view s)))
                                     (= frozen-options (frozen-data s options))) "Source capture request differs")
                          {:engine e :source src :input input :state-ref state-ref
                           :description {:profile "legacy-private-filesystem-nat-identities/2"
                                         :command-index command-index :command-count (:command-count captured)
                                         :action (:action command) :root (:root command) :binder (:binder command) :module (:module captured)
                                         :module-getter-sha main-module-getter-sha
                                         :command-end next-start :previous-start previous-start
                                         :input-sha256 (sha expected) :filename filename :utf8-bytes end
                                         :command-start command-start :compiler-ref-sha compiler-ref-sha
                                         :compiler-target-sha compiler-target-sha :options-shape-sha (sha (pr-str frozen-options))}})
       :before-call! (fn [{:keys [engine source header]}]
                       (check! nil) (need (and (identical? e engine) (identical? src source)) "Foreign source call")
                       (authenticate! header))
       :after-taken! (fn [{:keys [engine source header slot result]}]
                      (check! nil) (need (and (identical? e engine) (identical? src source)
                                            (= :owned (aget ^objects slot 1)) (identical? result (aget ^objects slot 0))) "Actual taken source result differs")
                      (authenticate! header))
       :inspect-observation! observation!})))))
