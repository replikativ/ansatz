(ns prototype.globals-consumer-factory
  "Closed globals-overlay consumer of the archived full-Init /2 preparation.
   Producer identity is reconstruction provenance, never the loaded consumer build.
   Definitions only; authenticated construction/linking executes no guest code."
  (:require [clojure.java.io :as io]
            [clojure.data.json :as json]
            [clojure.set :as set]
            [clojure.string :as str]
            [prototype.bootstrap-archive :as archive]
            [prototype.checkpoint-wire :as wire]
            [prototype.declaration-store :as ds]
            [prototype.import-ir :as ir]
            [prototype.runtime-abi :as abi]
            [prototype.raw-interop :as raw]
            [prototype.module-store :as modules]
            [prototype.module-import :as import]
            [prototype.import-capabilities :as regions]
            [prototype.module-init-capabilities :as initializers]
            [prototype.kernel-host :as kernel]
            [prototype.eval-const :as eval]
            [prototype.preparation :as prep]
            [prototype.machine :as machine]
            [prototype.globals-consumer-profile :as compatibility])
  (:import [java.nio.charset StandardCharsets CodingErrorAction]
           [java.nio ByteBuffer]
           [java.lang.ref WeakReference ReferenceQueue]
           [java.util HashMap ArrayList]))

(def factory-id "ansatz-full-init-source-bound-precheck/1")
(def shared-linear-factory-id "ansatz-full-init-source-bound-precheck/2")
(def lean-commit "819816b2e0a3bf405af45ae5c7af2491d8f5bee6")
(def kernel-policy {:allow-axioms? true :allow-unsafe? true :allow-compiler-markers? true})
(defn target [namespace part] ["str" ["str" ["anonymous"] namespace] part])
(def exporter (target "RuntimeCompileShim" "exportCompiled"))
(def json-target (target "RuntimeCompileShim" "exportEvalConstWitnessValue"))
(def typed-target (target "RuntimeCompileShim" "exportEvalConstWitnessIR"))
(def shared-target (target "RuntimeCompileShim" "exportEvalConstWitnessIRSharedNames"))
(def shared-linear-target (target "RuntimeCompileShim" "exportEvalConstWitnessIRSharedNamesLinear"))
(def shared-linear-sha256 "4b0d1548a3721ac87fac48a1260c4cd33181ac5baa60498dec25e49825f78ea4")
(def helpers
  (merge kernel/control-helpers
    (into {} (map (fn [[role name]] [role (target "KernelBridgeShim" name)]))
      {:root "checkedKernelRoot" :empty? "checkedEnvironmentIsEmpty"
       :constant-map "checkedConstantMapRoot" :constants "checkedConstants"
       :quot-init? "checkedQuotInit" :definition "postCheckSafeDefinition"
       :definition-any "postCheckDefinition" :axiom "postCheckSafeAxiom"
       :theorem "postCheckTheorem" :opaque "postCheckSafeOpaque"
       :mutual "postCheckMutualDefinitions" :error "otherError"
       :compiler-marker "postCheckCompilerMarker"})))
(def assembly-roots
  (vec (concat (vals helpers) (vals import/helpers)
               [import/bulk-helper import/header-finalize-helper
                (target "RuntimeCompileShim" "compileImportedFileState")
                (target "RuntimeCompileShim" "inspectFileHeader") exporter
                (target "RuntimeCompileShim" "exportEvalConstWitness")])))
(def pinned
  {:archive "21acd0e8e735f46232dcb64ea3071600a2b2b0973167d46517e91b0db58b8129"
   :declaration-index "74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e"
   :transport-descriptor "62b168762b4ef900ac783589d4e8b4df4fa4712f120722190fbe4b3cfc0de144"
   :initializer-witness "c735381b25e946357b44ad125f8bb7b188c3aea2009df930d09b491f8a2eac61"
   :json-witness "45dcd510324bdff6d0d95ac1093d26a087ad1d6e513e7fec1ea2d07f6a8873fd"
   :typed-witness "731bb72ce9928e0d46d50728c675df21a3d073c6d0f3c1dde96816af89c09cad"
   :linear-witness "a78a10859db267efa952f12b2635c6cdc3dfa32ce713f98f04f6a8ea6e2f9e98"
   :shared-witness "9864fa3afbf521fa541ef0a00931c34e237ea6538582ddad0746acf5e8e5bed8"})
(def overlay-order
  [:runtime-compile :kernel-bridge :kernel-declarations :kernel-control
   :runtime-files :transport-header :kernel-encoding])

(def kernel-probe-factory-id "ansatz-kernel-import-probe-source-bound-precheck/1")
(def kernel-probe-schema "kernel-import-probe-checkpoint-preparation/1")
(def kernel-probe-assembly-roots
  (vec (concat [(target "CheckpointFinalizerProbe" "registeredExtensionNames")
                (target "CheckpointFinalizerProbe" "addPreludeCompilerMarkers")]
               assembly-roots)))
(def kernel-probe-trusted-roots (vec (concat kernel-probe-assembly-roots [shared-linear-target exporter])))
(def ^:private kernel-probe-profile
  {:factory-id kernel-probe-factory-id :schema kernel-probe-schema
   :witness shared-linear-target :overlay-order (conj overlay-order :kernel-probe)
   :assembly-roots kernel-probe-assembly-roots :prepared-function-count 312167
   :source-shape {:size 516 :source-bytes 82847 :index-bytes 22704
                  :source-sha256 "e6d3e40d1d1c00a3a4cbe98eb8642d6be5321b16ed18c8fbcdbc69028606c2f3"
                  :index-sha256 "c7db7e45416090b7103d573941871f82c6db58c6a1ff6e093197136fd4a65d1e"}
   :pins (merge pinned
           {:transport-descriptor "609732edd2fcbf20cab33e5cf2f571965722f02785ace14dfe96d3d2237c0d90"
            :shared-linear-witness shared-linear-sha256
            :kernel-probe "8d4cbb50ab45234fef38831fd7988ae21fff8ff783e5b34bd4ca3fe20a5dda5e"
            :runtime-compile "82163d2e995d193fcfc65d70f9701a0d1cd98dd0d238ea510c56efdcce9cfa9a"
            :kernel-bridge "99eb4257f0dd86f7e302722bd0fc729a53d8bbd3d14b2aeb2c53e791332a599c"
            :kernel-declarations "a5fad5a20cc2a860ded2a9cfae20ef53abeb84d62df5a8aade1f9558ce80cf4e"
            :kernel-control "0d3fc3873b8cc4b1ceb4fa8a6bdc34e2ea619c432841ee7c6e10b63e151fa611"
            :runtime-files "f2aa20217b9007bc0ff982327e74377049e16a04194c31ecb59a5455d725734e"
            :transport-header "370d4a41b4ccc2c7aecf745bf6af233f33d4893484c20bfb19ed5e69d15918ff"
            :kernel-encoding "9eb84bf93d8e389377dfeeceac5e4d4552d68f933586a366dbf6316cbb612922"
            :aliases "51b80c4da0634b7f9d11496923865d6e9c171e29b0d5e0cc738480ba18d01e84"})})

(defn- exact! [x keys label]
  (wire/check (and (map? x) (= keys (set (clojure.core/keys x)))) (str "Invalid " label)))
(defn- utf8 [bytes]
  (str (.decode (doto (.newDecoder StandardCharsets/UTF_8)
                  (.onMalformedInput CodingErrorAction/REPORT) (.onUnmappableCharacter CodingErrorAction/REPORT))
                (ByteBuffer/wrap bytes))))
(defn- checked-bytes [resolver recipe id]
  (let [row (get-in recipe [:artifacts id])
        _ (exact! row #{:sha256 :max-bytes} "artifact recipe")
        _ (wire/check (and (wire/hash? (:sha256 row)) (integer? (:max-bytes row))
                           (<= 1 (:max-bytes row) (* 64 1024 1024))) "Invalid small artifact bound")
        bytes (with-open [input (io/input-stream (resolver id))]
                (.readNBytes input (int (inc (:max-bytes row)))))]
    (wire/check (and (<= (alength bytes) (:max-bytes row)) (= (:sha256 row) (wire/sha256 bytes)))
                (str "Factory artifact mismatch: " id)) bytes))
(defn- catalogue-bytes [resolver recipe id]
  (ir/index-bundles [(java.io.StringReader. (utf8 (checked-bytes resolver recipe id)))]))
(defn- read-row [catalogue name]
  (if-let [read! (:read-declaration catalogue)] (read! name) (get-in catalogue [:declarations name])))
(defn- lower [bindings catalogue row]
  (if (contains? bindings (some-> row :ir :extern abi/symbol-for))
    (raw/lower bindings row) (abi/lower-deferred-catalogue catalogue row)))

(defn canonicalize-verified-functions
  "Compare newly derived functions to actual canonical snapshot objects, including
   metadata. No unverified snapshot key can enter the result through this helper."
  [candidate derived]
  (reduce-kv
    (fn [out name function]
      (let [entry (find candidate name)]
        ;; Existing entries are already admitted canonical objects from the
        ;; previous stage. Identity alone can skip repeated encoding walks;
        ;; equal but distinct derived objects still require the exact metadata/
        ;; scalar-bit comparison before receiving canonical identity.
        (wire/check (and entry (or (identical? function (val entry))
                                   (wire/same-data? function (val entry))))
                    "Prepared function differs from pinned derivation")
        (assoc out (key entry) (val entry)))) {} derived))
(defn- complete [catalogue functions roots bindings candidate]
  (canonicalize-verified-functions candidate
    (prep/complete-functions catalogue
      (ir/load-closure catalogue roots #(lower bindings catalogue %) {:existing-functions functions})
      roots #(lower bindings catalogue %))))
(defn- manifest! [candidate]
  (doseq [manifest (:manifests candidate)]
    (ir/validate-manifest! manifest)
    (wire/check (and (= "lean-init-plan/1" (get-in manifest [:initializationPlan :schema]))
                     (= ["str" ["anonymous"] "RuntimeCompileShim"] (get-in manifest [:initializationPlan :module]))
                     (false? (get-in manifest [:initializationPlan :moduleSystem]))
                     (= [] (get-in manifest [:initializationPlan :actions])))
                "Witness stage may not add initialization actions")))
(defn- extension [baseline candidate expected target]
  (wire/check (= 1 (count (:manifests candidate))) "Expected one witness-stage manifest")
  (manifest! candidate)
  (wire/check (wire/same-data? (:manifests baseline) (:manifests candidate)) "Witness baseline manifest drift")
  (doseq [[name old] (:declarations baseline)]
    (wire/check (wire/same-data? old (get-in candidate [:declarations name])) "Witness changed a pinned baseline declaration"))
  (let [additions (apply dissoc (:declarations candidate) (keys (:declarations baseline)))]
    (wire/check (and (= expected (count additions)) (contains? additions target)) "Unexpected witness-stage additions")
    additions))
(defn- overlay-stage [catalogue functions rows manifests]
  (let [additions
        (reduce-kv
          (fn [out name row]
            (if (contains? (:declarations catalogue) name)
              (do (wire/check (wire/same-data? (select-keys (read-row catalogue name) [:kind :ir :dependencies :redirect :runtime])
                                              (select-keys row [:kind :ir :dependencies :redirect :runtime]))
                              "Witness addition conflicts with existing pinned catalogue") out)
              (do (wire/check (not (contains? functions name)) "Witness row collides with unbacked code")
                  (assoc out name row)))) {} rows)
        catalogue (ds/overlay catalogue {:manifests manifests :declarations additions})]
    catalogue))
(defn- add-stage [catalogue functions bindings candidate rows manifests root]
  (let [catalogue (overlay-stage catalogue functions rows manifests)
        ;; Match the existing scripts: load selected closure at each stage, then
        ;; complete actual shared/exporter bodies only after all stage overlays.
        functions (canonicalize-verified-functions candidate
                    (ir/load-closure catalogue [root] #(lower bindings catalogue %) {:existing-functions functions}))]
    {:catalogue catalogue :functions functions}))
(defn- add-shared-linear [catalogue functions bindings candidate typed shared selected]
  ;; Exact S4 policy: check every S3 baseline row, including the 19 previously
  ;; unadopted linear rows; admit the delta relative to stage 2, not just the
  ;; newly compiled wrapper. No initializer or guest function executes here.
  (wire/check (= 1 (count (:manifests selected))) "Expected one shared-linear witness manifest")
  (manifest! selected)
  (wire/check (wire/same-data? (:manifests shared) (:manifests selected)) "Shared-linear manifest drift")
  (doseq [[name row] (:declarations shared)]
    (wire/check (and (contains? (:declarations selected) name)
                     (wire/same-data? row (get-in selected [:declarations name])))
                "Shared-linear changed or removed pinned old declaration"))
  (wire/check (and (contains? (:declarations selected) shared-linear-target)
                   (not (contains? (:declarations shared) shared-linear-target)))
              "Shared-linear must add fresh named witness")
  (let [delta (apply dissoc (:declarations selected) (keys (:declarations typed)))
        catalogue (overlay-stage catalogue functions delta (:manifests selected))
        functions (canonicalize-verified-functions candidate
                    (prep/complete-functions catalogue functions [shared-linear-target]
                      #(lower bindings catalogue %)))]
    {:catalogue catalogue :functions functions}))
(defn- selected-profile [preparation]
  (wire/check (and (= shared-linear-factory-id (:factory-id preparation))
                   (= "full-init-checkpoint-preparation/2" (get-in preparation [:catalogue-recipe :schema])))
              "Unapproved globals consumer producer profile")
  (wire/check (= kernel-policy (:kernel-policy preparation)) "Unapproved producer kernel policy")
  (wire/check (= (vec (concat assembly-roots [shared-linear-target exporter])) (:trusted-roots preparation))
              "Unapproved producer helper roots")
  {:factory-id shared-linear-factory-id :schema "full-init-checkpoint-preparation/2"
   :witness shared-linear-target :pins (assoc pinned :shared-linear-witness shared-linear-sha256)})
(defn- witnesses [catalogue functions bindings candidate resolver recipe profile]
  (let [json (catalogue-bytes resolver recipe :json-witness)
        typed (catalogue-bytes resolver recipe :typed-witness)
        linear (catalogue-bytes resolver recipe :linear-witness)
        shared (catalogue-bytes resolver recipe :shared-witness)
        _ (manifest! json)
        json-additions (into {} (remove (fn [[name _]] (contains? (:declarations catalogue) name))) (:declarations json))
        _ (wire/check (contains? json-additions json-target) "Expected fresh additive JSON witness")
        typed-additions (extension json typed 9 typed-target)
        _ (wire/check (= 491 (count (:declarations linear))) "Pinned linear baseline count drift")
        linear-only (set/difference (set (keys (:declarations linear))) (set (keys (:declarations typed))))
        _ (wire/check (= 19 (count linear-only)) "Pinned linear-only inventory drift")
        shared-additions (extension linear shared 6 shared-target)
        _ (loop [pending [shared-target] seen #{}]
            (when-let [name (peek pending)]
              (wire/check (not (contains? linear-only name)) "Shared witness uses unadopted linear helper")
              (if (contains? seen name) (recur (pop pending) seen)
                (recur (into (pop pending) (get-in shared [:declarations name :dependencies])) (conj seen name)))))
        s1 (add-stage catalogue functions bindings candidate json-additions (:manifests json) json-target)
        s2 (add-stage (:catalogue s1) (:functions s1) bindings candidate typed-additions (:manifests typed) typed-target)
        s3 (add-stage (:catalogue s2) (:functions s2) bindings candidate shared-additions (:manifests shared) shared-target)
        selected (if (= shared-linear-target (:witness profile))
                   (add-shared-linear (:catalogue s3) (:functions s3) bindings candidate typed shared
                     (catalogue-bytes resolver recipe :shared-linear-witness)) s3)]
    (assoc selected :functions
      (complete (:catalogue selected) (:functions selected) [(:witness profile) exporter] bindings candidate))))

(defn build-identity
  "Content identity of an explicitly complete, reviewed host implementation inventory.
   Canonical bytes: prefix then sorted id TAB kind TAB SHA256 LF. This is not an
   automatic proof that disk source equals already loaded JVM namespace code."
  [inventory]
  (wire/check (and (vector? inventory) (seq inventory)
                   (= (count inventory) (count (set (map :id inventory))))) "Invalid build inventory")
  (doseq [row inventory]
    (exact! row #{:id :kind :sha256} "build inventory row")
    (wire/check (and (string? (:id row)) (re-matches #"[A-Za-z0-9_./$-]+" (:id row))
                     (contains? #{:host-source :host-resource :kernel-class} (:kind row)) (wire/hash? (:sha256 row)))
                "Invalid build inventory identity"))
  (wire/sha256 (.getBytes (str "ansatz-full-init-factory-build/1\n"
                              (apply str (for [{:keys [id kind sha256]} (sort-by :id inventory)]
                                           (str id "\t" (name kind) "\t" sha256 "\n")))) StandardCharsets/UTF_8)))
(defn- loaded-kernel-class-sha256! [id]
  ;; Select through the actual loaded kernel's class loader, never a resolver's
  ;; arbitrary .class filename. Fresh bootstrap separately attests CodeSource.
  (wire/check (.endsWith ^String id ".class") "Invalid kernel class inventory ID")
  (let [class-name (subs (str/replace id "/" ".") 0 (- (count id) 6))
        class (Class/forName class-name false (.getClassLoader ansatz.kernel.TypeChecker))]
    (with-open [input (.getResourceAsStream class (str "/" id))]
      (wire/check input "Kernel class resource unavailable")
      (let [digest (java.security.MessageDigest/getInstance "SHA-256") bytes (byte-array 65536)]
        (loop [] (let [n (.read input bytes)] (when (pos? n) (.update digest bytes 0 n) (recur))))
        (.formatHex (java.util.HexFormat/of) (.digest digest))))))

(defn- authenticate-build! [recipe preparation resolve-artifact]
  (wire/check (= (:implementation-sha256 preparation) (build-identity (:build-inventory recipe))) "Factory build identity mismatch")
  (doseq [{:keys [id kind sha256]} (:build-inventory recipe)]
    (if (= :kernel-class kind)
      (wire/check (= sha256 (loaded-kernel-class-sha256! id)) "Loaded kernel class resource drift")
      (wire/check (= sha256 (wire/file-sha256 (resolve-artifact id))) "Host implementation source/resource drift"))))

(defn- authenticate-hosted-application-build!
  "Keep original producer bytes/digest separate from the seventh consumer's
   fixed corrected kernel classes. Its resolver supplies every producer row,
   including original archived classes; no arbitrary loaded-class waiver exists."
  [recipe preparation resolve-artifact]
  (wire/check (= (:implementation-sha256 preparation) (build-identity (:build-inventory recipe)))
              "Factory build identity mismatch")
  (doseq [{:keys [id kind sha256]} (:build-inventory recipe)]
    (if (= :kernel-class kind)
      (let [loaded (get compatibility/hosted-application-substitutions id sha256)]
        ;; Original archived bytes remain producer provenance, independently of
        ;; the actual corrected class selected by this consumer's class loader.
        (wire/check (= sha256 (wire/file-sha256 (resolve-artifact id)))
                    "Archived producer kernel class drift")
        (wire/check (= loaded (loaded-kernel-class-sha256! id))
                    "Loaded hosted application kernel class resource drift"))
      (wire/check (= sha256 (wire/file-sha256 (resolve-artifact id)))
                  "Host implementation source/resource drift"))))

(defn- private-index-sha256 [^java.io.RandomAccessFile index]
  (locking index
    (let [position (.getFilePointer index) digest (java.security.MessageDigest/getInstance "SHA-256")
          buffer (byte-array 65536)]
      (try (.seek index 0)
           (loop [] (let [n (.read index buffer)]
                      (when (pos? n) (.update digest buffer 0 n) (recur))))
           (.formatHex (java.util.HexFormat/of) (.digest digest))
           (finally (.seek index position))))))
(defn- narrow-source! [profile descriptor source world]
  (when-let [shape (:source-shape profile)]
    ;; Borrow the loader's already-opened Store/private index. Never close it on
    ;; rejection: the generic loader owns the ResourceLease and handles failure.
    (wire/check (and (= "prototype.module_store.Store" (.getName (class source)))
                     (false? @(:closed source))
                     (= 1 (count (:native-imports world)))
                     (identical? source (first (:native-imports world)))
                     (= (:size shape) (:size source) (:nodes descriptor))
                     (= (:source-sha256 shape) (:digest source) (:sourceSha256 descriptor))
                     (= (:source-bytes shape) (:maximum-bytes source) (:sourceBytes descriptor)
                        (.size ^java.nio.channels.FileChannel (:channel source)))
                     (= (:index-bytes shape) (:indexBytes descriptor)
                        (.length ^java.io.RandomAccessFile (:index source)))
                     (= (:index-sha256 shape) (:indexSha256 descriptor)
                        (private-index-sha256 (:index source))))
                "Narrow factory source identity drift")
    (wire/check (and (= :done (:status world)) (empty? (:frames world)) (nil? (:host-request world))
                     (empty? (:kernel-environments world))
                     (empty? (:source-modules world)) (empty? (:source-regions world))
                     (empty? (:source-import-prefixes world)))
                "Narrow factory requires idle precheck state without published authority")))

(defn- prepared-registry! [profile trusted prepared]
  (when-let [n (:prepared-function-count profile)]
    (wire/check (= n (count trusted)) "Narrow prepared executable count drift"))
  (wire/check (= (set (keys trusted)) (set (keys prepared)))
              "Snapshot prepared flags differ from independently rebuilt registry")
  (doseq [[name function] trusted]
    (wire/check (identical? function (get prepared name)) "Prepared registry identity drift")))

;; Native-base readiness is explicitly opt-in. The six original constructors
;; never build this metadata or register a binding. Source-bound provenance is
;; recorded only at the end of their separately named successor's authenticated
;; invocation. A caller's map is NEVER hashed or compared for registry lookup.
(def ^:private native-init-symbol "lean_run_mod_init_core")
(def ^:private native-init-limits
  {:plans 4096 :imports 16384 :actions 16384 :symbols 12288 :queries 1024
   :symbol-bytes 4096 :total-symbol-bytes 262144 :host-work 33554432})
(defonce ^:private native-binding-provenance
  {:buckets (HashMap.) :queue (ReferenceQueue.)})
(defn- native-binding-hash [binding] (System/identityHashCode binding))
(defn- native-binding-proof! [binding proof]
  (locking native-binding-provenance
    (let [^HashMap buckets (:buckets native-binding-provenance)
          ^ReferenceQueue queue (:queue native-binding-provenance)]
      (loop []
        (when-let [dead (.poll queue)]
          (let [key (.hashCode dead) ^ArrayList bucket (.get buckets key)]
            (when bucket
              (loop [i (dec (.size bucket))]
                (when (<= 0 i)
                  (when (identical? dead (first (.get bucket i))) (.remove bucket (int i)))
                  (recur (dec i))))
              (when (.isEmpty bucket) (.remove buckets key))))
          (recur)))
      (let [key (native-binding-hash binding)
            ^ArrayList bucket (or (.get buckets key) (ArrayList.))
            found (some (fn [[^WeakReference reference saved]]
                          (when (identical? binding (.get reference)) saved)) bucket)]
        (if proof
          (do
            (wire/check (nil? found) "Native initializer binding already attested")
            ;; Only scalar KEY is captured by the proxy callback, never BINDING.
            ;; PROOF must not contain this binding, its handler, or a World.
            (.add bucket [(proxy [WeakReference] [binding queue] (hashCode [] key)) proof])
            (.put buckets key bucket)
            proof)
          found)))))
(defn- native-module-name! [value]
  (loop [value value nodes 0 chars 0]
    (wire/check (and (vector? value) (< nodes 256)) "Native module Name exceeds its bound")
    (if (= ["anonymous"] value) chars
      (do
        (wire/check (and (= 3 (count value)) (or (= "str" (first value)) (= "num" (first value)))
                         (string? (nth value 2))) "Malformed native module Name")
        (let [n (+' chars (count (nth value 2)))]
          (wire/check (<= n 16384) "Native module Name exceeds character bound")
          (recur (second value) (inc nodes) n))))))
(defn- native-init-metadata! [plans witness]
  (wire/check (and (map? plans) (<= 1 (count plans) (:plans native-init-limits))
                   (vector? (:symbols witness))
                   (<= (count (:symbols witness)) (:symbols native-init-limits)))
              "Native readiness metadata exceeds its fixed inventory bounds")
  (let [counts (reduce (fn [{:keys [imports actions name-chars]} [_ plan]]
                         (wire/check (and (vector? (:imports plan)) (vector? (:actions plan)))
                                     "Native readiness requires finite producer vectors")
                         ;; Check aggregate counts BEFORE scanning their elements.
                         (let [i (+' imports (count (:imports plan))) a (+' actions (count (:actions plan)))]
                           (wire/check (and (<= i (:imports native-init-limits)) (<= a (:actions native-init-limits)))
                                       "Native readiness aggregate metadata exceeds bounds")
                           (let [n (reduce (fn [n request]
                                             (let [n (+' n (native-module-name! (:module request)))]
                                               (wire/check (<= n 16777216) "Native readiness Name metadata exceeds64MiB UTF-8 ceiling") n))
                                           (+' name-chars (native-module-name! (:module plan))) (:imports plan))]
                             (wire/check (<= n 16777216) "Native readiness Name metadata exceeds64MiB UTF-8 ceiling")
                             {:imports i :actions a :name-chars n})))
                       {:imports 0 :actions 0 :name-chars 0} plans)
        _ (reduce (fn [chars {:keys [module symbol]}]
                    (wire/check (and (string? symbol) (<= 1 (count symbol) (:symbol-bytes native-init-limits)))
                                "Native witness symbol exceeds bound")
                    (let [n (+' chars (native-module-name! module) (count symbol))]
                      ;; Conservative UTF-16 length*4 UTF-8 upper bound. No
                      ;; unbounded byte encoding precedes this metadata gate.
                      (wire/check (<= n 16777216) "Native witness metadata exceeds64MiB UTF-8 ceiling") n))
                  (:name-chars counts) (:symbols witness))
        init ["str" ["anonymous"] "Init"]
        modules (loop [pending [init] seen #{}]
                  (if (empty? pending) seen
                    (let [module (peek pending) pending (pop pending)]
                      (if (contains? seen module) (recur pending seen)
                        (let [plan (get plans module)]
                          (wire/check (and plan (< (count seen) (:queries native-init-limits)))
                                      "Native readiness lacks bounded complete Init plans")
                          (recur (into pending (map :module (:imports plan))) (conj seen module)))))))
        valid (:initialized-symbols (initializers/options-from-witness plans witness))
        selected (reduce (fn [out {:keys [symbol module phase]}]
                           (if (and (= "all" phase) (contains? modules module)
                                    (= {:module module :phase :all} (get valid symbol)))
                             (do (wire/check (not (contains? out module)) "Ambiguous native initializer witness coverage")
                                 (wire/check (and (string? symbol) (<= 1 (count symbol) (:symbol-bytes native-init-limits)))
                                             "Native initializer symbol exceeds bound")
                                 (let [bytes (alength (.getBytes ^String symbol StandardCharsets/UTF_8))]
                                   (wire/check (<= bytes (:symbol-bytes native-init-limits)) "Native initializer UTF-8 symbol exceeds bound")
                                   (assoc out module {:module module :symbol symbol :bytes bytes}))) out))
                         {} (:symbols witness))
        bytes (reduce +' 0 (map :bytes (vals selected)))
        per-query (+' (*' 5 (count plans)) (*' 3 (:imports counts)))
        work (*' (count modules) per-query)]
    (wire/check (and (seq modules) (= modules (set (keys selected)))
                     (<= bytes (:total-symbol-bytes native-init-limits))
                     (<= work (:host-work native-init-limits)))
                "Native readiness has incomplete coverage or exceeds host work bound")
    ;; Witness order fixes query order without retaining plans/actions/graphs.
    {:queries (into [] (keep (fn [{:keys [module phase symbol]}]
                              (when (and (= "all" phase) (= symbol (get-in selected [module :symbol])))
                                (select-keys (get selected module) [:module :symbol])))) (:symbols witness))
     :host-units-per-query (long per-query) :max-host-work (:host-work native-init-limits)
     :counts {:plans (count plans) :imports (:imports counts) :actions (:actions counts)
              :queries (count modules) :symbol-bytes bytes :host-work (long work)}}))

(defn- make-factory*
  "Construct an explicit approved factory. RESOLVE-ARTIFACT maps recipe artifact/
   inventory IDs to local paths. STORE-ROOT names the content-addressed declaration
   store (index and per-row hashes remain authority). The caller separately attests
   this trusted JVM process loaded the separately authenticated CONSUMER inventory.
   The archived producer inventory is separately checked reconstruction provenance.
   On-disk hashes alone cannot attest loaded Vars after with-redefs/reload.
   This function and produced factory execute host validation/linking only."
  [profile reconstruction? runtime-ops? heap-net-dirty? source-graph? graph-frontend? hosted-application? {:keys [producer-preparation producer-resolve-artifact store-root] :as options} native-owner]
  (let [consumer-description (cond hosted-application? (compatibility/authenticate-hosted-application! options)
                                     graph-frontend? (compatibility/authenticate-source-graph-frontend-reconstruction! options)
                                     source-graph? (compatibility/authenticate-source-graph-reconstruction! options)
                                     heap-net-dirty? (compatibility/authenticate-heap-net-dirty-reconstruction! options)
                                     runtime-ops? (compatibility/authenticate-runtime-ops-reconstruction! options)
                                     reconstruction? (compatibility/authenticate-reconstruction! options)
                                     :else (compatibility/authenticate! options))
        expected-preparation producer-preparation
        resolve-artifact producer-resolve-artifact
        recipe (:catalogue-recipe expected-preparation)
        overlays (get profile :overlay-order overlay-order)
        roots (get profile :assembly-roots assembly-roots)]
    (exact! expected-preparation #{:factory-id :implementation-sha256 :catalogue-recipe :kernel-policy :trusted-roots} "full-Init preparation")
    (exact! recipe #{:schema :declaration-index :artifacts :build-inventory} "full-Init recipe")
    (wire/check (= (set (concat overlays [:aliases :transport-descriptor :initializer-witness
                                              :json-witness :typed-witness :linear-witness :shared-witness]
                               (when (= shared-linear-target (:witness profile)) [:shared-linear-witness])
                               [:archive]))
                   (set (keys (:artifacts recipe)))) "Full-Init artifact inventory drift")
    (wire/check (and (= (:factory-id profile) (:factory-id expected-preparation))
                     (= (:schema profile) (:schema recipe))
                     (= kernel-policy (:kernel-policy expected-preparation))
                     (fn? resolve-artifact) (string? store-root)) "Unapproved full-Init factory preparation")
    (doseq [[id sha] (:pins profile) :when (not= id :declaration-index)]
      (wire/check (= sha (get-in recipe [:artifacts id :sha256])) "Pinned full-Init artifact drift"))
    (wire/check (= (:declaration-index pinned) (:declaration-index recipe)) "Pinned declaration index drift")
    (wire/check (= (vec (concat roots [(:witness profile) exporter])) (:trusted-roots expected-preparation))
                "Factory helper-root inventory drift")
    (if hosted-application?
      (authenticate-hosted-application-build! recipe expected-preparation resolve-artifact)
      (authenticate-build! recipe expected-preparation resolve-artifact))
    (fn [{:keys [preparation world functions prepared-functions resources] :as parsed}]
      (exact! parsed #{:preparation :world :functions :prepared-functions :resources} "parsed restore context")
      (wire/check (wire/same-data? expected-preparation preparation) "Restore preparation drift")
      (wire/check (identical? functions (:functions world)) "Factory candidate/world mismatch")
      (wire/check (= 1 (count resources)) "Full-Init profile requires one verified native source")
      (let [source (first resources)
            descriptor (json/read-str (utf8 (checked-bytes resolve-artifact recipe :transport-descriptor)) :key-fn keyword)
            _ (wire/check (and (= (:manifest descriptor) (:manifest source))
                               (= (:sourceSha256 descriptor) (:digest source))
                               (= (:nodes descriptor) (:size source))) "Factory source differs from pinned transport")
            _ (narrow-source! profile descriptor source world)
            _ (wire/check (= :immutable-text-v1 (:sharecommon-profile world)) "Assembly storage profile drift")
            loaded (modules/describe-attached world source)
            backing (ds/open-index-verified-stream store-root (:declaration-index recipe))
            initial (abi/with-export-aliases
                      (reduce (fn [catalogue id] (ds/overlay catalogue (catalogue-bytes resolve-artifact recipe id)))
                              backing overlays)
                      (catalogue-bytes resolve-artifact recipe :aliases))
            plans (into {} (keep (fn [manifest] (when-let [plan (:initializationPlan manifest)] [(:module plan) plan])))
                        (:manifests initial))
            witness (json/read-str (utf8 (checked-bytes resolve-artifact recipe :initializer-witness)) :key-fn keyword)
            native-metadata (when native-owner (native-init-metadata! plans witness))
            transport (merge (regions/make-bindings loaded)
                             (initializers/make-bindings (initializers/options-from-witness plans witness)))
            ;; raw/lower consumes signatures only. These provisional handlers
            ;; never execute and never capture the enormous candidate registry.
            uncallable (fn [& _] (wire/fail "Provisional checkpoint binding cannot execute" {}))
            provisional (merge {"lean_elab_add_decl" {:signature kernel/signature :handler uncallable}
                                "lean_eval_const" {:signature eval/signature :handler uncallable}} transport)
            base (archive/verify-function-rows
                   (resolve-artifact :archive)
                   {:expected-sha256 (:archive pinned) :expected-lean-commit lean-commit
                    :verify-function
                    (fn [name original]
                      (let [entry (find functions name)
                            expected (if (or (:runtime-extern original) (:deferred-extern original) (:raw-extern original))
                                       (let [row (read-row initial name)]
                                         (wire/check (get-in row [:ir :extern]) "Missing archived extern backing")
                                         (second (lower provisional initial row))) original)]
                        (wire/check (and entry (wire/same-data? expected (val entry))) "Archived prepared executable drift")
                        [(key entry) (val entry)]))})
            _ (wire/check (= (:declaration-index pinned) (get-in base [:header :declaration-index])) "Bootstrap index header drift")
            _ (wire/check (= (:next-id base) (:base source)) "Source base differs from original bootstrap reservation")
            assembly (complete initial (:functions base) roots provisional functions)
            staged (witnesses initial assembly provisional functions resolve-artifact recipe profile)
            trusted (:functions staged) catalogue (:catalogue staged)
            _ (prepared-registry! profile trusted prepared-functions)
            _ (eval/validate-executables! world trusted (:trusted-roots expected-preparation))
            ;; Capture AFTER all authenticated overlays and actual closure
            ;; completion; use reconstructed original prepared subset, not the
            ;; candidate's later imported evalConst additions.
            bindings (merge transport
                       {"lean_elab_add_decl" (kernel/make-binding helpers kernel-policy)
                        "lean_eval_const" (eval/make-binding exporter
                                            {:witness (:witness profile) :witness-format :typed-ir
                                             :catalogue catalogue :trusted-functions trusted :research-traps? true})})]
        (let [result (assoc consumer-description :catalogue catalogue :bindings bindings)]
          (when native-owner
            (let [binding (get bindings native-init-symbol)
                  metadata native-metadata]
              (wire/check (and (= shared-linear-factory-id (:factory-id profile))
                               (= initializers/signature (:signature binding)) (fn? (:handler binding)))
                          "Native readiness requires the fixed authenticated initializer binding")
              (native-binding-proof! binding (assoc metadata :owner native-owner :source source
                                                   :producer compatibility/producer-implementation-sha256))))
          result)))))


(deftype Factory [])
(def ^:private issued-factories (java.util.WeakHashMap.))
(defn- capability! [factory]
  ;; Factory has no public token/callback fields to copy. Only an actually issued
  ;; object identity is accepted; values deliberately do not retain the weak key.
  (let [entry (when (instance? Factory factory)
                (locking issued-factories (.get issued-factories factory)))]
    (wire/check entry "Expected authenticated closed globals consumer factory")
    entry))
(defn descriptor
  "Immutable identities of this authenticated closed capability; no resource ownership."
  [factory]
  (:descriptor (capability! factory)))
(defn invoke!
  "Reconstruct authenticated catalogue/bindings over the parser's exact function
   identities. No guest steps, initializer replay, Java association or source close."
  [factory parsed]
  ((:invoke (capability! factory)) parsed))
(defn- issue-factory*
  "Authenticate the archived producer separately from this actual consumer.
   OPTIONS must include externally accepted consumer inventory digest and fresh
   loaded-code attestation. Resource hashes alone do not attest already loaded Vars.
   Returns an identity-registered capability, never a supplied reconstruction fn."
  [reconstruction? runtime-ops? heap-net-dirty? source-graph? graph-frontend? hosted-application? options native-owner]
  (let [profile (selected-profile (:producer-preparation options))
        invoke (make-factory* profile reconstruction? runtime-ops? heap-net-dirty? source-graph? graph-frontend? hosted-application? options native-owner)
        description {:producer-preparation (:producer-preparation options)
                     :consumer-implementation-sha256 (:expected-consumer-implementation-sha256 options)
                     :compatibility-profile (cond hosted-application? compatibility/hosted-application-profile-id
                                                  graph-frontend? compatibility/source-graph-frontend-reconstruction-profile-id
                                                  source-graph? compatibility/source-graph-reconstruction-profile-id
                                                  heap-net-dirty? compatibility/heap-net-dirty-reconstruction-profile-id
                                                  runtime-ops? compatibility/runtime-ops-reconstruction-profile-id
                                                  reconstruction? compatibility/reconstruction-profile-id
                                                  :else compatibility/profile-id)}]
    (let [factory (Factory.)]
      (locking issued-factories
        (.put issued-factories factory {:descriptor description :invoke invoke :native-owner native-owner}))
      factory)))

(defn- issue-factory [reconstruction? runtime-ops? heap-net-dirty? source-graph? graph-frontend? options]
  (issue-factory* reconstruction? runtime-ops? heap-net-dirty? source-graph? graph-frontend? false options nil))

(defn make-factory
  "Issue the original closed globals consumer capability with exact captured options."
  [options]
  (issue-factory false false false false false options))
(defn make-reconstruction-factory
  "Issue the separately named closed reconstruction consumer capability. Producer
   recipe/archive and option contract are identical to make-factory."
  [options]
  (issue-factory true false false false false options))

(defn make-runtime-ops-reconstruction-factory
  "Issue the closed ops-table reconstruction capability with its exact mutable pin.
   The original factory APIs retain their original inventories and identities."
  [options]
  (issue-factory true true false false false options))

(defn make-heap-net-dirty-reconstruction-factory
  "Issue the distinct net-dirty heap/ops reconstruction capability with its exact
   HeapOverlay source pin. All older factory source contracts remain unchanged."
  [options]
  (issue-factory true true true false false options))

(defn make-source-graph-reconstruction-factory
  "Issue only the fixed fifth graph consumer, with exact reviewed source-import
   and planner pins plus the fourth heap prerequisites. No helper executes here."
  [options]
  (issue-factory true true true true false options))

(defn make-source-graph-frontend-reconstruction-factory
  "Issue the distinct sixth graph frontend-protocol consumer with the exact
   reviewed frontend pin. The five prior contracts/options remain unchanged."
  [options]
  (issue-factory true true true true true options))

(defn make-source-graph-native-base-factory
  "Opt-in sixth-profile factory for fixed source-bound native Init readiness.
   All six previous constructors retain their exact options/output/validation.
   This constructor performs additional bounded provenance validation only when
   its authenticated restore invocation succeeds; it never executes a query."
  [options]
  (issue-factory* true true true true true false options (Object.)))

(defn make-hosted-application-factory
  "Issue the seventh fixed application consumer with native readiness support.
   Three added source members and helper/disposal substitutions are authenticated
   before restore. All six old consumer contracts remain unchanged. This does
   not execute or pre-authorize ordinary-inductive preparation or typed IO."
  [options]
  (issue-factory* true true true true true true options (Object.)))

(deftype NativeInitReadiness [])
(defonce ^:private native-readiness-issued (java.util.WeakHashMap.))
(defn- native-readiness! [token]
  (let [entry (when (instance? NativeInitReadiness token)
                (locking native-readiness-issued (.get native-readiness-issued token)))]
    (wire/check entry "Expected issued source-bound native readiness capability") entry))
(defn native-init-readiness
  "Issue a compact fixed readiness token from THIS opted-in factory's actual
   authenticated returned binding and borrowed Source. Copied maps, signatures,
   descriptors or options-from-witness confer no provenance. No World retained."
  [factory source binding]
  (let [factory-entry (capability! factory) owner (:native-owner factory-entry)]
    (wire/check owner "Factory did not opt in to native Init readiness")
    (let [proof (native-binding-proof! binding nil)]
      (wire/check (and proof (identical? owner (:owner proof))
                       (identical? source (:source proof)) (false? @(:closed source)))
                  "Native initializer binding/source provenance mismatch")
      (let [token (NativeInitReadiness.)]
        (locking native-readiness-issued
          (.put native-readiness-issued token (assoc proof :binding binding)))
        token))))
(defn native-init-coverage
  "Bounded descriptive native selection, not readiness/completion evidence."
  [token source binding]
  (let [entry (native-readiness! token)]
    (wire/check (and (identical? source (:source entry)) (false? @(:closed source))
                     (identical? binding (:binding entry))) "Native readiness lost Source/binding identity")
    {:modules (mapv :module (:queries entry)) :query-count (count (:queries entry))
     :host-units-per-query (:host-units-per-query entry) :max-host-work (:max-host-work entry)
     :counts (:counts entry)}))
(defn ^:no-doc query-native-init
  "Fixed token-indexed dispatch through the actual installed binding. Returns
   owned [World, IO Bool]; the staged caller MUST escrow before decoding/release.
   No IR/guest instructions, arbitrary symbol, callback, fallback or guard seed.
   This low-level owned-Bool operation receives no session and does NOT attest
   that a proposed binding is installed in an arbitrary World. The native staged
   control independently matches its actual session/configuration before every
   protected slice and finalizer entry; returned IO grants no import authority."
  [token world binding index]
  (let [entry (native-readiness! token) source (:source entry)]
    ;; Identity precedes any access to the caller's proposed binding map.
    (wire/check (and (identical? binding (:binding entry))
                     (integer? index) (<= 0 index) (< index (count (:queries entry)))
                     (= :done (:status world)) (empty? (:frames world)) (nil? (:host-request world))
                     (not (:initializing? world)) (not (:initialization-scope world))
                     (= 1 (count (:native-imports world)))
                     (identical? source (first (:native-imports world))) (false? @(:closed source))
                     (= initializers/signature (:signature binding)))
                "Native readiness query requires its exact idle Source/binding packet")
    ((:handler binding) nil world [(get-in entry [:queries (int index) :symbol]) machine/erased])))
