(ns ansatz.lean.jvm.compiler.products
  "Private used-origin byte custody. Only the opt-in /3 compilation profile
   certifies compile-era defining products; old caches retain current-byte custody.
   No native process, cache transition, entry admission or receipt issuer here."
  (:require [ansatz.lean.jvm.compiler.local :as local]
            [ansatz.lean.jvm.compiler.transport :as transport]
            [ansatz.lean.jvm.installed :as installed]
            [ansatz.lean.jvm.used-products :as used])
  (:import [java.nio.file Path Files LinkOption]
           [java.util WeakHashMap]))

(def ^:private no-links (into-array LinkOption [LinkOption/NOFOLLOW_LINKS]))
(deftype Capture [])
(defonce ^:private captures (WeakHashMap.))
(defn- need [ok reason facts]
  (when-not ok (throw (ex-info "Used-product custody refused"
                              (merge {:code "UsedProductConflict" :reason reason} facts)))))
(defn- confined! [^Path root ^String relative]
  (let [root (.normalize (.toAbsolutePath root)) path (.normalize (.resolve root relative))]
    (need (.startsWith path root) :path-escape {})
    (loop [p path]
      (when p
        (need (not (Files/isSymbolicLink p)) :symlink {:path (str p)})
        (recur (.getParent p))))
    path))
(defn- directory! [^Path root]
  (let [root (confined! root "")]
    (need (Files/isDirectory root no-links) :directory {:path (str root)}) root))
(defn- present! [^Path path]
  (cond (Files/exists path no-links) true
        (Files/notExists path no-links) false
        :else (need false :indeterminate-presence {:path (str path)})))
(defn- selected-root!
  "Pinned findOLean selects the first PACKAGE root, not the first full file.
   A missing child inside an earlier package does not fall through to sysroot."
  [roots module]
  (let [prefix (first (installed/components module))]
    (or (some (fn [^Path root]
                (let [dir (confined! root prefix) primary (confined! root (str prefix ".olean"))]
                  (when (or (Files/isDirectory dir no-links) (present! primary)) root))) roots)
        (need false :unresolved-package {:module module}))))
(defn- roles! [^Path root module total]
  (mapv (fn [suffix relative]
          (let [path (confined! root relative)]
            (if (present! path)
              (do
                (need (Files/isRegularFile path no-links) :nonregular-product {:module module :role suffix})
                (let [size (Files/size path)]
                  (need (<= 0 size installed/max-product-bytes) :product-byte-limit {:module module :role suffix})
                  (need (<= (+ @total size) installed/max-total-bytes) :total-byte-limit {})
                  (let [record (#'transport/file-record path installed/max-product-bytes)]
                    (swap! total + (get record "bytes"))
                    (need (<= @total installed/max-total-bytes) :total-byte-limit {})
                    (assoc record "role" suffix "present" true))))
              {"role" suffix "present" false})))
        installed/suffixes (installed/product-paths module)))
(defn- local-index! [compiled]
  (need (and (vector? compiled) (<= (count compiled) 128)
             (= (count compiled) (count (set (map #(get % "module") compiled))))) :compiled-records {})
  (into {} (map (fn [record]
                  (let [module (get record "module") expected (first (installed/product-paths module))]
                    (need (and (= expected (get record "olean")) (map? (get record "oleanRecord")))
                          :local-primary-record {:module module})
                    [module record])) compiled)))
(defn- verify-known! [{:keys [state directory cache-key inputs cache-manifest installed]}]
  ;; Existing cache validation is deliberately reused, not weakened or rewritten.
  (when cache-key
    (need (= cache-manifest (#'local/cache-hit! directory cache-key inputs)) :cache-mutation {}))
  (local/verify-installed! state installed)
  (local/verify-compilation-products! state inputs))
(defn- collect!
  [{:keys [state directory compiled files installed] :as context} required]
  (let [build (directory! (.resolve ^Path directory "build"))
        library (directory! (.resolve ^Path (:sysroot state) "lib/lean"))
        locals (local-index! compiled)
        declared (mapv #(get % "module") (get installed "modules" []))
        local-names (mapv #(get % "module") compiled)
        ;; Authorize before touching any inventory-requested module file.
        _ (need (and (vector? required) (<= (count required) used/max-modules)
                     (= (count required) (count (set required)))) :inventory {})
        _ (doseq [module required] (#'used/module! module))
        _ (need (and (not-any? (set declared) local-names)
                     (not-any? installed/init? (concat local-names declared))) :origin-shadowing {})
        _ (doseq [module required]
            (need (or (contains? locals module) (some #{module} declared) (installed/init? module))
                  :undeclared-origin {:module module}))
        total (atom 0)
        modules
        (mapv (fn [module]
                (let [local (get locals module) root (if (or local (contains? (get-in state [:workspace :products]) module)) build library)
                      selected (selected-root! [build library] module)
                      _ (need (= root selected) :native-resolution-shadow {:module module})
                      products (roles! root module total)
                      primary (first products)]
                  (need (true? (get primary "present")) :primary-missing {:module module})
                  (when local
                    (need (= (get local "oleanRecord") (select-keys primary ["bytes" "sha256"]))
                          :local-primary-mutation {:module module})
                    (doseq [[relative product] (map vector (installed/product-paths module) products)]
                      (let [baseline (get files (str "build/" relative))]
                        (need (= (boolean baseline) (get product "present")) :local-role-presence {:module module :path relative})
                        (when baseline
                          (need (= baseline (select-keys product ["bytes" "sha256"]))
                                :local-role-mutation {:module module :path relative})))))
                  (when-let [baseline (some #(when (= module (get % "module")) %) (get installed "modules"))]
                    (need (= (get baseline "products")
                             (mapv (fn [relative product]
                                     (assoc (dissoc product "role") "path" relative))
                                   (installed/product-paths module) products))
                          :installed-role-mutation {:module module}))
                  {"module" module "productSha256" (get primary "sha256") "products" products})) required)
        manifest {"schema" used/schema "modules" modules}]
    (when (= local/nominal-profile (get-in context [:inputs "profile"]))
      (let [baseline (into {} (map #(vector (get % "module") %)
                                   (get-in context [:inputs "compilationProducts" "modules"])))]
        (doseq [row modules :let [module (get row "module")] :when (not (contains? locals module))]
          (need (contains? baseline module) :missing-compilation-product
                {:module module :action :compile-under-new-v3-baseline})
          (need (= row (get baseline module)) :compilation-product-mutation {:module module}))))
    (used/authorize! manifest required local-names declared)
    ;; Materialize the bounded canonical encoding now, before exposing a receipt.
    (used/canonical-bytes manifest)
    manifest))
(defn- verify-context! [{:keys [context required manifest]}]
  (verify-known! context)
  (need (= manifest (collect! context required)) :used-product-mutation {})
  (verify-known! context)
  true)
(defn- capture-context! [context required]
  ;; Private fixture/issuer seam. Authority follows only the verified cache profile.
  (verify-known! context)
  (let [manifest (collect! context required)
        payload {:context context :required required :manifest manifest :sha256 (used/digest manifest)
                 :requires-v3-rebuild (not= local/nominal-profile (get-in context [:inputs "profile"]))}]
    (verify-context! payload)
    payload))
(defn- compiler-baseline! [state inputs]
  (let [toolchain (get inputs "toolchain")]
    (need (and (= "trusted-immutable-installed-official-toolchain/1" (get toolchain "policy"))
               (= (str (:sysroot state)) (get toolchain "sysroot"))
               (= (str (:producer state)) (get toolchain "typedSourceProducerPath"))
               (= (:producer-sha256 state) (get-in toolchain ["typedSourceProducer" "sha256"]))
               (= (str (:launcher state)) (get toolchain "resourceLauncherPath")))
          :compiler-baseline-mismatch {:action :capture-from-the-matching-compiler-configuration}))
  inputs)
(defn- parsed-context [compiler state directory key manifest]
  ;; Retain only the re-parsed immutable cache baseline, never descriptive
  ;; caller preparation values or their potentially mutable nested metadata.
  (let [inputs (compiler-baseline! state (get manifest "inputs"))]
    {:compiler compiler :state state :directory directory :cache-key key :inputs inputs
     :cache-manifest manifest :compiled (get manifest "compiled") :files (get manifest "files")
     :installed (get inputs "installedImports")}))
(defn- context! [compiler preparation]
  (let [state (#'transport/issued compiler) key (:cache-key preparation) inputs (:inputs preparation)]
    (need (and (map? preparation) (= :modules-compiled (:status preparation))
               (string? key) (re-matches #"[0-9a-f]{64}" key) (map? inputs))
          :missing-compiled-baseline {:action :compile-under-v3-baseline-before-admission})
    (need (= key (#'transport/digest (#'transport/canonical inputs))) :cache-key-input-mismatch {})
    (let [directory (directory! (.resolve ^Path (:cache state) (str "local-modules-" key)))
          manifest (#'local/cache-hit! directory key inputs)]
      (need (= (:compiled preparation) (get manifest "compiled")) :compiled-record-mismatch {})
      (parsed-context compiler state directory key manifest))))
(defn capture!
  "Internal source-issuer seam. Derive paths from an issued compiler's verified
   compiled-cache records, never caller paths. The preparation MAP is descriptive,
   not an issuer token. Old caches seal current bytes only. The /3 profile seals
   compile-era defining products; missing origins require a new /3 compilation.
   Transitive implementation dependencies retain the installed toolchain policy."
  [compiler preparation required]
  (let [state (#'transport/issued compiler)]
    (locking (:lock state)
      (need (identical? state (#'transport/issued compiler)) :compiler-identity {})
      (let [payload (capture-context! (context! compiler preparation) required) token (Capture.)]
        (locking captures (.put captures token payload)) token))))
(defn- issued! [capture]
  (need (= Capture (class capture)) :capture-identity {})
  (locking captures (or (.get captures capture) (need false :capture-identity {}))))
(defn manifest [capture] (:manifest (issued! capture)))
(defn description [capture]
  (let [payload (issued! capture)]
    {:manifest (:manifest payload) :sha256 (:sha256 payload)
     :requires-v3-rebuild (:requires-v3-rebuild payload)
     :authority (if (:requires-v3-rebuild payload) :verified-current-products-only
                    :verified-compilation-products)}))
(defn verify!
  "Recheck the exact captured set, optional absence and native package resolution.
   Call immediately before and after a helper; compare its echoed inventory/table
   separately. No retry or new origin capture occurs on a changed baseline.
   The trusted namespace contract applies: this is not an atomic snapshot that
   detects hostile transient ABA path/content replacement between checks."
  [capture]
  (let [{:keys [context required manifest]} (issued! capture)
        compiler (:compiler context) state (#'transport/issued compiler)]
    (locking (:lock state)
      (need (identical? (:state context) state) :compiler-identity {})
      (verify-context! {:context context :required required :manifest manifest}))))
