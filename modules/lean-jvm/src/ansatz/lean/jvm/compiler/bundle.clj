(ns ansatz.lean.jvm.compiler.bundle
  "Explicit external Linux producer bundle. SDK pins independently authorize its
   helpers; bundle self-description alone never authenticates native producers."
  (:require [ansatz.lean.jvm.compiler.transport :as transport]
            [ansatz.lean.jvm.entry :as checked-entry]
            [ansatz.lean.jvm.entry-v3 :as entry-v3]
            [ansatz.lean.jvm.producer :as producer]
            [clojure.data.json :as json] [clojure.string])
  (:import [java.nio.file Path Files LinkOption]
           [java.nio.charset StandardCharsets] [java.security MessageDigest]))

(def supported-producers
  {"entry" {"binarySHA256" (get-in checked-entry/cohorts [1 :binary])
            "sourceSHA256" (get-in checked-entry/cohorts [1 :source])}
   "startupHeader" {"binarySHA256" "2693f971452aa28190ca5c1033bf2b1030f9703b22f53181cd0591b1ab90399c"
                    "sourceSHA256" "f8c92d652c596b9bf656135348b190a5c09cf61ec40c8775835cf180a8833dd1"}
   "typedSource" {"binarySHA256" "83342c9582dd43aef3974ffadb6f989c1f7bd23d66b3c406258ca31223030041"
                  "sourceSHA256" "a48e00225fe08c1a74b66fff1102fd0c11ecefaaafc20ddcf6e28aaf363c99d3"}})
(defn- need [ok reason]
  (when-not ok (throw (ex-info reason {:code "UnsupportedProjectConfig" :stage :native-producer-bundle}))))
(defn- child! [^Path root relative]
  (need (and (string? relative) (<= 1 (count relative) 1024)
             (not (.isAbsolute (Path/of relative (make-array String 0)))))
        "Bounded relative producer path required")
  (let [path (.resolve root relative)]
    (need (and (= path (.normalize path)) (.startsWith path root)
               (= path (.toRealPath path (make-array LinkOption 0)))
               (Files/isRegularFile path (into-array LinkOption [LinkOption/NOFOLLOW_LINKS])))
          "Producer path escapes its bundle or uses a symlink")
    path))
(defn- producer! [root name descriptor]
  (let [entry-schema (when (= "entry" name)
                       (checked-entry/schema-for-pins! (get descriptor "sourceSHA256") (get descriptor "binarySHA256")))
        supported (if entry-schema
                    (select-keys descriptor ["binarySHA256" "sourceSHA256"])
                    (supported-producers name))]
    (need (and (map? descriptor)
               (= #{"binary" "binarySHA256" "source" "sourceSHA256"} (set (keys descriptor)))
               (or (#{1 2} entry-schema) (and (nil? entry-schema) (producer/supported? name (get descriptor "sourceSHA256") (get descriptor "binarySHA256")))))
          "Producer descriptor is not an independently supported SDK cohort")
    (let [supported descriptor
          binary (child! root (get descriptor "binary")) source (child! root (get descriptor "source"))]
      (need (Files/isExecutable binary) "Producer binary is not executable")
      (need (and (= (get supported "binarySHA256")
                    (get (#'transport/file-record binary (* 256 1048576)) "sha256"))
                 (= (get supported "sourceSHA256")
                    (get (#'transport/file-record source (* 2 1048576)) "sha256")))
            "Producer binary/source bytes differ from the SDK pins")
      {:binary binary :source source :binary-sha256 (get supported "binarySHA256")
       :source-sha256 (get supported "sourceSHA256") :entry-schema entry-schema})))
(defn- open-legacy!
  "Validate one explicitly supplied bundle, then configure the monitored native
   transport. No compiler is launched until the subsequent source build."
  [options]
  (let [root (#'transport/path! (.producerBundle options))
        manifest (child! root "producer-bundle.json")
        descriptor (#'transport/read-json! manifest 262144)]
    (need (and (map? descriptor) (= #{"schema" "leanCommit" "leanVersion" "target" "wordBits" "producers"}
                  (set (keys descriptor)))
               (= "lean-native-producer-bundle/1" (get descriptor "schema"))
               (= transport/lean-pin (get descriptor "leanCommit"))
               (= "4.33.1" (get descriptor "leanVersion"))
               (= "x86_64-unknown-linux-gnu" (get descriptor "target"))
               (= 64 (get descriptor "wordBits"))
               (= (set (keys supported-producers)) (set (keys (get descriptor "producers")))))
          "Unsupported native producer bundle profile")
    (let [producers (into {} (map (fn [[name value]] [name (producer! root name value)])
                                 (get descriptor "producers")))
          typed (producers "typedSource") header (producers "startupHeader") entry (producers "entry")
          compiler (transport/configure! {:sysroot (.sysroot options) :cache (.cache options)
                                          :typed-source (:binary typed)})]
      {:compiler compiler
       :project-options {:source-root "." :compile? true
                         :helper (:binary header) :helper-source (:source header)
                         :helper-sha256 (:binary-sha256 header) :helper-source-sha256 (:source-sha256 header)
                         :typed-exporter (:binary typed) :typed-exporter-source (:source typed)
                         :typed-exporter-sha256 (:binary-sha256 typed) :typed-exporter-source-sha256 (:source-sha256 typed)}
       :evidence-options {:entry-schema (:entry-schema entry)
                          :entry-helper (:binary entry) :entry-helper-source (:source entry)
                          :entry-helper-sha256 (:binary-sha256 entry) :entry-helper-source-sha256 (:source-sha256 entry)}})))


;; Candidate-only inspection does not configure a Compiler or issue a receipt.
;; The eventual independent cohort/closure registry owns producer admission.
(def ^:private closure-modules
  ["NativeEntryTransport" "NativeTypeGraph" "NativeNominalEntryEvidence"])
(def ^:private candidate-identities
  #{"binarySHA256" "sourceSHA256" "sourceClosureSHA256" "buildReceiptSHA256"})
(defn- sha! [value]
  (need (and (string? value) (boolean (re-matches #"[0-9a-f]{64}" value))) "Expected SHA-256") value)
(defn- exact! [value expected-keys]
  (need (and (map? value) (= expected-keys (set (keys value)))) "Unexpected candidate metadata keys"))
(defn- canonical [value]
  (cond (map? value) (into (sorted-map) (map (fn [[k v]] [k (canonical v)]) value))
        (vector? value) (mapv canonical value) :else value))
(defn- closure-bytes [rows]
  ;; EXACT native builder sourceClosure wire and dependency order. In particular,
  ;; these are root basenames, and the row digest key is sha256, not sourceSHA256.
  (need (and (vector? rows) (= 3 (count rows))) "Exactly three maintained sources required")
  (doseq [[row module] (map vector rows closure-modules)]
    (exact! row #{"module" "source" "sha256"})
    (need (= ["str" ["anonymous"] module] (get row "module")) "Unexpected source module/order")
    (need (= (str module ".lean") (get row "source")) "Expected maintained source basename")
    (sha! (get row "sha256")))
  (.getBytes (json/write-str (canonical rows) :escape-unicode false :escape-slash false)
             StandardCharsets/UTF_8))
(defn- closure-digest [rows]
  (apply str (map #(format "%02x" (bit-and 255 %))
                  (.digest (MessageDigest/getInstance "SHA-256") (closure-bytes rows)))))
(defn- candidate-profile! [descriptor]
  (exact! descriptor #{"schema" "leanCommit" "leanVersion" "target" "wordBits" "producers"})
  (need (and (= "lean-native-producer-bundle/2" (get descriptor "schema"))
             (= transport/lean-pin (get descriptor "leanCommit"))
             (= "4.33.1" (get descriptor "leanVersion"))
             (= "x86_64-unknown-linux-gnu" (get descriptor "target"))
             (= 64 (get descriptor "wordBits"))
             (map? (get descriptor "producers"))
             (= (set (keys supported-producers)) (set (keys (get descriptor "producers")))))
        "Unsupported candidate bundle profile"))
(defn- candidate-receipt! [receipt descriptor actual-binary]
  (need (and (map? receipt) (= "lean-native-entry-candidate/1" (get receipt "schema"))
             (= "entry-built-not-published" (get receipt "status"))
             (= transport/lean-pin (get receipt "leanCommit"))
             (= (get descriptor "sourceClosure") (get receipt "sourceClosure"))
             (= (get descriptor "sourceClosureSHA256") (get receipt "sourceClosureSHA256")))
        "Builder receipt does not bind the candidate source closure")
  (let [products (get receipt "products")
        _ (need (and (vector? products) (<= 1 (count products) 32)) "Builder product bound")
        binaries (filter #(= "entry" (get % "path")) products)
        processes (get receipt "processes")
        _ (need (and (vector? processes) (<= 1 (count processes) 64)) "Builder process bound")
        links (filter #(= "link-entry" (get % "label")) processes)]
    (need (and (= 1 (count binaries))
               (= (assoc actual-binary "path" "entry") (first binaries))
               (= 1 (count links)) (= 0 (get (first links) "exit"))
               (= {"supportInterpreter" true "interpreterExportFlag" "-rdynamic"
                   "linkerThreads" 1 "authority" "pinned Lake.Config.LeanExe.exeOnlyLinkArgs"}
                  (get receipt "standaloneLinkConfig")))
          "Builder receipt does not bind the actual interpreter executable")))
(defn- inspect-candidate!
  "Private descriptive byte correspondence ONLY. Expected identities come from
   the reviewed build, never from this bundle's self-description. No compiler,
   evidence options, BuildReceipt or admission capability is returned."
  [root expected]
  (exact! expected candidate-identities)
  (doseq [value (vals expected)] (sha! value))
  (let [root (#'transport/path! root) manifest (child! root "producer-bundle.json")
        manifest-record (#'transport/file-record manifest 262144)
        descriptor (#'transport/read-json! manifest 262144)
        _ (candidate-profile! descriptor)
        entry (get-in descriptor ["producers" "entry"])
        _ (exact! entry (into #{"binary" "source" "sourceClosure" "buildReceipt"} candidate-identities))
        _ (need (= expected (select-keys entry candidate-identities)) "Candidate differs from expected reviewed identities")
        rows (get entry "sourceClosure")
        _ (need (= (get entry "sourceClosureSHA256") (closure-digest rows)) "Source closure digest mismatch")
        _ (need (and (= "NativeNominalEntryEvidence.lean" (get entry "source"))
                     (= (get entry "sourceSHA256") (get (last rows) "sha256")))
                "Root source is absent from its exact source closure")
        files (atom [])
        capture (fn [relative maximum expected-sha]
                  (let [path (child! root relative) record (#'transport/file-record path maximum)]
                    (need (= expected-sha (get record "sha256")) "Candidate file differs from expected bytes")
                    (swap! files conj {:path path :maximum maximum :record record})
                    [path record]))
        _ (swap! files conj {:path manifest :maximum 262144 :record manifest-record})
        [binary binary-record] (capture (get entry "binary") (* 256 1048576) (get entry "binarySHA256"))
        _ (need (Files/isExecutable binary) "Candidate executable permission missing")
        sources (mapv (fn [row] (first (capture (get row "source") (* 2 1048576) (get row "sha256")))) rows)
        [receipt-path _] (capture (get entry "buildReceipt") (* 2 1048576) (get entry "buildReceiptSHA256"))
        receipt (#'transport/read-json! receipt-path (* 2 1048576))
        _ (candidate-receipt! receipt entry binary-record)
        auxiliary (into {} (for [name ["startupHeader" "typedSource"]]
                             [name (producer! root name (get-in descriptor ["producers" name]))]))]
    (doseq [[_ info] auxiliary
            [path maximum expected-sha] [[(:binary info) (* 256 1048576) (:binary-sha256 info)]
                                         [(:source info) (* 2 1048576) (:source-sha256 info)]]]
      (let [record (#'transport/file-record path maximum)]
        (need (= expected-sha (get record "sha256")) "Auxiliary producer changed during inspection")
        (swap! files conj {:path path :maximum maximum :record record})))
    (let [paths (mapv :path @files)]
      (doseq [i (range (count paths)) j (range i)]
        (need (not (Files/isSameFile (paths i) (paths j))) "Bundle roles must not alias one file")))
    (doseq [{:keys [path maximum record]} @files]
      (need (= record (#'transport/file-record path maximum)) "Candidate changed during inspection"))
    {:admission false :authority :byte-correspondence-only
     :descriptor descriptor :root root :entry-binary binary :entry-sources sources
     :expected-identities expected :file-records @files}))

(defn open!
  "Validate an explicitly supplied supported bundle and configure its transport.
   V3 binds the independently pinned complete source closure and build receipt."
  [options]
  (let [root (#'transport/path! (.producerBundle options))
        descriptor (#'transport/read-json! (child! root "producer-bundle.json") 262144)]
    (if (= "lean-native-producer-bundle/1" (get descriptor "schema"))
      (open-legacy! options)
      (let [producer (get-in descriptor ["producers" "entry"])
            version (checked-entry/schema-for-pins! (get producer "sourceSHA256") (get producer "binarySHA256"))
            _ (need (checked-entry/nominal-schema? version) "Expected a nominal entry producer")
            cohort (get checked-entry/cohorts version)
            expected {"sourceSHA256" (:source cohort) "binarySHA256" (:binary cohort)
                      "sourceClosureSHA256" (:source-closure cohort) "buildReceiptSHA256" (:build-receipt cohort)}
            inspected (inspect-candidate! root expected)
            entry (get-in (:descriptor inspected) ["producers" "entry"])
            custody {:source-closure (get entry "sourceClosure")
                     :source-closure-sha256 (get entry "sourceClosureSHA256")
                     :build-receipt (#'transport/read-json! (child! root (get entry "buildReceipt")) (* 2 1048576))
                     :build-receipt-sha256 (get entry "buildReceiptSHA256")}
            helper-record (#'transport/file-record (:entry-binary inspected) (* 256 1048576))
            source (last (:entry-sources inspected))
            source-record (#'transport/file-record source (* 2 1048576))
            _ (entry-v3/validate-producer-custody! custody source-record helper-record)
            typed (producer! root "typedSource" (get-in descriptor ["producers" "typedSource"]))
            header (producer! root "startupHeader" (get-in descriptor ["producers" "startupHeader"]))
            compiler (transport/configure! {:sysroot (.sysroot options) :cache (.cache options)
                                            :typed-source (:binary typed)})]
        {:compiler compiler
         :project-options {:source-root "." :compile? true
                           :helper (:binary header) :helper-source (:source header)
                           :helper-sha256 (:binary-sha256 header) :helper-source-sha256 (:source-sha256 header)
                           :typed-exporter (:binary typed) :typed-exporter-source (:source typed)
                           :typed-exporter-sha256 (:binary-sha256 typed) :typed-exporter-source-sha256 (:source-sha256 typed)}
         :evidence-options {:entry-schema version :entry-helper (:entry-binary inspected) :entry-helper-source source
                            :entry-helper-sha256 (:binary cohort) :entry-helper-source-sha256 (:source cohort)
                            :producer-custody custody :producer-files (:file-records inspected)}}))))

(defn source-configuration!
  "Select the existing source DAG or an explicitly requested built Lake workspace.
   Compiler discovery and artifacts remain separate; this never opens a Project."
  [compiler base source-root options]
  (let [name (fn [text] (reduce (fn [parent part] ["str" parent part]) ["anonymous"]
                               (clojure.string/split text #"\." -1)))
        root (name (.rootModule ^ansatz.lean.jvm.ProjectOptions options))]
    (if (.builtLakeWorkspace ^ansatz.lean.jvm.ProjectOptions options)
      (merge base ((requiring-resolve 'ansatz.lean.jvm.compiler.workspace/configure!) compiler source-root root))
      (cond-> (assoc base :project source-root :source-root (.sourceRoot ^ansatz.lean.jvm.ProjectOptions options) :roots [root])
        (seq (.installedImports ^ansatz.lean.jvm.ProjectOptions options))
        (assoc :installed-imports (mapv name (.installedImports ^ansatz.lean.jvm.ProjectOptions options)))))))
