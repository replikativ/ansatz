;; SOURCE-ONLY PROPOSAL. No project namespace may load until verify! completes.
;; Invocation under the separately reviewed sole-lane resource guard:
;; java -cp <exact dep jars>:<selected>:<classes> clojure.main bootstrap.clj
;;      <pack-root> <launch.edn> <external-launch-sha> <external-contract-sha>
;; The outer guard must authenticate this script before it starts executing.
(ns coherent-bootstrap
  (:require [clojure.edn :as edn] [clojure.java.io :as io]
            [clojure.string :as str] [clojure.set :as set])
  (:import [java.io PushbackReader StringReader]
           [java.nio.charset StandardCharsets CodingErrorAction]
           [java.nio ByteBuffer]
           [java.nio.file Files LinkOption FileVisitOption]
           [java.security MessageDigest]
           [java.util.jar JarFile]))

(defn- check! [ok message] (when-not ok (throw (ex-info message {}))))
(defn- exact! [value keys label]
  (check! (and (map? value) (= keys (set (clojure.core/keys value)))) (str "Invalid bootstrap " label)))
(defn- sha? [x] (and (string? x) (boolean (re-matches #"[0-9a-f]{64}" x))))
(defn- sha [bytes]
  (.formatHex (java.util.HexFormat/of) (.digest (MessageDigest/getInstance "SHA-256") ^bytes bytes)))
(defn- file-sha [file]
  (with-open [stream (io/input-stream file)]
    (let [md (MessageDigest/getInstance "SHA-256") bytes (byte-array 65536)]
      (loop [] (let [n (.read stream bytes)] (when (pos? n) (.update md bytes 0 n) (recur))))
      (.formatHex (java.util.HexFormat/of) (.digest md)))))
(defn- relative! [id]
  (check! (and (string? id) (<= 1 (count id) 512) (re-matches #"[A-Za-z0-9_./$-]+" id)
               (not (str/starts-with? id "/"))
               (not-any? #{"" "." ".."} (str/split id #"/" -1))) "Invalid bootstrap relative ID"))
(defn- resolve-file [root id]
  (relative! id)
  (let [file (io/file root id) canonical (.getCanonicalFile file)]
    (check! (.startsWith (.toPath canonical) (.toPath ^java.io.File root)) "Bootstrap input escapes captured pack")
    (check! (not (Files/isSymbolicLink (.toPath file))) "Bootstrap symbolic-link input")
    canonical))
(defn- no-symlink-ancestors! [^java.io.File file]
  (let [path (.normalize (.toAbsolutePath (.toPath file)))]
    (loop [cursor path]
      (when cursor
        (check! (not (Files/isSymbolicLink cursor)) "Bootstrap symbolic-link ancestor")
        (recur (.getParent cursor))))
    (check! (= path (.toPath (.getCanonicalFile file))) "Bootstrap canonical path mismatch")
    file))
(defn- external-store! [stores]
  (check! (and (vector? stores) (= 1 (count stores))) "Bootstrap exact external CAS store required")
  (let [store (first stores)
        _ (exact! store #{:role :root :index-relative :index-sha256} "external CAS store")
        _ (check! (and (= :producer-declarations (:role store)) (string? (:root store))
                       (.isAbsolute (io/file (:root store))) (sha? (:index-sha256 store))
                       (= (str "indexes/" (:index-sha256 store) ".json") (:index-relative store)))
                  "Bootstrap external CAS role/index mismatch")
        root (no-symlink-ancestors! (io/file (:root store)))
        index (no-symlink-ancestors! (io/file root (:index-relative store)))
        _ (check! (and (.isDirectory root) (.isFile index)
                       (.isDirectory (io/file root "declarations"))
                       (= (.getCanonicalFile root) (.getParentFile (.getParentFile (.getCanonicalFile index))))
                       (= (:index-sha256 store) (file-sha index))) "Bootstrap external CAS root/index drift")]
    ;; Only this exact index is returned externally. declaration_store retains
    ;; its per-blob SHA + exact Name checks. This is content authentication, not
    ;; a claim that external blob paths are a filesystem sandbox.
    {:root root :index index :sha256 (:index-sha256 store)}))
(defn- bytes! [file bound]
  (check! (and (.isFile ^java.io.File file) (<= 1 (.length ^java.io.File file) bound)) "Bootstrap file byte bound/missing file")
  (let [bytes (Files/readAllBytes (.toPath ^java.io.File file))]
    (check! (<= 1 (alength bytes) bound) "Bootstrap file grew beyond byte bound") bytes))
(defn- utf8 [bytes]
  (str (.decode (doto (.newDecoder StandardCharsets/UTF_8)
                  (.onMalformedInput CodingErrorAction/REPORT)
                  (.onUnmappableCharacter CodingErrorAction/REPORT)) (ByteBuffer/wrap bytes))))
(defn- read-data [bytes]
  (let [text (utf8 bytes)]
    ;; Prevent recursive EDN reader exhaustion before parsing authenticated data.
    (loop [i 0 depth 0 quoted? false escape? false comment? false forms 0]
      (if (= i (count text))
        (check! (and (zero? depth) (not quoted?)) "Bootstrap EDN delimiters")
        (let [c (.charAt ^String text i)]
          (cond
            comment? (recur (inc i) depth false false (not (contains? #{\newline \return} c)) forms)
            quoted? (recur (inc i) depth (or escape? (not= c \")) (and (not escape?) (= c \\)) false forms)
            (= c \;) (recur (inc i) depth false false true forms)
            (= c \") (recur (inc i) depth true false false forms)
            (contains? #{\# \^ \\ \( \)} c) (check! false "Bootstrap disallowed EDN reader syntax")
            (contains? #{\{ \[} c)
            (do (check! (and (< depth 256) (< forms 20000)) "Bootstrap EDN depth/form limit")
                (recur (inc i) (inc depth) false false false (inc forms)))
            (contains? #{\} \]} c)
            (do (check! (pos? depth) "Bootstrap EDN closing delimiter")
                (recur (inc i) (dec depth) false false false forms))
            :else (recur (inc i) depth false false false forms)))))
    (with-open [r (PushbackReader. (StringReader. text))]
      (let [eof (Object.) options {:eof eof :readers {} :default (fn [& _] (check! false "Bootstrap EDN tag"))}
            value (edn/read options r)]
        (check! (and (not (identical? value eof)) (identical? eof (edn/read options r))) "Bootstrap EDN requires one value")
        value))))
(defn- walk-files [root]
  (with-open [paths (Files/walk (.toPath ^java.io.File root) (make-array FileVisitOption 0))]
    (let [paths (vec (iterator-seq (.iterator (.limit paths 10001))))]
      (check! (<= (count paths) 10000) "Bootstrap selected directory traversal bound")
      (doseq [path paths] (check! (not (Files/isSymbolicLink path)) "Bootstrap selected directory contains symbolic link"))
      (set (for [path paths :when (Files/isRegularFile path (make-array LinkOption 0))]
             (str (.relativize (.toPath ^java.io.File root) path)))))))
(defn- consumer-identity [rows]
  (sha (.getBytes (str "ansatz-restored-runtime-consumer/1\n"
                       (apply str (for [{:keys [id kind sha256]} (sort-by :id rows)]
                                    (str id "\t" (name kind) "\t" sha256 "\n")))) StandardCharsets/UTF_8)))
(defn- aot-id [id]
  (when-let [n (cond (str/ends-with? id ".clj") 4 (str/ends-with? id ".cljc") 5)]
    (str (subs id 0 (- (count id) n)) "__init.class")))
(defn- selected-url! [loader id expected]
  (let [urls (vec (enumeration-seq (.getResources ^ClassLoader loader id)))]
    (check! (and (= 1 (count urls)) (= "file" (.getProtocol ^java.net.URL (first urls)))
                 (= expected (.getCanonicalFile (io/file (.toURI ^java.net.URL (first urls))))))
            "Bootstrap duplicate/mislocated selected resource")))

(def jvm-stages
  [:fresh-init :graph-helpers :panic :ordinary-helpers :typed-eio :cases-on :seal :helper-value
   :init-prefix :load-a :select-a :call-a :callback :load-b :select-b :call-b-a :dispose])

(defn- verify-jvm-result! [approved result]
  (exact! result #{:status :disposal-phase :stages :consumer-contract-sha256
                   :consumer-implementation-sha256 :compatibility-profile :backend :fuel
                   :compile-threshold :application-execution :measurements} "JVM slice result")
  (check! (and (= (:contract-sha256 approved) (:consumer-contract-sha256 result))
               (= (:implementation-sha256 approved) (:consumer-implementation-sha256 result))
               (= (:compatibility-profile approved) (:compatibility-profile result))
               (= :passed (:status result)) (= :disposed (:disposal-phase result))
               (= (:execution approved) (select-keys result [:backend :fuel :compile-threshold]))
               (= jvm-stages (:stages result))
               (= {:backend :jvm :fuel 500000000 :compile-threshold 1} (:application-execution result)))
          "Bootstrap JVM slice identity/stages/application execution mismatch")
  (let [measurements (:measurements result)]
    (exact! measurements #{:corpus :callback :phases} "JVM slice measurements")
    (check! (and (vector? (:corpus measurements)) (<= 1 (count (:corpus measurements)) 4)
                 (= {:loading-effects 0 :invocation-effects 1} (:callback measurements))
                 (vector? (:phases measurements)) (= jvm-stages (mapv :stage (:phases measurements))))
            "Bootstrap JVM slice measurements mismatch")))

(defn verify!
  "Authenticate complete selection before ANY project require/Class.forName.
   Returns captured text and a descriptor, never kernel admission/readiness."
  [root manifest-id expected-manifest expected-contract]
  (check! (and (sha? expected-manifest) (sha? expected-contract)) "Independent bootstrap pins required")
  (let [root (.getCanonicalFile (io/file root))
        manifest-bytes (bytes! (resolve-file root manifest-id) (* 4 1024 1024))
        _ (check! (= expected-manifest (sha manifest-bytes)) "Bootstrap external launch manifest digest mismatch")
        manifest (read-data manifest-bytes)
        _ (exact! manifest #{:schema :commit :source-root :class-root :dependencies :inventory
                             :direct-inputs :external-stores :contract-id :contract-sha256 :jdk :entrypoint :execution} "launch manifest")
        jvm? (= "ansatz-coherent-launch/2" (:schema manifest))
        _ (check! (and (or jvm? (= "ansatz-coherent-launch/1" (:schema manifest)))
                       (re-matches #"[0-9a-f]{40}" (:commit manifest))
                       (= expected-contract (:contract-sha256 manifest))) "Bootstrap fixed manifest identity mismatch")
        _ (exact! (:execution manifest) #{:backend :fuel :compile-threshold} "execution policy")
        _ (check! (= {:backend :mutable :fuel 500000000 :compile-threshold 1} (:execution manifest))
                  "This reviewed restore/controller cohort requires explicit mutable/500M/threshold1 policy")
        contract-bytes (bytes! (resolve-file root (:contract-id manifest)) (* 4 1024 1024))
        _ (check! (= expected-contract (sha contract-bytes)) "Bootstrap external contract digest mismatch")
        contract (read-data contract-bytes)
        _ (check! (= [(:schema contract) (:profile contract)]
                    (if jvm?
                      ["ansatz-coherent-jvm-application-contract/1" "ansatz-producer50f-coherent-jvm-application-consumer/1"]
                      ["ansatz-coherent-frontend-contract/1" "ansatz-producer50f-coherent-frontend-consumer/1"]))
                  "Bootstrap launch/contract profile mismatch")
        inventory (:inventory manifest)
        _ (check! (and (vector? inventory) (<= 1 (count inventory) 1000)
                       (= (count inventory) (count (set (map :id inventory))))
                       (= inventory (:inventory contract))) "Bootstrap exact contract inventory mismatch")
        source-root (resolve-file root (:source-root manifest)) class-root (resolve-file root (:class-root manifest))
        deps (:dependencies manifest) direct (:direct-inputs manifest)
        external (external-store! (:external-stores manifest))
        _ (check! (not-any? #(= "producer/declaration-index" (:id %)) direct) "Bootstrap external CAS ID duplicated in direct inputs")
        output-root (no-symlink-ancestors! (io/file root "run-output"))
        provider-root (no-symlink-ancestors! (io/file output-root "provider"))
        _ (check! (and (not (Files/exists (.toPath output-root) (into-array LinkOption [LinkOption/NOFOLLOW_LINKS])))
                       (not (Files/exists (.toPath provider-root) (into-array LinkOption [LinkOption/NOFOLLOW_LINKS]))))
                  "Bootstrap new output/provider paths required before any creation")
        _ (check! (and (vector? deps) (<= 1 (count deps) 16) (vector? direct) (<= (count direct) 10000))
                  "Bootstrap dependency/direct-input bounds")
        _ (doseq [rows [deps direct]]
            (check! (= (count rows) (count (set (map :id rows)))) "Bootstrap duplicate input identity")
            (doseq [row rows]
              (exact! row #{:id :path :sha256} "direct/dependency row")
              (relative! (:id row)) (relative! (:path row))
              (check! (sha? (:sha256 row)) "Bootstrap invalid file digest")))
        dependency-files (mapv #(resolve-file root (:path %)) deps)
        expected-cp (conj dependency-files source-root class-root)
        actual-cp (mapv #(.getCanonicalFile (io/file %))
                        (str/split (System/getProperty "java.class.path") (re-pattern (java.util.regex.Pattern/quote java.io.File/pathSeparator))))
        _ (check! (= expected-cp actual-cp)
                  "Bootstrap unexpected/missing/duplicate classpath root")
        _ (doseq [row (concat deps direct)]
            (check! (= (:sha256 row) (file-sha (resolve-file root (:path row)))) "Bootstrap direct/dependency bytes drift"))
        _ (doseq [name ["JAVA_TOOL_OPTIONS" "JDK_JAVA_OPTIONS" "_JAVA_OPTIONS"]]
            (check! (nil? (System/getenv name)) "Bootstrap unreviewed JVM option injection"))
        _ (doseq [option (.getInputArguments (java.lang.management.ManagementFactory/getRuntimeMXBean))]
            (check! (not (or (str/starts-with? option "-javaagent") (str/starts-with? option "-agentlib")
                             (str/starts-with? option "-agentpath") (str/starts-with? option "-Xbootclasspath")))
                    "Bootstrap unreviewed instrumentation/bootstrap classpath"))
        _ (exact! (:jdk manifest) #{:runtime-version :java-sha256 :release-sha256 :libjvm-sha256 :modules-sha256} "JDK identity")
        java-home (.getCanonicalFile (io/file (System/getProperty "java.home")))
        _ (check! (and (= (get-in manifest [:jdk :runtime-version]) (System/getProperty "java.runtime.version"))
                       (= (get-in manifest [:jdk :java-sha256]) (file-sha (io/file java-home "bin/java")))
                       (= (get-in manifest [:jdk :release-sha256]) (file-sha (io/file java-home "release")))
                       (= (get-in manifest [:jdk :libjvm-sha256]) (file-sha (io/file java-home "lib/server/libjvm.so")))
                       (= (get-in manifest [:jdk :modules-sha256]) (file-sha (io/file java-home "lib/modules"))))
                  "Bootstrap JDK runtime identity mismatch")
        source-ids (set (for [{:keys [id kind]} inventory :when (contains? #{:host-source :host-resource} kind)] id))
        class-ids (set (for [{:keys [id kind]} inventory :when (contains? #{:kernel-class :runtime-class} kind)] id))
        _ (check! (and (seq class-ids) (= source-ids (walk-files source-root)) (= class-ids (walk-files class-root)))
                  "Bootstrap extra/missing selected source/class file")
        loader (clojure.lang.RT/baseLoader)
        aot-ids (set (keep aot-id source-ids))
        project-prefixes (set (map #(str (first (str/split % #"/")) "/")
                                  (filter #(or (str/ends-with? % ".clj") (str/ends-with? % ".cljc")) source-ids)))
        _ (doseq [jar dependency-files]
            (with-open [archive (JarFile. jar)]
              (let [implicit (some-> archive .getManifest .getMainAttributes (.getValue "Class-Path"))]
                (check! (or (nil? implicit) (str/blank? implicit)) "Bootstrap dependency JAR Manifest Class-Path is forbidden"))
              (let [entries (vec (take 100001 (enumeration-seq (.entries archive))))]
                (check! (<= (count entries) 100000) "Bootstrap dependency JAR entry bound")
                (doseq [entry entries :let [raw-id (.getName ^java.util.jar.JarEntry entry)
                                        id (str/replace raw-id #"^META-INF/versions/[0-9]+/" "")]]
                  (check! (not (or (contains? source-ids id) (contains? class-ids id) (contains? aot-ids id)
                                   (and (some #(str/starts-with? id %) project-prefixes)
                                        (or (str/ends-with? id ".clj") (str/ends-with? id ".cljc") (str/ends-with? id ".class")))))
                          "Bootstrap project source/class/AOT provider in dependency JAR")))))
        _ (doseq [{:keys [id kind sha256] :as row} inventory]
            (exact! row #{:id :kind :sha256} "selected inventory row")
            (relative! id) (check! (sha? sha256) "Bootstrap selected hash shape")
            (check! (contains? #{:host-source :host-resource :kernel-class :runtime-class} kind) "Bootstrap selected role")
            (let [base (if (contains? #{:kernel-class :runtime-class} kind) class-root source-root)
                  file (resolve-file base id)]
              (check! (= sha256 (file-sha file)) "Bootstrap selected source/class bytes drift")
              (when-not (or (str/starts-with? id "src-java/") (str/starts-with? id "java/"))
                (selected-url! loader id file)))
            (when-let [aot (aot-id id)]
              (check! (empty? (enumeration-seq (.getResources ^ClassLoader loader aot))) "Bootstrap .clj/.cljc AOT shadow")))
        digest (consumer-identity inventory)
        _ (check! (= digest (:implementation-sha256 contract)) "Bootstrap consumer implementation identity mismatch")
        entry (:entrypoint manifest)
        _ (check! (and (string? entry) (re-matches #"[A-Za-z0-9_.!?*-]+/[A-Za-z0-9_!?*-]+" entry))
                  "Bootstrap entrypoint shape")
        [namespace operation] (str/split entry #"/" 2)
        _ (check! (or (not jvm?)
                       (and (= namespace "prototype.coherent-jvm-slice") (contains? #{"construct!" "run!"} operation)))
                  "Bootstrap application entrypoint mismatch")
        entry-id (str (str/replace (str/replace namespace "." "/") "-" "_") ".clj")
        approved (filter #(and (= entry-id (:id %)) (some #{entry} (:entrypoints %))) (get-in contract [:composition :controllers]))
        _ (check! (and (= 1 (count approved)) (contains? source-ids entry-id)
                       (= :host-source (:kind (first (filter #(= entry-id (:id %)) inventory)))))
                  "Bootstrap entrypoint namespace/source ID not selected and approved by actual contract")
        _ (doseq [space (all-ns) :let [n (str (ns-name space))]]
            (check! (not (or (str/starts-with? n "ansatz.") (str/starts-with? n "prototype.") (= namespace n)))
                    "Bootstrap project namespace loaded before selection authentication"))]
    {:manifest manifest :execution (:execution manifest) :contract-source (utf8 contract-bytes) :contract-sha256 expected-contract
     :compatibility-profile (:profile contract)
     :inventory inventory :implementation-sha256 digest :entrypoint [namespace operation]
     :output-root output-root
     :resolve-consumer-source
     (fn [id]
       (let [row (first (filter #(= id (:id %)) inventory))
             _ (check! row "Bootstrap unlisted consumer input requested")
             base (if (contains? #{:kernel-class :runtime-class} (:kind row)) class-root source-root)
             file (resolve-file base id)]
         (check! (= (:sha256 row) (file-sha file)) "Bootstrap selected input drift at use") file))
     :resolve-input
     (fn [id]
       (if (= id "producer/declaration-index")
         (let [file (no-symlink-ancestors! (:index external))]
           (check! (and (= (:root external) (.getParentFile (.getParentFile (.getCanonicalFile file))))
                        (= (:sha256 external) (file-sha file))) "Bootstrap external CAS index drift at use") file)
         (let [row (first (filter #(= id (:id %)) direct))]
           (check! row "Bootstrap undeclared direct input requested")
           (let [file (resolve-file root (:path row))]
             (check! (= (:sha256 row) (file-sha file)) "Bootstrap direct input drift at use") file))))}))

(let [[root manifest expected-manifest expected-contract & extra] *command-line-args*]
  (check! (and root manifest expected-manifest expected-contract (empty? extra)) "Exact bootstrap arguments required")
  (let [approved (verify! root manifest expected-manifest expected-contract)
        [namespace operation] (:entrypoint approved)]
    ;; The only project load follows full selection verification. Entrypoint
    ;; gets fresh attestation plus captured contract, never a candidate digest.
    (require (symbol namespace))
    (let [entry (ns-resolve (symbol namespace) (symbol operation))]
      (check! (and entry (not (:private (meta entry))) (fn? @entry)) "Bootstrap approved entrypoint unavailable")
      (let [result (entry approved)]
        (if (= "construct!" operation)
          (do
            (check! (and (= #{:status :consumer-contract-sha256 :consumer-implementation-sha256 :compatibility-profile
                              :native-resources-acquired :guest-executed :strictly-checked? :backend :fuel :compile-threshold} (set (keys result)))
                         (= (:execution approved) (select-keys result [:backend :fuel :compile-threshold]))
                         (= :constructed (:status result))
                         (= (:compatibility-profile approved) (:compatibility-profile result))
                         (= expected-contract (:consumer-contract-sha256 result))
                         (= (:implementation-sha256 approved) (:consumer-implementation-sha256 result))
                         (false? (:native-resources-acquired result)) (false? (:guest-executed result))
                         (false? (:strictly-checked? result))) "Bootstrap constructor returned wrong/unbounded stage")
            (println (pr-str result)) (flush))
          (do
            (when (= "ansatz-producer50f-coherent-jvm-application-consumer/1" (:compatibility-profile approved))
              (verify-jvm-result! approved result))
            (check! (and (= :passed (:status result)) (= :disposed (:disposal-phase result))
                         (= (:execution approved) (select-keys result [:backend :fuel :compile-threshold])))
                    "Bootstrap campaign did not complete all stages and disposal")
            (println (pr-str (select-keys result [:status :consumer-contract-sha256 :disposal-phase :stages :backend :fuel :compile-threshold]))) (flush)))))))
