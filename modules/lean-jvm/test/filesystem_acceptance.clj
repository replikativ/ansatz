;; Explicit public Feline campaigns. Load in a fresh retained-REPL namespace;
;; loading defines functions only, and starts no process, runtime, or Project.
(require '[ansatz.lean.jvm :as lean] '[ansatz.lean.jvm.project :as project]
         '[ansatz.lean.jvm.startup :as startup] '[ansatz.lean.jvm.compiler.evidence :as evidence]
         '[clojure.java.io :as io] '[clojure.string :as str])
(import '[ansatz.lean.jvm HostServices ReadOnlyFiles LeanException]
        '[java.nio.file Path Files LinkOption StandardOpenOption CopyOption]
        '[java.nio.file.attribute FileAttribute] '[java.nio.charset StandardCharsets]
        '[java.security MessageDigest] '[java.util.concurrent TimeUnit])

(def source-pin "0abeea545d560a324e2561f7210fbd6ed154fa02")
(def source-hashes {"Main.lean" "ea4d0e049dc32593d90c0413531f9b815554359d27ad8869d919e791f81a5d1e"
                    "FelineLib.lean" "cbce9a0420c395f1f1aadebf06bd3ba35a1b5cf8000d36a664d69ef0b278a8b0"})
(defn demand! [ok facts] (when-not ok (throw (ex-info "Filesystem acceptance differs" facts))))
(defn path [value] (.toPath (.getCanonicalFile (io/file (str value)))))
(defn utf8 [text] (.getBytes ^String text StandardCharsets/UTF_8))
(def binary [0 -64 -128 -16 -97 -104 -128 10])
(def fixture-data {"first.txt" (vec (utf8 "one\nλ\n")) "second.txt" (vec (utf8 "two\n"))
                   "empty.txt" [] "binary.dat" binary})
(defn cases []
  (let [first (fixture-data "first.txt") second (fixture-data "second.txt")]
    [{:label "stdin-default" :args [] :stdin (vec (utf8 "hello\nλ\n")) :exit 0 :stdout (vec (utf8 "hello\nλ\n")) :stderr []}
     {:label "stdin-explicit" :args ["-"] :stdin binary :exit 0 :stdout binary :stderr []}
     {:label "two-files" :args ["first.txt" "second.txt"] :stdin [] :exit 0 :stdout (into first second) :stderr []}
     {:label "file-stdin" :args ["first.txt" "-" "second.txt"] :stdin (vec (utf8 "middle\n")) :exit 0
      :stdout (into (into first (vec (utf8 "middle\n"))) second) :stderr []}
     {:label "missing-then-file" :args ["missing.txt" "first.txt"] :stdin [] :exit 1 :stdout first
      :stderr (vec (utf8 "File not found: missing.txt\n"))}
     {:label "empty-file" :args ["empty.txt"] :stdin [] :exit 0 :stdout [] :stderr []}
     {:label "repeated-file" :args ["first.txt" "first.txt"] :stdin [] :exit 0 :stdout (into first first) :stderr []}
     {:label "binary-file" :args ["binary.dat"] :stdin [] :exit 0 :stdout binary :stderr []}]))
(defn canonical [row] (select-keys row [:label :exit :stdout :stderr]))
(defn fresh-directory! [value]
  (let [root (path value)]
    (demand! (Files/notExists root (into-array LinkOption [LinkOption/NOFOLLOW_LINKS])) {:reason :fresh-directory :path (str root)})
    (when-let [parent (.getParent root)] (Files/createDirectories parent (make-array FileAttribute 0)))
    (Files/createDirectory root (make-array FileAttribute 0)) root))
(defn fixtures!
  "Create the explicit immutable-namespace test input BEFORE opening any scope."
  [fresh-root]
  (let [root (fresh-directory! fresh-root)]
    (doseq [[name bytes] fixture-data]
      (Files/write (.resolve root name) (byte-array bytes)
        (into-array java.nio.file.OpenOption [StandardOpenOption/CREATE_NEW StandardOpenOption/WRITE])))
    (Files/createDirectory (.resolve root "directory") (make-array FileAttribute 0)) root))
(defn check-fixtures! [root]
  (doseq [[name bytes] fixture-data]
    (demand! (= bytes (vec (Files/readAllBytes (.resolve ^Path root name)))) {:reason :fixture-bytes :file name}))
  (demand! (Files/notExists (.resolve ^Path root "missing.txt") (make-array LinkOption 0)) {:reason :missing-fixture-exists})
  (demand! (Files/isDirectory (.resolve ^Path root "directory") (make-array LinkOption 0)) {:reason :missing-directory-fixture}))
(defn check-sources! [source]
  (doseq [[name expected] source-hashes]
    (let [bytes (Files/readAllBytes (.resolve ^Path source name))
          actual (apply str (map #(format "%02x" (bit-and 255 %)) (.digest (MessageDigest/getInstance "SHA-256") bytes)))]
      (demand! (= expected actual) {:reason :upstream-source-changed :file name :actual actual}))))
(defn services [root]
  (.build (.files (HostServices/builder) (ReadOnlyFiles/root (path root)))))
(defn options [compiler] {:compiler compiler :root-module "Main" :entries ["main"]})
(defn invoke! [project sample]
  (let [result (lean/call-with-options project "main" {:stdin-bytes (byte-array (:stdin sample))} (:args sample))
        row {:label (:label sample) :exit (:value result) :stdout (vec (:stdout-bytes result)) :stderr (vec (:stderr-bytes result))}]
    (demand! (= (canonical sample) row) {:expected (canonical sample) :actual row}) row))
(defn check-project!
  "Every sample has a reusable configured handle; direct call-with-options is
   checked too. Each invocation receives fresh finite stdin and file state."
  [project]
  (mapv (fn [sample]
          (let [handle (lean/function project "main" {:stdin-bytes (byte-array (:stdin sample))})]
            (dotimes [_ 2]
              (let [result (handle (:args sample))]
                (demand! (= [(:exit sample) (:stdout sample) (:stderr sample)]
                            [(:value result) (vec (:stdout-bytes result)) (vec (:stderr-bytes result))])
                  {:reason :retained-invocation :case (:label sample)})))
            (invoke! project sample))) (cases)))
(defn quarantine-count [] (count @(var-get #'project/quarantine)))

(defn source!
  "SUCCESS campaign only: source, cache reuse, and portable artifact loading
   under an actual HostServices root. Does not run native reference or failures!."
  [compiler source-directory new-artifact-path read-only-root]
  (let [source (path source-directory) root (path read-only-root) output (path new-artifact-path)
        observations (atom []) original evidence/build! before (quarantine-count)]
    (check-sources! source) (check-fixtures! root)
    (demand! (Files/notExists output (make-array LinkOption 0)) {:reason :fresh-artifact})
    (when-let [parent (.getParent output)] (Files/createDirectories parent (make-array FileAttribute 0)))
    (with-redefs [evidence/build!
                  (fn [compiler configuration evidence-options entries journal]
                    (let [receipt (original compiler configuration evidence-options entries journal)
                          payload (evidence/authenticated-build receipt)]
                      (swap! observations conj {:cache-key (:module-cache-key payload) :cache-hit (:cache-hit @journal)
                                                :row-count (count (:rows payload))}) receipt))]
      (with-open [runtime (lean/open (services root))]
        (let [first (with-open [project (lean/load-project runtime source (options compiler))] (check-project! project))
              cached (with-open [project (lean/load-project runtime source (options compiler))] (check-project! project))
              description (with-open [out (Files/newOutputStream output
                                             (into-array java.nio.file.OpenOption [StandardOpenOption/CREATE_NEW StandardOpenOption/WRITE]))]
                            (lean/prepare-project source (options compiler) out))
              artifact (with-open [in (Files/newInputStream output (make-array java.nio.file.OpenOption 0))
                                   project (lean/load-artifact runtime in (:manifest-sha256 description))]
                         (check-project! project))]
          (demand! (= 3 (count @observations)) {:reason :missing-source-build-stage :observations @observations})
          (demand! (= 1 (count (set (map :cache-key @observations)))) {:reason :cache-identity :observations @observations})
          (demand! (every? :cache-hit (rest @observations)) {:reason :cache-reuse :observations @observations})
          (demand! (= before (quarantine-count)) {:reason :unexpected-quarantine})
          {:status :filesystem-source-cache-artifact-pass :source-pin source-pin :artifact description :artifact-path (str output)
           :groups {:source first :cache cached :artifact artifact} :builds @observations})))))

(defn load-artifact! [runtime artifact manifest]
  (with-open [in (Files/newInputStream (path artifact) (make-array java.nio.file.OpenOption 0))]
    (lean/load-artifact runtime in manifest)))
(defn expect-code! [expected action]
  (try (action) (throw (AssertionError. (str "Expected " expected)))
       (catch LeanException failure
         (demand! (= expected (.code failure)) {:expected expected :actual (.code failure)}) expected)))
(defn failures!
  "FAILURE campaign, independent of native parity: missing service, stdout/read
   limits, and directory POLICY. Close each failed cell, retain a healthy peer,
   and assert no quarantine growth. Directory POLICY is deliberately NOT the
   native directory IO.Error behavior and is excluded from compare-native!."
  [artifact manifest read-only-root]
  (let [root (path read-only-root) before (quarantine-count) startup-calls (atom 0) original startup/open!]
    (check-fixtures! root)
    (with-redefs [startup/open! (fn [& args] (swap! startup-calls inc) (apply original args))]
      (with-open [runtime (lean/open)]
        (expect-code! "CapabilityMissing" #(load-artifact! runtime artifact manifest))))
    (demand! (zero? @startup-calls) {:reason :missing-service-entered-startup})
    (with-open [runtime (lean/open (services root)) good (load-artifact! runtime artifact manifest)]
      (let [sample (first (filter #(= "two-files" (:label %)) (cases)))]
        (invoke! good sample)
        (with-open [failed (load-artifact! runtime artifact manifest)]
          (expect-code! "ResourceLimit" #(lean/call-with-options failed "main"
                                           {:stdin-bytes (byte-array 0) :stdout-limit-bytes 2} ["first.txt"]))
          (.close failed) (.close failed))
        (invoke! good sample)
        (with-open [failed (load-artifact! runtime artifact manifest)]
          (expect-code! "FilesystemPolicy" #(lean/call-with-options failed "main" {:stdin-bytes (byte-array 0)} ["directory"]))
          (.close failed) (.close failed))
        (let [limited (.limits (ReadOnlyFiles/root root) 32 1 16777216 10000 4096)
              config (.build (.files (HostServices/builder) limited))]
          (with-open [limited-runtime (lean/open config) failed (load-artifact! limited-runtime artifact manifest)]
            (expect-code! "ResourceLimit" #(lean/call-with-options failed "main" {:stdin-bytes (byte-array 0)} ["first.txt"]))
            (.close failed) (.close failed)))
        (invoke! good sample)))
    (demand! (= before (quarantine-count)) {:reason :failure-quarantine})
    {:status :filesystem-failure-branches-pass :cases ["CapabilityMissing" "stdout ResourceLimit" "directory FilesystemPolicy" "read ResourceLimit"]
     :startup-calls-without-service @startup-calls :quarantine-growth 0}))

(defn native-headroom!
  "Linux memory preflight, including before compilation. Files.readString is
   intentional: procfs may report size=0, which makes slurp misleading here."
  []
  (let [text (Files/readString (Path/of "/proc/meminfo" (make-array String 0)))
        match (re-find #"(?m)^MemAvailable:\s+([0-9]+)\s+kB$" text)
        available (when match (Long/parseLong (second match)))]
    (demand! (and available (>= available (* 2 1024 1024)))
      {:code "NativePreflightResourceLimit" :available-kib available :required-kib (* 2 1024 1024)})))
(defn native!
  "Independent official executable references. Copies the two pinned sources to
   a fresh receipt directory, compiles FelineLib ONCE, then runs eight raw-byte
   cases with explicit root as cwd. No directory-policy parity claim. CPU=60s,
   Lean M512, process wait=60s, and >=2GiB available-memory preflight per process."
  [sysroot source-directory fresh-output-directory read-only-root]
  (let [sysroot (path sysroot) source (path source-directory) root (path read-only-root)
        output (fresh-directory! fresh-output-directory) build (.resolve output "modules")]
    (check-sources! source) (check-fixtures! root)
    (Files/createDirectory build (make-array FileAttribute 0))
    (doseq [name (keys source-hashes)] (Files/copy (.resolve source name) (.resolve build name) (make-array CopyOption 0)))
    (letfn [(run! [label cwd arguments input]
              (native-headroom!)
              (let [in (.resolve output (str label ".stdin")) out (.resolve output (str label ".stdout"))
                    err (.resolve output (str label ".stderr"))
                    command (into ["/usr/bin/prlimit" "--cpu=60:60" "--core=0:0" "--"
                                   (str (.resolve sysroot "bin/lean")) "-j1" "-M512"] arguments)
                    _ (Files/write in (byte-array input) (make-array java.nio.file.OpenOption 0))
                    builder (doto (ProcessBuilder. ^java.util.List command)
                              (.directory (.toFile ^Path cwd)) (.redirectInput (.toFile in))
                              (.redirectOutput (.toFile out)) (.redirectError (.toFile err)))
                    environment (.environment builder)
                    _ (.put environment "LEAN_SYSROOT" (str sysroot))
                    _ (.put environment "LEAN_PATH" (str build java.io.File/pathSeparator (.resolve sysroot "lib/lean")))
                    start (System/nanoTime) process (.start builder)]
                (when-not (.waitFor process 60 TimeUnit/SECONDS)
                  (.destroyForcibly process) (throw (ex-info "Native filesystem reference timeout" {:case label})))
                (let [row {:label label :command command :exit (.exitValue process) :elapsed-ms (/ (- (System/nanoTime) start) 1e6)
                           :stdout (vec (Files/readAllBytes out)) :stderr (vec (Files/readAllBytes err))}]
                  (spit (.toFile (.resolve output (str label ".edn"))) (pr-str row)) row)))]
      (let [compiled (run! "compile" build ["-o" "FelineLib.olean" "FelineLib.lean"] [])]
        (demand! (and (zero? (:exit compiled)) (empty? (:stderr compiled))) {:reason :native-compilation :receipt compiled})
        (let [rows (mapv (fn [sample]
                           (let [row (run! (:label sample) root
                                       (into ["--run" (str (.resolve build "Main.lean"))] (:args sample)) (:stdin sample))]
                             (demand! (= (canonical sample) (canonical row)) {:reason :native-result :expected sample :receipt row}) row)) (cases))
              report {:status :filesystem-native-pass :source-pin source-pin :compile compiled :cases rows}]
          (spit (.toFile (.resolve output "native.edn")) (pr-str report)) report)))))

(defn compare-native! [source-result native-result]
  (demand! (= :filesystem-source-cache-artifact-pass (:status source-result)) {:reason :source-campaign-missing})
  (demand! (= :filesystem-native-pass (:status native-result)) {:reason :native-campaign-missing})
  (let [native (mapv canonical (:cases native-result)) expected (mapv canonical (cases))]
    (demand! (= #{:source :cache :artifact} (set (keys (:groups source-result)))) {:reason :missing-jvm-group})
    (demand! (= expected native) {:reason :native-expected :actual native})
    (doseq [[group rows] (:groups source-result)]
      (demand! (= native rows) {:reason :native-jvm-differential :group group :native native :jvm rows}))
    {:status :filesystem-native-source-cache-artifact-pass :cases (count native) :artifact (:artifact source-result)}))

(defn initializer-refusal!
  "Own generated negative fixture, not an upstream program. Native preparation
   reads an explicit existing file; the JVM must refuse the same operation while
   initializing, before its relative-path policy could hide that phase check."
  [compiler fresh-source-directory read-only-root]
  (let [root (path read-only-root) source (fresh-directory! fresh-source-directory)
        filename (str (.resolve root "first.txt"))
        program (str "initialize textFromFile : String ← do\n"
                     "  let handle ← IO.FS.Handle.mk (System.FilePath.mk " (pr-str filename) ") .read\n"
                     "  handle.getLine\n\ndef readInit : IO String := pure textFromFile\n")
        before (quarantine-count)]
    (check-fixtures! root)
    (spit (.toFile (.resolve source "Main.lean")) program)
    (with-open [runtime (lean/open (services root))]
      (try
        (with-open [loaded (lean/load-project runtime source {:compiler compiler :entries ["readInit"]})]
          (throw (AssertionError. "Filesystem initializer unexpectedly succeeded")))
        (catch LeanException failure
          (demand! (and (= "RuntimeBoundary" (.code failure))
                        (.contains (.getMessage failure) "invocation-only capability"))
                   {:reason :wrong-initializer-boundary :code (.code failure) :message (.getMessage failure)}))))
    (demand! (= before (quarantine-count)) {:reason :initializer-failure-quarantine})
    {:status :filesystem-initializer-refused :quarantine-growth 0 :native-preparation-effects :trusted-source-execution}))
