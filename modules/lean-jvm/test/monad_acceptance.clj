;; Load in a fresh namespace in a retained packaged-SDK REPL. Loading this file
;; only defines helpers; it does not start Lean/JVM/native processes or projects.
(require '[ansatz.lean.jvm :as lean] '[clojure.java.io :as io]
         '[clojure.edn :as edn] '[clojure.string :as str])
(import '[java.util.concurrent TimeUnit] '[ansatz.lean.jvm LeanException])

(def entries
  ["readerStateExcept" "stateRollback" "stRefs" "estFinally" "exceptTFinally"
   "baseIORunner" "eioRunner" "stateRefRunner" "stateRefDiscard"
   "ioCatchFinally" "retainedRead" "retainedBump" "uncaughtUserError" "legacyUserError" "otherIOError"])

;; Expectations come from pinned source semantics, not claimed native receipts.
;; [id entry arguments expected-value io?]
(def cases
  (vec
    (concat
      [["reader-ok" "readerStateExcept" [3 10 false] [{:ok 13} 13] false]
       ["reader-error" "readerStateExcept" [3 10 true] [{:error "body"} 13] false]
       ["state-rollback" "stateRollback" [10] {:ok [11 11]} false]
       ["st-refs" "stRefs" [10] [10 [15 true]] false]]
      (mapcat (fn [[id body cleanup expected]]
                [[(str "est-" id) "estFinally" [body cleanup] expected false]
                 [(str "exceptT-" id) "exceptTFinally" [body cleanup] expected false]])
              [["ok" false false {:ok [7 {:some 7}]}]
               ["body" true false {:error "body"}]
               ["cleanup" false true {:error "cleanup"}]
               ["both" true true {:error "cleanup"}]])
      [["baseio" "baseIORunner" [10] [10 15] true]
       ["eio-ok" "eioRunner" [false] {:ok 23} true]
       ["eio-error" "eioRunner" [true] {:error "typed"} true]
       ["state-ref" "stateRefRunner" [3 10] {:ok [123 123]} true]
       ["state-ref-discard" "stateRefDiscard" [10] 15 true]
       ["io-catch-finally" "ioCatchFinally" [10] [21 121 1121] true]
       ["retained-initial" "retainedRead" [] 40 true]
       ["retained-plus2" "retainedBump" [2] 42 true]
       ["retained-plus3" "retainedBump" [3] 45 true]
       ["retained-read" "retainedRead" [] 45 true]])))

(defn demand! [ok message data]
  (when-not ok (throw (ex-info message data))))

(defn open-project!
  "Caller supplies its retained runtime, compiler cohort, and fixture directory.
   Close returned project explicitly. Compilation/load is distinct from native!."
  [runtime compiler source-directory]
  (lean/load-project runtime source-directory
    {:compiler compiler :root-module "Main" :entries entries}))

(defn check-project!
  "Run once on a freshly loaded project. Retains each handle and exercises it
   repeatedly; does not close caller-owned runtime/project. Returns observed rows."
  [project]
  (let [handles (into {} (map (fn [entry] [entry (lean/function project entry)]) entries))
        invoke (fn [entry args io?]
                 (let [result (apply (get handles entry) args)]
                   (when io?
                     (demand! (= ["" ""] [(:stdout result) (:stderr result)])
                       "Unexpected guest output" {:entry entry :result result}))
                   (if io? (:value result) result)))
        rows (mapv (fn [[id entry args expected io?]]
                     (let [actual (invoke entry args io?)]
                       (demand! (= expected actual) "Source expectation differs"
                         {:id id :expected expected :actual actual})
                       [id actual])) cases)]
    ;; Identical retained pure/IO handles are reusable, and fresh local refs do
    ;; not perturb the independent initialized global cell.
    (dotimes [_ 3]
      (demand! (= [10 [15 true]] (invoke "stRefs" [10] false)) "Repeated ST handle" {})
      (demand! (= [10 15] (invoke "baseIORunner" [10] true)) "Repeated BaseIO handle" {})
      (demand! (= 45 (invoke "retainedRead" [] true)) "Retained global changed" {}))
    {:status :source-pass :rows rows :retained-repeat-checks 9}))

(defn native!
  "Explicit independent official Lean --run oracle. Never called on file load.
   Uses a fresh output directory, writes compile/run receipts, and returns native
   rows. This is the official executable's --run route, not C-backend evidence."
  [sysroot source-directory output-directory]
  (let [source (.getCanonicalFile (io/file source-directory))
        output (.getCanonicalFile (io/file output-directory))
        executable (.getCanonicalPath (io/file sysroot "bin/lean"))]
    (demand! (not (.exists output)) "Use a fresh native receipt directory" {:path (str output)})
    (demand! (.mkdirs output) "Cannot create receipt directory" {:path (str output)})
    (letfn [(run! [stage command]
              (let [stdout (io/file output (str stage ".stdout"))
                    stderr (io/file output (str stage ".stderr"))
                    builder (doto (ProcessBuilder. ^java.util.List command)
                              (.directory source) (.redirectOutput stdout) (.redirectError stderr))
                    _ (.put (.environment builder) "LEAN_PATH" (.getPath output))
                    process (.start builder)]
                (when-not (.waitFor process 60 TimeUnit/SECONDS)
                  (.destroyForcibly process)
                  (throw (ex-info "Native oracle timeout" {:stage stage})))
                (let [receipt {:stage stage :command command :exit (.exitValue process)
                               :stdout (.getPath stdout) :stderr (.getPath stderr)}]
                  (spit (io/file output (str stage ".edn")) (pr-str receipt))
                  (demand! (zero? (:exit receipt)) "Native stage failed" receipt)
                  (demand! (str/blank? (slurp stderr)) "Native stage emitted stderr" receipt)
                  stdout)))]
      ;; Preparation gets its own receipt; never infer oracle success from it.
      (run! "compile" [executable "-j1" "-M512" "-o"
                       (.getPath (io/file output "Main.olean")) "Main.lean"])
      (let [stdout (run! "oracle" [executable "-j1" "-M512" "--run" "NativeOracle.lean"])]
        (mapv (fn [line]
                (let [[id value] (str/split line #"\t" 2)]
                  (demand! (and id value) "Malformed native row" {:line line})
                  [id (edn/read-string value)]))
              (str/split-lines (slurp stdout)))))))

(defn compare-native!
  "Compare independent oracle observations with source expectations AND JVM rows.
   Passing source checks without calling this is not native differential evidence."
  [source-result native-rows]
  (let [expected (mapv (fn [[id _ _ value _]] [id value]) cases)]
    (demand! (= expected native-rows) "Native oracle differs from pinned-source expectations"
      {:expected expected :native native-rows})
    (demand! (= (:rows source-result) native-rows) "Native/JVM differential differs"
      {:jvm (:rows source-result) :native native-rows})
    {:status :native-differential-pass :native-cases (count native-rows)
     :retained-repeat-checks (:retained-repeat-checks source-result)}))

(defn check-error!
  "Invoke once on a fresh Project; failed guest calls are terminal. The caller
   closes the Project. Assert real public projection, not model-only evidence."
  [project entry arguments expected-details]
  (try
    (apply lean/call project entry arguments)
    (throw (AssertionError. "Expected GuestIOError"))
    (catch LeanException error
      (demand! (= "GuestIOError" (.code error)) "Wrong public error code" {:code (.code error)})
      (demand! (= expected-details (.details error)) "Lost public error details"
        {:expected expected-details :actual (.details error)})
      (demand! (nil? (.getCause error)) "Guest owner leaked through cause" {})
      (try (.put (.details error) "owner" (Object.))
           (throw (AssertionError. "Mutable public error details"))
           (catch UnsupportedOperationException _))
      {:status :error-pass :details (.details error)})))
