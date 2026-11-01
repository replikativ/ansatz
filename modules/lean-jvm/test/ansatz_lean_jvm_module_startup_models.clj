(ns ansatz-lean-jvm-module-startup-models
  (:require [clojure.test :refer [deftest is run-tests]]
            [ansatz.lean.jvm.startup :as startup]))
(def n ["str" ["anonymous"] "Module"])
(def a [["str" ["anonymous"] "global"] ["str" ["anonymous"] "action"]])
(def b [["str" ["anonymous"] "global2"] ["str" ["anonymous"] "action2"]])
(defn module-row [first-list ir-list phases in-server]
  (let [sequence (into first-list (remove (set first-list) ir-list))
        init-runtime (or in-server (not= phases "runtime"))]
    {"index" 0 "effectiveImport" {"import" {"module" n} "irPhases" phases}
     "initRuntime" init-runtime "regularModuleEntries" first-list "regularIREntries" ir-list
     "builtinModuleEntries" [] "builtinIREntries" [] "regularSequence" sequence
     "phaseDecisions" (mapv (fn [i pair] {"ordinal" i "pair" pair "declarationIRPhases" "all" "selected" true})
                                (range) sequence)}))
(defn capture [modules]
  {"schema" "lean-native-startup-evidence/1" "leanCommit" "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
   "profile" "legacy-private-ordinary/1" "actualHeader" {"isModule" false "globalLevel" "private" "inServer" false "imports" []}
   "request" {"requestedImports" []} "requestedImports" []
   "unsupportedActivationReasons" [] "dynamicAPSites" 0 "modules" modules
   "moduleOrder" (mapv #(get-in % ["effectiveImport" "import" "module"]) modules)
   "declarations" [] "selectedActions" []})
(deftest preserve-first-list-occurrences-and-ir-only-order
  (let [plan (startup/module-plan (module-row [a a] [a b b] "all" false) false)]
    (is (= [a a b b] (mapv :pair plan)))
    (is (= [0 1 2 3] (mapv :ordinal plan)))
    (is (every? :selected plan))))
(deftest phase-skipping-and-server-runtime
  (let [row (-> (module-row [a] [] "runtime" false)
                (assoc-in ["phaseDecisions" 0 "declarationIRPhases"] "runtime")
                (assoc-in ["phaseDecisions" 0 "selected"] false))]
    (is (false? (:selected (first (startup/module-plan row false)))))
    (is (true? (:selected (first (startup/module-plan
                                  (-> row (assoc "initRuntime" true)
                                      (assoc-in ["phaseDecisions" 0 "selected"] true)) true)))))))
(deftest phase-and-sequence-tampering-refused
  (let [row (module-row [a] [] "all" false)]
    (doseq [bad [(assoc row "regularSequence" []) (assoc row "initRuntime" false)
                 (assoc-in row ["phaseDecisions" 0 "selected"] false)
                 (assoc-in row ["phaseDecisions" 0 "ordinal"] 1)
                 (assoc-in row ["effectiveImport" "irPhases"] "unknown")]]
      (is (thrown? Exception (startup/module-plan bad false))))))
(deftest builtin-and-anonymous-actions-are-not-dropped
  (let [row (module-row [a] [] "all" false)]
    (doseq [key ["builtinModuleEntries" "builtinIREntries"]]
      (is (thrown? Exception (startup/module-plan (assoc row key [a]) false)))))
  (is (thrown? Exception (startup/module-plan (module-row [[(first a) ["anonymous"]]] [] "all" false) false))))
(deftest bounded-collection-check-before-realization
  (let [realized (atom 0) row (assoc (module-row [] [] "all" false)
                                   "regularModuleEntries" (map #(do (swap! realized inc) %) (repeat a)))]
    (is (thrown? Exception (startup/module-plan row false)))
    (is (zero? @realized)))
  (is (thrown? Exception (startup/module-plan (assoc (module-row [] [] "all" false)
                                                    "regularIREntries" (vec (repeat 129 a))) false))))
(deftest empty-module-still-produces-a-ledger-entry
  (let [plan (startup/validate-capture (capture [(module-row [] [] "all" false)]))]
    (is (= 1 (count (:modules plan))))
    (is (= {:index 0 :name n :actions []} (first (:modules plan)))))
  (is (thrown? Exception (startup/validate-capture
                          (capture [(module-row [] [] "all" false) (assoc (module-row [] [] "all" false) "index" 1)])))))
(deftest wrong-order-header-and-actions-refused
  (let [base (capture [(module-row [] [] "all" false)])]
    (doseq [bad [(assoc base "moduleOrder" []) (assoc-in base ["modules" 0 "index"] 1)
                 (assoc-in base ["actualHeader" "imports"] [{}])
                 (assoc base "selectedActions" [{}])]]
      (is (thrown? Exception (startup/validate-capture bad))))))
(deftest repeated-selected-global-refused-before-evidence-or-engine
  (is (thrown-with-msg? Exception #"Repeated selected global"
                        (startup/validate-capture
                          (assoc (capture [(module-row [a a] [] "all" false)])
                                 "selectedActions" [{"moduleIndex" 0 "module" n "sequenceOrdinal" 0 "pair" a}
                                                    {"moduleIndex" 0 "module" n "sequenceOrdinal" 1 "pair" a}])))))
(deftest invalid-budget-refused-before-borrow-or-state
  (let [borrowed (atom 0)]
    (with-redefs-fn {(ns-resolve 'ansatz.lean.jvm.startup 'live-cell!)
                    (fn [_] (swap! borrowed inc) (throw (ex-info "Must not borrow" {})))}
      #(doseq [budget [0 -1 20001 1.5 nil]]
         (is (thrown-with-msg? Exception #"budget" (startup/poll! nil budget)))))
    (is (zero? @borrowed))))
(deftest cancellation-only-closes-known-empty-idle-custody
  (let [closeable (ns-resolve 'ansatz.lean.jvm.startup 'closeable-state?)
        empty-state {:status :cancelled :active nil :error-state nil :error-slot (object-array 1)}]
    (is (true? (closeable empty-state)))
    (is (false? (closeable (assoc empty-state :active {:disposition :running}))))
    (is (false? (closeable (assoc empty-state :error-slot (object-array [(Object.)])))))
    (is (false? (closeable (assoc empty-state :error-state :release-started))))
    (is (false? (closeable (assoc empty-state :status :host-failed))))
    (is (false? (closeable {:status :closed})))
    (is (true? (closeable (assoc empty-state :status :io-error :error-state :released))))))
(deftest independent-project-registry-access-is-serialized
  (let [registry (java.util.WeakHashMap.)
        put! (ns-resolve 'ansatz.lean.jvm.startup 'put-issued!)
        issued! (ns-resolve 'ansatz.lean.jvm.startup 'issued!)
        tokens (vec (repeatedly 16 #(Object.)))
        workers (mapv (fn [token]
                        (future
                          (let [cell (Object.)]
                            (dotimes [_ 40]
                              (put! registry token cell)
                              (when-not (identical? cell (issued! registry token Object))
                                (throw (ex-info "Foreign registry value" {}))))
                            true))) tokens)]
    (try
      (doseq [worker workers] (is (= true (deref worker 10000 :timeout))))
      (finally (doseq [worker workers] (future-cancel worker))))))
(deftest stream-growth-cannot-force-an-unbounded-read
  (let [read! (ns-resolve 'ansatz.lean.jvm.startup 'read-bounded!)]
    (with-open [input (java.io.ByteArrayInputStream. (byte-array 8))]
      (is (thrown? Exception (read! input 3)))
      (is (= 4 (.available input))))
    (with-open [input (java.io.ByteArrayInputStream. (byte-array [1 2 3]))]
      (is (= [1 2 3] (vec (read! input 3)))))))
(deftest capture-file-rejects-symlinks-and-nonregular-paths
  (let [read! (ns-resolve 'ansatz.lean.jvm.startup 'read-bytes!)
        attributes (make-array java.nio.file.attribute.FileAttribute 0)
        parent (java.nio.file.Paths/get "target" (into-array String ["module-startup-read-models"]))
        _ (java.nio.file.Files/createDirectories parent attributes)
        directory (java.nio.file.Files/createTempDirectory parent "bounded-" attributes)
        source (.resolve directory "capture") link (.resolve directory "link")]
    (try
      (java.nio.file.Files/write source (byte-array [1 2 3]) (make-array java.nio.file.OpenOption 0))
      (java.nio.file.Files/createSymbolicLink link (.getFileName source) attributes)
      (is (= [1 2 3] (vec (read! (.toFile source) 3))))
      (is (thrown? Exception (read! (.toFile source) 2)))
      (is (thrown? Exception (read! (.toFile link) 3)))
      (is (thrown? Exception (read! (.toFile directory) 3)))
      (finally (java.nio.file.Files/deleteIfExists link)
               (java.nio.file.Files/deleteIfExists source)
               (java.nio.file.Files/deleteIfExists directory)))))
(defn check! [] (run-tests 'ansatz-lean-jvm-module-startup-models))
