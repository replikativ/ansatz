(ns lake-acceptance
  "Optional actual-Lake acceptance, callable from a retained REPL. It operates
   only on a fresh copy of the authored fixture, never a user's workspace."
  (:refer-clojure :exclude [run!])
  (:require [ansatz.lean.jvm :as lean] [ansatz.lean.jvm.compiler.bundle :as bundle]
            [ansatz.lean.jvm.compiler.transport :as transport]
            [ansatz.lean.jvm.compiler.workspace :as workspace]
            [ansatz.lean.jvm.compiler.local :as local]
            [clojure.java.io :as io] [clojure.edn :as edn] [clojure.string :as str])
  (:import [java.nio.file Path Files StandardOpenOption OpenOption]
           [java.nio.file.attribute FileAttribute]
           [java.io ByteArrayInputStream ByteArrayOutputStream]
           [ansatz.lean.jvm LeanException]))

(defn- check! [value label] (when-not value (throw (ex-info "Lake acceptance failed" {:check label}))))
(defn- sha [file] (get (#'transport/file-record (.toPath (io/file file)) (* 64 1048576)) "sha256"))
(defn- native! [compiler-options directory label arguments]
  (let [{:keys [compiler]} (bundle/open! compiler-options)]
    (try
      (let [state (#'transport/issued compiler)
            logs (Files/createTempDirectory ^Path (:cache state) (str ".lake-acceptance-" label "-") (make-array FileAttribute 0))
            lake (str (.resolve ^Path (:sysroot state) "bin/lake"))
            execution (assoc state :working-directory (.toPath (io/file directory)) :diagnostics-executable lake)
            receipt (#'transport/run-process! execution (atom {:processes []}) logs label
                       (mapv #(case % :lake lake :lean (str (.resolve ^Path (:sysroot state) "bin/lean")) %) arguments)
                       (#'transport/environment state (str (.resolve ^Path (:sysroot state) "lib/lean"))))]
        (slurp (.toFile (.resolve logs (get receipt "stdout")))) )
      (finally (transport/close! compiler)))))
(defn- prepare [directory options]
  (let [output (ByteArrayOutputStream.)
        description (lean/prepare-project directory options output)]
    {:bytes (.toByteArray output) :description description}))
(defn- loaded [runtime prepared bindings]
  (lean/load-artifact runtime (ByteArrayInputStream. (:bytes prepared))
                      (get-in prepared [:description :manifest-sha256]) bindings))
(defn- rejected! [f codes]
  (try (f) (check! false :expected-refusal)
       (catch LeanException failure
         (check! (contains? codes (.code failure)) [:refusal-code (.code failure)]) (.code failure))
       (catch IllegalArgumentException failure
         ;; Clojure tagged-view normalization rejects incompatible nominal values
         ;; before entering the Java invocation boundary.
         (check! (contains? codes "InvalidArgument") :clojure-argument-refusal) "InvalidArgument")))

(defn run!
  "CONFIG contains :compiler and optional :fixture-root. Leaves owned evidence
   under that compiler cache and returns a compact, reviewable report."
  [{:keys [compiler fixture-root] :or {fixture-root "test/fixtures/lake-workspace"}}]
  (let [cache (io/file (:cache compiler)) _ (.mkdirs cache)
        directory (.toFile (Files/createTempDirectory (.toPath cache) "lake-acceptance-" (make-array FileAttribute 0)))
        _ (doseq [relative ["app/lakefile.toml" "app/lake-manifest.json" "app/lean-toolchain" "app/App.lean" "app/Oracle.lean"
                            "domain/lakefile.toml" "domain/lean-toolchain" "domain/Domain.lean"]]
            (let [target (io/file directory relative)] (io/make-parents target) (io/copy (io/file fixture-root relative) target)))
        app (io/file directory "app") source (io/file directory "domain/Domain.lean")
        product (io/file directory "domain/.lake/build/lib/lean/Domain.olean")
        options {:compiler compiler :root-module "App" :built-lake-workspace? true
                 :entries ["App.calculate" "App.account" "Domain.credit"]}
        java-options (lean/project-options options)
        _ (native! (.compiler java-options) app "build-original" [:lake "--no-cache" "build"])
        oracle (native! (.compiler java-options) app "native-oracle" [:lake "--no-build" "--quiet" "env" :lean "-M384" "-j1" "--run" "Oracle.lean"])
        _ (check! (= "42\n42,true\n" oracle) :native-reference)
        first (prepare app options)
        original-artifact (io/file directory "original.leanjvm")
        _ (with-open [output (io/output-stream original-artifact)] (.write output ^bytes (:bytes first)))
        frozen-product (sha product)
        callback-count (atom 0)
        registrations {"Domain.credit" {:implementation-id "credit/1" :fn
                          (fn [account amount] (swap! callback-count inc) (update-in account [:lean/fields 0] + amount))}}]
    (with-open [runtime (lean/open)]
      (let [detached
            (with-open [project (loaded runtime first {})]
              (check! (= 42 (lean/call project "App.calculate" 32)) :dependency-initialization)
              (let [account (lean/call project "App.account" 35)]
                (check! (= [42 true] (:lean/fields account)) :dependency-datatype) account))]
        (with-open [project (lean/load-project runtime app (assoc options :entries ["App.calculate" "App.account"]) registrations)]
          (check! (= 42 (lean/call project "App.calculate" 32)) :cross-package-source-host-binding)
          (check! (pos? @callback-count) :host-binding-used))
        ;; An edited source must not trigger an implicit build, or silently load
        ;; a stale dependency product. Previously prepared artifacts stay stable.
        (let [original (slurp source)]
          (spit source (str/replace original "pure 3" "pure 5"))
          (rejected! #(prepare app options) #{"NativeCompilationFailed"})
          (check! (= frozen-product (sha product)) :no-implicit-rebuild)
          (with-open [project (loaded runtime first {})]
            (check! (= 42 (lean/call project "App.calculate" 32)) :artifact-independent-of-workspace))
          (native! (.compiler java-options) app "build-edited" [:lake "--no-cache" "build"])
          (let [edited (prepare app options)]
            (check! (not= (get-in first [:description :manifest-sha256]) (get-in edited [:description :manifest-sha256])) :dependency-cache-invalidation)
            (with-open [project (loaded runtime edited {})]
              (check! (= 44 (lean/call project "App.calculate" 32)) :rebuilt-dependency-result)
              (rejected! #(lean/call project "Domain.credit" detached 1) #{"InvalidArgument" "UnsupportedArgumentType"})
              (check! (= 44 (lean/call project "App.calculate" 32)) :nominal-refusal-preserves-project))))
        ;; A missing product remains missing after the no-build path refuses it.
        (let [backup (io/file directory "Domain.olean.backup")]
          (Files/move (.toPath product) (.toPath backup) (make-array java.nio.file.CopyOption 0))
          (try
            (rejected! #(prepare app options) #{"NativeCompilationFailed"})
            (check! (not (.exists product)) :no-implicit-product-repair)
            (finally (Files/move (.toPath backup) (.toPath product) (make-array java.nio.file.CopyOption 0)))))
        ;; Mutation after capture is rejected even though helpers use frozen
        ;; copies: the issuer must not issue a receipt against a changed source.
        (let [original-bytes (Files/readAllBytes (.toPath product)) injected (atom false)
              original-run @#'transport/run-process!]
          (try
            (with-redefs-fn {#'transport/run-process!
                            (fn [state journal stage label arguments environment]
                              (when (and (= "entries-0" label) (compare-and-set! injected false true))
                                (Files/write (.toPath product) (byte-array [0]) (into-array OpenOption [StandardOpenOption/APPEND])))
                              (original-run state journal stage label arguments environment))}
              #(rejected! (fn [] (prepare app options)) #{"ArtifactConflict" "UsedProductConflict"}))
            (check! @injected :mid-collection-mutation-exercised)
            (finally (Files/write (.toPath product) original-bytes (into-array OpenOption [StandardOpenOption/TRUNCATE_EXISTING StandardOpenOption/WRITE])))))
        (let [output (io/file directory "report.edn")
              report {:passed true :workspace (.getPath directory) :native-output oracle
                      :original-artifact (:description first) :original-artifact-path (.getPath original-artifact) :checks
                      [:separate-package-calls :dependency-initializer :custom-value :source-host-binding
                       :stale-source-refusal :no-implicit-build :artifact-isolation :dependency-cache-invalidation
                       :nominal-product-change-refusal :missing-product-refusal :mid-collection-mutation-refusal]}]
          (spit output (pr-str report)) report)))))
