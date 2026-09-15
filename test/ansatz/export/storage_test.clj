(ns ansatz.export.storage-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.export.storage :as storage]
            [ansatz.export.parser :as parser]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel Name ConstantInfo Env Expr]
           [java.io File Writer]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(def example-file "test-data/Nat.add_succ.ndjson")

(defn- temp-dir []
  (str (Files/createTempDirectory "ansatz-storage-test"
                                  (into-array FileAttribute []))))

(defn- delete-dir-recursive [^String path]
  (let [f (File. path)]
    (when (.exists f)
      (doseq [child (.listFiles f)]
        (if (.isDirectory child)
          (delete-dir-recursive (.getPath child))
          (.delete child)))
      (.delete f))))

(defn- write-quot-ndjson! [path]
  (spit path
        (str "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Quot\"}}\n"
             "{\"il\":1,\"succ\":0}\n"
             "{\"ie\":0,\"sort\":1}\n"
             "{\"quot\":{\"kind\":\"type\",\"levelParams\":[],\"name\":1,\"type\":0}}\n")))

(deftest roundtrip-test
  (testing "Parse → persist → close → open → load-env round-trip"
    (let [dir (temp-dir)]
      (try
        ;; Parse
        (let [st (parser/parse-ndjson-file example-file)
              e (parser/build-env (:decls st))]

          ;; Persist
          (let [store-map (storage/open-store dir)]
            (storage/persist-all! store-map st e "main")
            (storage/close-store store-map))

          ;; Reopen and load
          (let [store-map (storage/open-store dir)
                loaded-env (storage/load-env store-map "main")]

            (testing "Nat is in loaded environment"
              (let [nat (env/lookup loaded-env (name/from-string "Nat"))]
                (is (some? nat))
                (is (env/induct? nat))))

            (testing "Nat.zero is in loaded environment"
              (let [zero (env/lookup loaded-env (name/from-string "Nat.zero"))]
                (is (some? zero))
                (is (env/ctor? zero))))

            (testing "Nat.add_succ theorem is in loaded environment"
              (let [thm (env/lookup loaded-env (name/from-string "Nat.add_succ"))]
                (is (some? thm))
                (is (env/thm? thm))))

            (storage/close-store store-map)))
        (finally
          (delete-dir-recursive dir))))))

(deftest fork-branch-test
  (testing "Fork creates a new branch with same data"
    (let [dir (temp-dir)]
      (try
        (let [st (parser/parse-ndjson-file example-file)
              e (parser/build-env (:decls st))
              store-map (storage/open-store dir)]

          ;; Persist to "main"
          (storage/persist-all! store-map st e "main")

          ;; Fork
          (storage/fork-branch store-map "main" "experiment")

          ;; List branches
          (let [branches (storage/list-branches store-map)]
            (is (= 2 (count branches)))
            (is (some #(= "main" (:name %)) branches))
            (is (some #(= "experiment" (:name %)) branches)))

          ;; Load from forked branch
          (let [forked-env (storage/load-env store-map "experiment")]
            (is (some? (env/lookup forked-env (name/from-string "Nat"))))
            (is (some? (env/lookup forked-env (name/from-string "Nat.add_succ")))))

          (storage/close-store store-map))
        (finally
          (delete-dir-recursive dir))))))

(deftest load-names-test
  (testing "Load names from persisted store"
    (let [dir (temp-dir)]
      (try
        (let [st (parser/parse-ndjson-file example-file)
              e (parser/build-env (:decls st))
              store-map (storage/open-store dir)]

          (storage/persist-all! store-map st e "main")

          (let [names (storage/load-names store-map "main")]
            (is (seq names))
            (is (> (count names) 50))
            ;; First entry should be id 0 = anonymous name
            (let [[id n] (first names)]
              (is (= 0 id))))

          (storage/close-store store-map))
        (finally
          (delete-dir-recursive dir))))))

(deftest resolve-expr-test
  (testing "Resolve raw expression bytes from persisted store"
    (let [dir (temp-dir)]
      (try
        (let [st (parser/parse-ndjson-file example-file)
              e (parser/build-env (:decls st))
              store-map (storage/open-store dir)]

          (storage/persist-all! store-map st e "main")

          ;; Expression 0 should exist and have bytes
          (let [raw (storage/resolve-expr store-map "main" 0)]
            (is (some? raw))
            (is (bytes? raw))
            (is (pos? (alength ^bytes raw))))

          (storage/close-store store-map))
        (finally
          (delete-dir-recursive dir))))))

(deftest streaming-import-test
  (testing "Streaming import persists declarations and tracks order"
    (let [dir (temp-dir)]
      (try
        (let [store-map (storage/open-store dir)
              meta (storage/import-ndjson-streaming! store-map example-file "streamed"
                                                     :verbose? false)]
          (is (some? (:env-root meta)))
          (is (pos? (:env-count meta)))

          ;; Load env from streamed branch and check declarations
          (let [loaded-env (storage/load-env store-map "streamed")]
            (is (some? (env/lookup loaded-env (name/from-string "Nat"))))
            (is (some? (env/lookup loaded-env (name/from-string "Nat.add_succ")))))

          (storage/close-store store-map))
        (finally
          (delete-dir-recursive dir))))))

(deftest streaming-verify-test
  (testing "Streaming import then verify produces correct results"
    (let [dir (temp-dir)]
      (try
        (let [store-map (storage/open-store dir)]
          (storage/import-ndjson-streaming! store-map example-file "verify-test")
          (let [stats (storage/verify-from-store! store-map "verify-test" :verbose? false)]
            (is (pos? (:ok stats)))
            (is (zero? (:errors stats)))
            (is (= (:total stats) (+ (:ok stats) (:errors stats)))))
          (storage/close-store store-map))
        (finally
          (delete-dir-recursive dir))))))

(deftest verify-corpus-parallel-and-resumable
  (testing "Sliced parallel verification checks everything, checkpoints, and resumes to a no-op"
    (let [dir (temp-dir)]
      (try
        (let [store-map (storage/open-store dir)]
          (storage/import-ndjson-streaming! store-map example-file "verify-test")
          (let [r1 (storage/verify-corpus! store-map "verify-test" :workers 2 :checkpoint-every 3)
                f (java.io.File. dir "verify-verify-test.edn")]
            (is (:done? r1))
            (is (= (:total r1) (:ok r1)))
            (is (zero? (:errors r1)))
            (is (.exists f) "the checkpoint is the run's durable state")
            (testing "and a second run resumes from the completed checkpoint without re-verifying"
              (let [r2 (storage/verify-corpus! store-map "verify-test" :workers 2 :checkpoint-every 3)]
                (is (:done? r2))
                (is (= (:ok r1) (:ok r2)))))
            (testing "a slice that was interrupted continues where it stopped"
              (let [cp (clojure.edn/read-string (slurp f))
                    back (update-in cp [:slices 1] (fn [sl] (assoc sl :idx (:start sl) :ok 0)))
                    _ (spit f (pr-str back))
                    r3 (storage/verify-corpus! store-map "verify-test" :workers 2 :checkpoint-every 3)]
                (is (:done? r3))
                (is (= (:ok r1) (:ok r3))))))
          (storage/close-store store-map))
        (finally
          (delete-dir-recursive dir))))))

(deftest verify-corpus-one-slice-per-process
  (testing "each slice can run in its own process with its own checkpoint, and the retry pass
            reads them merged"
    (let [dir (temp-dir)]
      (try
        (let [store-map (storage/open-store dir)]
          (storage/import-ndjson-streaming! store-map example-file "verify-test")
          (let [r0 (storage/verify-corpus! store-map "verify-test" :workers 2 :slice 0 :checkpoint-every 3)
                r1 (storage/verify-corpus! store-map "verify-test" :workers 2 :slice 1 :checkpoint-every 3)
                merged (#'storage/read-checkpoint store-map "verify-test")]
            (is (and (:done? r0) (:done? r1)))
            (is (= 2 (count (:slices merged))))
            (is (= (:total r0) (reduce + (map :ok (:slices merged)))))
            (is (zero? (reduce + (map :errors (:slices merged)))))
            (is (.exists (java.io.File. dir "verify-verify-test-s1.edn"))))
          (storage/close-store store-map))
        (finally
          (delete-dir-recursive dir))))))

(deftest prepare-verify-stages-environment
  (testing "Verification env exposes only declarations admitted before the current index"
    (let [dir (temp-dir)]
      (try
        (let [store-map (storage/open-store dir)]
          (storage/import-ndjson-streaming! store-map example-file "verify-test")
          (let [ctx (storage/prepare-verify store-map "verify-test")
                nat-name (name/from-string "Nat")
                thm-name (name/from-string "Nat.add_succ")
                [[thm-idx _]] (storage/find-decl ctx "Nat.add_succ")]
            (try
              (is (nil? (env/lookup (:env ctx) thm-name)))
              (storage/skip-to! ctx thm-idx)
              (is (some? (env/lookup (:env ctx) nat-name)))
              (is (nil? (env/lookup (:env ctx) thm-name)))
              (finally
                (.close ^java.io.Writer (:log-writer ctx)))))
          (storage/close-store store-map))
        (finally
          (delete-dir-recursive dir))))))

(deftest failed-declaration-is-not-made-visible
  (testing "Advancing after a failed declaration does not admit it"
    (let [dir (temp-dir)]
      (try
        (let [store-map (storage/open-store dir)]
          (storage/import-ndjson-streaming! store-map example-file "verify-test")
          (let [ctx (storage/prepare-verify store-map "verify-test")
                first-name-str (first (:decl-order ctx))
                first-name (name/from-string first-name-str)
                original-resolve (:resolve-fn ctx)
                bad-ci (ConstantInfo/mkAxiom first-name
                                             (object-array [])
                                             (Expr/bvar 0)
                                             false)
                failing-ctx (assoc ctx :resolve-fn
                                   (fn [name-str]
                                     (if (= name-str first-name-str)
                                       bad-ci
                                       (original-resolve name-str))))]
            (try
              (let [result (storage/verify-one! failing-ctx :timeout-ms 0)]
                (is (= :error (:status result)))
                (testing "unless the corpus run asks to admit failures (recorded, not cascading)"
                  (let [ctx2 (assoc failing-ctx :idx (atom 0) :ok (atom 0) :errors (atom 0)
                                    :error-names (atom []) :admitted-ranks (java.util.BitSet. 8))
                        r2 (storage/verify-one! ctx2 :timeout-ms 0 :admit-failures? true)]
                    (is (= :error (:status r2)))
                    (is (.get ^java.util.BitSet (:admitted-ranks ctx2) 0))))
                (is (= 1 @(:idx ctx)))
                (is (nil? (env/lookup (:env ctx) first-name))))
              (finally
                (.close ^java.io.Writer (:log-writer ctx)))))
          (storage/close-store store-map))
        (finally
          (delete-dir-recursive dir))))))

