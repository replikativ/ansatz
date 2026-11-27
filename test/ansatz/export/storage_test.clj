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
            (is (.exists (java.io.File. dir "verify-verify-test-s1.edn")))
            (testing "the per-slice files supersede a stale combined checkpoint, and the retry
                      pass rewrites them"
              (let [s1 (java.io.File. dir "verify-verify-test-s1.edn")
                    cp1 (clojure.edn/read-string (slurp s1))
                    fake [{:name "Nat.add" :error "recorded"}]
                    _ (spit s1 (pr-str (-> cp1 (assoc :error-names fake :errors 1)
                                           (assoc-in [:slices 0 :error-names] fake)
                                           (assoc-in [:slices 0 :errors] 1))))
                    _ (spit (java.io.File. dir "verify-verify-test.edn")
                            (pr-str (assoc merged :error-names [{:name "Nat.zero" :error "stale"}] :errors 1)))
                    cp (#'storage/read-checkpoint store-map "verify-test")
                    r (storage/reverify-errors! store-map "verify-test")
                    after1 (clojure.edn/read-string (slurp s1))
                    after (clojure.edn/read-string (slurp (java.io.File. dir "verify-verify-test.edn")))]
                (is (= ["Nat.add"] (mapv :name (:error-names cp))))
                (is (= ["Nat.add"] (:fixed r)))
                (is (zero? (:errors after1)))
                (is (zero? (get-in after1 [:slices 0 :errors])))
                (is (zero? (:errors after)))
                (is (= 2 (count (:slices after)))))))
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

(deftest reverify-errors-retries-through-the-bundle-head
  (testing "recorded constructor/recursor entries are retried via their inductive and cleared"
    (let [dir (temp-dir)]
      (try
        (let [store-map (storage/open-store dir)]
          (storage/import-ndjson-streaming! store-map example-file "verify-test")
          (let [r0 (storage/verify-corpus! store-map "verify-test" :workers 1 :checkpoint-every 3)
                f (java.io.File. dir "verify-verify-test.edn")
                cp (clojure.edn/read-string (slurp f))
                fake [{:name "Nat.succ" :error "recorded"}
                      {:name "Nat.rec" :error "recorded"}
                      {:name "Nat.add" :error "recorded"}
                      {:name "NoSuch.decl" :error "recorded"}]
                cp' (-> cp
                        (assoc :error-names fake :errors 4 :ok (- (:total cp) 4))
                        (assoc-in [:slices 0 :error-names] fake)
                        (assoc-in [:slices 0 :errors] 4)
                        (update-in [:slices 0 :ok] - 4))
                _ (spit f (pr-str cp'))
                r (storage/reverify-errors! store-map "verify-test")
                after (clojure.edn/read-string (slurp f))]
            (is (:done? r0))
            (is (= #{"Nat.succ" "Nat.rec" "Nat.add"} (set (:fixed r))))
            (testing "what still fails stays recorded with its new error, and does not stop the pass"
              (is (= ["NoSuch.decl"] (mapv :name (:still-failing r))))
              (is (= 1 (:errors after)))
              (is (= ["NoSuch.decl"] (mapv :name (:error-names after))))
              (is (re-find #"not found" (:error (first (:error-names after)))))
              (is (= 1 (get-in after [:slices 0 :errors])))
              (is (= (:total after) (+ (:ok after) (:errors after)))
                  "a fixed entry counts as verified")))
          (storage/close-store store-map))
        (finally
          (delete-dir-recursive dir))))))

(defn- write-detached-members-ndjson!
  "E : Prop (no constructors) with E.rec, an unrelated axiom, then two rows that claim E but
   lie outside its block: a constructor E.intro : E and an auxiliary-style recursor E.rec_1."
  [path]
  (spit path
        (str "{\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"},\"format\":{\"version\":\"3.1.0\"},\"lean\":{\"githash\":\"x\",\"version\":\"4.36.0\"}}}\n"
             "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"E\"}}\n"
             "{\"in\":2,\"str\":{\"pre\":1,\"str\":\"intro\"}}\n"
             "{\"in\":3,\"str\":{\"pre\":1,\"str\":\"rec\"}}\n"
             "{\"in\":4,\"str\":{\"pre\":0,\"str\":\"u\"}}\n"
             "{\"in\":5,\"str\":{\"pre\":0,\"str\":\"motive\"}}\n"
             "{\"in\":6,\"str\":{\"pre\":0,\"str\":\"t\"}}\n"
             "{\"in\":7,\"str\":{\"pre\":0,\"str\":\"ax\"}}\n"
             "{\"in\":8,\"str\":{\"pre\":1,\"str\":\"rec_1\"}}\n"
             "{\"il\":1,\"param\":4}\n"
             "{\"ie\":0,\"sort\":0}\n"
             "{\"ie\":1,\"const\":{\"name\":1,\"us\":[]}}\n"
             "{\"ie\":2,\"sort\":1}\n"
             "{\"ie\":3,\"forallE\":{\"binderInfo\":\"default\",\"name\":6,\"type\":1,\"body\":2}}\n"
             "{\"ie\":4,\"bvar\":1}\n"
             "{\"ie\":5,\"bvar\":0}\n"
             "{\"ie\":6,\"app\":{\"fn\":4,\"arg\":5}}\n"
             "{\"ie\":7,\"forallE\":{\"binderInfo\":\"default\",\"name\":6,\"type\":1,\"body\":6}}\n"
             "{\"ie\":8,\"forallE\":{\"binderInfo\":\"default\",\"name\":5,\"type\":3,\"body\":7}}\n"
             "{\"inductive\":{\"constructorVals\":[],\"inductiveVals\":[{\"all\":[1],\"ctors\":[],\"isRec\":false,\"isReflexive\":false,\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"numIndices\":0,\"numNested\":0,\"numParams\":0,\"type\":0}],\"recursorVals\":[{\"all\":[1],\"isUnsafe\":false,\"k\":false,\"levelParams\":[4],\"name\":3,\"numIndices\":0,\"numMinors\":0,\"numMotives\":1,\"numParams\":0,\"rules\":[],\"type\":8}]}}\n"
             "{\"axiom\":{\"name\":7,\"levelParams\":[],\"type\":0,\"isUnsafe\":false}}\n"
             "{\"inductive\":{\"constructorVals\":[{\"cidx\":0,\"induct\":1,\"isUnsafe\":false,\"levelParams\":[],\"name\":2,\"numFields\":0,\"numParams\":0,\"type\":1}],\"inductiveVals\":[],\"recursorVals\":[]}}\n"
             "{\"inductive\":{\"constructorVals\":[],\"inductiveVals\":[],\"recursorVals\":[{\"all\":[1],\"isUnsafe\":false,\"k\":false,\"levelParams\":[4],\"name\":8,\"numIndices\":0,\"numMinors\":0,\"numMotives\":1,\"numParams\":0,\"rules\":[{\"ctor\":2,\"nfields\":0,\"rhs\":0}],\"type\":8}]}}\n")))

(deftest reverify-does-not-clear-members-detached-from-their-block
  (testing "a retried head's success clears only the names its own block check covered"
    (let [dir (temp-dir) f (str dir "/detached.ndjson")]
      (try
        (write-detached-members-ndjson! f)
        (let [store-map (storage/open-store dir)]
          (storage/import-ndjson-streaming! store-map f "detached")
          (let [r0 (storage/verify-corpus! store-map "detached" :workers 1)
                cp (clojure.edn/read-string (slurp (java.io.File. dir "verify-detached.edn")))]
            (is (:done? r0))
            (is (= #{"E.intro" "E.rec_1"} (set (map :name (:error-names cp)))))
            (let [r (storage/reverify-errors! store-map "detached")
                  after (clojure.edn/read-string (slurp (java.io.File. dir "verify-detached.edn")))]
              (is (empty? (:fixed r)))
              (is (= #{"E.intro" "E.rec_1"} (set (map :name (:still-failing r)))))
              (is (= 2 (:errors after)))))
          (storage/close-store store-map))
        (finally
          (delete-dir-recursive dir))))))

(deftest verified-blocks-admit-their-rows-and-only-their-own-names
  (let [dir (temp-dir)]
    (try
      (let [store-map (storage/open-store dir)]
        (storage/import-ndjson-streaming! store-map example-file "verify-test")
        (let [ctx (storage/prepare-verify store-map "verify-test")
              nat-rec (name/from-string "Nat.rec")]
          (try
            (testing "after a block is admitted its rows are visible"
              (is (= "Nat" (first (:decl-order ctx))))
              (is (nil? (env/lookup (:env ctx) nat-rec)))
              (let [r (storage/verify-one! ctx)]
                (is (= :ok (:status r)))
                (is (= #{"Nat" "Nat.zero" "Nat.succ" "Nat.rec"} (set (:checked-names r)))))
              (is (some? (env/lookup (:env ctx) nat-rec))))
            (testing "a row whose declaration has another name is an error and is not admitted"
              (let [next-name (nth (:decl-order ctx) @(:idx ctx))
                    stored-rec ((:resolve-fn ctx) "Nat.rec")
                    aliasing (assoc ctx :resolve-fn (fn [n] (if (= n next-name) stored-rec ((:resolve-fn ctx) n))))
                    r (storage/verify-one! aliasing)]
                (is (= :error (:status r)))
                (is (re-find #"holds the declaration Nat.rec" (:error r)))
                (is (nil? (env/lookup (:env ctx) (name/from-string next-name))))))
            (finally (.close ^java.io.Writer (:log-writer ctx)))))
        (storage/close-store store-map))
      (finally
        (delete-dir-recursive dir)))))

(deftest a-malformed-row-does-not-abort-the-other-retries
  ;; one recorded failure whose row cannot be resolved (a malformed key) and one retryable
  ;; failure: the second is still retried and cleared, the first stays recorded
  (let [dir (temp-dir)]
    (try
      (let [store-map (storage/open-store dir)]
        (storage/import-ndjson-streaming! store-map example-file "verify-test")
        (let [_ (storage/verify-corpus! store-map "verify-test" :workers 1)
              f (java.io.File. dir "verify-verify-test.edn")
              cp (clojure.edn/read-string (slurp f))
              fake [{:name "Nat.add" :error "recorded"} {:name "Nat.succ" :error "recorded"}]
              _ (spit f (pr-str (-> cp (assoc :error-names fake :errors 2 :ok (- (:total cp) 2))
                                    (assoc-in [:slices 0 :error-names] fake)
                                    (assoc-in [:slices 0 :errors] 2)
                                    (update-in [:slices 0 :ok] - 2))))
              prepare storage/prepare-verify
              r (with-redefs [storage/prepare-verify
                              (fn [& args]
                                (let [ctx (apply prepare args) resolve (:resolve-fn ctx)]
                                  (assoc ctx :resolve-fn (fn [n] (if (= n "Nat.add")
                                                                   (throw (ex-info "Store row key differs from its declaration's name" {}))
                                                                   (resolve n))))))]
                  (storage/reverify-errors! store-map "verify-test"))]
          (is (= ["Nat.succ"] (:fixed r)))
          (is (= ["Nat.add"] (mapv :name (:still-failing r))))
          (is (re-find #"key differs" (:error (first (:still-failing r))))))
        (storage/close-store store-map))
      (finally
        (delete-dir-recursive dir)))))

(deftest a-failed-block-head-consumes-its-own-rank
  ;; a head whose `all` omits it collects no members; the verifier must still advance
  (let [dir (temp-dir)]
    (try
      (let [store-map (storage/open-store dir)]
        (storage/import-ndjson-streaming! store-map example-file "verify-test")
        (let [ctx (storage/prepare-verify store-map "verify-test")
              ^ConstantInfo nat ((:resolve-fn ctx) "Nat")
              headless (ConstantInfo/mkInduct (.name nat) (.levelParams nat) (.type nat) (.numParams nat)
                                              (.numIndices nat) (object-array []) (.ctors nat) 0 (.isRec nat)
                                              (.isReflexive nat) (.isUnsafe nat))
              bad (assoc ctx :resolve-fn (fn [n] (if (= n "Nat") headless ((:resolve-fn ctx) n))))]
          (try
            (is (= :error (:status (storage/verify-one! bad))))
            (is (= 1 @(:idx ctx)))
            (finally (.close ^java.io.Writer (:log-writer ctx)))))
        (storage/close-store store-map))
      (finally
        (delete-dir-recursive dir)))))

(deftest external-lookup-must-return-the-named-declaration
  (let [rec (env/mk-axiom (name/from-string "T.rec") [] (Expr/sort ansatz.kernel.Level/ZERO_LEVEL false))
        e (.withExternalLookup (Env.) (fn [_] rec) 1)]
    (is (some? (env/lookup e (name/from-string "T.rec"))))
    (is (thrown-with-msg? RuntimeException #"returned the declaration 'T.rec'"
                          (env/lookup e (name/from-string "Alias"))))))

(deftest branch-enumeration-read-failures-are-errors
  (let [dir (temp-dir)]
    (try
      (let [sm (storage/open-store dir)
            blobs (storage/blobs-dir dir)
            corrupt (java.io.File. blobs "corrupt.ksv")]
        (storage/store-put (:store sm) [:branches "main"] {:timestamp 1})
        (is (= ["main"] (mapv :name (storage/list-branches sm))))
        (spit corrupt "not a blob")
        (is (thrown? clojure.lang.ExceptionInfo (storage/list-branches sm))
            "a corrupt blob must not silently disappear from enumeration")
        (.delete corrupt)
        (with-redefs [storage/store-get (fn [& _] nil)]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Branch metadata missing"
                                (storage/list-branches sm))))
        (delete-dir-recursive (.getPath blobs))
        (is (thrown? java.nio.file.NoSuchFileException (storage/list-branches sm))
            "an unreadable directory must not look like an empty store"))
      (finally (delete-dir-recursive dir)))))
