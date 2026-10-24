(ns ansatz.bundle-validation-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.java.io :as io]
            [ansatz.bundle :as bundle]
            [ansatz.bundle-metadata :as metadata]
            [ansatz.bundle-validation :as validation]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.wf-supplement-test :as fixture])
  (:import [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]
           [java.io Closeable]))

(defn- with-staging [f]
  (let [directory (.toFile (Files/createTempDirectory "ansatz-bundle-validation-" (make-array FileAttribute 0)))
        selected (fixture/fixture)
        recipe (assoc-in (:generation (:manifest selected)) [:roots]
                         {:init ["A"] :lex ["A"] :sizeof ["A"]})]
    (try
      (io/make-parents (io/file directory "raw" "init.ndjson"))
      (spit (io/file directory "generation.json") (json/write-str recipe))
      (doseq [role [:init :lex :sizeof]]
        (spit (io/file directory "raw" (str (name role) ".ndjson"))
              (fixture/toy-text (:producer selected) fixture/toy-records)))
      (spit (io/file directory "raw" "attrs.ndjson") (str (json/write-str {:kind "unfold" :name "A"}) "\n"))
      (spit (io/file directory "raw" "matchers.ndjson") "")
      (spit (io/file directory "raw" "instances.tsv") "")
      (f directory selected)
      (finally
        (doseq [file (reverse (file-seq directory))] (io/delete-file file true))))))

(defn- manifest-file [directory] (io/file directory "resources" bundle/manifest-resource))
(defn- tracked-parses [close!]
  (let [parse parser/parse-ndjson-string remaining (atom [:init :lex :sizeof])]
    (fn [text]
      (let [role (first @remaining)
            _ (swap! remaining subvec 1)
            state (parse text) store (:exprs state)]
        (assoc state :exprs
               (reify Closeable
                 (close [_]
                   (.close ^Closeable store)
                   (close! role))))))))

(deftest union-closed-but-role-open-fails-before-replay-and-closes-every-parser
  (with-staging
    (fn [directory selected]
      (let [records (filterv #(not (or (:def %) (:thm %) (= 2 (get-in % [:axiom :name])))) fixture/toy-records)
            closed (atom []) replayed (atom false)]
        (spit (io/file directory "raw" "lex.ndjson") (fixture/toy-text (:producer selected) records))
        (spit (io/file directory "raw" "attrs.ndjson")
              (str (json/write-str {:kind "impl" :name "A" :target "x"}) "\n"))
        (with-redefs [parser/parse-ndjson-string (tracked-parses #(swap! closed conj %))
                      replay/replay (fn [& _] (reset! replayed true) (throw (AssertionError. "role gate must precede replay")))]
          (let [error (fixture/error #(validation/validate-candidate! directory))]
            (is (= :lex (:kernel-role (ex-data error))))
            (is (= 1 (:missing-root-count (ex-data error))))
            (is (= ["x"] (:missing-root-sample (ex-data error))))))
        (is (false? @replayed))
        (is (= [:sizeof :lex :init] @closed))
        (is (not (.exists (manifest-file directory))))))))

(deftest role-closed-candidate-publishes-only-after-all-parsers-close
  (with-staging
    (fn [directory _]
      (let [closed (atom []) write @#'validation/write-manifest!
            observed (with-redefs-fn
                       {#'parser/parse-ndjson-string (tracked-parses #(swap! closed conj %))
                        #'validation/write-manifest! (fn [file manifest]
                                                       (is (= [:sizeof :lex :init] @closed))
                                                       (write file manifest))}
                       #(validation/validate-candidate! directory))]
        (is (= :not-performed (:promotion observed)))
        (is (true? (get-in observed [:publication :published])))
        (is (.exists (manifest-file directory)))
        (is (= "ansatz-bundle/2"
               (:bundle/schema (bundle/verify! {:read-resource
                                                (fn [path] (Files/readAllBytes (.toPath (io/file directory "resources" path))))}))))))))

(deftest each-parser-close-failure-prevents-candidate-marker-and-attempts-all-closes
  (doseq [failed-role [:init :lex :sizeof]]
    (with-staging
      (fn [directory _]
        (let [closed (atom []) failure (ex-info "injected parser close failure" {:role failed-role})
              observed (with-redefs [parser/parse-ndjson-string
                                     (tracked-parses (fn [role]
                                                       (swap! closed conj role)
                                                       (when (= role failed-role) (throw failure))))]
                         (fixture/error #(validation/validate-candidate! directory)))]
          (is (identical? failure observed))
          (is (= [:sizeof :lex :init] @closed))
          (is (not (.exists (manifest-file directory))))
          (is (not (.exists (io/file directory "resources")))))))))

(deftest primary-validation-failure-retains-all-close-failures-and-no-marker
  (with-staging
    (fn [directory _]
      (let [closed (atom []) original (ex-info "kernel validation failed" {})
            cleanup (into {} (map #(vector % (ex-info "cleanup failed" {:role %})) [:init :lex :sizeof]))
            observed (with-redefs [parser/parse-ndjson-string
                                   (tracked-parses (fn [role] (swap! closed conj role) (throw (get cleanup role))))
                                   replay/replay (fn [& _] (throw original))]
                       (fixture/error #(validation/validate-candidate! directory)))]
        (is (identical? original observed))
        (is (= [:sizeof :lex :init] @closed))
        (is (= (set (vals cleanup)) (set (.getSuppressed original))))
        (is (not (.exists (manifest-file directory))))))))

(deftest manifest-write-failure-propagates-instead-of-returning-success
  (with-staging
    (fn [directory _]
      (let [closed (atom []) failure (ex-info "manifest publication failed" {})
            observed (with-redefs-fn
                       {#'parser/parse-ndjson-string (tracked-parses #(swap! closed conj %))
                        #'validation/write-manifest! (fn [& _] (throw failure))}
                       #(fixture/error (fn [] (validation/validate-candidate! directory))))]
        (is (identical? failure observed))
        (is (= [:sizeof :lex :init] @closed))
        (is (not (.exists (manifest-file directory))))))))

(deftest role-gate-diagnostics-cap-edge-count-and-text-without-hiding-totals
  (let [large (apply str (repeat 1000 "x"))
        rows (mapv #(hash-map :kind "impl" :name "A" :target (str large %)) (range 20))
        error (fixture/error #(metadata/assert-role-closure!
                               {:attrs rows :matchers [] :instances []}
                               {:init #{"A"} :lex #{"A"} :sizeof #{"A"}}))
        data (ex-data error)]
    (is (= 20 (:missing-edge-count data) (:missing-root-count data)))
    (is (= 8 (count (:missing-edge-sample data)) (count (:missing-root-sample data))))
    (is (:samples-truncated? data))
    (is (:sample-text-truncated? data))
    (is (every? #(<= (count %) 256) (:missing-root-sample data)))))

(deftest precommit-temp-write-and-link-failures-leave-no-final-marker
  (doseq [stage [:write :link]]
    (with-staging
      (fn [directory _]
        (let [failure (ex-info "precommit failure" {:stage stage})
              write @#'validation/write-manifest-temp!
              observed (with-redefs-fn
                         {(if (= stage :write) #'validation/write-manifest-temp! #'validation/publish-manifest-link!)
                          (if (= stage :write)
                            (fn [path manifest] (write path manifest) (throw failure))
                            (fn [& _] (throw failure)))}
                         #(fixture/error (fn [] (validation/validate-candidate! directory))))]
          (is (identical? failure observed))
          (is (not (.exists (manifest-file directory))))
          (is (empty? (filter #(.startsWith (.getName %) ".ansatz-bundle-")
                              (file-seq (io/file directory "resources"))))))))))

(deftest raced-existing-marker-is-never-overwritten-by-atomic-publication
  (with-staging
    (fn [directory _]
      (let [publish @#'validation/publish-manifest-link!
            observed (with-redefs-fn
                       {#'validation/publish-manifest-link!
                        (fn [destination temporary]
                          (spit (.toFile destination) "raced-existing-marker")
                          (publish destination temporary))}
                       #(fixture/error (fn [] (validation/validate-candidate! directory))))]
        (is (instance? java.nio.file.FileAlreadyExistsException observed))
        (is (= "raced-existing-marker" (slurp (manifest-file directory))))))))

(deftest postcommit-temp-cleanup-failure-reports-published-valid-marker
  (with-staging
    (fn [directory _]
      (let [failure (ex-info (apply str (repeat 1000 "x")) {})
            report (with-redefs-fn {#'validation/delete-manifest-temp! (fn [_] (throw failure))}
                     #(validation/validate-candidate! directory))
            publication (:publication report)]
        (is (true? (:published publication)))
        (is (= :retained (:temporary-cleanup publication)))
        (is (= 256 (count (get-in publication [:diagnostic :message]))))
        (is (.exists (manifest-file directory)))
        (is (.exists (io/file (.getParentFile (manifest-file directory))
                              (get-in publication [:diagnostic :temporary-file]))))
        (is (= "ansatz-bundle/2"
               (:bundle/schema (bundle/verify! {:read-resource
                                                (fn [path] (Files/readAllBytes (.toPath (io/file directory "resources" path))))}))))))))

(deftest later-parse-failure-closes-earlier-owned-stores-and-never-publishes
  (with-staging
    (fn [directory _]
      (let [failure (ex-info "lex parse failure" {}) closed (atom [])
            parse (tracked-parses #(swap! closed conj %)) calls (atom 0)
            observed (with-redefs [parser/parse-ndjson-string
                                   (fn [text]
                                     (if (= 2 (swap! calls inc))
                                       (throw failure) (parse text)))]
                       (fixture/error #(validation/validate-candidate! directory)))]
        (is (identical? failure observed))
        (is (= [:init] @closed))
        (is (not (.exists (manifest-file directory))))))))

(deftest resource-compression-uses-the-same-raw-bytes-that-were-checked
  (with-staging
    (fn [directory _]
      (let [raw-file (io/file directory "raw" "init.ndjson")
            original-text (slurp raw-file :encoding "UTF-8")
            replay replay/replay once (atom true)]
        (with-redefs [replay/replay (fn [& args]
                                      (when (compare-and-set! once true false)
                                        (spit raw-file "changed-after-capture"))
                                      (apply replay args))]
          (let [report (validation/validate-candidate! directory)
                file (io/file directory "resources" (get bundle/role-resources :init))
                emitted (with-open [stream (java.util.zip.GZIPInputStream. (io/input-stream file))]
                          (slurp stream :encoding "UTF-8"))]
            (is (true? (get-in report [:publication :published])))
            (is (= "changed-after-capture" (slurp raw-file)))
            (is (= original-text emitted))))))))

(deftest invalid-utf8-fails-before-replay-or-publication
  (with-staging
    (fn [directory _]
      (with-open [stream (io/output-stream (io/file directory "raw" "init.ndjson"))]
        (.write stream (byte-array [(unchecked-byte 195) 40])))
      (let [replayed (atom false)
            error (with-redefs [replay/replay (fn [& _] (reset! replayed true))]
                    (fixture/error #(validation/validate-candidate! directory)))]
        (is (instance? java.nio.charset.CharacterCodingException error))
        (is (false? @replayed))
        (is (not (.exists (manifest-file directory))))))))

(deftest interleaved-second-validator-cannot-alter-the-winner-cohort
  (with-staging
    (fn [directory _]
      (let [publish @#'validation/publish-manifest-link! second-error (atom nil)
            parse parser/parse-ndjson-string parses (atom 0)
            artifact-bytes (fn []
                             (into {} (map (fn [path]
                                             [path (vec (Files/readAllBytes (.toPath (io/file directory path))))]))
                                   (conj (mapv #(str "resources/" %) (vals bundle/role-resources)) "validation.edn")))
            observed (with-redefs-fn
                       {#'parser/parse-ndjson-string (fn [text] (swap! parses inc) (parse text))
                        #'validation/publish-manifest-link!
                        (fn [destination temporary]
                          (let [before (artifact-bytes)]
                            (reset! second-error (fixture/error #(validation/validate-candidate! directory)))
                            (is (= 3 @parses) "second attempt refused before parsing")
                            (is (= before (artifact-bytes)) "all six resources/report unchanged"))
                          (publish destination temporary))}
                       #(validation/validate-candidate! directory))
            final-bytes (artifact-bytes)
            marker-bytes (vec (Files/readAllBytes (.toPath (manifest-file directory))))]
        (is (= :ansatz.bundle-validation/staging-claimed (:type (ex-data @second-error))))
        (is (true? (get-in observed [:publication :published])))
        (is (.exists (io/file directory ".ansatz-bundle-validation.claim")))
        (is (some? (fixture/error #(validation/validate-candidate! directory))))
        (is (= final-bytes (artifact-bytes)))
        (is (= marker-bytes (vec (Files/readAllBytes (.toPath (manifest-file directory))))))))))

(deftest failed-validation-retains-claim-and-refuses-any-retry-before-parse
  (with-staging
    (fn [directory _]
      (let [failure (ex-info "kernel failed" {})
            first-error (with-redefs [replay/replay (fn [& _] (throw failure))]
                          (fixture/error #(validation/validate-candidate! directory)))
            retried (atom false)
            second-error (with-redefs [parser/parse-ndjson-string (fn [& _] (reset! retried true))]
                           (fixture/error #(validation/validate-candidate! directory)))]
        (is (identical? failure first-error))
        (is (.exists (io/file directory ".ansatz-bundle-validation.claim")))
        (is (= :ansatz.bundle-validation/staging-claimed (:type (ex-data second-error))))
        (is (false? @retried))
        (is (not (.exists (manifest-file directory))))))))
