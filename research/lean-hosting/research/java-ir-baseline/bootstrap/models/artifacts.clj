(ns ansatz.research.ir.bootstrap.artifacts-models
  "Filesystem metadata/loader models only. Caller supplies an explicit task-owned
   scratch directory; these tests open no catalogue, engine, image or store."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.java.io :as io]
            [clojure.data.json :as json]
            [ansatz.research.ir.bootstrap.artifacts :as artifacts]
            [ansatz.research.ir.bootstrap.definitions :as definitions])
  (:import [java.nio.file Files] [java.nio.file.attribute FileAttribute]))
(def ^:dynamic *scratch-root* nil)
(defn- fixture [f]
  (when-not *scratch-root* (throw (ex-info "Bind explicit task-owned model scratch root" {})))
  (let [dir (.toFile (Files/createTempDirectory (.toPath (io/file *scratch-root*)) "bootstrap-model-"
                        (make-array FileAttribute 0)))
        group (doto (io/file dir "group") .mkdir)
        file (io/file group "sample.json") manifest (io/file dir "profile.json")]
    (try
      (spit file (json/write-str {"sample" 7}))
      (let [m {"schema" "ansatz-source4-bootstrap/1" "profile" artifacts/profile-id
               "lean-commit" artifacts/lean-pin "target" {"triple" "x86_64-unknown-linux-gnu" "word-bits" 64}
               "overlays" [{} {} {} {}]
               "artifacts" {"sample" {"root" "test" "path" "group/sample.json" "sha256" (artifacts/sha256 file) "bytes" (.length file)}}
               "directories" {"group" {"root" "test" "path" "group" "files" ["sample"]}}}
            write! (fn [p] (spit manifest (json/write-str p)) (artifacts/sha256 manifest))]
        (f {:dir dir :group group :file file :manifest manifest :profile m :write! write! :roots {"test" dir}}))
      (finally (doseq [file (reverse (file-seq dir))] (io/delete-file file true))))))
(deftest independent-profile-pin-and-exact-byte-lease
  (fixture
    (fn [{:keys [file manifest profile write! roots]}]
      (let [sha (write! profile) cap (artifacts/authenticate-profile! manifest sha roots)]
        (is (= profile (artifacts/description cap)))
        (is (= (.getCanonicalFile file) (artifacts/file! cap "sample")))
        (is (= {"sample" 7} (artifacts/json! cap "sample" 64)))
        (is (thrown? Exception (artifacts/file! cap "unknown")))
        (is (thrown? Exception (artifacts/authenticate-profile! manifest (apply str (repeat 64 "0")) roots)))
        (spit file (json/write-str {"sample" 888}))
        (is (thrown? Exception (artifacts/guard! cap)))))))
(deftest profile-close-revokes-only-metadata-access
  (fixture
    (fn [{:keys [manifest profile write! roots file]}]
      (let [cap (artifacts/authenticate-profile! manifest (write! profile) roots)]
        (is (nil? (artifacts/close! cap)))
        (is (thrown? Exception (artifacts/description cap)))
        (is (thrown? Exception (artifacts/file! cap "sample")))
        (is (.isFile file))))))
(deftest wrong-file-hash-size-and-normalized-paths-reject-before-issue
  (fixture
    (fn [{:keys [manifest profile write! roots]}]
      (doseq [[key value] [["sha256" (apply str (repeat 64 "0"))] ["bytes" 1000]
                           ["path" "../escape"] ["path" "/absolute"] ["path" "group/./sample.json"]
                           ["path" (str "group" (char 92) "sample.json")]]]
        (let [bad (assoc-in profile ["artifacts" "sample" key] value)]
          (is (thrown? Exception (artifacts/authenticate-profile! manifest (write! bad) roots)))))
      (is (thrown? Exception (artifacts/authenticate-profile! manifest (write! profile) {}))))))
(deftest directory-file-set-is-explicit-at-issue-and-every-access
  (fixture
    (fn [{:keys [group manifest profile write! roots]}]
      (let [cap (artifacts/authenticate-profile! manifest (write! profile) roots)]
        (is (= (.getCanonicalFile group) (artifacts/directory! cap "group")))
        (spit (io/file group "undeclared") "extra")
        (is (thrown? Exception (artifacts/directory! cap "group")))
        (is (thrown? Exception (artifacts/authenticate-profile! manifest (artifacts/sha256 manifest) roots)))))))
(deftest no-map-or-public-empty-profile-constructor-is-authority
  (doseq [token [nil {} (artifacts/->Profile)]]
    (is (thrown? Exception (artifacts/description token)))
    (is (thrown? Exception (artifacts/file! token "sample")))))
(deftest source-archive-is-pin-and-path-scoped
  (fixture
    (fn [{:keys [manifest profile write! roots]}]
      (let [p (assoc profile "lean-source" {"commit" artifacts/lean-pin "files" {"src/source.cpp" "sample"}})
            cap (artifacts/authenticate-profile! manifest (write! p) roots)
            reader (artifacts/source-reader cap)]
        (is (= artifacts/lean-pin (:commit reader)))
        (is (pos? (alength ^bytes ((:read-blob! reader) "src/source.cpp"))))
        (is (thrown? Exception ((:read-blob! reader) "src/unknown.cpp")))
        (is (thrown? Exception ((:read-blob! reader) "../source.cpp")))
        (artifacts/close! cap)
        (is (thrown? Exception ((:read-blob! reader) "src/source.cpp")))))))
(deftest loader-preflights-all-namespace-and-file-identities-before-load
  (fixture
    (fn [{:keys [manifest profile write! roots]}]
      (let [p (assoc profile "definitions" [["sample" "not.the.actual.namespace"]])
            cap (artifacts/authenticate-profile! manifest (write! p) roots) loads (atom [])]
        (with-redefs [clojure.core/load-file #(swap! loads conj %)]
          (is (thrown? Exception (definitions/load-definitions! cap))))
        (is (empty? @loads))))))
(deftest profile-authority-hash-and-parser-share-one-bounded-read
  (fixture
    (fn [{:keys [manifest profile write! roots]}]
      (let [sha (write! profile) calls (atom 0) original @#'artifacts/bounded-bytes]
        (with-redefs-fn
          {#'artifacts/bounded-bytes (fn [file limit]
                                      (when (= (.getCanonicalFile (io/file file)) (.getCanonicalFile manifest))
                                        (swap! calls inc))
                                      (original file limit))}
          #(let [cap (artifacts/authenticate-profile! manifest sha roots)]
             (is (= 1 @calls))
             (is (= profile (artifacts/description cap)))
             (artifacts/close! cap)))))))

(defn check! [scratch-root]
  (binding [*scratch-root* scratch-root] (run-tests 'ansatz.research.ir.bootstrap.artifacts-models)))
