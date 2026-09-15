(ns ansatz.store.fetch-test
  "Packing a store, serving the artifacts over HTTP, and fetching them back — the path a
   library user takes when they ask for Mathlib and do not have it."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.java.io :as io]
            [clojure.edn :as edn]
            [ansatz.store :as store]
            [ansatz.store.archive :as archive]
            [ansatz.store.fetch :as fetch]
            [ansatz.store.pack :as pack]
            [ansatz.export.storage :as storage])
  (:import [com.sun.net.httpserver HttpServer HttpHandler]
           [java.net InetSocketAddress]
           [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(defn- temp-dir ^String [] (str (Files/createTempDirectory "ansatz-fetch" (into-array FileAttribute []))))

(defn- delete-dir [^String path]
  (let [f (File. path)]
    (when (.exists f)
      (doseq [c (.listFiles f)] (if (.isDirectory c) (delete-dir (.getPath c)) (.delete c)))
      (.delete f))))

(defn- serve!
  "An HTTP server over `root`. `truncate` (bytes) makes every response stop short, to exercise
   resume; `ignore-range?` makes it answer 200 to a Range request, as some CDNs do."
  [root {:keys [truncate ignore-range?]}]
  (let [server (HttpServer/create (InetSocketAddress. "127.0.0.1" 0) 0)]
    (.createContext server "/"
                    (reify HttpHandler
                      (handle [_ ex]
                        (let [p (.getPath (.getRequestURI ex))
                              f (io/file root (subs p 1))]
                          (if-not (.isFile f)
                            (do (.sendResponseHeaders ex 404 -1) (.close ex))
                            (let [all (Files/readAllBytes (.toPath f))
                                  range (.getFirst (.getRequestHeaders ex) "Range")
                                  from (if (and range (not ignore-range?))
                                         (Long/parseLong (second (re-find #"bytes=(\d+)-" range)))
                                         0)
                                  body (java.util.Arrays/copyOfRange all (int from) (alength all))
                                  body (if truncate
                                         (java.util.Arrays/copyOfRange body 0 (int (min truncate (alength body))))
                                         body)]
                              (.sendResponseHeaders ex (if (and range (not ignore-range?)) 206 200) (alength body))
                              (with-open [os (.getResponseBody ex)] (.write os body))
                              (.close ex)))))))
    (.start server)
    server))

(defn- make-store! [dir branch]
  (let [sm (storage/open-store dir)]
    (storage/import-ndjson-streaming! sm "test-data/Nat.add_succ.ndjson" branch)
    (storage/close-store sm)
    (store/write-manifest! dir {:store/format store/store-format
                                :ansatz/version "test"
                                :branch branch
                                :provenance {:library/tag "v0.0.1-test"}})
    dir))

(defn- with-fixture [f]
  (let [root (temp-dir) src (str (io/file root "src" "mathlib"))
        artifacts (str (io/file root "artifacts"))]
    (.mkdirs (io/file src))
    (make-store! src "mathlib")
    (try (f root src artifacts)
         (finally (delete-dir root)))))

(deftest pack-serve-fetch-roundtrip
  (with-fixture
    (fn [root src artifacts]
      (let [d (pack/pack! src artifacts :id "mathlib-v0.0.1-test-f1")
            out (io/file artifacts (:store/id d))
            server (serve! artifacts {})
            base (str "http://127.0.0.1:" (.getPort (.getAddress server)))
            ;; the index carries exactly what pack! wrote for it
            entry (get-in (edn/read-string (slurp (io/file out "index-entry.edn")))
                          ["mathlib" store/store-format])
            index {:base base :stores {"mathlib" {store/store-format entry}}}
            data-root (str (io/file root "data"))]
        (try
          (testing "pack! writes one part per store component, each with its size and checksum"
            (is (= #{"blobs.tar.gz" "meta.tar.gz"} (set (map :file (:parts d)))))
            (is (every? #(and (pos? (:size %)) (= 64 (count (:sha256 %)))) (:parts d)))
            (is (= "mathlib-v0.0.1-test-f1" (:store/id d)))
            (is (= store/store-format (:store/format d))))

          (with-redefs [store/data-root (fn [] data-root)]
            (testing "a fetched store is a store: same declarations, readable manifest"
              (let [path (fetch/fetch! "mathlib" :index index :verbose? false)
                    sm (storage/open-store path)]
                (try
                  (is (= (str (io/file data-root "mathlib")) path))
                  (is (= store/store-format (:store/format (store/check-format! path))))
                  (is (= (count (storage/load-names sm "mathlib"))
                         (let [s2 (storage/open-store src)]
                           (try (count (storage/load-names s2 "mathlib"))
                                (finally (storage/close-store s2)))))
                      "every declaration came through")
                  (finally (storage/close-store sm)))))

            (testing "an existing store is never overwritten, and ensure-store! just finds it"
              (is (thrown-with-msg? Exception #"already exists" (fetch/fetch! "mathlib" :index index :verbose? false)))
              (is (= (str (io/file data-root "mathlib")) (fetch/ensure-store! "mathlib" :index index :verbose? false))))

            (testing "ANSATZ_OFFLINE refuses to fetch what is not there"
              (with-redefs [fetch/read-index (fn [] index)]
                (delete-dir (str (io/file data-root "mathlib")))
                (with-redefs [fetch/fetch! (fn [& _] (throw (ex-info "ANSATZ_OFFLINE is set" {})))]
                  (is (thrown-with-msg? Exception #"OFFLINE" (fetch/ensure-store! "mathlib")))))))
          (finally (.stop server 0)))))))

(deftest resumes-and-verifies
  (with-fixture
    (fn [root src artifacts]
      (let [d (pack/pack! src artifacts :id "mathlib-v0.0.1-test-f1")
            out (io/file artifacts (:store/id d))
            entry (get-in (edn/read-string (slurp (io/file out "index-entry.edn")))
                          ["mathlib" store/store-format])
            data-root (str (io/file root "data"))
            blobs (first (filter #(= "blobs.tar.gz" (:file %)) (:parts d)))]
        (with-redefs [store/data-root (fn [] data-root)]
          (testing "a download cut short is resumed on the next call, not restarted"
            (let [half (quot (:size blobs) 2)
                  s1 (serve! artifacts {:truncate half})
                  index1 {:base (str "http://127.0.0.1:" (.getPort (.getAddress s1))) :stores {"mathlib" {store/store-format entry}}}]
              (try (is (thrown? Exception (fetch/fetch! "mathlib" :index index1 :verbose? false)))
                   (finally (.stop s1 0)))
              (let [part (io/file data-root ".mathlib.fetch" (:store/id d) "blobs.tar.gz")]
                (is (.exists part) "the partial part survives for the next attempt")
                (is (< 0 (.length part) (:size blobs)))
                (let [s2 (serve! artifacts {})
                      index2 {:base (str "http://127.0.0.1:" (.getPort (.getAddress s2))) :stores {"mathlib" {store/store-format entry}}}]
                  (try (is (= (str (io/file data-root "mathlib"))
                              (fetch/fetch! "mathlib" :index index2 :verbose? false)))
                       (finally (.stop s2 0)))))))

          (testing "a server that ignores Range restarts the part rather than corrupting it"
            (delete-dir (str (io/file data-root "mathlib")))
            (let [s (serve! artifacts {:ignore-range? true})
                  index {:base (str "http://127.0.0.1:" (.getPort (.getAddress s))) :stores {"mathlib" {store/store-format entry}}}
                  part (io/file data-root ".mathlib.fetch" (:store/id d) "blobs.tar.gz")]
              (.mkdirs (.getParentFile part))
              (spit part "not the real bytes")
              (try (is (= (str (io/file data-root "mathlib")) (fetch/fetch! "mathlib" :index index :verbose? false)))
                   (finally (.stop s 0)))))

          (testing "a corrupted part is rejected by its checksum and removed"
            (delete-dir (str (io/file data-root "mathlib")))
            (let [bad (assoc entry :parts (mapv #(assoc % :sha256 (apply str (repeat 64 "0"))) (:parts entry)))
                  s (serve! artifacts {})
                  index {:base (str "http://127.0.0.1:" (.getPort (.getAddress s))) :stores {"mathlib" {store/store-format bad}}}]
              (try
                (is (thrown-with-msg? Exception #"checksum mismatch" (fetch/fetch! "mathlib" :index index :verbose? false)))
                (is (not (.exists (io/file data-root "mathlib"))) "nothing is installed")
                (is (not (.exists (io/file data-root ".mathlib.fetch" (:store/id d) "blobs.tar.gz"))))
                (finally (.stop s 0)))))

          (testing "a store of another format is not offered to this build"
            (is (nil? (fetch/entry {:stores {"mathlib" {(inc store/store-format) entry}}} "mathlib")))
            (let [s (serve! artifacts {})
                  index {:base (str "http://127.0.0.1:" (.getPort (.getAddress s)))
                         :stores {"mathlib" {(inc store/store-format) entry}}}]
              (try (is (thrown-with-msg? Exception #"no published store" (fetch/fetch! "mathlib" :index index :verbose? false)))
                   (finally (.stop s 0))))))))))

(deftest archive-roundtrip-is-deterministic
  (let [root (temp-dir)]
    (try
      (let [src (io/file root "s")]
        (.mkdirs (io/file src "a" "b"))
        (spit (io/file src "a" "one.txt") "one")
        (spit (io/file src "a" "b" "two.txt") "two")
        (spit (io/file src "top.edn") "{:a 1}")
        (let [t1 (io/file root "1.tar.gz") t2 (io/file root "2.tar.gz")]
          (archive/pack! src t1 ["a" "top.edn"])
          (Thread/sleep 1100)                               ; a different mtime must not change the bytes
          (spit (io/file src "a" "one.txt") "one")
          (archive/pack! src t2 ["a" "top.edn"])
          (is (= (seq (Files/readAllBytes (.toPath t1))) (seq (Files/readAllBytes (.toPath t2))))
              "packing the same store twice gives the same bytes")
          (let [dest (io/file root "out")
                r (archive/unpack! t1 dest)]
            (is (= 3 (:files r)))
            (is (= "one" (slurp (io/file dest "a" "one.txt"))))
            (is (= "two" (slurp (io/file dest "a" "b" "two.txt"))))
            (is (= "{:a 1}" (slurp (io/file dest "top.edn")))))))
      (finally (delete-dir root)))))
