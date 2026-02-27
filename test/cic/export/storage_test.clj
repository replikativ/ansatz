(ns cic.export.storage-test
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [cic.export.storage :as storage]
            [cic.export.parser :as parser]
            [cic.kernel.env :as env]
            [cic.kernel.name :as name])
  (:import [cic.kernel Name ConstantInfo Env]
           [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(def example-file "/home/christian-weilbach/Development/lean4export/examples/Nat.add_succ.ndjson")

(defn- temp-dir []
  (str (Files/createTempDirectory "cic-storage-test"
                                   (into-array FileAttribute []))))

(defn- delete-dir-recursive [^String path]
  (let [f (File. path)]
    (when (.exists f)
      (doseq [child (.listFiles f)]
        (if (.isDirectory child)
          (delete-dir-recursive (.getPath child))
          (.delete child)))
      (.delete f))))

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
