(ns ansatz.export.store-format-writer-test
  "Writer compatibility is enforced by the actual store registry, both for
   konserve derived values and PSS node blobs. Reader support stays independent."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.java.io :as io]
            [ansatz.store :as store]
            [ansatz.export.storage :as storage]
            [ansatz.export.codec :as codec]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as expr]
            [ansatz.kernel.level :as level]
            [ansatz.kernel.name :as name]
            [boring.core :as boring]
            [org.replikativ.persistent-sorted-set :as pss])
  (:import [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]
           [ansatz.kernel ConstantInfo]
           [ansatz.export.types CIShell]))

(def legacy-hints [:opaque :abbrev {:regular 1} {:regular 2147483647}])
(def extended-hints [{:regular 0} {:regular 2147483648} {:regular 4294967295}])

(defn- definition [hint]
  (env/mk-def (name/from-string "writerDefinition") []
              (expr/sort' (level/succ level/zero)) (expr/sort' level/zero) :hints hint))

(defn- delete-directory! [directory]
  (doseq [file (reverse (file-seq (io/file directory)))] (io/delete-file file)))

(defn- with-store [format f]
  (let [directory (.toFile (Files/createTempDirectory "ansatz-writer-format" (make-array FileAttribute 0)))]
    (try
      (when format (store/write-manifest! directory {:store/format format :branch "main"}))
      (let [sm (storage/open-store (.getPath directory))]
        (try (f sm directory)
             (finally (storage/close-store sm))))
      (finally (delete-directory! directory)))))

(defn- store-tree! [sm value]
  (let [tree (conj (pss/sorted-set* {:cmp storage/id-cmp :storage (:storage sm)
                                     :branching-factor 8 :ref-type :weak}) [0 value])]
    (pss/store tree)))

(defn- root-value [sm root]
  (let [tree (pss/restore-by storage/id-cmp root (:storage sm))]
    (second (pss/lookup tree [0 nil]))))

(deftest format-one-derived-writes-reject-extended-full-ci-hints
  (with-store 1
    (fn [sm directory]
      (is (= 1 (:write-format sm)))
      (doseq [hint extended-hints]
        (is (thrown? Exception (storage/write-derived! (:store sm) "main" [:unsupported hint]
                                                       {:nested [(definition hint)]}))))
      (doseq [hint legacy-hints]
        (storage/write-derived! (:store sm) "main" :legal (definition hint))
        (is (= hint (env/get-reducibility-hints (storage/read-derived (:store sm) "main" :legal)))))
      (is (= 1 (:store/format (store/read-manifest directory)))))))

(deftest format-one-pss-nodes-reject-extended-full-ci-hints
  (with-store 1
    (fn [sm directory]
      (doseq [hint extended-hints]
        (is (thrown? Exception (store-tree! sm (definition hint)))))
      (doseq [hint legacy-hints]
        (let [root (store-tree! sm (definition hint))]
          (storage/flush-writes! (:storage sm))
          (is (= hint (env/get-reducibility-hints (root-value sm root))))))
      (is (= 1 (:store/format (store/read-manifest directory)))))))

(deftest format-one-symbolic-shell-hints-and-ordinary-maps-remain-supported
  (with-store 1
    (fn [sm _]
      (doseq [hint extended-hints]
        (let [ci (definition hint)
              shell (CIShell. {:tag 1 :name (.name ^ConstantInfo ci) :lps [] :type-id 0 :value-id 1
                               :hints hint :safety :safe :all [(.name ^ConstantInfo ci)]})]
          (storage/write-derived! (:store sm) "main" :shell {:shell shell :ordinary-map hint})
          (let [restored (storage/read-derived (:store sm) "main" :shell)]
            (is (= hint (:ordinary-map restored)))
            (is (= (.data shell) (.data ^CIShell (:shell restored)))))
          (let [root (store-tree! sm shell)]
            (storage/flush-writes! (:storage sm))
            (is (= (.data shell) (.data ^CIShell (root-value sm root))))))))))

(deftest current-writer-supports-all-full-ci-hints-in-fresh-and-manifested-stores
  (doseq [format [nil 2]]
    (with-store format
      (fn [sm directory]
        (is (= 2 (:write-format sm)))
        (doseq [hint (concat legacy-hints extended-hints)]
          (storage/write-derived! (:store sm) "main" :exact (definition hint))
          (is (= hint (env/get-reducibility-hints (storage/read-derived (:store sm) "main" :exact))))
          (let [root (store-tree! sm (definition hint))]
            (storage/flush-writes! (:storage sm))
            (is (= hint (env/get-reducibility-hints (root-value sm root))))))
        (is (= format (:store/format (store/read-manifest directory))))))))

(deftest explicit-writer-options-preserve-manifest-and-reader-contracts
  (let [ci (definition {:regular 0})
        old-registry (codec/registry (constantly nil) {:write-format 1})
        new-registry (codec/registry (constantly nil) {:write-format 2})]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"require store format 2"
                          (boring/encode ci {:registry old-registry})))
    (testing "writer format 1 still reads format-2-capable full-CI bytes"
      (let [restored (boring/decode (boring/encode ci {:registry new-registry}) {:registry old-registry})]
        (is (= {:regular 0} (env/get-reducibility-hints restored)))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported store codec writer"
                          (codec/registry (constantly nil) {:write-format 3}))))
  (with-store 1
    (fn [_ directory]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cannot override"
                            (storage/open-store (.getPath directory) {:write-format 2})))
      (is (= 1 (:store/format (store/read-manifest directory)))))))

(deftest unmanifested-store-can-explicitly-select-the-legacy-writer
  (let [directory (.toFile (Files/createTempDirectory "ansatz-explicit-writer" (make-array FileAttribute 0)))]
    (try
      (let [sm (storage/open-store (.getPath directory) {:write-format 1})]
        (try
          (is (= 1 (:write-format sm)))
          (is (thrown? Exception (store-tree! sm (definition {:regular 0}))))
          (is (nil? (store/read-manifest directory)) "opening does not invent or relabel a manifest")
          (finally (storage/close-store sm))))
      (finally (delete-directory! directory)))))
