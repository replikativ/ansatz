(ns ansatz.store-test
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.store :as store]
            [ansatz.store.fetch :as fetch]
            [clojure.java.io :as io])
  (:import [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(defn- with-manifest [manifest f]
  (let [dir (.toFile (Files/createTempDirectory "ansatz-format" (make-array FileAttribute 0)))]
    (try
      (when manifest (store/write-manifest! dir manifest))
      (f (.getPath dir))
      (finally
        (io/delete-file (store/manifest-file dir) true)
        (io/delete-file dir)))))

(deftest reader-and-writer-versions-are-independent
  (is (= 2 store/write-format store/store-format))
  (doseq [format [1 2]]
    (with-manifest {:store/format format :branch "mathlib"}
      #(is (= format (:store/format (store/check-compatible! % {:branch "mathlib"}))))))
  (doseq [manifest [nil {:store/format 0} {:store/format 3} {}]]
    (with-manifest manifest #(is (thrown? clojure.lang.ExceptionInfo (store/check-format! %))))))

(deftest compatibility-is-explicit-and-does-not-mean-verification
  (let [m {:store/format 2 :branch "mathlib" :artifact/cohort "lean-4.33.1"
           :provenance {:lean/rev "abc" :library/tag "v4.33.1"}
           :store/capabilities #{:kernel :frontend}}]
    (is (empty? (store/compatibility-errors m {:provenance {:lean/rev "abc"}
                                               :store/capabilities #{:kernel}})))
    (doseq [requirements [{:branch "init"} {:store/format 1}
                          {:artifact/cohort "other"} {:provenance {:lean/rev "xyz"}}
                          {:store/capabilities #{:llvm}}]]
      (with-manifest m #(is (thrown? clojure.lang.ExceptionInfo
                                     (store/check-compatible! % requirements)))))
    (is (seq (store/compatibility-errors {} {:artifact/cohort "lean-4.33.1"})))
    (is (seq (store/compatibility-errors {} {:store/capabilities #{:frontend}})))
    (is (thrown? clojure.lang.ExceptionInfo (store/compatibility-errors m {:typo true})))
    (is (empty? (store/compatibility-errors (assoc m :verified true) {}))))
  (testing "existing named stores are checked rather than silently bypassing requirements"
    (with-manifest {:store/format 1 :branch "mathlib"}
      (fn [path]
        (with-redefs [store/resolve-existing (constantly path)]
          (is (= path (fetch/ensure-store! "mathlib")))
          (is (thrown? clojure.lang.ExceptionInfo
                       (fetch/ensure-store! "mathlib" :requirements {:branch "init"})))
          (is (thrown? clojure.lang.ExceptionInfo
                       (fetch/ensure-store! "mathlib" :requirements {:artifact/cohort "missing"}))))))))

(deftest discovery-keeps-published-legacy-stores-available
  (let [old {:id "old" :library/tag "v4.33.1"}
        new {:id "new" :provenance {:lean/rev "abc"}
             :artifact/cohort "cohort" :store/capabilities #{:frontend}}
        index {:stores {"mathlib" {1 old 2 new 3 {:id "future"}}}}]
    (is (= old (fetch/entry {:stores {"mathlib" {1 old}}} "mathlib")))
    (is (= new (fetch/entry index "mathlib")))
    (is (= old (fetch/entry index "mathlib" {:provenance {:library/tag "v4.33.1"}})))
    (is (= new (fetch/entry index "mathlib" {:provenance {:lean/rev "abc"}
                                             :store/capabilities #{:frontend}})))
    (is (nil? (fetch/entry index "mathlib" {:artifact/cohort "other"})))
    (is (nil? (fetch/entry index "mathlib" {:store/capabilities #{:llvm}})))
    (is (nil? (fetch/entry index "init")))))
