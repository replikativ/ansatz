(ns ansatz.clj-core-conformance-mathlib-test
  "The rows of the clojure.core contract table that need constants the bundled Init does not
   carry (Int.tdiv/Int.tmod, Float), run against the Mathlib store. Skipped without the store."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.clj-check :as cc]
            [ansatz.clj-contract :as contract]))

(def ^:private mathlib-store
  (delay ((requiring-resolve 'ansatz.store/resolve-existing) "mathlib")))

(defn- with-mathlib [f]
  (if-let [path @mathlib-store]
    (binding [a/*verbose* false]
      (a/init! (str path) "mathlib")
      (cc/run-setup! contract/setup-forms)
      (f))
    (println "  (skipping clj-core-conformance-mathlib-test — no mathlib store)")))

(use-fixtures :once fixtures/isolated-session with-mathlib)

(deftest rows-that-need-more-than-the-bundled-init
  (doseq [row contract/rows :when (seq (:requires row))]
    (let [result (cc/run-row row)
          {:keys [ok? why]} (cc/row-verdict row result)]
      (testing (str (:id row) " " (pr-str (:form row)))
        (is (not= :skipped (:status result)) (str (:id row) " still lacks " (:missing result)))
        (is ok? (str (:id row) ": " why))))))
