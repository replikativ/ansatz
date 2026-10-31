(ns original-extern-bootstrap-checks-v1
  "Pure backend/ABI/inventory models. No actual receipt, Program, VM or source grant."
  (:require [clojure.test :refer [deftest is]] [clojure.java.io :as io]
            [clojure.data.json :as json] [original-extern-bootstrap-v1 :as b]))
(def directory (io/file (.getParentFile (io/file *file*)) "../data/externs"))
(defn- backend [s] ["str" ["anonymous"] s])
(defn- standard [target symbol] {"standard" {"backend" (backend target) "fn" symbol}})
(defn- row [entries] {"ir" {"extern" {"ext" {"entries" entries}}}})
(deftest backend-selection-matches-first-supported-c-or-all-entry
  (is (= {:status :standard :symbol "selected"}
         (#'b/selected-extern (row [(standard "llvm" "ignored") (standard "c" "selected") (standard "all" "later")]))))
  (is (= :inline-backend (:status (#'b/selected-extern (row [{"inline" {"backend" (backend "all") "code" "ignored"}} (standard "c" "later")])))))
  (is (= :unsupported-backend (:status (#'b/selected-extern (row [(standard "llvm" "not-c")])))))
  (is (thrown? clojure.lang.ExceptionInfo (#'b/selected-extern (row [{"standard" {} "inline" {}}])))))
(deftest overloads-preserve-borrow-result-and-raw-lane-identity
  (let [s {:symbol "same" :parameters ["tobject"] :borrowed [false] :result "object"}]
    (is (= (#'b/abi-key s) (#'b/abi-key (into {} s))))
    (doseq [other [(assoc s :parameters ["tagged"]) (assoc s :borrowed [true])
                   (assoc s :result "tobject") (assoc s :symbol "other")]]
      (is (not= (#'b/abi-key s) (#'b/abi-key other))))))
(deftest complete-fixture-has-unique-typed-names-and-full-original-abi-metadata
  (let [manifest (json/read-str (slurp (io/file directory "manifest.json")))
        rows (with-open [r (io/reader (io/file directory "extern-rows.jsonl"))]
               (mapv json/read-str (line-seq r)))]
    (is (= 961 (count rows) (get manifest "extern-row-count")))
    (is (= 961 (count (set (map #(get % "name") rows)))))
    (is (every? #(= (get % "name") (get-in % ["row" "ir" "extern" "f"])) rows))
    (is (every? #(and (= #{"extern"} (set (keys (get-in % ["row" "ir"]))))
                     (re-matches #"[0-9a-f]{64}" (get % "sha256"))) rows))
    (is (every? #(every? boolean? (map (fn [x] (get x "borrow")) (get-in % ["row" "ir" "extern" "xs"]))) rows))))
