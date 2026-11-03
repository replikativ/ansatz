(ns lake-corpus
  "Optional source/artifact checks for already built, pinned external callers."
  (:refer-clojure :exclude [run!])
  (:require [ansatz.lean.jvm :as lean] [clojure.java.io :as io])
  (:import [java.io ByteArrayOutputStream ByteArrayInputStream]
           [ansatz.lean.jvm LeanProject LeanChoice IOResult]))
(defn- check! [value] (when-not value (throw (ex-info "External Lake corpus mismatch" {}))))
(defn- exercise [label project]
  (case label
    :cli (do
           (let [result ^LeanChoice (.call ^LeanProject project "CliProbe.parse"
                                          (object-array [(java.util.Arrays/asList (into-array String ["--verbose" "input"]))]))]
             (check! (and (not (.isLeft result)) (true? (.value result)))))
           (check! (= {:ok true} (lean/call project "CliProbe.parse" ["--verbose" "input"])))
           (check! (= {:ok false} (lean/call project "CliProbe.parse" ["input"])))
           (check! (= {:error "invalid arguments"} (lean/call project "CliProbe.parse" ["--unknown" "input"])))
           (check! (= [[1 0] [2 3]] (lean/call project "CliProbe.matchNumbers" [1] [2 3]))))
    :fp-sort (do
               (let [result ^IOResult (.call ^LeanProject project "LakeTutorial.sortNats"
                                             (object-array [(java.util.Arrays/asList (into-array java.math.BigInteger [(biginteger 3) (biginteger 1) (biginteger 2)]))]))]
                 (check! (= [1 2 3] (.value result))))
               (check! (= [1 2 3] (:value (lean/call project "LakeTutorial.sortNats" [3 1 2]))))
               (check! (= [[1 2 3] [3 1 2]] (:value (lean/call project "LakeTutorial.sortAndOriginal" [3 1 2])))))))
(defn run!
  "CONFIG supplies :compiler, :cli-directory and :fp-sort-directory. Libraries
   must already be built; this runner issues no dependency update/build itself."
  [{:keys [compiler cli-directory fp-sort-directory workloads]
    :or {workloads #{:cli :fp-sort}}}]
  (with-open [runtime (lean/open)]
    (mapv (fn [[label directory entries]]
            (let [_ (println "LAKE_CORPUS_BEGIN" label)
                  options {:compiler compiler :built-lake-workspace? true :root-module "App" :entries entries}
                  output (ByteArrayOutputStream.) start (System/nanoTime)
                  description (lean/prepare-project directory options output)
                  elapsed (/ (- (System/nanoTime) start) 1000000.0)
                  bytes (.toByteArray output)]
              (with-open [project (lean/load-artifact runtime (ByteArrayInputStream. bytes) (:manifest-sha256 description))]
                (exercise label project))
              (let [result {:workload label :prepared true :artifact-loaded true :executed true
                            :prepare-ms elapsed :artifact-bytes (alength bytes) :artifact description}]
                (println "LAKE_CORPUS_PASS" (pr-str result)) result)))
          (filter #(contains? workloads (first %))
                  [[:cli cli-directory ["CliProbe.parse" "CliProbe.matchNumbers"]]
                   [:fp-sort fp-sort-directory ["LakeTutorial.sortNats" "LakeTutorial.sortAndOriginal"]]]))))
