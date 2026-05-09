(ns ansatz.tools.kernel-trace-test
  (:require [clojure.edn :as edn]
            [ansatz.tools.kernel-trace :as kt]
            [clojure.test :refer [deftest is testing]]
            [clojure.java.io :as io]))

(defn- write-lines! [path lines]
  (with-open [w (io/writer path)]
    (doseq [line lines]
      (.write w line)
      (.write w "\n"))))

(deftest compare-traces-reports-first-mismatch
  (testing "compare-traces ignores non-event rows and reports mismatch indices"
    (let [left (str (System/getProperty "java.io.tmpdir") "/kernel-trace-left.jsonl")
          right (str (System/getProperty "java.io.tmpdir") "/kernel-trace-right.jsonl")]
      (write-lines! left
                    ["{\"decl\":\"Foo\"}"
                     "{\"s\":0,\"d\":1,\"l\":\"A\",\"r\":\"A\",\"res\":true,\"by\":\"quick\"}"
                     "{\"binding_domain\":\"check\"}"
                     "{\"s\":1,\"d\":2,\"l\":\"B\",\"r\":\"C\",\"res\":false,\"by\":\"fail\"}"])
      (write-lines! right
                    ["{\"decl\":\"Foo\"}"
                     "{\"s\":0,\"d\":1,\"l\":\"A\",\"r\":\"A\",\"res\":true,\"by\":\"quick\"}"
                     "{\"s\":1,\"d\":2,\"l\":\"B\",\"r\":\"D\",\"res\":false,\"by\":\"fail\"}"])
      (let [result (kt/compare-traces left right 5 1)]
        (is (= 1 (:common-prefix result)))
        (is (= 1 (:mismatch-count result)))
        (is (= [1] (:mismatch-indices result)))
        (is (= {:d 2 :l "B" :r "C" :res false :by "fail"}
               (get-in result [:first-mismatch :left])))
        (is (= {:d 2 :l "B" :r "D" :res false :by "fail"}
               (get-in result [:first-mismatch :right])))))))

(deftest compare-traces-semantic-skips-reflexive-quick-events
  (testing "semantic compare treats reflexive quick successes as epsilon events"
    (let [left (str (System/getProperty "java.io.tmpdir") "/kernel-trace-left.jsonl")
          right (str (System/getProperty "java.io.tmpdir") "/kernel-trace-right.jsonl")]
      (write-lines! left
                    ["{\"decl\":\"Foo\"}"
                     "{\"s\":0,\"d\":1,\"l\":\"A\",\"r\":\"A\",\"res\":true,\"by\":\"quick\"}"
                     "{\"s\":1,\"d\":2,\"l\":\"B\",\"r\":\"B\",\"res\":true,\"by\":\"quick\"}"
                     "{\"s\":2,\"d\":2,\"l\":\"C\",\"r\":\"D\",\"res\":false,\"by\":\"fail\"}"])
      (write-lines! right
                    ["{\"decl\":\"Foo\"}"
                     "{\"s\":0,\"d\":1,\"l\":\"A\",\"r\":\"A\",\"res\":true,\"by\":\"quick\"}"
                     "{\"s\":1,\"d\":2,\"l\":\"C\",\"r\":\"D\",\"res\":false,\"by\":\"fail\"}"])
      (let [result (kt/compare-traces-semantic left nil right nil 5 1)]
        (is (true? (get-in result [:semantic :matched-all?])))
        (is (= 1 (get-in result [:semantic :skipped-left])))
        (is (= 0 (get-in result [:semantic :skipped-right])))
        (is (nil? (:first-mismatch result)))))))

(deftest compare-traces-semantic-normalizes-fvars
  (testing "semantic compare normalizes kernel fresh variable names"
    (let [left (str (System/getProperty "java.io.tmpdir") "/kernel-trace-left.jsonl")
          right (str (System/getProperty "java.io.tmpdir") "/kernel-trace-right.jsonl")]
      (write-lines! left
                    ["{\"s\":0,\"d\":1,\"l\":\"fvar(_kernel_fresh.10)\",\"r\":\"T\",\"res\":true,\"by\":\"lazy_delta\"}"])
      (write-lines! right
                    ["{\"s\":0,\"d\":1,\"l\":\"fvar(_kernel_fresh.99)\",\"r\":\"T\",\"res\":true,\"by\":\"lazy_delta\"}"])
      (let [result (kt/compare-traces-semantic left nil right nil 5 1)]
        (is (true? (get-in result [:semantic :matched-all?])))
        (is (nil? (:first-mismatch result)))))))

(deftest compare-traces-semantic-preserves-hard-mismatch
  (testing "semantic compare still reports non-trivial mismatches"
    (let [left (str (System/getProperty "java.io.tmpdir") "/kernel-trace-left.jsonl")
          right (str (System/getProperty "java.io.tmpdir") "/kernel-trace-right.jsonl")]
      (write-lines! left
                    ["{\"s\":0,\"d\":1,\"l\":\"A\",\"r\":\"A\",\"res\":true,\"by\":\"quick\"}"
                     "{\"s\":1,\"d\":2,\"l\":\"B\",\"r\":\"C\",\"res\":false,\"by\":\"fail\"}"])
      (write-lines! right
                    ["{\"s\":0,\"d\":1,\"l\":\"B\",\"r\":\"D\",\"res\":false,\"by\":\"fail\"}"])
      (let [result (kt/compare-traces-semantic left nil right nil 5 1)]
        (is (false? (get-in result [:semantic :matched-all?])))
        (is (= {:d 2 :l "B" :r "C" :res false :by "fail"}
               (get-in result [:first-mismatch :left])))
        (is (= {:d 1 :l "B" :r "D" :res false :by "fail"}
               (get-in result [:first-mismatch :right])))))))

(deftest compare-traces-semantic-accepts-compatible-truncation
  (testing "semantic compare accepts trace fields truncated at slightly different points"
    (let [left (str (System/getProperty "java.io.tmpdir") "/kernel-trace-left.jsonl")
          right (str (System/getProperty "java.io.tmpdir") "/kernel-trace-right.jsonl")]
      (write-lines! left
                    ["{\"s\":0,\"d\":1,\"l\":\"@(Long.Namespace.parseFir...\",\"r\":\"T\",\"res\":true,\"by\":\"lazy_delta\"}"])
      (write-lines! right
                    ["{\"s\":0,\"d\":1,\"l\":\"@(Long.Namespace.parseFirst...\",\"r\":\"T\",\"res\":true,\"by\":\"lazy_delta\"}"])
      (let [result (kt/compare-traces-semantic left nil right nil 5 1)]
        (is (true? (get-in result [:semantic :matched-all?])))
        (is (nil? (:first-mismatch result)))))))

(deftest compare-traces-semantic-normalizes-universe-max
  (testing "semantic compare normalizes common Lean universe max equalities"
    (let [left (str (System/getProperty "java.io.tmpdir") "/kernel-trace-left.jsonl")
          right (str (System/getProperty "java.io.tmpdir") "/kernel-trace-right.jsonl")]
      (write-lines! left
                    ["{\"s\":0,\"d\":1,\"l\":\"Sort(max (succ u_2) (succ u_1))\",\"r\":\"Sort(max (succ u_1) (succ u_2))\",\"res\":true,\"by\":\"quick\"}"
                     "{\"s\":1,\"d\":1,\"l\":\"Eq.{max 1 (succ u_9)}\",\"r\":\"Eq.{succ u_9}\",\"res\":true,\"by\":\"const_eq\"}"
                     "{\"s\":2,\"d\":1,\"l\":\"Sort(max (succ u_10) (succ u_9))\",\"r\":\"Sort(succ (max u_10 u_9))\",\"res\":true,\"by\":\"quick\"}"
                     "{\"s\":3,\"d\":1,\"l\":\"Sort(max (succ (max u_10 u_9)) (succ u_9))\",\"r\":\"Sort(succ (max u_10 u_9))\",\"res\":true,\"by\":\"quick\"}"])
      (write-lines! right
                    ["{\"s\":0,\"d\":1,\"l\":\"Sort(max (succ u_1) (succ u_2))\",\"r\":\"Sort(max (succ u_1) (succ u_2))\",\"res\":true,\"by\":\"quick\"}"
                     "{\"s\":1,\"d\":1,\"l\":\"Eq.{succ u_9}\",\"r\":\"Eq.{succ u_9}\",\"res\":true,\"by\":\"const_eq\"}"
                     "{\"s\":2,\"d\":1,\"l\":\"Sort(succ (max u_9 u_10))\",\"r\":\"Sort(succ (max u_9 u_10))\",\"res\":true,\"by\":\"quick\"}"
                     "{\"s\":3,\"d\":1,\"l\":\"Sort(succ (max u_9 u_10))\",\"r\":\"Sort(succ (max u_9 u_10))\",\"res\":true,\"by\":\"quick\"}"])
      (let [result (kt/compare-traces-semantic left nil right nil 5 1)]
        (is (true? (get-in result [:semantic :matched-all?])))
        (is (nil? (:first-mismatch result)))))))

(deftest source-mdata-mismatch-classifier-test
  (testing "source metadata mismatches are classified without changing semantic status"
    (let [result {:ansatz {:type-mdata 0
                           :value-mdata 0}
                  :semantic {:first-mismatch {:left {:l "fvar(_kernel_fresh.1)"
                                                     :r "mdata(fvar(_kernel_fresh.1))"
                                                     :res true
                                                     :by "quick_whnfcore"}}}}]
      (is (true? (#'kt/source-mdata-mismatch? result false)))
      (is (false? (#'kt/source-mdata-mismatch? result true)))
      (is (false? (#'kt/source-mdata-mismatch?
                   (assoc-in result [:ansatz :value-mdata] 1)
                   false))))))

(deftest trace-batch-manifest-parser-test
  (testing "batch manifests accept comments, blanks, and declaration/file rows"
    (let [path (str (System/getProperty "java.io.tmpdir") "/kernel-trace-manifest.txt")]
      (write-lines! path
                    ["# selected trace cases"
                     ""
                     "Foo.bar src/Foo.lean"
                     "Baz.quux\tMathlib/Baz.lean"])
      (is (= [{:decl "Foo.bar" :file "src/Foo.lean"}
              {:decl "Baz.quux" :file "Mathlib/Baz.lean"}]
             (#'kt/read-batch-manifest path))))))

(deftest trace-batch-summary-keeps-actionable-rows
  (testing "batch summaries drop full trace payloads but keep mismatches and classifications"
    (let [summary (kt/summarize-batch-result
                   {:total 3
                    :trace-comparable 3
                    :raw-length-ok 1
                    :semantic-ok 2
                    :lean-exit-ok 2
                    :source-mdata-mismatch 1
                    :errors 0
                    :results [{:decl "A"
                               :lean-file "A.lean"
                               :trace-comparable? true
                               :semantic-ok? true
                               :raw-length-ok? true
                               :lean-exit-ok? true}
                              {:decl "B"
                               :lean-file "B.lean"
                               :trace-comparable? true
                               :semantic-ok? true
                               :raw-length-ok? false
                               :lean-exit-ok? false
                               :lean {:events 7}
                               :ansatz {:events 5}
                               :semantic {:semantic {:skipped-left 2
                                                     :skipped-right 0}}}
                              {:decl "C"
                               :lean-file "C.lean"
                               :trace-comparable? true
                               :semantic-ok? false
                               :raw-length-ok? false
                               :lean-exit-ok? true
                               :source-mdata-mismatch? true
                               :lean {:events 10}
                               :ansatz {:events 8}
                               :semantic {:first-mismatch {:left {:l "mdata(x)"}
                                                           :right {:l "x"}}}}]})]
      (is (nil? (:results summary)))
      (is (= 1 (:semantic-with-reflexive-skips summary)))
      (is (= 1 (:lean-nonzero-exit summary)))
      (is (= 2 (:length-drift summary)))
      (is (= 17 (:lean-events summary)))
      (is (= 13 (:ansatz-events summary)))
      (is (= -4 (:net-event-delta summary)))
      (is (= 2 (:semantic-skipped-left summary)))
      (is (= 0 (:semantic-skipped-right summary)))
      (is (= [{:decl "B"
               :file "B.lean"
               :lean-events 7
               :ansatz-events 5
               :delta -2
               :skipped-left 2
               :skipped-right 0}
              {:decl "C"
               :file "C.lean"
               :lean-events 10
               :ansatz-events 8
               :delta -2
               :skipped-left 0
               :skipped-right 0}]
             (:largest-length-deltas summary)))
      (is (= ["C"] (mapv :decl (:bad-results summary))))
      (is (= 10 (get-in summary [:bad-results 0 :lean-events])))
      (is (true? (get-in summary [:bad-results 0 :source-mdata-mismatch?]))))))

(deftest trace-batch-curation-writes-promote-and-quarantine-files
  (testing "candidate curation promotes semantic matches and quarantines actionable failures"
    (let [dir (io/file (System/getProperty "java.io.tmpdir")
                       (str "kernel-trace-curation-" (System/nanoTime)))
          summary (#'kt/write-curation-files!
                   {:total 4
                    :trace-comparable 3
                    :raw-length-ok 1
                    :semantic-ok 2
                    :lean-exit-ok 2
                    :source-mdata-mismatch 1
                    :errors 1
                    :results [{:decl "A"
                               :lean-file "A.lean"
                               :trace-comparable? true
                               :semantic-ok? true
                               :raw-length-ok? true
                               :lean-exit-ok? true
                               :lean {:events 3}
                               :ansatz {:events 3}
                               :semantic {:semantic {:skipped-left 0
                                                     :skipped-right 0}}}
                              {:decl "B"
                               :lean-file "B.lean"
                               :trace-comparable? true
                               :semantic-ok? true
                               :raw-length-ok? false
                               :lean-exit-ok? false
                               :lean {:events 7}
                               :ansatz {:events 5}
                               :semantic {:semantic {:skipped-left 2
                                                     :skipped-right 0}}}
                              {:decl "C"
                               :lean-file "C.lean"
                               :trace-comparable? true
                               :semantic-ok? false
                               :raw-length-ok? false
                               :lean-exit-ok? true
                               :source-mdata-mismatch? true
                               :lean {:events 4}
                               :ansatz {:events 4}
                               :semantic {:first-mismatch {:left {:l "mdata(x)"}
                                                           :right {:l "x"}}}}
                              {:decl "D"
                               :lean-file "D.lean"
                               :error "boom"
                               :trace-comparable? false
                               :semantic-ok? false
                               :raw-length-ok? false
                               :source-mdata-mismatch? false}]}
                   (.getPath dir))
          promote (slurp (io/file dir "promote.tsv"))
          quarantine (slurp (io/file dir "quarantine.tsv"))
          persisted-summary (edn/read-string (slurp (io/file dir "summary.edn")))]
      (is (= 2 (:promoted summary)))
      (is (= 2 (:quarantined summary)))
      (is (= 1 (:promoted-with-warnings summary)))
      (is (re-find #"(?m)^A\tA\.lean$" promote))
      (is (re-find #"(?m)^B\tB\.lean$" promote))
      (is (not (re-find #"(?m)^C\tC\.lean$" promote)))
      (is (re-find #"(?m)^C\tC\.lean\tsource-mdata-mismatch" quarantine))
      (is (re-find #"(?m)^D\tD\.lean\terror" quarantine))
      (is (= (:promoted summary) (:promoted persisted-summary)))
      (is (= {:raw-length-drift 2
              :lean-nonzero-exit 1}
             (:warnings-by-kind summary))))))

(deftest trace-lean-command-selects-mathlib-lake-mode
  (testing "Mathlib files under a Lake root use direct lean with computed search path"
    (let [dir (io/file (System/getProperty "java.io.tmpdir") "kernel-trace-lake-root")]
      (.mkdirs dir)
      (write-lines! (.getPath (io/file dir "lakefile.lean")) ["import Lake"])
      (.mkdirs (io/file dir ".lake/build/lib/lean"))
      (.mkdirs (io/file dir ".lake/packages/batteries/.lake/build/lib/lean"))
      (is (= ["/tmp/lean" "-j1" "Mathlib/Data/Nat/Basic.lean"]
             (#'kt/trace-lean-command (.getPath dir) "Mathlib/Data/Nat/Basic.lean" "/tmp/lean")))
      (is (= ["/tmp/lake" "env" "lean" "-j1" "Mathlib/Data/Nat/Basic.lean"]
             (#'kt/trace-lean-command (.getPath dir) "Mathlib/Data/Nat/Basic.lean" "/tmp/lake")))
      (is (re-find #"kernel-trace-lake-root/.lake/build/lib/lean"
                   (get (#'kt/trace-lean-env (.getPath dir)
                                             "Mathlib/Data/Nat/Basic.lean"
                                             "/tmp/lean"
                                             "Foo.bar"
                                             "/tmp/out.jsonl")
                        "LEAN_PATH")))
      (is (= ["/tmp/lean" "-j1" "-R" "src" "src/Init/Data/Nat/Basic.lean"]
             (#'kt/trace-lean-command (.getPath dir) "src/Init/Data/Nat/Basic.lean" "/tmp/lean"))))))
