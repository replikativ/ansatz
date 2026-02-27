(ns cic.export.replay-test
  (:require [clojure.test :refer [deftest testing is]]
            [cic.export.replay :as replay]
            [cic.export.parser :as parser]
            [cic.kernel.name :as name]
            [cic.kernel.env :as env]))

(def example-file "/home/christian-weilbach/Development/lean4export/examples/Nat.add_succ.ndjson")

(deftest replay-nat-add-succ-test
  (testing "Replay Nat.add_succ example"
    (let [st (parser/parse-ndjson-file example-file)
          result (replay/replay (:decls st) :verbose? true)]
      (println "\nStats:" (:stats result))
      (when (pos? (:errors (:stats result)))
        (replay/summarize-errors (:results result)))
      (testing "environment is populated"
        (is (some? (env/lookup (:env result) (name/from-string "Nat"))))
        (is (some? (env/lookup (:env result) (name/from-string "Nat.add_succ"))))))))
