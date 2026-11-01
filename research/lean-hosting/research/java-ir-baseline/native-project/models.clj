(ns native-project-entry-models-v1
  "Pure admission/rejection models. The genuine native/Java execution receipt is
   separate; these models do not fabricate native compiler or kernel authority."
  (:require [clojure.test :refer [deftest is run-tests]]
            [native-project-entry-v1 :as entry])
  (:import [java.nio.file Path] [java.nio.charset StandardCharsets]))
(deftest utf8-capture-is-exact-not-replacement-decoded
  (doseq [text ["" "Hello, world!\n" "λ"]]
    (is (= text (#'entry/text! (.getBytes ^String text StandardCharsets/UTF_8)))))
  (is (thrown? Exception (#'entry/text! (byte-array [-1])))))
(deftest json-nesting-rejects-before-recursive-reader
  (is (= {"text" "[{}]"} (#'entry/json! "{\"text\":\"[{}]\"}")))
  (is (thrown? Exception (#'entry/json! (str (apply str (repeat 257 "[")) "0" (apply str (repeat 257 "]")))))))
(deftest typed-name-components-do-not-collapse-to-display-authority
  (is (= "Main.main" (#'entry/label ["str" ["str" ["anonymous"] "Main"] "main"])))
  (is (not= (#'entry/module-name "Main.main") ["str" ["anonymous"] "Main.main"]))
  (doseq [wire [nil ["str" nil "main"] ["num" ["anonymous"] "0"]]]
    (is (thrown? Exception (#'entry/label wire)))))
(deftest relative-artifact-paths-cannot-escape-before-filesystem-read
  (let [root (Path/of "/native-artifact-model" (make-array String 0))]
    (doseq [relative ["../outside" "/absolute" "a/../b" ""]]
      (is (thrown? Exception (#'entry/path! root relative))))))
(deftest source-profile-is-finite-and-execution-pin-is-distinct-from-type-proof
  (is (= #{"Greeting.Basic" "Greeting" "Main"} (set (keys entry/source-pins))))
  (is (every? #(boolean (re-matches #"[0-9a-f]{64}" %)) (vals entry/source-pins)))
  (is (boolean (re-matches #"[0-9a-f]{64}" entry/execution-pin)))
  (is (not= entry/exporter-pin entry/execution-pin)))
(deftest unissued-artifacts-and-runs-carry-no-execution-authority
  (doseq [value [nil {} {:accepted true} (entry/->Artifact) (entry/->Run)]]
    (is (thrown? Exception (entry/execute-io-unit! value)))
    (is (thrown? Exception (entry/owner-packet value)))))
(defn check! [] (run-tests 'native-project-entry-models-v1))
