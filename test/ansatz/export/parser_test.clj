(ns ansatz.export.parser-test
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.export.parser :as parser]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name])
  (:import [java.util ArrayList]
           [ansatz.kernel ConstantInfo ExprStore Name]))

(def example-file "test-data/Nat.add_succ.ndjson")

(deftest parse-ndjson-file-test
  (testing "Parse Nat.add_succ.ndjson example"
    (let [st (parser/parse-ndjson-file example-file)]
      (testing "metadata is parsed"
        (is (some? (:meta st)))
        (is (= "lean4export" (get-in (:meta st) ["exporter" "name"]))))

      (testing "names are parsed"
        (is (> (.size ^ArrayList (:names st)) 50))
        (let [^Name nat-name (.get ^ArrayList (:names st) 1)]
          (is (= "Nat" (name/->string nat-name))))
        (let [^Name nat-zero (.get ^ArrayList (:names st) 2)]
          (is (= "Nat.zero" (name/->string nat-zero))))
        (let [^Name nat-succ (.get ^ArrayList (:names st) 3)]
          (is (= "Nat.succ" (name/->string nat-succ)))))

      (testing "levels are parsed"
        (is (> (.size ^ArrayList (:levels st)) 5)))

      (testing "expressions are parsed"
        (is (> (.size ^ExprStore (:exprs st)) 400)))

      (testing "declarations are parsed"
        (is (> (count (:decls st)) 10))

        (let [nat-decls (filter #(= "Nat" (.toString (.name ^ConstantInfo %))) (:decls st))]
          (is (= 1 (count nat-decls)))
          (is (.isInduct ^ConstantInfo (first nat-decls))))

        (let [zero-decls (filter #(= "Nat.zero" (.toString (.name ^ConstantInfo %))) (:decls st))]
          (is (= 1 (count zero-decls)))
          (is (.isCtor ^ConstantInfo (first zero-decls))))

        (let [succ-decls (filter #(= "Nat.succ" (.toString (.name ^ConstantInfo %))) (:decls st))]
          (is (= 1 (count succ-decls)))
          (is (.isCtor ^ConstantInfo (first succ-decls))))

        (let [rec-decls (filter #(= "Nat.rec" (.toString (.name ^ConstantInfo %))) (:decls st))]
          (is (= 1 (count rec-decls)))
          (is (.isRecursor ^ConstantInfo (first rec-decls)))
          (let [^ConstantInfo rec (first rec-decls)]
            (is (= 2 (alength (.rules rec))))
            (is (= 0 (.numParams rec)))
            (is (= 1 (.numMotives rec)))
            (is (= 2 (.numMinors rec)))))

        (let [thm-decls (filter #(= "Nat.add_succ" (.toString (.name ^ConstantInfo %))) (:decls st))]
          (is (= 1 (count thm-decls)))
          (is (.isThm ^ConstantInfo (first thm-decls))))))))

(deftest build-env-test
  (testing "Build environment from parsed declarations"
    (let [st (parser/parse-ndjson-file example-file)
          env (parser/build-env (:decls st))]
      (testing "Nat is in environment"
        (let [nat (env/lookup env (name/from-string "Nat"))]
          (is (some? nat))
          (is (env/induct? nat))))

      (testing "Nat.add_succ theorem is in environment"
        (let [thm (env/lookup env (name/from-string "Nat.add_succ"))]
          (is (some? thm))
          (is (env/thm? thm)))))))

(deftest load-ndjson-test
  (testing "Full load pipeline"
    (let [result (parser/load-ndjson example-file)]
      (is (some? (:env result)))
      (is (> (:num-decls result) 10))
      (is (> (:num-exprs result) 400))
      (println "Loaded:" (:num-decls result) "declarations,"
               (:num-names result) "names,"
               (:num-levels result) "levels,"
               (:num-exprs result) "expressions"))))

(def ^:private ownership-fixture
  (str "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"P\"}}\n"
       "{\"ie\":0,\"sort\":0}\n"
       "{\"axiom\":{\"name\":1,\"levelParams\":[],\"type\":0,\"isUnsafe\":false}}\n"))

(defn- with-tracked-parser-stores [f]
  (let [allocate parser/mk-parser-state
        states (atom [])]
    (try
      (with-redefs [parser/mk-parser-state
                    (fn []
                      (let [state (allocate)
                            ^ExprStore expressions (:exprs state)]
                        ;; An unused readable record distinguishes closure from a
                        ;; missing record when asserting resource ownership below.
                        (.storeBvar expressions 127 0)
                        (is (bytes? (.readRaw expressions 127)))
                        (swap! states conj state)
                        state))]
        (f states))
      (finally
        (doseq [state @states] (.close ^ExprStore (:exprs state)))))))

(defn- last-store [states] (:exprs (last @states)))

(deftest string-and-file-parse-failures-close-allocated-stores
  (let [file (java.io.File/createTempFile "ansatz-parser-failure-" ".ndjson")
        malformed (str ownership-fixture "not-json\n")]
    (try
      (spit file malformed)
      (doseq [parse [#(parser/parse-ndjson-string malformed)
                     #(parser/parse-ndjson-file (.getPath file))]]
        (with-tracked-parser-stores
          (fn [states]
            (is (thrown? Exception (parse)))
            (is (= 1 (count @states)))
            (is (thrown? Exception (.readRaw ^ExprStore (last-store states) 127))))))
      (finally (.delete file)))))

(deftest successful-string-and-file-parser-stores-remain-caller-owned
  (let [file (java.io.File/createTempFile "ansatz-parser-success-" ".ndjson")]
    (try
      (spit file ownership-fixture)
      (doseq [parse [#(parser/parse-ndjson-string ownership-fixture)
                     #(parser/parse-ndjson-file (.getPath file))]]
        (with-tracked-parser-stores
          (fn [states]
            (let [state (parse)]
              (is (= 1 (count (:decls state))))
              (is (identical? (:exprs state) (last-store states)))
              (is (bytes? (.readRaw ^ExprStore (:exprs state) 127)))))))
      (finally (.delete file)))))

(deftest raw-streaming-failures-close-unreturned-store-and-preserve-error
  (let [file (java.io.File/createTempFile "ansatz-parser-callback-" ".ndjson")]
    (try
      (spit file ownership-fixture)
      (doseq [parse [parser/parse-ndjson-file-streaming parser/parse-ndjson-file-streaming-raw]]
        (with-tracked-parser-stores
          (fn [states]
            (let [failure (AssertionError. "callback failed")]
              (is (identical? failure
                              (try (parse (.getPath file) nil (fn [& _] (throw failure)))
                                   (catch Throwable actual actual))))
              (is (thrown? Exception (.readRaw ^ExprStore (last-store states) 127)))))))
      (finally (.delete file)))))

(deftest raw-streaming-parse-failures-close-unreturned-store
  (let [file (java.io.File/createTempFile "ansatz-raw-parser-failure-" ".ndjson")]
    (try
      (spit file (str ownership-fixture "not-json\n"))
      (with-tracked-parser-stores
        (fn [states]
          (is (thrown? Exception (parser/parse-ndjson-file-streaming-raw (.getPath file) nil (fn [s _] s))))
          (is (thrown? Exception (.readRaw ^ExprStore (last-store states) 127)))))
      (finally (.delete file)))))

(deftest streaming-success-preserves-each-entrypoints-ownership-contract
  (let [file (java.io.File/createTempFile "ansatz-parser-stream-success-" ".ndjson")]
    (try
      (spit file ownership-fixture)
      (with-tracked-parser-stores
        (fn [states]
          (let [result (parser/parse-ndjson-file-streaming-raw (.getPath file) 0 (fn [n _] (inc n)))
                expressions (get-in result [:parser-state :exprs])]
            (is (= 1 (:final-state result)))
            (is (identical? expressions (last-store states)))
            (is (bytes? (.readRaw ^ExprStore expressions 127))))))
      (with-tracked-parser-stores
        (fn [states]
          (let [result (parser/parse-ndjson-file-streaming (.getPath file) 0 (fn [n _] (inc n)))]
            (is (= 1 (:final-state result)))
            (is (thrown? Exception (.readRaw ^ExprStore (last-store states) 127))))))
      (finally (.delete file)))))

(deftest raw-streaming-reader-close-failure-closes-unreturned-store
  (with-tracked-parser-stores
    (fn [states]
      (let [failure (java.io.IOException. "reader close failed")
            reader (proxy [java.io.BufferedReader] [(java.io.StringReader. ownership-fixture)]
                     (close [] (proxy-super close) (throw failure)))]
        (with-redefs [clojure.java.io/reader (fn [& _] reader)]
          (is (identical? failure
                          (try (parser/parse-ndjson-file-streaming-raw "fixture-reader" nil (fn [s _] s))
                               (catch Throwable actual actual)))))
        (is (thrown? Exception (.readRaw ^ExprStore (last-store states) 127)))))))

(deftest file-parser-reads-lines-without-slurping
  (let [file (java.io.File/createTempFile "ansatz-parser-lines-" ".ndjson")]
    (try
      (spit file (str "\n" ownership-fixture "  \n"))
      (with-redefs [clojure.core/slurp (fn [& _] (throw (AssertionError. "file parser must stream")))]
        (parser/with-parser-state
          (parser/parse-ndjson-file file)
          (fn [state]
            (is (= ["P"] (mapv #(str (.name ^ConstantInfo %)) (:decls state)))))))
      (finally (.delete file)))))
