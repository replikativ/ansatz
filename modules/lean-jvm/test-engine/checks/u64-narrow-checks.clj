(ns java-ir-u64-narrow-checks
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-u64-narrow-runtime/")
(defn context []
  (let [rows (mapv #(get % "row") (json/read-str (slurp (str directory "original-rows.json"))))
        box (c/decl "narrow-box" [(c/p 1 "uint64")] "object"
              (c/let-ir 2 "object" {:box {:ty "uint64" :x {:idx 1}}} (c/ret 2)))]
    (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(into rows (x/raw [box]))]))))
(deftest pinned-original-abi-and-native-cast-oracle
  (let [p (json/read-str (slurp (str directory "provenance.json")))
        rows (json/read-str (slurp (str directory "original-rows.json")))]
    (is (= 2 (count rows)))
    (is (= (get p "fixture-sha256") (corpus/sha256 (str directory "original-rows.json"))))
    (is (= (get-in p ["native-oracle" "source-sha256"]) (corpus/sha256 (str directory "NarrowOracle.c"))))
    (is (= (get-in p ["native-oracle" "vectors-sha256"]) (corpus/sha256 (str directory "native-vectors.json"))))
    (is (= ["uint64"] (mapv #(get % "ty") (get-in (first rows) ["row" "ir" "extern" "xs"]))))
    (is (= "uint32" (get-in (first rows) ["row" "ir" "extern" "type"])))))
(deftest raw-and-original-boxed-wrapper-match-native-cast
  (let [ctx (context) engine (j/machine ctx)
        vectors (json/read-str (slurp (str directory "native-vectors.json")))]
    (try
      (is (= 8 (count vectors)))
      (doseq [[input expected] vectors
              :let [input (biginteger input) expected (biginteger expected)
                    boxed (j/call ctx engine "narrow-box" [input])]]
        (is (= expected (j/call ctx engine "UInt64.toUInt32" [input])))
        (is (= expected (j/call ctx engine "UInt64.toUInt32._boxed" [boxed])))
        (is (= 0 (c/rc ctx boxed))))
      (finally (j/close! ctx engine)))))
(deftest invalid-public-scalar-lanes-reject-before-entry
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [value [-1 (.shiftLeft java.math.BigInteger/ONE 64) 1.5]]
        (is (re-find #"[Uu]nsigned scalar" (c/failure #(j/call ctx engine "UInt64.toUInt32" [value]))))
        (is (= "idle" (j/phase ctx engine))))
      (finally (j/close! ctx engine)))))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-u64-narrow-checks)))
