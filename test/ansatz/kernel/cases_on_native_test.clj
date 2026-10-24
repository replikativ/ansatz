(ns ansatz.kernel.cases-on-native-test
  "Full structural comparison to captured native819816 output. Input native CI
   carriers are assembled WITHOUT admission; this is not an imported Env certificate."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is]]
            [ansatz.export.parser :as parser]
            [ansatz.kernel.cases-on :as cases]
            [ansatz.kernel.constant-info :as ci])
  (:import [ansatz.kernel Env Name ConstantInfo TypeChecker]
           [java.security MessageDigest]))

(def fixture "ansatz/kernel/fixtures/cases_on/native.ndjson")
(defn resource-bytes [path]
  (with-open [stream (io/input-stream (or (io/resource path) (throw (ex-info "Missing native fixture" {:resource path}))))]
    (.readAllBytes stream)))
(def roots ["Colour" "Pair" "Box" "Sized" "Ping" "Pong" "Rose" "ChoiceProp" "UnsafeBox"])
(def limits {:pairs 1000000 :edges 4000000 :scalar-bytes 10000000 :items 1000000 :depth 256})

(deftest captured-native-definitions-match-complete-structural-fields
  (let [bytes (resource-bytes fixture)
        digest (format "%064x" (java.math.BigInteger. 1 (.digest (MessageDigest/getInstance "SHA-256") bytes)))
        _ (is (= "e99e7defd1f78debd454c07286b12c556357e23536a3dd1cb7a187524f5800ac" digest))]
    (parser/with-parser-state
      (parser/parse-ndjson-string (String. bytes java.nio.charset.StandardCharsets/UTF_8))
      (fn [state]
        (is (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (get-in state [:meta "lean" "githash"])))
        (let [selected (set (map #(Name/fromString (str "CasesOnOracle." % ".casesOn")) roots))
              declarations (:decls state)
              native (into {} (for [^ConstantInfo decl declarations :when (contains? selected (.name decl))]
                                [(.name decl) decl]))
              ;; No output is installed, so the generator cannot return a stored native answer.
              input (reduce (fn [^Env env ^ConstantInfo decl]
                              (if (contains? selected (.name decl)) env (.addConstant env decl)))
                            (Env.) declarations)]
          (is (= 9 (count native)))
          (doseq [root roots]
            (let [name (Name/fromString (str "CasesOnOracle." root))
                  generated (cases/make-declaration input name)
                  expected (get native (.name generated))]
              (is (nil? (.lookup input (.name generated))))
              (is (ci/full-equal-bounded? expected generated limits) root)
              (is (identical? generated (.lookup (TypeChecker/checkConstant input generated) (.name generated)))
                  (str root " generated definition checked relative to native unchecked carrier Env"))
              (is (ci/full-equal-bounded? generated (cases/make-declaration input name) limits)
                  (str root " repeated generation")))))))))
