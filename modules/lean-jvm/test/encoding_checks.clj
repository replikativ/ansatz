(ns ansatz-lean-jvm-encoding-checks
  (:require [clojure.test :refer [deftest is run-tests]]
            [ansatz.lean.jvm.compiler.encoding :as encoding]))
(defn rejected? [f] (try (f) false (catch Exception _ true)))
(deftest exactly-one-json-value-with-only-json-trailing-whitespace
  (doseq [suffix ["" " " "\t" "\n" "\r" " \t\n\r"]]
    (is (= {} (encoding/json! (str "{}" suffix)))))
  (doseq [text ["{} {}" "{}\n{}" "true false" "[]garbage" "{}\u00a0" "{}\f" "{}\u000b"]]
    (is (rejected? #(encoding/json! text)))))
(deftest bounded-depth-and-exact-utf8
  (is (= "λ\u0000😀" (encoding/text! (.getBytes "λ\u0000😀" "UTF-8"))))
  (is (rejected? #(encoding/text! (byte-array [(unchecked-byte 0xff)]))))
  (is (rejected? #(encoding/json! (str (apply str (repeat 257 "[")) "0" (apply str (repeat 257 "]")))))))
(defn check! [] (run-tests 'ansatz-lean-jvm-encoding-checks))
