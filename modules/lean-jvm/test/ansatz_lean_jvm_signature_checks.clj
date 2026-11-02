(ns ansatz-lean-jvm-signature-checks
  (:refer-clojure :exclude [type])
  (:require [clojure.test :refer [deftest is run-tests]]
            [ansatz.lean.jvm.signature :as signature]))
(defn- type [kind] {"kind" kind})
(defn- function-type [arguments result effect]
  {"arguments" arguments "result" result "effect" effect})
(defn- rejected? [value]
  (try (signature/validate! value) false
       (catch clojure.lang.ExceptionInfo error (= "UnsupportedSignature" (:code (ex-data error))))))

(deftest nary-application-and-nested-value-types
  (let [product {"kind" "product" "first" (type "bool") "second" (type "nat")}
        descriptor (function-type [(type "bool") (type "nat")] product "pure")
        expression (signature/expected-type descriptor)]
    (is (= descriptor (signature/validate! descriptor)))
    (is (= 2 (signature/arity descriptor) (signature/runtime-arity descriptor)))
    (is (= "forall" (first expression)))
    (is (= "forall" (first (nth expression 4))))
    (is (= "app" (first (nth (nth expression 4) 4)))))
  (let [descriptor (function-type [(type "int")]
                                 {"kind" "option" "element" {"kind" "list" "element" (type "string")}}
                                 "io")]
    (is (= 1 (signature/arity descriptor)))
    (is (= 2 (signature/runtime-arity descriptor)))
    (is (vector? (signature/expected-type descriptor))))
  (is (= 0 (signature/runtime-arity (function-type [] (type "unit") "pure")))))

(deftest legacy-profiles-and-io-world-are-explicit
  (doseq [profile ["nat-to-nat" "string-to-string" "io-unit"]]
    (is (= 1 (signature/runtime-arity (signature/from-legacy profile))))
    (is (vector? (signature/expected-type (signature/from-legacy profile)))))
  (is (= 0 (signature/arity (signature/from-legacy "io-unit"))))
  (is (= "io" (get (signature/from-legacy "io-unit") "effect"))))

(deftest unsupported-and-excessive-signatures-refuse-explicitly
  (doseq [descriptor [(function-type [(type "float")] (type "nat") "pure")
                      (function-type [(type "nat")] (type "nat") "callback")
                      (function-type (vec (repeat 65 (type "nat"))) (type "nat") "pure")
                      (assoc (function-type [] (type "nat") "pure") "trusted" true)
                      (function-type [] {"kind" "product" "first" (type "nat")} "pure")
                      (function-type [] {"kind" "nat" "bits" 64} "pure")
                      (function-type [] (reduce (fn [element _] {"kind" "list" "element" element})
                                                (type "nat") (range 33)) "pure")]]
    (is (rejected? descriptor)))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unknown legacy"
                        (signature/from-legacy "unknown"))))

(deftest scalar-buffer-and-sum-descriptors-have-exact-lean-types
  (let [cases (concat
               (for [bits [8 16 32 64] signed [false true]]
                 [{"kind" "machine-int" "bits" bits "signed" signed}
                  (str (if signed "Int" "UInt") bits)])
               [[{"kind" "word" "signed" false} "USize"]
                [{"kind" "word" "signed" true} "ISize"]
                [{"kind" "float" "bits" 32} "Float32"]
                [{"kind" "float" "bits" 64} "Float"]
                [(type "char") "Char"] [(type "bytes") "ByteArray"]])]
    (doseq [[result name] cases]
      (let [descriptor (function-type [] result "pure")]
        (is (= ["const" ["str" ["anonymous"] name] []]
               (signature/expected-type descriptor)))
        (is (= name (signature/display descriptor))))))
  (doseq [[result name] [[{"kind" "array" "element" (type "bool")} "Array"]
                         [{"kind" "sum" "left" (type "bool") "right" (type "nat")} "Sum"]
                         [{"kind" "except" "error" (type "string") "value" (type "unit")} "Except"]]]
    (let [descriptor (function-type [] result "pure")
          expression (signature/expected-type descriptor)
          head (loop [e expression] (if (= "app" (first e)) (recur (second e)) e))]
      (is (= name (last (second head))))
      (is (= descriptor (signature/validate! descriptor)))))
  (doseq [result [{"kind" "machine-int" "bits" 7 "signed" false}
                  {"kind" "machine-int" "bits" 64 "signed" 1}
                  {"kind" "word" "signed" nil}
                  {"kind" "float" "bits" 16}
                  {"kind" "char" "bits" 16}
                  {"kind" "bytes" "mutable" true}
                  {"kind" "sum" "left" (type "bool")}
                  {"kind" "except" "error" (type "string") "value" (type "closure")}]]
    (is (rejected? (function-type [] result "pure")))))

(defn check! [] (run-tests 'ansatz-lean-jvm-signature-checks))
