(ns ansatz-lean-jvm-extended-entry-checks
  "Policy models only. Synthetic representation maps are not native evidence,
   do not authenticate a producer, and never issue a build/artifact receipt."
  (:require [clojure.test :refer [deftest is run-tests]]
            [ansatz.lean.jvm.entry :as entry]))
(defn- rejected? [f] (try (f) false (catch clojure.lang.ExceptionInfo _ true)))
(defn- descriptor [type] {"arguments" [] "result" type "effect" "pure"})
(defn- observation [type lane]
  {"algorithm" "Lean.Compiler.LCNF.toLCNFType/toMonoType/toImpureType"
   "types" [{"type" type "irType" lane}]})
(defn- representation! [descriptor observation] (#'entry/representation! descriptor observation))
(deftest explicit-scalar-lanes-and-word-profile
  (doseq [bits [8 16 32 64] signed [false true]]
    (let [type {"kind" "machine-int" "bits" bits "signed" signed} lane (str "uint" bits)]
      (is (nil? (representation! (descriptor type) (observation type lane))))
      (is (rejected? #(representation! (descriptor type) (observation type "object"))))))
  (doseq [[type lane] [[{"kind" "word" "signed" false} "usize"]
                      [{"kind" "word" "signed" true} "usize"]
                      [{"kind" "float" "bits" 32} "float32"]
                      [{"kind" "float" "bits" 64} "float"]
                      [{"kind" "char"} "uint32"]]]
    (is (nil? (representation! (descriptor type) (observation type lane))))
    (is (rejected? #(representation! (descriptor type) (observation type "uint64"))))))
(deftest exact-native-representation-set-required
  (let [type {"kind" "float" "bits" 32} d (descriptor type) valid (observation type "float32")]
    (doseq [changed [nil {} (assoc valid "algorithm" "host-layout")
                     (assoc valid "types" [])
                     (update valid "types" #(conj % (first %)))
                     (assoc-in valid ["types" 0 "irType"] "float")
                     (assoc-in valid ["types" 0 "extra"] true)
                     (assoc valid "trusted" true)]]
      (is (rejected? #(representation! d changed))))))
(deftest special-buffers-are-not-constructor-families
  (doseq [type [{"kind" "bytes"} {"kind" "array" "element" {"kind" "nat"}}]]
    (is (nil? (representation! (descriptor type) (observation type "object")))))
  (let [element {"kind" "machine-int" "bits" 8 "signed" false}
        array {"kind" "array" "element" element}
        d (descriptor array) valid {"algorithm" "Lean.Compiler.LCNF.toLCNFType/toMonoType/toImpureType"
                                  "types" [{"type" array "irType" "object"}
                                           {"type" element "irType" "uint8"}]}]
    (is (nil? (representation! d valid)))
    (is (rejected? #(representation! d (update valid "types" pop))))))
(deftest old-core-only-v2-observation-remains-optional
  (let [d (descriptor {"kind" "nat"})]
    (is (nil? (representation! d nil)))
    (is (nil? (representation! d {"algorithm" "Lean.Compiler.LCNF.toLCNFType/toMonoType/toImpureType" "types" []})))
    (is (rejected? #(representation! d (observation {"kind" "char"} "uint32"))))))
(deftest sum-except-traverse-nested-special-types
  (let [leaf {"kind" "float" "bits" 64}
        d {"arguments" [{"kind" "sum" "left" {"kind" "nat"} "right" leaf}]
           "result" {"kind" "except" "error" {"kind" "string"} "value" {"kind" "array" "element" leaf}}
           "effect" "io"}
        types (#'entry/special-types (get d "result"))
        array (get-in d ["result" "value"])]
    (is (= #{leaf array} types))
    (is (nil? (representation! d {"algorithm" "Lean.Compiler.LCNF.toLCNFType/toMonoType/toImpureType"
                                 "types" [{"type" leaf "irType" "float"} {"type" array "irType" "object"}]})))
    (is (rejected? #(representation! d (observation leaf "float"))))))
(deftest new-producer-pairs-require-explicit-admission
  (is (= 2 (entry/schema-for-pins! (get-in entry/cohorts [2 :source]) (get-in entry/cohorts [2 :binary]))))
  (is (rejected? #(entry/schema-for-pins! (apply str (repeat 64 "0")) (get-in entry/cohorts [2 :binary])))))
(defn check! [] (run-tests 'ansatz-lean-jvm-extended-entry-checks))
