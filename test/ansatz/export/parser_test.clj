(ns ansatz.export.parser-test
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.export.parser :as parser]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name])
  (:import [java.util ArrayList]
           [ansatz.kernel ConstantInfo ExprStore Name]))

(def example-file "/home/christian-weilbach/Development/lean4export/examples/Nat.add_succ.ndjson")

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
