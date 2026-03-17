(ns ansatz.tactic.instance-test
  "Tests for typeclass instance synthesis."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.tactic.instance :as inst]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay])
  (:import [ansatz.kernel ConstantInfo]))

;; ============================================================
;; Environment setup
;; ============================================================

(def ^:private test-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (let [st (parser/parse-ndjson-file f)]
          (:env (replay/replay (:decls st))))))))

(defn- require-env [] (or @test-env (throw (ex-info "init-medium.ndjson not found" {}))))

(def ^:private test-index
  (delay (inst/build-instance-index (require-env))))

;; ============================================================
;; Basic instance lookup
;; ============================================================

(deftest test-get-instances
  (testing "Instance index has candidates for common classes"
    (let [idx @test-index]
      (is (seq (inst/get-instances idx (name/from-string "Add")))
          "Add should have instances")
      (is (seq (inst/get-instances idx (name/from-string "Decidable")))
          "Decidable should have instances")
      (is (seq (inst/get-instances idx (name/from-string "BEq")))
          "BEq should have instances"))))

;; ============================================================
;; Instance synthesis for Nat
;; ============================================================

(deftest test-synthesize-add-nat
  (testing "Synthesize Add Nat instance"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          nat (e/const' (name/from-string "Nat") [])
          goal (e/app (e/const' (name/from-string "Add") [lvl/zero]) nat)
          result (inst/synthesize* st env @test-index goal 0)]
      (is (some? result) "Should find Add Nat instance")
      (when result
        (is (e/const? (e/get-app-fn result))
            "Result should be a constant application")))))

(deftest test-synthesize-decidable-eq-nat
  (testing "Synthesize DecidableEq Nat"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          nat (e/const' (name/from-string "Nat") [])
          goal (e/app (e/const' (name/from-string "DecidableEq") [lvl/zero]) nat)
          result (inst/synthesize* st env @test-index goal 0)]
      (is (some? result) "Should find DecidableEq Nat instance"))))

;; ============================================================
;; TSV loading
;; ============================================================

(deftest test-load-instance-tsv
  (testing "Load instance registry from TSV"
    (let [tsv "resources/instances.tsv"]
      (when (.exists (java.io.File. tsv))
        (let [idx (inst/load-instance-tsv tsv)]
          (is (map? idx))
          (is (> (count idx) 1000) "TSV should have 1000+ classes")
          (is (seq (inst/get-instances idx (name/from-string "LE")))
              "LE should have instances from TSV"))))))

;; ============================================================
;; Negative tests
;; ============================================================

(deftest test-synthesize-nonexistent
  (testing "Synthesis fails for nonexistent class"
    (let [env (require-env)
          st (tc/mk-tc-state env)
          goal (e/app (e/const' (name/from-string "NonexistentClass") [lvl/zero])
                      (e/const' (name/from-string "Nat") []))]
      (is (nil? (inst/synthesize* st env @test-index goal 0))
          "Should return nil for unknown class"))))
