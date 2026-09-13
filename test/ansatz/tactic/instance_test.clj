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
            [ansatz.export.replay :as replay]
            [ansatz.config :as config]
            [ansatz.state :as state])
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

;; ============================================================
;; Lean's registry: order, selection, and which index a session uses
;; ============================================================

(deftest test-parse-instance-tsv-order
  (testing "Lean's try order: higher priority first, most recently declared first among equals"
    (let [idx (inst/parse-instance-tsv ["C\tearly\t1000" "C\tlow\t100" "C\tlate\t1000" "C\thigh\t2000"])]
      (is (= ["high" "late" "early" "low"]
             (mapv (comp str :name) (inst/get-instances idx (name/from-string "C")))))))
  (testing "a re-registered instance (a re-exporting module) is one instance, at its first registration"
    (let [idx (inst/parse-instance-tsv ["C\ta\t1000" "C\tb\t1000" "C\ta\t1000"])]
      (is (= ["b" "a"] (mapv (comp str :name) (inst/get-instances idx (name/from-string "C")))))))
  (testing "present? drops what the env does not have (a full-Init registry over a smaller tier)"
    (let [idx (inst/parse-instance-tsv ["C\ta\t1000" "C\tb\t1000" "D\tc\t1000"] #{"a" "c"})]
      (is (= ["a"] (mapv (comp str :name) (inst/get-instances idx (name/from-string "C")))))
      (is (= ["c"] (mapv (comp str :name) (inst/get-instances idx (name/from-string "D"))))))))

(deftest test-select-candidates-keys-on-the-carrier
  (testing "over the cap, only instances for the goal's carrier plus the generic ones survive
            (Lean's DiscrTree selection, one level deep)"
    (let [env (require-env)
          cands (mapv (fn [n] {:name (name/from-string n) :priority 1000})
                      ["Fin.instOfNat" "instOfNatNat" "BitVec.instOfNat" "Zero.toOfNat0"])
          goal (e/app* (e/const' (name/from-string "OfNat") [lvl/zero])
                       (e/const' (name/from-string "Nat") []) (e/lit-nat 5))]
      (binding [config/*max-candidates* 2]
        (is (= ["instOfNatNat" "Zero.toOfNat0"]
               (mapv (comp str :name) (inst/select-candidates env cands goal)))))
      (testing "and a list within the cap is left alone"
        (is (= 4 (count (inst/select-candidates env cands goal))))))))

(deftest test-index-for-prefers-the-installed-registry
  (let [env (require-env)
        saved @state/ansatz-instance-index
        registry {(name/from-string "Nonempty") [{:name (name/from-string "instNonemptyOfInhabited") :priority 1000}]}]
    (try
      (reset! state/ansatz-instance-index registry)
      (is (identical? registry (inst/index-for env)) "a session with a registry synthesizes against it")
      (reset! state/ansatz-instance-index nil)
      (is (seq (inst/get-instances (inst/index-for env) (name/from-string "Add")))
          "without one, name-based discovery over the env")
      (finally (reset! state/ansatz-instance-index saved)))))
