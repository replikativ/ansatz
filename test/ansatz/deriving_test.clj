(ns ansatz.deriving-test
  "Tests for the deriving framework — DecidableEq for simple enums."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.deriving :as deriving]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]))

;; ============================================================
;; Environment setup (same pattern as core_test)
;; ============================================================

(def ^:private init-medium-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (let [st (parser/parse-ndjson-file f)
              env (:env (replay/replay (:decls st)))]
          env)))))

(defn- require-env []
  (or @init-medium-env
      (throw (ex-info "test-data/init-medium.ndjson not found" {}))))

(defn- with-env [f]
  (let [env (require-env)]
    (reset! a/ansatz-env env)
    (let [tsv "resources/instances.tsv"
          load-tsv (requiring-resolve 'ansatz.tactic.instance/load-instance-tsv)
          build-fn (requiring-resolve 'ansatz.tactic.instance/build-instance-index)
          idx (if (.exists (java.io.File. tsv))
                (load-tsv tsv)
                (build-fn env))]
      (reset! a/ansatz-instance-index idx))
    (binding [a/*verbose* false]
      (f))))

(use-fixtures :once with-env)

;; ============================================================
;; Direct API tests — derive-decidable-eq!
;; ============================================================

(deftest test-derive-decidable-eq-color
  (testing "Derive DecidableEq for 3-constructor enum"
    (binding [a/*verbose* false]
      ;; Define Color inductive
      (a/inductive DColor [] (red) (green) (blue))

      ;; Derive DecidableEq programmatically
      (let [env @a/ansatz-env
            env' (deriving/derive-decidable-eq!
                  env "DColor"
                  [["red" []] ["green" []] ["blue" []]])]
        (reset! a/ansatz-env env')

        ;; Verify the instance exists in the env
        (is (some? (env/lookup env' (name/from-string "instDecidableEqDColor")))
            "instDecidableEqDColor should be in the environment")))))

(deftest test-derive-decidable-eq-5-ctors
  (testing "Derive DecidableEq for 5-constructor enum (integrant scale)"
    (binding [a/*verbose* false]
      (a/inductive DState5 [] (s1) (s2) (s3) (s4) (s5))

      (let [env @a/ansatz-env
            env' (deriving/derive-decidable-eq!
                  env "DState5"
                  [["s1" []] ["s2" []] ["s3" []] ["s4" []] ["s5" []]])]
        (reset! a/ansatz-env env')

        (is (some? (env/lookup env' (name/from-string "instDecidableEqDState5")))
            "instDecidableEqDState5 should be in the environment")))))

;; ============================================================
;; Macro integration — :deriving [DecidableEq]
;; ============================================================

(deftest test-inductive-deriving-macro
  (testing ":deriving [DecidableEq] on a/inductive"
    (binding [a/*verbose* false]
      (a/inductive DDirection [] (north) (south) (east) (west)
                   :deriving [DecidableEq])

      (is (some? (env/lookup @a/ansatz-env
                             (name/from-string "instDecidableEqDDirection")))
          "instDecidableEqDDirection should exist after :deriving"))))

;; ============================================================
;; decide tactic tests — prove equality/inequality using derived instance
;; ============================================================

(deftest test-decide-equality
  (testing "decide closes equality goal on derived type"
    (binding [a/*verbose* false]
      ;; Fresh type to avoid conflicts
      (a/inductive DEqTest [] (alpha) (beta) (gamma)
                   :deriving [DecidableEq])

      ;; Rebuild instance index to pick up new instance
      (let [build-fn (requiring-resolve 'ansatz.tactic.instance/build-instance-index)]
        (reset! a/ansatz-instance-index (build-fn @a/ansatz-env)))

      ;; Prove alpha = alpha using decide
      (is (nil? (a/theorem deq-test-eq []
                  (= DEqTest (DEqTest.alpha) (DEqTest.alpha))
                  (decide)))
          "decide should close alpha = alpha"))))

(deftest test-decide-inequality
  (testing "decide closes inequality goal on derived type"
    (binding [a/*verbose* false]
      (a/inductive DNeqTest [] (x1) (x2) (x3)
                   :deriving [DecidableEq])

      (let [build-fn (requiring-resolve 'ansatz.tactic.instance/build-instance-index)]
        (reset! a/ansatz-instance-index (build-fn @a/ansatz-env)))

      ;; Prove Not (x1 = x2) using decide
      (is (nil? (a/theorem dneq-test []
                  (Not (= DNeqTest (DNeqTest.x1) (DNeqTest.x2)))
                  (decide)))
          "decide should close Not (x1 = x2)"))))
