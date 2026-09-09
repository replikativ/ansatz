(ns ansatz.tools.arena-check-test
  "The Lean Kernel Arena entry point: exit-code contract over small arena fixtures.
   Fixtures in test-data/arena are tutorial exports from
   https://github.com/leanprover/lean-kernel-arena (Apache-2.0), format 3.1.0."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.java.io :as io]
            [ansatz.tools.arena-check :as ac]))

(def ^:private fixtures "test-data/arena/")

(defn- exit-of [file & opts]
  (:exit (apply ac/check-file (str fixtures file) opts)))

(deftest accept-valid-export
  (testing "a well-typed definition is accepted (exit 0)"
    (is (= ac/exit-accept (exit-of "001_basicDef.ndjson"))))
  (testing "sparse / out-of-order internalization indices are fine"
    (is (= ac/exit-accept (exit-of "sparse-name-index.ndjson")))))

(deftest reject-invalid-export
  (testing "a value whose type does not match its declared type is rejected (exit 1)"
    (let [o (ac/check-file (str fixtures "002_badDef.ndjson"))]
      (is (= ac/exit-reject (:exit o)))
      (is (= "badDef" (:decl o)))))
  (testing "a safe theorem that uses an unsafe definition is rejected"
    ;; Lean adds an `unsafe` definition to the environment BEFORE checking its
    ;; value (unsafe recursion is allowed), so it accepts `unsafeLoop` and
    ;; rejects `falseFromUnsafe`. Our kernel currently rejects one step early,
    ;; at the self-referential `unsafeLoop` (known incompleteness; the verdict
    ;; on the file is the same).
    (let [o (ac/check-file (str fixtures "141_falseFromUnsafe.ndjson"))]
      (is (= ac/exit-reject (:exit o)))
      (is (contains? #{"falseFromUnsafe" "unsafeLoop"} (:decl o))))))

(deftest decline-unreadable-export
  (testing "an unparseable file is declined (exit 2), never rejected"
    (let [f (java.io.File/createTempFile "arena-garbage" ".ndjson")]
      (try
        (spit f "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n{\"bogusRecord\":{}}\n")
        (is (= ac/exit-decline (:exit (ac/check-file (.getPath f)))))
        (finally (.delete f)))))
  (testing "an export without a 3.x format meta record is declined"
    (let [f (java.io.File/createTempFile "arena-nometa" ".ndjson")]
      (try
        (spit f "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"x\"}}\n")
        (is (= ac/exit-decline (:exit (ac/check-file (.getPath f)))))
        (finally (.delete f))))))

(deftest fuel-exhaustion-is-a-decline
  (testing "running out of reduction fuel declines rather than rejects"
    ;; With no fuel the checker either finishes without reducing or exhausts;
    ;; exhaustion must never be reported as a rejection of the proof.
    (let [o (ac/check-file (str fixtures "001_basicDef.ndjson") :fuel 0)]
      (is (contains? #{ac/exit-accept ac/exit-decline} (:exit o)))
      (is (not= ac/exit-reject (:exit o))))))
