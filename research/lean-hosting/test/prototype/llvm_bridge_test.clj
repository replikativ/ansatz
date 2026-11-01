(ns prototype.llvm-bridge-test
  "Optional integration tests: Pattern checkout and LLVM 20 required."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.string :as str]
            [prototype.pattern-probe :as pattern]
            [prototype.llvm-bridge :as llvm]))

(def arithmetic
  '(llvm-module
    (define tailcc i64 plus (params [i64 a] [i64 b])
      (blocks (block entry (instructions (assign answer (add i64 a b))) (ret i64 answer))))
    (define tailcc i32 minus (params [i32 a] [i32 b])
      (blocks (block entry (instructions (assign answer (sub i32 a b))) (ret i32 answer))))
    (define tailcc i1 flip (params [i1 a])
      (blocks (block entry (instructions (assign answer (add i1 a 1))) (ret i1 answer))))))

(deftest scalar-roundtrip
  (doseq [module [pattern/sample arithmetic]]
    (let [text (llvm/export-text module) imported (llvm/import-text text)]
      (is (= module imported))
      (is (= imported (llvm/import-text (llvm/export-text imported)))))))

(deftest deep-tail-execution
  (let [module (llvm/import-text (llvm/export-text pattern/sample))]
    (doseq [[args expected] [[[0 42] 42] [[7 5] 12] [[200000 0] 200000]]]
      (is (= expected (llvm/evaluate module 'count args)))
      (is (= 0 (:exit (llvm/native-check! module 'count args expected)))))))

(deftest cross-function-tail-transfer-and-unconditional-branch
  (let [module (cons 'llvm-module
                     (concat (rest pattern/sample)
                             '((define tailcc i64 start (params [i64 n] [i64 acc])
                                 (blocks
                                  (block entry (instructions) (br forward))
                                  (block forward
                                    (instructions
                                     (assign answer (call musttail tailcc i64 count (args [i64 n] [i64 acc]))))
                                    (ret i64 answer)))))))
        imported (llvm/import-text (llvm/export-text module))]
    (is (= module imported))
    (is (= 107 (llvm/evaluate imported 'start [100 7])))
    (is (= 0 (:exit (llvm/native-check! imported 'start [100 7] 107))))))

(deftest modulo-arithmetic-agrees-with-llvm
  (let [module (llvm/import-text (llvm/export-text arithmetic))]
    (doseq [[entry args expected]
            [['plus [9223372036854775807 1] 9223372036854775808N]
             ['plus [-1 1] 0]
             ['minus [0 1] 4294967295]
             ['flip [1] 0]
             ['flip [0] 1]]]
      (is (= expected (llvm/evaluate module entry args)))
      (is (= 0 (:exit (llvm/native-check! module entry args expected)))))))

(deftest verifier-rejects-invalid-ssa-and-types
  (let [text (llvm/export-text pattern/sample)]
    (is (thrown? clojure.lang.ExceptionInfo
                 (llvm/import-text (str/replace text "ret i64 %acc" "ret i64 %undefined"))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (llvm/import-text (str/replace text "ret i64 %result" "ret i32 0"))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (llvm/import-text (str/replace text "ret i64 %result" "%extra = add i64 %result, 1\n  ret i64 %extra"))))))

(deftest supported-llvm-outside-profile-is-rejected
  (let [text (llvm/export-text arithmetic)]
    (doseq [unsupported [(str/replace text "add i64" "add nsw i64")
                         (str "target triple = \"x86_64-unknown-linux-gnu\"\n" text)
                         (str "target datalayout = \"e-p:64:64\"\n" text)
                         (str/replace text "@plus(i64 %a, i64 %b) {" "@plus(i64 %a, i64 %b) nounwind {")
                         (str/replace text "add i64 %a, %b" "add i64 %a, poison")]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported|outside"
                            (llvm/import-text unsupported))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (llvm/import-text "define tailcc i64 @loadit(ptr %p) {\nentry:\n%x = load i64, ptr %p\nret i64 %x\n}")))))

(deftest evaluator-fuel-and-arity
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"fuel"
                        (llvm/evaluate pattern/sample 'count [100 0] 5)))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"arity"
                        (llvm/evaluate pattern/sample 'count [1]))))

(defn -main [& _]
  (let [result (run-tests 'prototype.llvm-bridge-test)]
    (shutdown-agents)
    (when (pos? (+ (:fail result) (:error result))) (System/exit 1))))
