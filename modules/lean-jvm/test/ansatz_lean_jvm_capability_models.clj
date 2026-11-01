(ns ansatz-lean-jvm-capability-models
  "Runtime metadata models; no engine or native frontend execution."
  (:require [clojure.test :refer [deftest is run-tests]]
            [ansatz.lean.jvm.ir :as j] [ansatz.lean.jvm.capabilities :as caps]))
(def ^:dynamic *basis* nil)
(defn- row [symbol params borrowed result]
  (let [n ["str" ["anonymous"] symbol]]
    {"kind" "decl" "name" n "dependencies" [] "runtime" {"role" "ordinary" "initializer" nil}
     "ir" {"extern" {"f" n "type" result
                       "xs" (mapv (fn [i ty borrow] {"x" {"idx" (inc i)} "ty" ty "borrow" borrow}) (range) params borrowed)
                       "ext" {"entries" [{"standard" {"backend" ["str" ["anonymous"] "all"] "fn" symbol}}]}}}}))
(def nat-row (row "lean_nat_add" ["tobject" "tobject"] [true true] "tobject"))
(deftest actual-abi-and-semantic-family-must-both-match
  (let [d (caps/check-rows! *basis* [nat-row]) r (first (vals (:externs d)))]
    (is (= :nat (:family r)))
    (is (= "ADD" (:field r)))
    (is (identical? (:class *basis*) (:runtime-class d)))
    (is (false? (:task-runtime d))))
  (is (thrown? Exception (caps/check-rows! *basis* [(assoc-in nat-row ["ir" "extern" "xs" 0 "borrow"] false)]))))
(deftest task-policy-and-unconfigured-stdio-operations-refused
  (doseq [unsupported [(row "lean_io_promise_new" ["erased" "erased" "void"] [false false false] "tobject")
                        (row "lean_task_pure" ["erased" "tobject"] [false false] "object")
                        (row "lean_profileit" ["erased" "object" "object" "tobject" "tobject"] [false true true false false] "tobject")
                        (row "lean_get_stderr" ["void"] [false] "object")
                        (row "lean_get_set_stdout" ["object" "void"] [false false] "object")]]
    (is (thrown-with-msg? Exception #"audited task-free profile" (caps/check-rows! *basis* [unsupported])))))
(deftest unknown-extern-is-never-deferred-until-after-startup
  (is (thrown? Exception (caps/check-rows! *basis* [(row "unknown_native_capability" [] [] "object")]))))
(deftest entropy-and-captured-stdout-are-explicit-families
  (let [d (caps/check-rows! *basis* [(let [n ["str" ["str" ["anonymous"] "IO"] "getRandomBytes"]]
                                     (-> (row "lean_io_get_random_bytes" ["usize" "void"] [false false] "object")
                                         (assoc "name" n) (assoc-in ["ir" "extern" "f"] n)))
                                   (row "lean_get_stdout" ["void"] [false] "object")])]
    (is (= #{:entropy :captured-stdout} (set (map :family (vals (:externs d))))))
    (is (= :captured-stdout-write-flush-tty (:dynamic-io-profile d)))
    (is (contains? (:runtime-unsupported d) :captured-stream-read))))
(deftest panic-is-a-declared-terminal-trap-not-a-fake-result
  (let [d (caps/check-rows! *basis* [(row "lean_panic_fn_borrowed" ["erased" "tobject" "object"] [false true false] "tobject")])]
    (is (= :terminal-trap (:family (first (vals (:externs d))))))
    (is (contains? (:runtime-unsupported d) :panic-default-return))))
(deftest descriptor-is-bound-to-actual-program-and-canonical-headers
  (let [d (caps/check-rows! *basis* [nat-row]) base (j/prepare-host-program *basis* [] [])
        source (j/source-binding base {"test-only-capability-model" true})
        header (j/declaration-header source nat-row (apply str (repeat 64 "0")))
        headers {(get nat-row "name") header} ctx (j/register-headers base [header])]
    (is (identical? d (caps/check-program! ctx headers d)))
    (is (thrown? Exception (caps/check-program! ctx headers (assoc d :runtime-class Object))))
    (is (thrown? Exception (caps/check-program! ctx headers (assoc d :registry-object {}))))
    (is (thrown? Exception (caps/check-program! ctx headers (assoc-in d [:externs (get nat-row "name") :intrinsic] 99999))))
    (is (thrown? Exception (caps/check-program! ctx {} d)))))
(defn check! [basis] (binding [*basis* basis] (run-tests 'ansatz-lean-jvm-capability-models)))
