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
(deftest task-policy-and-stdio-redirection-refused
  (doseq [unsupported [(row "lean_io_promise_new" ["erased" "erased" "void"] [false false false] "tobject")
                        (row "lean_task_pure" ["erased" "tobject"] [false false] "object")
                        (row "lean_profileit" ["erased" "object" "object" "tobject" "tobject"] [false true true false false] "tobject")
                        (row "lean_get_set_stdout" ["object" "void"] [false false] "object")]]
    (is (thrown-with-msg? Exception #"audited task-free profile" (caps/check-rows! *basis* [unsupported])))))
(deftest unknown-extern-is-never-deferred-until-after-startup
  (is (thrown? Exception (caps/check-rows! *basis* [(row "unknown_native_capability" [] [] "object")]))))
(deftest entropy-and-captured-stdout-are-explicit-families
  (let [d (caps/check-rows! *basis* [(let [n ["str" ["str" ["anonymous"] "IO"] "getRandomBytes"]]
                                     (-> (row "lean_io_get_random_bytes" ["usize" "void"] [false false] "object")
                                         (assoc "name" n) (assoc-in ["ir" "extern" "f"] n)))
                                   (row "lean_get_stdout" ["void"] [false] "object")
                                   (row "lean_get_stdin" ["void"] [false] "object")
                                   (row "lean_get_stderr" ["void"] [false] "object")])]
    (is (= #{:entropy :captured-stdout :captured-stdin :captured-stderr} (set (map :family (vals (:externs d))))))
    (is (= :bounded-stdio-read-line-write-flush-tty (:dynamic-io-profile d)))
    (is (= :native-like-finite-byte-input (:stdin-profile d)))
    (is (contains? (:runtime-unsupported d) :host-filesystem))))
(deftest panic-is-admitted-with-native-default-return
  (let [d (caps/check-rows! *basis* [(row "lean_panic_fn_borrowed" ["erased" "tobject" "object"] [false true false] "tobject")])]
    (is (= :panic (:family (first (vals (:externs d))))))))
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
(deftest integer-arithmetic-matrix-is-admitted-before-startup
  ;; Lean 4.33.1 Init ABIs: borrowed Int/Nat operands, owned unsigned scalars.
  (let [types ["uint8" "uint16" "uint32" "uint64" "usize"]
        words (concat
                (for [ty types op ["add" "sub" "mul" "div" "mod" "land" "lor" "xor" "shift_left" "shift_right"]]
                  (row (str "lean_" ty "_" op) [ty ty] [false false] ty))
                (for [ty types op ["dec_eq" "dec_lt" "dec_le"]]
                  (row (str "lean_" ty "_" op) [ty ty] [false false] "uint8"))
                (for [ty types op ["complement" "neg" "log2"]]
                  (row (str "lean_" ty "_" op) [ty] [false] ty))
                (for [from types to types :when (not= from to)]
                  (row (str "lean_" from "_to_" to) [from] [false] to))
                (for [ty types] (row (str "lean_" ty "_of_nat_mk") ["tobject"] [false] ty))
                (for [ty types] (row (str "lean_bool_to_" ty) ["uint8"] [false] ty)))
        ints (concat
               (for [op ["mul" "div" "mod" "ediv" "emod"]]
                 (row (str "lean_int_" op) ["tobject" "tobject"] [true true] "tobject"))
               [(row "lean_int_div_exact" ["tobject" "tobject" "erased"] [true true false] "tobject")
                (row "lean_int_dec_nonneg" ["tobject"] [true] "uint8")])
        nats (concat
               (for [op ["land" "lxor" "gcd"]]
                 (row (str "lean_nat_" op) ["tobject" "tobject"] [true true] "tobject"))
               [(row "lean_nat_pred" ["tobject"] [true] "tobject")
                (row "lean_nat_div_exact" ["tobject" "tobject" "erased"] [true true false] "tobject")])
        d (caps/check-rows! *basis* (concat words ints nats))
        family (fn [symbol] (:family (get (:externs d) ["str" ["anonymous"] symbol])))]
    (is (= (+ (count words) (count ints) (count nats)) (count (:externs d))))
    (is (every? #(= :word (family (get-in % ["ir" "extern" "ext" "entries" 0 "standard" "fn"]))) words))
    (is (every? #(= :int (family (get-in % ["ir" "extern" "ext" "entries" 0 "standard" "fn"]))) ints))
    (is (every? #(= :nat (family (get-in % ["ir" "extern" "ext" "entries" 0 "standard" "fn"]))) nats))
    (is (= :task-free-captured-output-v1 (:profile d))))
  ;; Signed fixed-width integers remain outside the audited profile.
  (is (thrown-with-msg? Exception #"Unsupported Lean runtime extern"
        (caps/check-rows! *basis* [(row "lean_int32_add" ["uint32" "uint32"] [false false] "uint32")]))))
(defn check! [basis] (binding [*basis* basis] (run-tests 'ansatz-lean-jvm-capability-models)))
