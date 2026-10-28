(ns java-ir-extern-checks
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json]
            [clojure.edn :as edn]
            [java-ir-baseline :as j]
            [java-ir-baseline-checks :as c]
            [lean-compatibility-corpus :as corpus]
            [prototype.import-ir :as ir]))

(def ^:dynamic *basis* nil)
(defn originals []
  (into {} (for [row (j/rows "test/fixtures/unchanged-programs/rbmap-main.jsonl")
                 :when (get-in row ["ir" "extern"])]
             [(ir/name-label (get row "name")) row])))
(defn raw [value] (json/read-str (json/write-str value)))
(defn abi [row]
  (j/invoke-static (.getMethod ^Class (:class *basis*) "validateExternAbi"
                              (into-array Class [java.util.Map])) [row]))
(defn prepare [rows]
  (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(raw rows)])))
(defn nat [value]
  (let [n (biginteger value)]
    (if (<= n Long/MAX_VALUE) (.longValue n) n)))

(deftest captured-signature-validation-preserves-erasure-and-borrows
  (let [rows (originals)]
    (doseq [[label symbol] [["Nat.add" "lean_nat_add"] ["Nat.sub" "lean_nat_sub"]
                            ["Nat.mod" "lean_nat_mod"] ["Nat.decEq" "lean_nat_dec_eq"]
                            ["Nat.decLt" "lean_nat_dec_lt"] ["Nat.mul" "lean_nat_mul"]
                            ["Nat.div" "lean_nat_div"] ["Nat.pow" "lean_nat_pow"]
                            ["USize.ofNat" "lean_usize_of_nat"] ["USize.ofNatLT" "lean_usize_of_nat"]]]
      (is (= symbol (abi (rows label)))))
    ;; These differ despite sharing the old preparer's physical object lane.
    (doseq [row [(assoc-in (rows "Nat.mul") ["ir" "extern" "xs" 0 "borrow"] false)
                 (assoc-in (rows "Nat.mul") ["ir" "extern" "xs" 0 "ty"] "object")
                 (assoc-in (rows "Nat.mul") ["ir" "extern" "type"] "object")
                 (update-in (rows "Nat.mul") ["ir" "extern" "xs" 0] dissoc "borrow")
                 (assoc-in (rows "USize.ofNatLT") ["ir" "extern" "xs" 1 "ty"] "void")
                 (assoc-in (rows "USize.ofNatLT") ["ir" "extern" "xs" 1 "borrow"] true)
                 (assoc-in (rows "USize.ofNat") ["ir" "extern" "xs"] [])]]
      (is (re-find #"Captured extern ABI mismatch" (c/failure #(abi row)))))
    ;; Known ABI remains distinct from executable machine lane coverage.
    (doseq [label ["USize.ofNat" "USize.ofNatLT"]]
      (is (re-find #"Unsupported baseline IR type: usize" (c/failure #(prepare [(rows label)])))))))

(deftest preparation-uses-the-same-registry
  (let [row ((originals) "Nat.mul")]
    (doseq [path [["xs" 0 "ty"] ["type"]]]
      (let [changed (assoc-in row (into ["ir" "extern"] path) "object")]
        (is (re-find #"Captured extern ABI mismatch" (c/failure #(prepare [changed]))))))))

(defn extern-entry [backend symbol]
  {"standard" {"backend" ["str" ["anonymous"] backend] "fn" symbol}})

(deftest extern-backend-precedence-and-rejection
  (let [row ((originals) "Nat.mul")
        with-entries #(assoc-in row ["ir" "extern" "ext" "entries"] %)]
    (is (= "lean_nat_mul" (abi (with-entries [(extern-entry "llvm" "unknown")
                                              (extern-entry "c" "lean_nat_mul")]))))
    (is (= "lean_nat_div" (abi (with-entries [(extern-entry "all" "lean_nat_div")
                                              (extern-entry "c" "lean_nat_mul")]))))
    (doseq [[entries pattern] [[[] #"Missing extern"]
                               [[(extern-entry "llvm" "lean_nat_mul")] #"No supported extern backend"]
                               [[(extern-entry "c" "unknown")] #"Unsupported baseline extern"]
                               [[{"inline" {"backend" ["str" ["anonymous"] "c"] "pattern" "ignored"}}]
                                #"Inline extern outside baseline profile"]]]
      (is (re-find pattern (c/failure #(abi (with-entries entries))))))))

(defn executable-rows []
  (let [rows (originals)]
    (into (mapv rows ["Nat.mul" "Nat.div" "Nat.pow"])
          (for [op ["mul" "div" "pow"]]
            (c/decl (str "wrapped-" op) [(c/p 1 "object") (c/p 2 "object")] "object"
                    (c/let-ir 3 "object" {:fap {:c ["str" (c/name-ir "Nat") op]
                                                      :ys [(c/v 1) (c/v 2)]}}
                      (c/ret 3)))))))

(deftest original-nat-externs-match-pinned-native-oracle
  (let [oracle (edn/read-string (slurp "measurements/java-ir-nat-extern-oracle.edn"))
        ctx (prepare (executable-rows)) engine (j/machine ctx)]
    (try
      (is (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (:producer oracle)))
      (is (= 1 (:schema oracle)))
      (is (zero? (:exit oracle)))
      (is (= 288 (count (:cases oracle))))
      (is (= #{"mul" "div" "pow"} (set (map :op (:cases oracle)))))
      (is (= (:source-sha256 oracle) (corpus/sha256 (:source oracle))))
      (is (= 1 (get-in oracle [:rejected-input :exit])))
      (is (re-find #"Nat.pow exponent is too big" (get-in oracle [:rejected-input :stderr])))
      (doseq [{:keys [op a b value]} (:cases oracle)
              label [(str "Nat." op) (str "wrapped-" op)]]
        (is (= (biginteger value) (j/call ctx engine label [(nat a) (nat b)]))
            (str label " " a " " b)))
      (finally (j/close! ctx engine)))))

(defn probe-failure! [ctx label args pattern]
  (let [engine (j/machine ctx)]
    (try
      (is (re-find pattern (c/failure #(j/call ctx engine label args))))
      (finally
        (if (= "failed" (j/phase ctx engine))
          ;; Managed failure cleanup is a separate, existing engine limitation.
          ;; Each failed pure probe is discarded; do not replay poisoned state.
          (is (re-find #"requires ownership cleanup" (c/failure #(j/close! ctx engine))))
          (j/close! ctx engine))))))

(deftest nat-errors-and-large-exponent-boundary
  (let [ctx (prepare (executable-rows))]
    (doseq [label ["Nat.mul" "Nat.div" "Nat.pow" "wrapped-mul" "wrapped-div" "wrapped-pow"]
            args [[-1 2] [(biginteger -1) 2] [2 -1] [2 (biginteger -1)] [1.0 2] [2 1.0]]]
      (probe-failure! ctx label args #"Invalid Nat"))
    (doseq [label ["Nat.pow" "wrapped-pow"] base [0 1 2]
            exponent [4294967296 (biginteger "18446744073709551616")]]
      (probe-failure! ctx label [base exponent] #"Nat.pow exponent is too big"))))

(defn check! [basis]
  (binding [*basis* basis] (run-tests 'java-ir-extern-checks)))
