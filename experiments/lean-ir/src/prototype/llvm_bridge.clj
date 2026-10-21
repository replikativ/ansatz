(ns prototype.llvm-bridge
  "Optional LLVM 20 scalar bridge. LLVM parses/verifies first; a deliberately
  narrow adapter reads its canonical output. No LLVM dependency in the guest VM."
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as str]
            [pattern.nanopass.dialect :refer [valid?]]
            [prototype.pattern-probe :as pattern]))

(defn- reject [message value]
  (throw (ex-info message {:value value :profile :llvm20-scalar})))

(defn- checked-sh [& argv]
  (let [result (apply shell/sh argv)]
    (when-not (zero? (:exit result))
      (throw (ex-info "LLVM tool rejected input" (assoc result :argv argv))))
    (:out result)))

(defn- temporary [f]
  (let [dir (.toFile (java.nio.file.Files/createTempDirectory
                     "ansatz-llvm-" (make-array java.nio.file.attribute.FileAttribute 0)))]
    (try (f dir)
         (finally (doseq [file (reverse (file-seq dir))] (io/delete-file file true))))))

(defn tool-version []
  (let [v (checked-sh "llvm-as" "--version")]
    (when-not (re-find #"LLVM version 20\." v) (reject "Adapter requires LLVM 20" v))
    (str/trim (first (str/split-lines v)))))

(defn canonical-text
  "Invoke LLVM's parser and verifier, then disassemble. Text input only."
  [text]
  (tool-version)
  (temporary
   (fn [dir]
     (let [ll (str (io/file dir "input.ll"))
           bc (str (io/file dir "input.bc"))]
       (spit ll text)
       (checked-sh "llvm-as" ll "-o" bc)
       (checked-sh "opt" "-passes=verify" bc "-disable-output")
       (checked-sh "llvm-dis" bc "-o" "-")))))

(defn- identifier [x]
  (when-not (and (symbol? x) (re-matches #"[A-Za-z_][A-Za-z_0-9]*" (str x)))
    (reject "Only simple named identifiers are supported" x))
  (str x))

(defn- ty [x]
  (when-not (pattern/llvm-type? x) (reject "Unsupported integer type" x))
  (str x))

(defn- operand [x]
  (if (integer? x) (str x) (str "%" (identifier x))))

(defn- typed [[t a]] (str (ty t) " " (operand a)))

(defn- emit-expression [[op & xs :as form]]
  (case op
    (add sub) (let [[t a b] xs] (str op " " (ty t) " " (operand a) ", " (operand b)))
    icmp (let [[pred t a b] xs]
           (when-not (= 'eq pred) (reject "Only equality comparison is supported" form))
           (str "icmp eq " (ty t) " " (operand a) ", " (operand b)))
    call (let [[tail cc t callee [_ & args]] xs]
           (when-not (= ['musttail 'tailcc] [tail cc]) (reject "Unsupported call" form))
           (str "musttail call tailcc " (ty t) " @" (identifier callee)
                "(" (str/join ", " (map typed args)) ")"))
    (reject "Unsupported expression" form)))

(defn- emit-terminator [[op & xs :as form]]
  (case op
    ret (let [[t a] xs] (str "ret " (typed [t a])))
    br (str "br label %" (identifier (first xs)))
    cbr (let [[a yes no] xs]
          (str "br i1 " (operand a) ", label %" (identifier yes) ", label %" (identifier no)))
    (reject "Unsupported terminator" form)))

(defn export-text
  "Pure emitter. Pattern checks shape; use canonical-text for LLVM SSA/type checks."
  [module]
  (when-not (valid? pattern/LLVMScalar module) (reject "Invalid Pattern scalar dialect" module))
  (str/join
   "\n"
   (for [[_ _ t name [_ & params] [_ & blocks]] (rest module)]
     (str "define tailcc " (ty t) " @" (identifier name)
          "(" (str/join ", " (map typed params)) ") {\n"
          (str/join
           "\n"
           (for [[_ label [_ & instructions] terminator] blocks]
             (str (identifier label) ":\n"
                  (apply str (for [[_ dest expr] instructions]
                               (str "  %" (identifier dest) " = " (emit-expression expr) "\n")))
                  "  " (emit-terminator terminator))))
          "\n}\n"))))

(defn- read-operand [s]
  (cond
    (str/starts-with? s "%") (symbol (subs s 1))
    (= s "true") 1
    (= s "false") 0
    (re-matches #"-?[0-9]+" s) (bigint s)
    :else (reject "Unsupported operand" s)))

(defn- read-typed [s]
  (if-let [[_ t value] (re-matches #"(i1|i32|i64) (%[A-Za-z_][A-Za-z_0-9]*|-?[0-9]+|true|false)" s)]
    [(symbol t) (read-operand value)]
    (reject "Unsupported typed value" s)))

(defn- read-args [s] (if (str/blank? s) [] (mapv read-typed (str/split s #", "))))

(defn- read-operation [line]
  (or
   (when-let [[_ dest op t a b] (re-matches #"%([A-Za-z_][A-Za-z_0-9]*) = (add|sub) (i1|i32|i64) ([^,]+), (.+)" line)]
     (list 'assign (symbol dest) (list (symbol op) (symbol t) (read-operand a) (read-operand b))))
   (when-let [[_ dest t a b] (re-matches #"%([A-Za-z_][A-Za-z_0-9]*) = icmp eq (i1|i32|i64) ([^,]+), (.+)" line)]
     (list 'assign (symbol dest) (list 'icmp 'eq (symbol t) (read-operand a) (read-operand b))))
   (when-let [[_ dest t callee args] (re-matches #"%([A-Za-z_][A-Za-z_0-9]*) = musttail call tailcc (i1|i32|i64) @([A-Za-z_][A-Za-z_0-9]*)\((.*)\)" line)]
     (list 'assign (symbol dest)
           (list 'call 'musttail 'tailcc (symbol t) (symbol callee) (cons 'args (read-args args)))))
   (when-let [[_ t a] (re-matches #"ret (i1|i32|i64) (.+)" line)]
     (list 'ret (symbol t) (read-operand a)))
   (when-let [[_ label] (re-matches #"br label %([A-Za-z_][A-Za-z_0-9]*)" line)]
     (list 'br (symbol label)))
   (when-let [[_ a yes no] (re-matches #"br i1 ([^,]+), label %([A-Za-z_][A-Za-z_0-9]*), label %([A-Za-z_][A-Za-z_0-9]*)" line)]
     (list 'cbr (read-operand a) (symbol yes) (symbol no)))
   (reject "LLVM construct outside the scalar profile" line)))

(defn- read-block [lines]
  (let [label (first lines)]
    (when-not (re-matches #"[A-Za-z_][A-Za-z_0-9]*:" label) (reject "Expected named block" label))
    (let [ops (mapv read-operation (rest lines))]
      (when-not (and (seq ops) (every? #(= 'assign (first %)) (butlast ops))
                     (contains? '#{ret br cbr} (first (last ops))))
        (reject "Unsupported block structure" lines))
      (list 'block (symbol (subs label 0 (dec (count label))))
            (cons 'instructions (butlast ops)) (last ops)))))

(defn- read-function [lines]
  (if-let [[_ t name params] (re-matches #"define tailcc (i1|i32|i64) @([A-Za-z_][A-Za-z_0-9]*)\((.*)\) \{" (first lines))]
    (let [body (butlast (rest lines))
          groups (reduce (fn [groups line]
                           (if (str/ends-with? line ":") (conj groups [line])
                               (if (empty? groups) (reject "Unnamed entry block" line)
                                   (update groups (dec (count groups)) conj line)))) [] body)]
      (when-not (= "}" (last lines)) (reject "Unclosed function" lines))
      (list 'define 'tailcc (symbol t) (symbol name)
            (cons 'params (read-args params)) (cons 'blocks (map read-block groups))))
    (reject "Unsupported function signature or module declaration" (first lines))))

(defn import-text
  "LLVM parses/verifies first. Reject anything outside this bounded dialect.
  Discards only source_filename and comments; target/layout/attrs are rejected."
  [text]
  (let [lines (->> (str/split-lines (canonical-text text))
                   (map #(str/trim (first (str/split % #";" 2))))
                   (remove #(or (str/blank? %) (str/starts-with? % "source_filename = "))))
        functions (loop [remaining lines result []]
                    (if (empty? remaining) result
                        (let [[body more] (split-with #(not= "}" %) remaining)]
                          (when (empty? more) (reject "Unsupported module content" (first remaining)))
                          (recur (rest more) (conj result (read-function (concat body ["}"])))))))
        module (cons 'llvm-module functions)]
    (when-not (valid? pattern/LLVMScalar module) (reject "Imported module fails dialect" module))
    module))

(defn- bits [t] (case t i1 1 i32 32 i64 64))
(defn- unsigned [t n]
  (mod (bigint n) (bigint (.shiftLeft java.math.BigInteger/ONE (bits t)))))

(defn evaluate
  "LLVM-free scalar evaluator. Inputs must be verified/in-profile. Explicit loop
  for musttail transfers, modulo integer arithmetic, bounded instruction fuel."
  ([module entry args] (evaluate module entry args 2000000))
  ([module entry args fuel]
   (let [functions (into {} (map (fn [f] [(nth f 3) f]) (rest module)))
         activation (fn [name values]
                      (let [[_ _ _ _ [_ & params] [_ & blocks]] (get functions name)]
                        (when-not (and (seq blocks) (= (count params) (count values)))
                          (reject "Missing function or wrong arity" [name values]))
                        {:blocks (into {} (map (fn [[_ label & _ :as b]] [label b]) blocks))
                         :label (second (first blocks))
                         :env (into {} (map (fn [[t p] v] [p (unsigned t v)]) params values))}))]
     (loop [{:keys [blocks label env] :as state} (activation entry args) fuel fuel]
       (when-not (pos? fuel) (reject "Scalar evaluation fuel exhausted" state))
       (let [[_ _ [_ & instructions] terminator] (get blocks label)
             value (fn [env a] (if (integer? a) a
                                   (if (contains? env a) (get env a) (reject "Unbound SSA value" a))))
             result (reduce
                     (fn [env [_ dest [op & xs]]]
                       (case op
                         (add sub) (let [[t a b] xs]
                                     (assoc env dest (unsigned t ((if (= op 'add) +' -') (value env a) (value env b)))))
                         icmp (let [[_ t a b] xs]
                                (assoc env dest (if (= (unsigned t (value env a)) (unsigned t (value env b))) 1 0)))
                         call (let [[_ _ _ callee [_ & args]] xs]
                                (reduced {:tail [callee (mapv (fn [[_ a]] (value env a)) args)]}))))
                     env instructions)
             remaining (- fuel (inc (count instructions)))]
         (when (neg? remaining) (reject "Scalar evaluation fuel exhausted" state))
         (if-let [[callee args] (:tail result)]
           (recur (activation callee args) remaining)
           (case (first terminator)
             ret (unsigned (second terminator) (value result (nth terminator 2)))
             br (recur (assoc state :label (second terminator) :env result) remaining)
             cbr (recur (assoc state :label (if (zero? (value result (second terminator)))
                                             (nth terminator 3) (nth terminator 2)) :env result) remaining))))))))

(defn native-check!
  "Execute a verified scalar entry in a disposable lli process; compare full
  scalar value using an LLVM harness, rather than truncating it to an exit byte."
  [module entry args expected]
  (let [function (some #(when (= entry (nth % 3)) %) (rest module))
        t (nth function 2)
        params (rest (nth function 4))
        harness (str "\ndefine i32 @main() {\nentry:\n  %answer = call tailcc " (ty t)
                     " @" (identifier entry) "(" (str/join ", " (map (fn [[t _] a] (typed [t a])) params args))
                     ")\n  %ok = icmp eq " (ty t) " %answer, " expected
                     "\n  br i1 %ok, label %yes, label %no\nyes:\n  ret i32 0\nno:\n  ret i32 1\n}\n")]
    (canonical-text (str (export-text module) harness))
    (temporary (fn [dir]
                 (let [ll (str (io/file dir "run.ll")) bc (str (io/file dir "run.bc"))]
                   (spit ll (str (export-text module) harness))
                   (checked-sh "llvm-as" ll "-o" bc)
                   (checked-sh "lli" bc)
                   {:entry entry :args args :expected expected :exit 0})))))
