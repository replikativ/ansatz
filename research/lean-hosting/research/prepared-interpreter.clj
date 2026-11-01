(ns prepared-interpreter
  "Research-only, one-instruction prepared :let interpreter. Load once; never
  reload prototype.mutable. Prepared code is host state, outside snapshots."
  (:refer-clojure :exclude [run!])
  (:require [prototype.mutable :as u]
            [prototype.machine :as m])
  (:import [java.util IdentityHashMap]))

;; Private Vars are invoked as Vars: dynamic hooks are observed at their normal
;; call points. Baselines come from the definition owner's table, never from
;; whichever functions happen to be installed while preparing a guest program.
(def ^:private ctl-var (ns-resolve 'prototype.mutable 'ctl))
(def ^:private put-var (ns-resolve 'prototype.mutable 'put!))
(def ^:private bump-var (ns-resolve 'prototype.mutable 'bump!))
(def ^:private expr-var (ns-resolve 'prototype.mutable 'expr!))
(def ^:private value-var (ns-resolve 'prototype.mutable 'value))
(def ^:private node-var (ns-resolve 'prototype.mutable 'node))
(def ^:private field-var (ns-resolve 'prototype.mutable 'field-at))
(def ^:private allocate-var (ns-resolve 'prototype.mutable 'allocate!))
(def ^:private owner-roots
  @(ns-resolve 'prototype.mutable 'scalar-wrapper-roots))

(defn- stock-step? []
  (and (identical? (nth owner-roots 5) @#'u/step!)
       (identical? (nth owner-roots 6) @expr-var)
       (identical? (nth owner-roots 7) @value-var)
       (identical? (nth owner-roots 9) @ctl-var)
       (identical? (nth owner-roots 11) @bump-var)))

(defprotocol Operand (operand-value [operand machine]))
(deftype CurrentValueOperand [original local? data]
  Operand
  (operand-value [_ machine]
    ;; A previous argument can redefine private value after the step guard.
    ;; Select the function before read-local/ctl, just as value's caller does.
    (let [value-fn @value-var]
      (if (identical? (nth owner-roots 7) value-fn)
        (if local? (u/read-local (@ctl-var machine 1) data) data)
        (value-fn machine original)))))

(defprotocol Arguments (argument-values [arguments machine]))
(deftype Args0 []
  Arguments (argument-values [_ _] []))
(deftype Args1 [a]
  Arguments (argument-values [_ s] [(operand-value a s)]))
(deftype Args2 [a b]
  Arguments (argument-values [_ s] [(operand-value a s) (operand-value b s)]))
(deftype Args3 [a b c]
  Arguments (argument-values [_ s] [(operand-value a s) (operand-value b s) (operand-value c s)]))
(deftype ArgsMany [operands]
  Arguments (argument-values [_ s] (mapv #(operand-value % s) operands)))

(defprotocol Expression (expression-value [expression machine]))
(deftype Literal [value]
  Expression (expression-value [_ _] value))
(deftype Project [operand slot]
  Expression
  (expression-value [_ s]
    (@field-var (:fields (@node-var s (operand-value operand s))) slot)))
(deftype ScalarGet [operand slot]
  Expression (expression-value [_ s] (u/scalar-get s (operand-value operand s) slot)))
(deftype Constructor [tag arguments empty?]
  Expression
  (expression-value [_ s]
    (if empty? (m/->Tag tag)
      (@allocate-var s :ctor tag (argument-values arguments s) nil))))
(deftype RuntimeExpr [symbol arguments]
  Expression (expression-value [_ s] (u/runtime-value! s symbol (argument-values arguments s))))
(deftype Primitive [operation arguments]
  Expression
  (expression-value [_ s]
    ;; Keep the current scalar Var and its exact validation/carrier semantics.
    ;; In particular ALL operand reads precede ANY input validation. A fused
    ;; primitive needs a source-owned scalar/small-integer baseline first.
    (m/scalar operation (argument-values arguments s))))

(defprotocol Instruction (execute-instruction! [instruction machine]))
(deftype LetInstruction [destination expression continuation]
  Instruction
  (execute-instruction! [_ s]
    ;; Match u/step!: status, charge, locals/index, expression, store, body.
    (when-not (= :running (@ctl-var s 4))
      (m/fail "Machine is not running" {:status (@ctl-var s 4)}))
    (@bump-var s 2 1)
    (let [locals (@ctl-var s 1)
          index (int destination)
          value (expression-value expression s)]
      (aset ^objects locals index value)
      (@put-var s 0 continuation))
    s))

(defn- static-vector? [value]
  ;; Do not specialize custom vectors whose reads can execute host callbacks
  ;; or change between preparation and execution.
  (identical? (class value) clojure.lang.PersistentVector))

(defn- prepare-operand [operand]
  (when (static-vector? operand)
    (case (first operand)
      :var (CurrentValueOperand. operand true (second operand))
      :imm (CurrentValueOperand. operand false (second operand))
      nil)))

(defn- prepare-arguments [operands]
  (when (static-vector? operands)
    (let [args (mapv prepare-operand operands)]
      (when (every? some? args)
        (case (count args)
          0 (Args0.)
          1 (Args1. (nth args 0))
          2 (Args2. (nth args 0) (nth args 1))
          3 (Args3. (nth args 0) (nth args 1) (nth args 2))
          (ArgsMany. args))))))

(defn- prepare-expression [expression]
  (when (static-vector? expression)
    (let [[op a b] expression]
      (case op
        :literal (Literal. a)
        :project (when-let [operand (prepare-operand a)] (Project. operand b))
        :scalar-get (when-let [operand (prepare-operand a)] (ScalarGet. operand b))
        :ctor (when-let [arguments (prepare-arguments b)]
                (Constructor. a arguments (empty? b)))
        :runtime (when-let [arguments (prepare-arguments b)] (RuntimeExpr. a arguments))
        :prim (when-let [arguments (prepare-arguments b)] (Primitive. a arguments))
        nil))))

(defn- children [body]
  ;; Only syntactic body positions; literals, operands and runtime values are
  ;; never traversed as code. Unknown/malformed syntax remains interpreter work.
  (when (static-vector? body)
    (let [[op _ b c d] body]
      (case op
        :let [c]
        :call [d]
        :join [c d]
        :case (when (static-vector? b)
                (into [] (keep #(when (static-vector? %) (second %))) b))
        (:inc :dec :set-tag) [c]
        (:set :scalar-set :host) [d]
        (:del :suspend) [b]
        nil))))

(defn prepare-program
  "Prepare immutable static function-body identities only. Returns a host-side
  program with :preparation-ns/:prepared-lets/:visited-bodies measurements.
  Functions must be IDENTICAL to machine :functions. Dynamic continuations and
  restored/copied body identities simply use the current u/step! fallback."
  [functions]
  (let [started (System/nanoTime)
        prepared (IdentityHashMap.)
        seen (IdentityHashMap.)]
    (loop [todo (if (map? functions) (mapv :body (vals functions)) [])]
      (when (seq todo)
        (let [body (peek todo) todo (pop todo)]
          (if (or (not (static-vector? body)) (.containsKey seen body))
            (recur todo)
            (do
              (.put seen body true)
              ;; Preparation must not advance malformed-IR error timing.
              (when (and (= :let (first body))
                         ;; Malformed/custom destination coercions can run
                         ;; arbitrary host code; retain their original path.
                         (or (instance? Long (nth body 1 nil))
                             (instance? Integer (nth body 1 nil))))
                (when-let [expression (try (prepare-expression (nth body 2 nil))
                                          (catch Exception _ nil))]
                  (.put prepared body (LetInstruction. (nth body 1 nil) expression (nth body 3 nil)))))
              (recur (into todo (try (children body) (catch Exception _ nil)))))))))
    {:functions functions :instructions prepared
     :prepared-lets (.size prepared) :visited-bodies (.size seen)
     :preparation-ns (- (System/nanoTime) started)}))

(defn- check-program! [program machine]
  (when-not (identical? (:functions program) (:functions machine))
    (m/fail "Prepared program does not match machine code identity" {})))

(defn step!
  "Exactly one canonical instruction. Redefined core interpreter roots always
  fall back to the CURRENT u/step!, including private expr/value/ctl/bump hooks."
  [program machine]
  (check-program! program machine)
  (if (stock-step?)
    (if-let [instruction (.get ^IdentityHashMap (:instructions program) (@ctl-var machine 0))]
      (execute-instruction! instruction machine)
      (u/step! machine))
    (u/step! machine)))

(defn run!
  ([program machine] (run! program machine 10000000))
  ([program machine fuel]
   (check-program! program machine)
   (when-not (and (integer? fuel) (not (neg? fuel)))
     (m/fail "Invalid step budget" {:fuel fuel}))
   (loop [remaining fuel]
     ;; Match u/run!'s public status semantics and its dynamic pause hook.
     (cond
       (not= :running (@ctl-var machine 4)) machine
       (zero? remaining) (do (@put-var machine 4 :paused) machine)
       :else (do (step! program machine) (recur (dec remaining)))))))

(defn open
  "Convenience harness: {:program (prepare-program functions), :run! run!}.
  Call (:run! harness) with (:program harness), a mutable machine and fuel."
  [functions]
  {:program (prepare-program functions) :run! run! :step! step!})
