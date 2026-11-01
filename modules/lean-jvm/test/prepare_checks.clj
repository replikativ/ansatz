(ns ansatz-lean-jvm-prepare-checks
  "Small adapter checks: no legacy research namespaces, native evidence or API."
  (:require [clojure.test :refer [deftest is run-tests]] [ansatz.lean.jvm.ir :as ir]))
(def ^:dynamic *engine-class* nil)
(def digest (apply str (repeat 64 "a")))
(defn name-row [s] ["str" ["anonymous"] s])
(defn identity-row []
  {"kind" "decl" "name" (name-row "identity")
   "ir" {"fdecl" {"f" (name-row "identity")
                    "xs" [{"x" {"idx" 1} "ty" "object" "borrow" false}]
                    "type" "object" "body" ["ret" {"var" {"id" {"idx" 1}}}]}}})
(defn empty-context [] (ir/prepare-host-program (ir/basis-for-class *engine-class*) [] []))
(defn rejected? [f] (try (f) false (catch Throwable _ true)))
(deftest in-memory-preparation-and-explicit-driver-use-one-linked-engine
  (let [ctx (ir/prepare-host-program (ir/basis-for-class *engine-class*) [(identity-row)] [])
        engine (ir/machine ctx)]
    (try
      (is (identical? *engine-class* (class engine)))
      (ir/start! ctx engine "identity" [37])
      (loop [left 10]
        (when (zero? left) (throw (ex-info "Adapter model exceeded budget" {})))
        (when-not (ir/advance! ctx engine 10) (recur (dec left))))
      (is (= 37 (ir/take-result! ctx engine)))
      (is (= "idle" (ir/phase ctx engine)))
      (is (= 42 (ir/call ctx engine "identity" [42])))
      (finally (ir/close! ctx engine)))))
(deftest header-admission-prepares-only-the-selected-body
  (let [base (empty-context) source (ir/source-binding base {:model "packaging-prepare"})
        row (identity-row) header (ir/declaration-header source row digest)
        registered (ir/register-headers base [header])
        ready (ir/materialize-body registered header row []) engine (ir/machine ready)]
    (try
      (is (= 1 (.functionCount (:program ready))))
      (is (= 99 (ir/call ready engine "identity" [99])))
      (is (identical? source (ir/request-value header "source")))
      (finally (ir/close! ready engine)))))
(deftest adapter-refuses-extended-policies-and-wrong-engine-class
  (is (rejected? #(ir/basis-for-class String)))
  (let [ctx (empty-context)]
    (is (rejected? #(ir/machine (assoc ctx :task-runtime (Object.)))))))
(defn check! [engine-class]
  (binding [*engine-class* engine-class] (run-tests 'ansatz-lean-jvm-prepare-checks)))
