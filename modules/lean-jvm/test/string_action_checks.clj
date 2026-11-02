(ns ansatz-lean-jvm-string-action-checks
  "Actual JVM String.any action classification, not source/native acceptance."
  (:require [clojure.test :refer [deftest is run-tests]]
            [ansatz.lean.jvm.ir :as ir] [ansatz.lean.jvm.capabilities :as caps]
            [ansatz.lean.jvm.startup :as startup])
  (:import [java.lang.reflect InvocationTargetException]))

(defn name-of [s] ["str" ["anonymous"] s])
(defn arg [i] {"var" {"id" {"idx" i}}})
(defn param [i type] {"x" {"idx" i} "ty" type "borrow" false})
(defn decl [i type expression next] ["vdecl" {"idx" i} type expression next])
(defn external [label symbol result types]
  {"kind" "decl" "name" (name-of label)
   "ir" {"extern" {"f" (name-of label) "type" result "xs" (mapv param (iterate inc 1) types)
                    "ext" {"entries" [{"standard" {"backend" (name-of "all") "fn" symbol}}]}}}})
(def rows
  [(external "any" "lean_string_any" "uint8" ["object" "object"])
   (external "prefix" "lean_string_isprefixof" "uint8" ["object" "object"])
   (external "eq" "lean_uint32_dec_eq" "uint8" ["uint32" "uint32"])
   {"kind" "decl" "name" (name-of "predicate")
    "ir" {"fdecl" {"f" (name-of "predicate") "type" "uint8" "xs" [(param 1 "object") (param 2 "object")]
                     "body" (decl 3 "uint32" {"unbox" {"x" {"idx" 1}}}
                              (decl 4 "uint32" {"unbox" {"x" {"idx" 2}}}
                                (decl 5 "uint8" {"fap" {"c" (name-of "eq") "ys" [(arg 3) (arg 4)]}}
                                  ["ret" (arg 5)])))}}}
   {"kind" "decl" "name" (name-of "make")
    "ir" {"fdecl" {"f" (name-of "make") "type" "object" "xs" [(param 1 "object")]
                     "body" (decl 2 "object" {"pap" {"c" (name-of "predicate") "ys" [(arg 1)]}}
                              ["ret" (arg 2)])}}}])
(defn field [value label] (#'startup/engine-field value label))
(defn set-field! [value label replacement]
  (let [f (.getDeclaredField (class value) label)] (.setAccessible f true) (.set f value replacement)))
(defn classify! [{:keys [ctx requirements]} action]
  (#'startup/heap-action-chain! action requirements (:program ctx)))
(defn rejected? [f] (try (f) false (catch clojure.lang.ExceptionInfo _ true)))
(defn paused []
  (let [basis (ir/linked-basis) ctx (ir/prepare-host-program basis rows []) engine (ir/machine ctx)
        predicate (ir/call ctx engine "make" [65])]
    (ir/start! ctx engine "any" [(apply str (repeat 100 "x")) predicate])
    (ir/advance! ctx engine 1)
    {:ctx ctx :engine engine :requirements (caps/check-rows! basis rows)}))
(defn finish! [{:keys [ctx engine]}]
  (loop [left 32]
    (when (zero? left) (throw (AssertionError. "String.any completion exceeded model budget")))
    (when (= "running" (ir/phase ctx engine)) (ir/advance! ctx engine 128) (recur (dec left))))
  (is (= 0 (ir/take-result! ctx engine))) (ir/close! ctx engine))

(deftest paused-native-string-action-is-classified-with-its-actual-program
  (let [{:keys [ctx engine] :as sample} (paused)]
    (try
      (is (= "running" (ir/phase ctx engine)))
      (let [action (field engine "runtimeAction")]
        (is (some? action)) (is (nil? (classify! sample action)))
        (is (nil? (classify! sample (field engine "failedRuntimeAction")))))
      (finally (finish! sample)))))

(deftest same-intrinsic-from-another-program-and-other-native-functions-are-refused
  (let [{:keys [ctx engine] :as sample} (paused)
        other (ir/prepare-host-program (ir/linked-basis) rows [])
        action (field engine "runtimeAction") original (field action "function")
        own-functions (field (:program ctx) "functions") other-functions (field (:program other) "functions")]
    (try
      (is (rejected? #(classify! (assoc sample :ctx other) action)))
      (set-field! action "function" (aget ^objects other-functions (int (ir/function-id other "any"))))
      (is (rejected? #(classify! sample action)))
      (set-field! action "function" (aget ^objects own-functions (int (ir/function-id ctx "prefix"))))
      (is (rejected? #(classify! sample action)))
      (finally (set-field! action "function" original) (finish! sample)))))

(deftest native-string-action-cannot-carry-foreign-resource-protocol
  (let [{:keys [engine] :as sample} (paused) action (field engine "runtimeAction")]
    (try
      (doseq [label ["guest" "completion" "request" "task" "scope"]]
        (let [f (.getDeclaredField (class action) label)
              constructor (first (.getDeclaredConstructors (.getType f)))]
          (.setAccessible constructor true)
          (try
            ;; Zeroed typed protocol records are refusal probes, never invoked.
            (set-field! action label (.newInstance constructor (object-array (count (.getParameterTypes constructor)))))
            (is (rejected? #(classify! sample action)) label)
            (finally (set-field! action label nil)))))
      (finally (finish! sample)))))

(deftest cancelled-string-action-remains-a-classifiable-terminal-heap-root
  (let [thread (Thread/currentThread) interrupted? (Thread/interrupted)]
    (try
      (let [{:keys [ctx engine] :as sample} (paused)
            failure (try
                      (.interrupt thread)
                      (dotimes [_ 32] (ir/advance! ctx engine 1)) nil
                      (catch InvocationTargetException e (.getCause e)))]
        (Thread/interrupted)
        (is (some? failure))
        (when failure (is (= "Cancelled" (.code failure))))
        (is (= "failed" (ir/phase ctx engine)))
        (let [roots (mapv #(field engine %) ["runtimeAction" "failedRuntimeAction"])]
          (is (some some? roots))
          (doseq [action roots] (is (nil? (classify! sample action)))))
        ;; Failed explicit engines cannot be closed or replayed. Classification
        ;; permits dropping this stopped pure heap; no DEC/unwinding is invented.
        )
      (finally (Thread/interrupted) (when interrupted? (.interrupt thread))))))

(defn check! [] (run-tests 'ansatz-lean-jvm-string-action-checks))
