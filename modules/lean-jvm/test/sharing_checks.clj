(ns ansatz-lean-jvm-sharing-checks
  "Synthetic provenance/adversarial models, not native execution evidence."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.java.io :as io]
            [ansatz.lean.jvm.sharing :as sharing]))

(def ^:dynamic *module-root* ".")
(defn- n [s] ["str" ["anonymous"] s])
(def ^:private debug (n "debug"))
(def ^:private requirements {:externs {debug {:field "DBG_TRACE_SHARED"}}})
(defn- p [i] {"x" {"idx" i} "ty" "object" "borrow" false})
(defn- a [i] {"var" {"id" {"idx" i}}})
(defn- ret [i] ["ret" (a i)])
(defn- bind [i expression next] ["vdecl" {"idx" i} "object" expression next])
(defn- call [target arguments] {"fap" {"c" target "ys" arguments}})
(defn- trace [i next] (bind 90 (call debug ["erased" "erased" (a i)]) next))
(defn- ctor [] {"ctor" {"i" {"cidx" 0 "size" 1 "ssize" 0 "usize" 0} "ys" ["erased"]}})
(defn- literal [value] {"lit" {"v" (if (string? value) {"str" {"v" value}} {"num" {"v" value}})}})
(defn- f [name parameters body]
  {"name" name "ir" {"fdecl" {"f" name "xs" parameters "type" "object" "body" body}}})
(defn- check [rows] (sharing/check! rows [] requirements))
(defn- denied? [run]
  (try (run) false
    (catch clojure.lang.ExceptionInfo failure
      (= :sharing-managed-domain (:restriction (ex-data failure))))))
(defn- root [name expression target]
  (f (n name) [] (bind 1 expression (bind 2 (call target [(a 1)]) (ret 2)))))

(deftest dormant-without-a-diagnostic-requirement
  (is (= {} (sharing/check! [{"unrelated" true}] [] {}))))

(deftest managed-immediate-and-untracked-leaf-origins
  (doseq [expression [(ctor) (literal 0) (literal Long/MAX_VALUE)]]
    (is (= requirements (check [(f (n "root") [] (bind 1 expression (trace 1 (ret 90))))]))))
  (doseq [expression [(literal "leaf") (literal (inc (bigint Long/MAX_VALUE)))
                      {"box" {"ty" "uint64" "x" {"idx" 1}}}
                      {"ap" {"x" {"idx" 1} "ys" []}}
                      {"proj" {"x" {"idx" 1} "i" 0}}]]
    (is (denied? #(check [(f (n "root") [] (bind 1 (ctor) (bind 2 expression (trace 2 (ret 90)))))])))))

(deftest every-direct-caller-must-establish-the-invariant
  (let [helper (f (n "helper") [(p 1)] (trace 1 (ret 90)))
        good (root "good" (ctor) (n "helper"))
        bad (root "bad" (literal "leaf") (n "helper"))]
    (is (= requirements (check [helper good])))
    (is (denied? #(check [helper good bad])))
    (is (denied? #(check [helper])))))

(deftest recursive-invariant-needs-an-established-boundary
  (let [helper (f (n "helper") [(p 1)]
                  (trace 1 (bind 2 (call (n "helper") [(a 90)]) (ret 2))))]
    (is (= requirements (check [helper (root "good" (ctor) (n "helper"))])))
    (is (denied? #(check [helper])))))

(deftest every-return-branch-is-required
  (let [caller (f (n "caller") [] (bind 1 (call (n "value") []) (trace 1 (ret 90))))
        value (fn [bad?]
                (f (n "value") []
                   ["case" (n "Bool") {"idx" 0} "uint8"
                    [["default" (bind 1 (ctor) (ret 1))]
                     ["default" (bind 2 (if bad? (literal "leaf") (ctor)) (ret 2))]]]))]
    (is (= requirements (check [caller (value false)])))
    (is (denied? #(check [caller (value true)])))))

(deftest lexical-join-arguments-are-universal
  (let [row (fn [expression]
              (f (n "join") []
                 ["jdecl" {"idx" 1} [(p 3)] (trace 3 (ret 90))
                  ["case" (n "Bool") {"idx" 0} "uint8"
                   [["default" (bind 1 (ctor) ["jmp" {"idx" 1} [(a 1)]])]
                    ["default" (bind 2 expression ["jmp" {"idx" 1} [(a 2)]])]]]]))]
    (is (= requirements (check [(row (ctor))])))
    (is (denied? #(check [(row (literal "leaf"))])))))

(deftest no-partial-application-backdoor
  (let [helper (f (n "helper") [(p 1)] (trace 1 (ret 90)))
        escape (fn [target] (f (n "escape") [] (bind 1 {"pap" {"c" target "ys" []}} (ret 1))))]
    (is (denied? #(check [(escape debug)])))
    (is (denied? #(check [helper (root "good" (ctor) (n "helper")) (escape (n "helper"))])))
    ;; Unrelated closures need not force a general higher-order analysis.
    (is (= requirements (check [helper (root "good" (ctor) (n "helper")) (escape (n "unrelated"))])))))

(deftest only-reviewed-extern-result-factories
  (let [factory (n "factory")
        rows [(f (n "root") [] (bind 1 (call factory []) (trace 1 (ret 90))))]]
    (is (= (assoc-in requirements [:externs factory] {:field "ARRAY_EMPTY"})
           (sharing/check! rows [] (assoc-in requirements [:externs factory] {:field "ARRAY_EMPTY"}))))
    (doseq [field ["ARRAY_GET" "STR_APPEND" "UNKNOWN"]]
      (is (denied? #(sharing/check! rows [] (assoc-in requirements [:externs factory] {:field field})))))))

(defn- entry-case [entry-name]
  (let [document (json/read-str (slurp (io/file *module-root* "test/fixtures/general-entry-v2.json")))
        e (first (filter #(= entry-name (last (get % "name"))) (get document "entries")))
        target (get-in e ["raw" "name"])
        ;; Deliberately synthetic body substitution. The fixture supplies real
        ;; structural entry metadata, not authority for this changed source.
        rows (mapv (fn [row]
                     (if (= target (get row "name"))
                       (assoc-in row ["ir" "fdecl" "body"] (trace 1 (ret 90))) row))
                   (get document "declarations"))]
    [rows [e]]))

(deftest checked-entry-roots-distinguish-immediates-from-heap-leaves
  (let [[rows entries] (entry-case "unitIdentity")]
    (is (= requirements (sharing/check! rows entries requirements)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (sharing/check! rows (assoc-in entries [0 "argumentPlan"] []) requirements))))
  (doseq [name ["counts" "greet"]]
    (let [[rows entries] (entry-case name)]
      (is (denied? #(sharing/check! rows entries requirements))))))

(deftest initialization-roots-and-analysis-budget
  (let [initializer (n "initialize")
        row (assoc (f initializer [(assoc (p 1) "ty" "void")] (trace 1 (ret 90)))
                   "runtime" {"initializer" initializer})]
    (is (= requirements (check [row])))
    (is (denied? #(check [(assoc-in row ["ir" "fdecl" "xs" 0 "ty"] "object")])))
    (is (denied? #(with-redefs-fn {#'sharing/maximum-work 2} (fn [] (check [row])))))))

(defn check! [] (run-tests 'ansatz-lean-jvm-sharing-checks))
(defn -main [& _]
  (let [result (check!)]
    (when (pos? (+ (:fail result) (:error result))) (System/exit 1))))
