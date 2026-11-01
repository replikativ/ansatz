(ns ansatz-lean-jvm-publisher-models
  "Pure publisher models; toy metadata is never issued or executed."
  (:require [clojure.test :refer [deftest is run-tests]]
            [ansatz.lean.jvm.publisher :as project]
            [ansatz-lean-jvm-module-startup-models :as module]))
(def n ["str" ["anonymous"] "entry"])
(def row {"kind" "decl" "name" n "dependencies" [] "sourceModule" module/n "sourceLocal" false
          "runtime" {"role" "ordinary" "initializer" nil}
          "ir" {"fdecl" {"f" n "xs" [{"borrow" false "ty" "object" "x" {"idx" 1}}]
                          "type" "object" "body" ["ret" {"var" {"id" {"idx" 1}}}]}}})
(def abi {"name" n "xs" [{"borrow" false "ty" "object" "x" {"idx" 1}}] "type" "object"})
(def entry {"name" n "levelParams" [] "raw" abi "callable" abi
            "typeCheck" {"signature" "nat-to-nat" "algorithm" "Lean.Meta.isDefEq" "transparency" "default"}})
(defn payload []
  {:profile "native-project-build-evidence/2" :rows {n row} :entries [entry]
   :startup (assoc (module/capture [(module/module-row [] [] "all" false)]) "declarations" [row])})
(defn validate! [data] ((ns-resolve 'ansatz.lean.jvm.publisher 'validate-combined!) data))
(deftest only-issued-build-receipts-can-enter-public-publisher
  (doseq [fake [nil {} {:profile "native-project-build-evidence/2" :authenticated true} (Object.)]]
    (is (thrown? Exception (project/prepare! nil fake "unused-codec")))))
(deftest combined-canonical-rows-and-native-entries-remain-unchanged
  (let [data (payload) admitted (validate! data)]
    (is (= [row] (:rows admitted)))
    (is (identical? row (first (:rows admitted))))
    (is (identical? (:entries data) (:entries admitted)))
    (is (= 1 (count (get-in admitted [:plan :modules]))))))
(deftest changed-source-body-or-dependency-refused
  (is (thrown? Exception (validate! (assoc-in (payload) [:rows n "ir" "fdecl" "body"] ["unreachable"]))))
  (is (thrown? Exception (validate! (assoc-in (payload) [:rows n "dependencies"] [module/n])))))
(deftest imported-value-source-closed-observation-is-not-a-fabricated-initializer
  (let [data (-> (payload)
                 (assoc-in [:rows n "sourceLocal"] true)
                 (assoc-in [:rows n "runtime" "role"] "closed")
                 (assoc-in [:startup "declarations" 0 "runtime" "role"] "value"))
        selected (first (:rows (validate! data)))]
    (is (= "closed" (get-in selected ["runtime" "role"])))
    (is (not (contains? (get selected "runtime") "initializationAction")))))
(deftest wrong-native-type-or-callable-abi-refused
  (doseq [bad [(assoc-in (payload) [:entries 0 "callable" "type"] "uint64")
               (assoc-in (payload) [:entries 0 "typeCheck" "algorithm"] "caller-asserted")
               (assoc-in (payload) [:entries 0 "levelParams"] [module/n])]]
    (is (thrown? Exception (validate! bad)))))
(deftest typed-display-collision-refused-before-header-construction
  (let [left ["str" ["anonymous"] "x.y"] right ["str" ["str" ["anonymous"] "x"] "y"]
        rename #(-> row (assoc "name" %) (assoc-in ["ir" "fdecl" "f"] %))]
    (is (thrown-with-msg? Exception #"display collision"
                          (validate! (assoc (payload) :rows {left (rename left) right (rename right)}))))))
(deftest deeply-nested-body-refused-before-json-or-header
  (let [nested (nth (iterate vector 0) 257)]
    (is (thrown-with-msg? Exception #"nesting limit"
                          (validate! (assoc-in (payload) [:rows n "ir" "fdecl" "body"] nested))))))
(deftest artifact-observation-profile-shares-validation-not-authority
  (is (= [row] (:rows (validate! (assoc (payload) :profile "lean-native-local-project/2")))))
  (is (thrown? Exception (validate! (assoc (payload) :profile "caller-accepted")))))
(defn check! [] (run-tests 'ansatz-lean-jvm-publisher-models))
