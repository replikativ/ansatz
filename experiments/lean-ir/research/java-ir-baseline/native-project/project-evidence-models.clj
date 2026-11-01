(ns native-project-build-evidence-models-v2
  "Pure negative models. No mock data can issue a native BuildReceipt."
  (:require [clojure.test :refer [deftest is run-tests]]
            [native-project-build-evidence-v2 :as evidence]))
(defn- n [s] ["str" ["anonymous"] s])
(defn- row [name dependencies]
  {"kind" "decl" "name" name "dependencies" dependencies "redirect" nil
   "sourceModule" (n "Local") "sourceLocal" false
   "ir" {"fdecl" {"f" name "xs" [] "type" "object" "body" ["ret" {"idx" 0}]}}
   "runtime" {"role" "value" "initializer" nil "initializationAction" nil}})
(deftest no-caller-data-can-issue-receipt
  (doseq [v [nil {} {:accepted true} (native_project_build_evidence_v2.BuildReceipt.)]]
    (is (thrown? clojure.lang.ExceptionInfo (evidence/authenticated-build v)))))
(deftest typed-name-limits-and-numeric-distinction
  (is (= ["num" (n "A") "7"] (#'evidence/name! ["num" (n "A") "7"])))
  (doseq [bad [["num" (n "A") "07"] ["num" (n "A") "-1"] ["num" (n "A") "18446744073709551616"]
               ["num" (n "A") ""] ["str" (n "A") (str (char 0xD800))]]]
    (is (thrown? clojure.lang.ExceptionInfo (#'evidence/name! bad)))))
(deftest source-role-observation-is-not-reconstructed
  (let [name (n "cached") imported (row name []) source (-> imported (assoc "sourceLocal" true "pretty" "actual old source schema display")
                          (update "runtime" dissoc "initializationAction") (assoc-in ["runtime" "role"] "closed"))]
    (is (= {name source} (#'evidence/merge-source {name imported} {name source})))
    (is (not (contains? (get-in (#'evidence/merge-source {name imported} {name source}) [name "runtime"]) "initializationAction")))
    (doseq [bad [(assoc-in source ["ir" "fdecl" "body"] ["unreachable"])
                 (assoc source "sourceModule" (n "Other"))
                 (assoc-in source ["runtime" "initializer"] (n "init"))
                 (assoc-in source ["runtime" "role"] "initialized")]]
      (is (thrown? clojure.lang.ExceptionInfo (#'evidence/merge-source {name imported} {name bad}))))))
(deftest canonical-row-conflicts-and-full-static-closure
  (let [a (n "A") b (n "B") ra (row a [b]) rb (row b [])]
    (is (= {a ra b rb} (#'evidence/static-closure! {a ra b rb} [a])))
    (is (thrown? clojure.lang.ExceptionInfo (#'evidence/static-closure! {a ra} [a])))
    (is (thrown? clojure.lang.ExceptionInfo (#'evidence/row-index [ra (assoc ra "dependencies" [])])))))
(deftest requested-signature-is-not-proof
  (let [nat ["const" (n "Nat") []] unit ["const" (n "Unit") []] io ["const" (n "IO") []]]
    (is (nil? (#'evidence/expected-type! "io-unit" ["app" io unit])))
    (is (nil? (#'evidence/expected-type! "nat-to-nat" ["forall" (n "x") "default" nat nat])))
    (is (thrown? clojure.lang.ExceptionInfo (#'evidence/expected-type! "string-to-string" ["forall" (n "x") "default" nat nat])))))
(defn check! [] (run-tests 'native-project-build-evidence-models-v2))

(deftest foreign-identity-cannot-consult-issued-registry
  (let [consulted (atom false)
        foreign (proxy [Object] []
                  (hashCode [] (reset! consulted true) 17)
                  (equals [_] true))]
    (is (thrown? clojure.lang.ExceptionInfo (evidence/authenticated-build foreign)))
    (is (false? @consulted))))
(deftest aggregate-output-admission-precedes-json-work
  (let [budget (atom (- (* 64 1048576) 8))]
    (is (= (* 64 1048576) (#'evidence/charge-bytes! budget 8)))
    (is (thrown? clojure.lang.ExceptionInfo (#'evidence/charge-bytes! budget 1)))
    (is (= (* 64 1048576) @budget))
    (is (thrown? clojure.lang.ExceptionInfo (#'evidence/charge-bytes! budget -1)))))
