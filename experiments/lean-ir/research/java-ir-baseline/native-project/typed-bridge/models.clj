(ns native-typed-bridge-models-v1
  (:require [clojure.test :refer [deftest is run-tests]]
            [native-typed-bridge-probe-v1 :as p])
  (:import [java.math BigInteger]))
(deftest exact-immutable-carrier-domain
  (doseq [n [(long 0) Long/MAX_VALUE (.shiftLeft BigInteger/ONE 80)]]
    (is (= n (#'p/nat! n))))
  (doseq [n [nil -1 (int 1) (bigint 1) (.shiftLeft BigInteger/ONE 4097)]]
    (is (thrown? Exception (#'p/nat! n))))
  (let [calls (atom 0) mutable (proxy [BigInteger] ["1"] (signum [] (swap! calls inc) 0))]
    (is (thrown? Exception (#'p/nat! mutable)))
    (is (zero? @calls)))
  (doseq [s ["" "ascii" "a\u0000b" "λ😀"]] (is (= s (#'p/string! s))))
  (is (thrown? Exception (#'p/string! (String. (char-array [(char 0xd800)]))))))
(deftest requested-template-is-structural-not-a-caller-tag
  (let [nat ["const" ["str" ["anonymous"] "Nat"] []]
        good ["forall" ["str" ["anonymous"] "ignored-binder"] "default" nat nat]]
    (is (nil? (#'p/expected-type! "nat-to-nat" good)))
    (is (thrown? Exception (#'p/expected-type! "string-to-string" good)))
    (is (thrown? Exception (#'p/expected-type! "nat-to-nat" (assoc good 2 "implicit"))))))
(deftest initializer-and-dynamic-application-are-explicit-frontiers
  (let [row {"runtime" {"role" "ordinary" "initializer" nil "initializationAction" nil}
             "redirect" nil "ir" {"fdecl" {"body" ["ret" {}]}}}]
    (is (= row (#'p/pure-row! row)))
    (doseq [changed [(assoc-in row ["runtime" "initializer"] ["anonymous"])
                     (assoc-in row ["runtime" "initializationAction"] "io")
                     (assoc-in row ["runtime" "role"] "initialized")
                     (assoc row "redirect" {})
                     (assoc-in row ["ir" "fdecl" "body"] {"ap" {}})]]
      (is (thrown? Exception (#'p/pure-row! changed))))))
(deftest typed-name-validation-and-static-closure
  (let [a (p/entry-name "A" "x") row {"name" a "runtime" {"role" "ordinary"} "dependencies" []}]
    (is (= "A.x" (#'p/label a)))
    (is (= {a row} (#'p/closure {a row} [a])))
    (is (thrown? Exception (#'p/closure {} [a])))
    (doseq [n [nil ["num" ["anonymous"] "01"] ["num" ["anonymous"] "18446744073709551616"]]]
      (is (thrown? Exception (#'p/label n))))))
(deftest no-caller-map-or-unissued-token-authority
  (doseq [x [nil {} {:accepted true} (p/->Session)]]
    (is (thrown? Exception (p/invoke! x (p/entry-name "NativeEntryCases" "natStep") 0)))
    (is (thrown? Exception (p/close! x)))))
(defn check! [] (run-tests 'native-typed-bridge-models-v1))
