(ns prototype.runtime-audit-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.runtime-audit :as audit]
            [prototype.bootstrap :as bootstrap]))

(deftest inventories-real-interop-code-without-admitting-externs
  (let [report (audit/audit "fixtures/interop.jsonl")]
    (is (= 8 (:declarations report)))
    (is (= 6 (:functions report)))
    (is (= 2 (:extern-count report)))
    (is (= 2 (:extern-symbol-count report)))
    (is (= 6 (:admitted-by-current-importer report)))
    (is (= 2 (get-in report [:first-failure-per-declaration "Missing body or extern" :declarations])))
    (is (pos? (get-in report [:instructions "vdecl"])))
    (is (zero? (:persistent-rc-operations report)))))

(deftest invalid-bootstrap-request-is-rejected-before-running-native-tools
  (doseq [request [{:module "../escape" :roots ["x"]}
                   {:module "InteropProbe" :roots []}
                   {:module "InteropProbe" :roots [42]}]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"explicit roots" (bootstrap/load-file! request)))))
