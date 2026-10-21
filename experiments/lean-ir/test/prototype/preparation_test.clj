(ns prototype.preparation-test
  "Trusted-link orchestration models; no claim of actual frontend acceptance."
  (:require [clojure.test :refer [deftest is]]
            [prototype.preparation :as preparation]
            [prototype.eval-const :as eval]
            [prototype.import-ir :as ir]))

(defn function [body] {:params [] :body body})
(defn catalogue [functions]
  {:manifests [] :declarations (into {} (map (fn [[name f]] [name {:name name :function f}])) functions)})
(defn lower [row] [(:name row) (:function row)])

(deftest completes-existing-bodies-and-runtime-helpers-preserving-identities
  (let [root (function [:tail [:direct :middle] []])
        old-helper (assoc (function [:return [:imm 0]]) :runtime-dependencies [:leaf])
        middle (assoc (function [:return [:imm 0]]) :runtime-dependencies [:old-helper])
        leaf (function [:tail [:direct :root] []])
        before {:root root :old-helper old-helper :unrelated (function [:return [:imm 1]])}
        reads (atom [])
        complete (preparation/complete-functions (catalogue {:middle middle :leaf leaf}) before [:root]
                                                 (fn [row] (swap! reads conj (:name row)) (lower row)))]
    (is (= #{:middle :leaf} (set @reads)))
    (doseq [[name original] before] (is (identical? original (get complete name))))
    (is (= #{:root :middle :old-helper :leaf}
           (set (keys (eval/validate-executables! {:functions complete} complete [:root])))))
    (is (not (contains? before :middle)))
    (is (= complete (preparation/complete-functions (catalogue {}) complete [:root]
                                                    (fn [_] (throw (AssertionError. "must reuse existing code"))))))))

(deftest new-global-wrappers-are-validated-without-initialization
  (let [root (function [:tail [:direct :constant] []])
        complete (preparation/complete-functions
                  (catalogue {:constant (assoc (function [:return [:imm 42]]) :global-role "closed")})
                  {:root root} [:root] lower)
        wrapper ["str" :constant "_ansatz_global_initializer"]]
    (is (identical? root (:root complete)))
    (is (= [:global :constant wrapper] (:body (:constant complete))))
    (is (= [:return [:imm 42]] (:body (get complete wrapper))))
    (is (= #{:root :constant wrapper}
           (set (keys (eval/validate-executables! {:functions complete} complete [:root])))))))

(deftest static-edges-ignore-literals-and-inspect-executable-positions
  (let [body [:let 1 [:imm [:direct :literal-only]]
              [:let 2 [:closure :captured []]
               [:case [:imm 0]
                [[0 [:call 3 [:direct :callee] [] [:return [:imm [:closure :also-literal []]]]]]
                 [1 [:begin-init :global-name :initializer [] "object"]]]]]]
        f (assoc (function body) :runtime-dependencies [:runtime])
        expected #{:captured :callee :initializer :runtime}]
    (is (= (disj expected :runtime) (ir/static-targets body)))
    (is (= expected (eval/executable-dependencies f)))
    (let [functions (into {:root f} (map #(vector % (function [:return [:imm 0]])) expected))]
      (is (= (conj expected :root)
             (set (keys (eval/validate-executables! {:functions functions} functions [:root]))))))))

(deftest missing-and-malformed-edges-fail-closed
  (doseq [f [(function [:tail [:direct :missing] []])
             (assoc (function [:return [:imm 0]]) :runtime-dependencies [:missing])
             (function [:global :x ["str" :x "_ansatz_global_initializer"]])]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Missing declaration dependency"
                          (preparation/complete-functions (catalogue {}) {:root f} [:root] lower))))
  (doseq [f [(function [:tail [:direct nil] []])
             (function [:let 1 [:closure nil []] [:return [:var 1]]])
             (function [:global :x nil])
             (function [:begin-init :x nil [] "object"])
             (assoc (function [:return [:imm 0]]) :runtime-dependencies [nil])
             (assoc (function [:return [:imm 0]]) :runtime-dependencies nil)]]
    (is (thrown? clojure.lang.ExceptionInfo (eval/executable-dependencies f)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (preparation/complete-functions (catalogue {}) {:root f} [:root] lower))))
  (is (thrown? clojure.lang.ExceptionInfo
               (preparation/complete-functions (catalogue {}) {} [nil] lower)))
  (is (thrown? clojure.lang.ExceptionInfo
               (eval/validate-executables! {:functions {}} {} [nil])))
  (let [functions {false (function [:tail [:direct :missing] []])}]
    (is (thrown? clojure.lang.ExceptionInfo
                 (eval/validate-executables! {:functions functions} functions [false])))))
