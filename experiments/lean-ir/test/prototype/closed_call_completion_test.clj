(ns prototype.closed-call-completion-test
  (:require [clojure.test :refer [deftest is testing]]
            [prototype.machine :as m]))

(defn- functions []
  {:identity {:params [1] :body [:return [:var 1]]}})

(deftest publishes-actual-ownership-without-inventing-steps
  (let [fs (functions)
        [entry argument] (m/allocate (m/world fs) :ctor 0 [])
        [allocated result] (m/allocate entry :ctor 1 [])
        owned (m/release allocated argument 1)
        done (m/complete-closed-call entry owned fs :identity result)]
    (is (= :done (:status done)))
    (is (= result (:result done)))
    (is (= {:body nil :locals {} :joins {} :frames []}
           (select-keys done [:body :locals :joins :frames])))
    (is (not (contains? done :host-request)))
    (is (not (contains? done :resume-var)))
    (is (identical? (:heap owned) (:heap done)))
    (is (identical? (:stats owned) (:stats done)))
    (is (= 0 (get-in done [:stats :steps])))
    (is (= 2 (get-in done [:stats :allocations])))
    (is (= 1 (:rc (m/node done result))))
    (is (not (contains? (:heap done) (:id argument))))
    (is (= 1 (:rc (m/node entry argument))))
    (is (= (dissoc owned :body :locals :joins :frames :status :result)
           (dissoc done :body :locals :joins :frames :status :result)))))

(deftest completed-world-can-enter-another-ordinary-call
  (let [fs (functions)
        entry (m/run (m/start (m/world fs) :identity [7]))
        done (m/complete-closed-call entry entry fs :identity "λ\u0000🦉")
        next-world (m/run (m/start done :identity [42]))]
    (is (= "λ\u0000🦉" (:result done)))
    (is (= :done (:status next-world)))
    (is (= 42 (:result next-world)))
    (is (= (inc (get-in entry [:stats :steps]))
           (get-in next-world [:stats :steps])))))

(deftest rejects-code-generation-and-control-mismatches
  (let [fs (functions) entry (m/world fs)
        other-fs (into (sorted-map) fs)]
    (is (= fs other-fs))
    (is (not (identical? fs other-fs)))
    (doseq [[a b expected target]
            [[entry entry other-fs :identity]
             [entry (assoc entry :functions other-fs) fs :identity]
             [(assoc entry :functions other-fs) entry fs :identity]
             [entry entry fs :missing]]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"executable identity"
                           (m/complete-closed-call a b expected target 0))))
    (doseq [change [{:status :running} {:status :paused} {:status :failed}
                    {:frames [{:dest 0}]} {:host-request {:symbol "effect"}}
                    {:resume-var 0} {:body [:return [:imm 0]]}
                    {:locals {0 1}} {:joins {0 {}}} {:result 7}]]
      (testing (str change)
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unchanged idle"
                             (m/complete-closed-call entry (merge entry change) fs :identity 0)))))
    (let [running (assoc entry :status :running)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unchanged idle"
                           (m/complete-closed-call running running fs :identity 0))))))

(deftest rejects-foreign-or-released-result-carriers
  (let [fs (functions) entry (m/world fs)
        [allocated result] (m/allocate entry :ctor 0 [])
        released (m/release allocated result 1)]
    (doseq [result [(Object.) nil -1]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"legacy guest value"
                           (m/complete-closed-call entry entry fs :identity result))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (m/complete-closed-call allocated released fs :identity result)))))
