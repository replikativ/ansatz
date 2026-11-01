(ns prototype.klara-branch-bridge-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.branch-lab :as lab]
            [prototype.branch-lab-test :refer [rejected?]]
            [prototype.klara-branch-generated :as generated]
            [prototype.machine :as m]))

(deftest generated-program-composes-with-branch-authority-and-scoped-execution
  (let [{:keys [world cell functions]} (generated/fixture)
        admitted (lab/admit-choice world)
        all-results
        (for [backend [:persistent :mutable :compiled] scoped? [false true]]
          (let [s (lab/session admitted {:version :pinned})
                [a b] (lab/fork! s (:initial s))
                run ((if scoped? lab/scoped-runner lab/runner) backend functions)
                advance! (if scoped? lab/advance-scoped! lab/advance!)
                a (advance! s a run 10) b (advance! s b run 20)
                packets (mapv #(lab/snapshot s %) [a b])
                trace (atom [])]
            (is (= [10 20] (mapv #(generated/result-value (:world %)) packets)))
            (is (= [[10] [20]] (mapv :outbox packets)))
            (is (= [0] (:fields (m/node world cell))))
            (doseq [packet packets]
              (is (empty? (:heap (generated/dispose-result (:world packet))))))
            (lab/adopt! s a #(swap! trace conj %))
            (is (rejected? #(lab/adopt! s b identity)))
            (is (= [10] @trace))
            packets))]
    (is (apply = all-results))))

(deftest choice-classification-does-not-admit-other-host-effects
  (let [{:keys [world]} (generated/fixture)]
    (is (rejected? #(lab/session world {})))
    (is (rejected? #(lab/admit-choice (assoc-in world [:host-request :symbol] :lab/emit))))
    (is (rejected? #(lab/admit-choice (assoc-in world [:host-request :arguments] []))))
    (is (rejected? #(lab/admit-choice (assoc-in world [:host-request :dest] -1))))))

(deftest family-selection-and-owner-cleanup-compose-as-separate-ledgers
  (let [{:keys [world functions cell]} (generated/fixture)
        s (lab/session (lab/admit-choice world) {})
        [a b] (lab/fork! s (:initial s))
        run (lab/scoped-runner :compiled functions)
        a (lab/advance-scoped! s a run 10)
        b (lab/advance-scoped! s b run 20)
        retired (lab/snapshot s b)
        selected (lab/adopt! s a identity)
        ledgers (mapv #(generated/result-disposal-ledger (:world %)) [selected retired])]
    ;; Logical result owners belong to separate guest branches; both may retire.
    ;; This sequence deliberately makes no cross-ledger atomicity claim.
    (doseq [[index ledger] (map-indexed vector ledgers)]
      (let [key [:branch index :result]
            disposed (generated/dispose-recorded-result! ledger key)]
        (is (= {} (:heap disposed)))
        (is (identical? disposed (generated/dispose-recorded-result! ledger key)))))
    (is (= [0] (:fields (m/node world cell))))
    (is (= :adopted (:family @(:ledger s))))))
