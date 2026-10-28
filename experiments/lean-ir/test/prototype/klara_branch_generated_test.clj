(ns prototype.klara-branch-generated-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.klara-branch-generated :as generated]
            [prototype.branch-lab :as lab]
            [prototype.machine :as m]))

(defn trial [backend]
  (let [{:keys [world cell closure functions]} (generated/fixture)
        run (lab/runner backend functions)
        finish (fn [answer]
                 (let [emitting (run world answer)
                       done (run emitting 0)]
                   (is (= :host-call (:status emitting)))
                   (is (= {:symbol :lab/emit :arguments [answer]}
                          (select-keys (:host-request emitting) [:symbol :arguments])))
                   ;; Generated dec instructions free both aliases before output.
                   (is (not (contains? (:heap emitting) (:id cell))))
                   (is (not (contains? (:heap emitting) (:id closure))))
                   (is (= answer (generated/result-value done)))
                   (is (= 1 (count (:heap done))))
                   (let [disposed (generated/dispose-result done)]
                     (is (= {} (:heap disposed)))
                     (is (= :disposed (:status disposed)))
                     [emitting done disposed])))
        left (finish 10) right (finish 20)]
    (is (= [0] (:fields (m/node world cell))))
    (is (= [cell] (:fields (m/node world closure))))
    (is (= 2 (:rc (m/node world cell))))
    [world left right]))

(deftest generated-front-end-alias-and-lifetime-parity
  ;; Exact World equality includes stores, RC, continuations, outputs and stats.
  (is (apply = (mapv trial [:persistent :mutable :compiled]))))

(defn completed-fixture []
  (let [{:keys [world functions]} (generated/fixture)
        run (lab/runner :persistent functions)]
    (run (run world 10) 0)))

(deftest existing-owner-ledger-escrows-result-and-does-not-repeat-drop
  (let [done (completed-fixture)
        state (generated/result-disposal-ledger done)
        validations (atom 0)
        disposed (generated/dispose-recorded-result! state :result
                   (fn [_] (swap! validations inc)))]
    (is (identical? done (:returned-world @state)))
    (is (identical? (:result done) (:returned-owner @state)))
    (is (identical? disposed
          (generated/dispose-recorded-result! state :result
            (fn [_] (throw (ex-info "Must not repeat validation or drop" {}))))))
    (is (= 1 @validations))
    (is (thrown? clojure.lang.ExceptionInfo
          (generated/dispose-recorded-result! state :different-key)))
    (is (= :completed (get-in @state [:cleanup-operations :result :phase])))
    (is (= {} (:heap disposed)))
    (is (false? (:unsafe-partial? @state)))
    (is (= 10 (generated/result-value done)))))

(deftest failed-post-validation-preserves-actual-return-and-blocks-retry
  (let [done (completed-fixture)
        state (generated/result-disposal-ledger done)
        validations (atom 0)]
    (is (thrown? clojure.lang.ExceptionInfo
          (generated/dispose-recorded-result! state :result
            (fn [_] (swap! validations inc) (throw (ex-info "Audit failed" {}))))))
    (is (true? (:unsafe-partial? @state)))
    (is (= :failed (get-in @state [:cleanup-operations :result :phase])))
    (is (= :disposed (get-in @state [:cleanup-operations :result :result :status])))
    (is (= {} (get-in @state [:cleanup-operations :result :result :heap])))
    (is (identical? done (:returned-world @state)))
    (is (thrown? clojure.lang.ExceptionInfo
          (generated/dispose-recorded-result! state :result)))
    (is (= 1 @validations))))

(deftest invalid-world-is-recorded-but-never-dropped
  (let [done (completed-fixture)
        ;; An unrelated resource owner makes this ineligible for fixture cleanup.
        [invalid _] (m/allocate done :resource 251 [42])
        state (generated/result-disposal-ledger invalid)]
    (is (thrown? clojure.lang.ExceptionInfo
          (generated/dispose-recorded-result! state :result)))
    (is (identical? invalid (:returned-world @state)))
    (is (= [] (:events (:returned-world @state))))
    (is (= 2 (count (:heap (:returned-world @state)))))
    (is (nil? (get-in @state [:cleanup-operations :result :result])))
    (is (true? (:unsafe-partial? @state)))))
