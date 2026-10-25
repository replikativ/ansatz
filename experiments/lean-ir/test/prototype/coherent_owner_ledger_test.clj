(ns prototype.coherent-owner-ledger-test
  (:require [clojure.test :refer [deftest is testing]]
            [prototype.coherent-owner-ledger :as owners]))

(defn- thrown [f] (try (f) nil (catch Throwable failure failure)))
(defn- counter [calls key result failure]
  (fn [& _] (swap! calls update key (fnil inc 0))
    (when failure (throw failure)) result))

(deftest pre-adoption-rejection-keeps-checked-environment-and-lease
  (let [state (atom {:phase :ready}) checked (Object.) prepared (Object.) lease (Object.)
        calls (atom {}) failure (ex-info "bad Factory/controller/configuration" {})]
    (owners/claim-execution! state lease checked prepared)
    (is (identical? failure
          (thrown #(owners/recover! state failure (counter calls :lease-close nil nil)))))
    (is (empty? @calls))
    (is (= :before-adoption (:owner-phase @state)))
    (is (identical? checked (:checked-before-adoption @state)))
    (is (identical? lease (:lease @state)))
    (is (not= :disposed (:disposal-phase @state)))))

(deftest failed-adoption-never-disposes-earlier-checked-snapshot
  (let [state (atom {:phase :ready}) failure (ex-info "partial adoption" {}) calls (atom {})]
    (owners/claim-execution! state :lease :checked :prepared)
    (is (identical? failure (thrown #(owners/adopt! state (counter calls :adopt nil failure)))))
    (thrown #(owners/recover! state failure (counter calls :cleanup nil nil)))
    (is (= {:adopt 1} @calls))
    (is (= :adopting (:owner-phase @state)))
    (is (nil? (:resident-context @state)))))

(deftest successful-adoption-escrows-actual-context-before-clearing-unsafe
  (let [state (atom {:phase :ready}) context (Object.)]
    (owners/claim-execution! state :lease :checked :prepared)
    (is (identical? context (owners/adopt! state (constantly context))))
    (is (identical? context (:resident-context @state)))
    (is (false? (:unsafe-partial? @state)))
    (is (= :claimed (owners/begin-disposal! state)))))

(deftest eio-and-primary-prefix-release-failures-are-never-retried
  (doseq [role [:eio-prefix :primary-prefix]]
    (testing (str role)
      (let [state (atom {}) calls (atom {}) failure (ex-info "partial release" {})
            release (counter calls :release nil failure) close (counter calls :close nil nil)
            cleanup #(owners/release-prefix! state role {:context :old :prefix :p} release close true)]
        (is (identical? failure (thrown cleanup)))
        (is (identical? failure (thrown #(owners/recover! state failure cleanup))))
        (is (some? (thrown cleanup)))
        (is (= {:release 1} @calls))
        (is (= :failed (get-in @state [:cleanup-operations [role :release] :phase])))
        (is (not= :disposed (:disposal-phase @state)))))))

(deftest returned-prefix-context-survives-close-failure-with-no-old-branch-replay
  (doseq [role [:eio-prefix :primary-prefix]]
    (let [state (atom {}) calls (atom {}) returned {:context (Object.)}
          failure (ex-info "close returned Context failed" {})
          release (counter calls :release returned nil) close (counter calls :close nil failure)
          cleanup #(owners/release-prefix! state role {:context :old :prefix :p} release close true)]
      (is (identical? failure (thrown cleanup)))
      (is (identical? returned (get-in @state [:cleanup-operations [role :release] :result])))
      (thrown #(owners/recover! state failure cleanup))
      (is (some? (thrown cleanup)))
      (is (= {:release 1 :close 1} @calls)))))

(deftest original-prefix-context-close-failure-does-not-repeat-either-close
  (let [state (atom {}) calls (atom {}) failure (ex-info "old branch close failed" {})
        close (fn [context] (swap! calls update context (fnil inc 0))
                (when (= :old context) (throw failure)))
        cleanup #(owners/release-prefix! state :primary-prefix {:context :old :prefix :p}
                   (counter calls :release {:context :returned} nil) close true)]
    (is (identical? failure (thrown cleanup)))
    (thrown #(owners/recover! state failure cleanup))
    (is (= {:release 1 :returned 1 :old 1} @calls))
    (is (= :failed (:disposal-phase @state)))))

(deftest disposal-on-normal-path-is-not-restarted-by-catch
  (doseq [key [[:context-close 0] [:lease-close]]]
    (let [state (atom {}) calls (atom {}) failure (ex-info "disposition failed" {})
          cleanup (fn [] (swap! calls update :cleanup (fnil inc 0))
                    (owners/begin-disposal! state)
                    (owners/operation! state key (counter calls :operation nil failure)))]
      (is (identical? failure (thrown cleanup)))
      (is (identical? failure (thrown #(owners/recover! state failure cleanup))))
      (is (= {:cleanup 1 :operation 1} @calls))
      (is (some? (thrown #(owners/begin-disposal! state))))
      (is (= :failed (:disposal-phase @state))))))

(deftest returned-result-is-escrowed-before-fallible-invariant
  (let [state (atom {}) calls (atom {}) actual (Object.) failure (ex-info "invariant" {})]
    (is (identical? failure
          (thrown #(owners/operation! state [:lease-close]
                     (counter calls :close actual nil) (fn [_] (throw failure))))))
    (is (identical? actual (get-in @state [:cleanup-operations [:lease-close] :result])))
    (thrown #(owners/recover! state failure (counter calls :retry nil nil)))
    (is (= {:close 1} @calls))
    (is (= :failed (:disposal-phase @state)))))

(deftest independent-cleanup-error-preserves-original-failure
  (let [state (atom {}) original (ex-info "stage" {}) cleanup (ex-info "cleanup" {}) calls (atom {})]
    (is (identical? original
          (thrown #(owners/recover! state original
                     (fn [] (owners/begin-disposal! state)
                       (owners/operation! state [:context-close]
                         (counter calls :close nil cleanup)))))))
    (is (= [cleanup] (vec (.getSuppressed original))))
    (thrown #(owners/recover! state original (counter calls :retry nil nil)))
    (is (= {:close 1} @calls))))

(deftest recovery-never-reenters-a-started-disposal
  (let [state (atom {}) calls (atom {}) failure (ex-info "between cleanup steps" {})]
    (owners/begin-disposal! state)
    (thrown #(owners/recover! state failure (counter calls :cleanup nil nil)))
    (is (empty? @calls))
    (is (= :disposing (:disposal-phase @state)))
    (is (some? (thrown #(owners/begin-disposal! state))))))

(deftest completed-operations-return-canonical-results-without-owner-reuse
  (let [state (atom {}) calls (atom {}) result (Object.) invoke (counter calls :close result nil)]
    (owners/begin-disposal! state)
    (is (identical? result (owners/operation! state [:context-close] invoke)))
    (is (identical? result (owners/operation! state [:context-close] invoke)))
    (swap! state assoc :disposal-phase :disposed)
    (is (= :already-disposed (owners/begin-disposal! state)))
    (is (= {:close 1} @calls))))
