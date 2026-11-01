(ns allocation-heartbeat-provider-checks-v1
  "Small terminal models plus an EXPLICIT borrowed-source bare-engine smoke.
   Loading never constructs an engine or runs the smoke. No image/bootstrap."
  (:require [clojure.test :refer [deftest is]]
            [allocation-heartbeat-lab-v1 :as hb]
            [java-ir-baseline :as j]
            [ansatz.research.ir.source-setup :as source]
            [ansatz.research.ir.authenticated-demand :as demand]))
(deftest revoked-holder-rejects-before-context-read
  (let [reads (atom 0)]
    (with-redefs-fn {#'hb/ctx (fn [_] (swap! reads inc) (throw (Exception. "must not read context")))}
      #(is (thrown-with-msg? clojure.lang.ExceptionInfo #"closed" (#'hb/live! (atom {:status :revoked})))))
    (is (zero? @reads))))
(deftest wrong-thread-rejects-before-context-read
  (let [reads (atom 0)]
    (with-redefs-fn {#'hb/ctx (fn [_] (swap! reads inc) (throw (Exception. "must not read context")))}
      #(is (thrown-with-msg? clojure.lang.ExceptionInfo #"thread" (#'hb/live! (atom {:status :ready :thread (Thread.)})))))
    (is (zero? @reads))))
(defn smoke!
  "Optional real get/set/fork/claim test using BORROWED actual parent CodeReceipt
   and class basis. Builds four tiny empty-stack engines (at most two live), no534 image/Module.
   Caller keeps source catalogue lease live. Does not mutate parent engine/Program.
   Failure preserves actual engines/provider journal in ex-data; no fake unwind."
  [parent]
  (let [borrowed (:driver parent) receipt (:code-receipt parent) src (:source borrowed)
        _ (source/guard-source! receipt src)
        borrowed-ctx @(:current-ctx borrowed)
        spec (get hb/specifications hb/get-symbol)
        original (source/lookup-entry receipt (:name spec))
        header (j/declaration-header src (:row original) (:sha256 original))
        setter-spec (get hb/specifications hb/set-symbol)
        setter-entry (source/lookup-entry receipt (:name setter-spec))
        setter-header (j/declaration-header src (:row setter-entry) (:sha256 setter-entry))
        setter-descriptor (hb/bootstrap-specification! receipt)
        getter-descriptor (select-keys spec [:symbol :parameters :borrowed :result])
        base #(j/prepare-host-program (dissoc borrowed-ctx :program :profiling-policy) [] %)
        ;; Correct bootstrap: registry exists BEFORE BOTH original Headers.
        tiny (j/register-headers (base [getter-descriptor setter-descriptor]) [header setter-header])
        engine (j/machine tiny)
        driver {:engine engine :source src :current-ctx (atom tiny) :headers-by-name (atom {(demand/exact-name-key (:name setter-spec)) {:header setter-header :sha256 (:sha setter-spec)}}) :requests (atom [])}
        branch {:driver driver :code-receipt receipt}
        journal (atom {:engines [engine] :branches [branch] :providers []}) checks (atom 0)
        verify (fn [ok message] (swap! checks inc) (when-not ok (throw (ex-info message {}))))
        raw (fn [d] (.getLong (.getField ^Class (:class @(:current-ctx d)) "allocations") (:engine d)))
        finish (fn [d]
                 (loop [left 1000]
                   (let [c @(:current-ctx d) e (:engine d) phase (j/phase c e)]
                     (cond
                       (= "complete" phase) (j/take-result! c e)
                       (and (pos? left) (= "running" phase)) (do (j/advance! c e 100) (recur (dec left)))
                       :else (throw (ex-info "Tiny heartbeat smoke paused" {:phase phase}))))))
        call (fn [provider d label args]
               (j/start! @(:current-ctx d) (:engine d) label args)
               (hb/serve! provider {:driver d}) (finish d))]
    (try
      ;; Immutable-Program discriminator: adding host registry AFTER unavailable
      ;; Function creation does not bind that old Function. Reject before effects.
      (let [unavailable (j/register-headers (base [getter-descriptor]) [header setter-header])
            late-registry (j/register-headers unavailable [] [setter-descriptor])
            bad-engine (j/machine late-registry)
            bad-driver (assoc driver :engine bad-engine :current-ctx (atom late-registry)
                              :headers-by-name (atom @(:headers-by-name driver)))
            before @(:headers-by-name bad-driver) allocation (raw bad-driver)]
        (swap! journal update :engines conj bad-engine)
        (swap! journal update :branches conj {:driver bad-driver :code-receipt receipt})
        (let [failure (try (hb/install! {:driver bad-driver :code-receipt receipt}) nil
                          (catch clojure.lang.ExceptionInfo error error))]
          (verify (and failure (re-find #"bootstrap pre-registration" (.getMessage failure))) "Unavailable setter was falsely upgraded")
          (verify (and (identical? late-registry @(:current-ctx bad-driver))
                       (identical? before @(:headers-by-name bad-driver)) (= allocation (raw bad-driver))
                       (= "idle" (j/phase late-registry bad-engine))) "Rejected late upgrade mutated Program/memo/counter"))
        (j/start-dispose! late-registry bad-engine) (finish bad-driver) (j/close! late-registry bad-engine))
      ;; Absent setter remains a supported atomic Header+spec creation case.
      (let [absent (j/register-headers (base [getter-descriptor]) [header])
            absent-engine (j/machine absent)
            absent-driver (assoc driver :engine absent-engine :current-ctx (atom absent) :headers-by-name (atom {}))
            absent-parent {:driver absent-driver :code-receipt receipt}]
        (swap! journal update :engines conj absent-engine)
        (swap! journal update :branches conj absent-parent)
        (let [p (hb/install! absent-parent)]
          (swap! journal update :providers conj p)
          (verify (= 0 (call p absent-driver "IO.setNumHeartbeats" [9 0])) "Absent setter installation failed")
          (verify (= 9 (call p absent-driver "IO.getNumHeartbeats" [0])) "Fresh absent setter did not change virtual count")
          (j/start-dispose! @(:current-ctx absent-driver) absent-engine) (finish absent-driver)
          (hb/revoke! p) (j/close! @(:current-ctx absent-driver) absent-engine)))
      ;; A second authentic Header for the same Name must not overwrite h1.
      (let [clone-header (j/declaration-header src (:row setter-entry) (:sha256 setter-entry))
            conflicting (assoc driver :headers-by-name (atom {(demand/exact-name-key (:name setter-spec))
                                                        {:header clone-header :sha256 (:sha setter-spec)}}))
            failure (try (hb/install! {:driver conflicting :code-receipt receipt}) nil
                         (catch clojure.lang.ExceptionInfo error error))]
        (verify (and failure (re-find #"identities differ" (.getMessage failure))) "Distinct canonical memo Header was accepted")
        (verify (identical? tiny @(:current-ctx driver)) "Rejected memo conflict changed Program"))
      (let [provider (hb/install! branch)
            _ (verify (identical? tiny @(:current-ctx driver)) "Existing HOST setter adoption rebuilt Program")
            _ (verify (identical? setter-header (:header (get @(:headers-by-name driver) (demand/exact-name-key (:name setter-spec))))) "Existing canonical setter Header was replaced")
            _ (swap! journal update :providers conj provider)
            d (:driver (hb/attach branch provider))
            initial (raw d)
            first-result (call provider d "IO.getNumHeartbeats" [0])]
        (let [before (hb/inspect provider)
              rejected (try (hb/revoke! provider) false (catch clojure.lang.ExceptionInfo _ true))]
          (verify rejected "Provider revoked before actual disposal")
          (verify (= before (hb/inspect provider)) "Rejected early revoke changed provider"))
        (verify (= initial first-result) "Offset0 actual getter differs from cumulative allocations")
        (verify (= 0 (call provider d "IO.setNumHeartbeats" [(biginteger "18446744073709551658") 0])) "Setter must return direct Unit0")
        (verify (= 42 (call provider d "IO.getNumHeartbeats" [0])) "Actual >UInt64 setter modulo differs")
        (verify (= initial (raw d)) "Setter/getter rewrote cumulative allocations")
        ;; Duplicate completion attempts do not reapply/reset the counter.
        (j/start! @(:current-ctx d) (:engine d) "IO.getNumHeartbeats" [0])
        (hb/serve! provider {:driver d})
        (let [before (hb/inspect provider)
              rejected (try (hb/serve! provider {:driver d}) false (catch clojure.lang.ExceptionInfo _ true))]
          (verify rejected "Duplicate serve was accepted")
          (verify (= before (hb/inspect provider)) "Duplicate serve mutated provider"))
        (verify (= 42 (finish d)) "Actual getter claim result changed")
        ;; Fork a real paused request; each branch owns its actual request token.
        (j/start! @(:current-ctx d) (:engine d) "IO.getNumHeartbeats" [0])
        (let [packet (hb/fork! provider []) child-driver (:driver packet) child-provider (:provider packet)]
          (swap! journal update :engines conj (:engine packet))
          (swap! journal update :branches conj {:driver child-driver :code-receipt receipt})
          (swap! journal update :providers conj child-provider)
          (verify (not (identical? (j/host-request @(:current-ctx d) (:engine d))
                                  (j/host-request @(:current-ctx child-driver) (:engine child-driver)))) "Fork reused parent's HostRequest")
          (hb/serve! child-provider {:driver child-driver})
          (hb/serve! provider {:driver d})
          (verify (= [42 42] [(finish child-driver) (finish d)]) "Fork lost virtual counter")
          (call child-provider child-driver "IO.setNumHeartbeats" [7 0])
          (verify (= [42 7] [(call provider d "IO.getNumHeartbeats" [0])
                            (call child-provider child-driver "IO.getNumHeartbeats" [0])]) "Branch reset leaked")
          ;; Wrong source is rejected before install/claim or counter mutation.
          (let [before @(:current-ctx child-driver) allocation (raw child-driver)
                foreign (j/source-binding before {"schema" "deliberately-foreign-test-source"})
                wrong (assoc child-driver :source foreign)
                rejected (try (hb/install! {:driver wrong :code-receipt receipt}) false
                              (catch clojure.lang.ExceptionInfo _ true))]
            (verify rejected "Forged source accepted")
            (verify (and (identical? before @(:current-ctx child-driver)) (= allocation (raw child-driver))) "Rejected source mutated engine/Program"))
          ;; Genuine normal disposal; provider stays live until callback work ends.
          (doseq [[p actual-driver] [[child-provider child-driver] [provider d]]]
            (j/start-dispose! @(:current-ctx actual-driver) (:engine actual-driver))
            (verify (= 0 (finish actual-driver)) "Tiny engine disposal failed")
            (hb/revoke! p)
            (j/close! @(:current-ctx actual-driver) (:engine actual-driver)))
          (reset! journal {:status :disposed-and-closed})
          {:status :bare-original-source-heartbeat-pair-passed :assertions @checks
           :engines 4 :module-imported false :kernel-association false :native-physical-parity false}))
      (catch Throwable error
        (throw (ex-info "Tiny heartbeat smoke failed; preserve actual owner packet, no automatic unwind" {:journal @journal} error))))))
