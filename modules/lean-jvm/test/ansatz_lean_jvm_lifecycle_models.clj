(ns ansatz-lean-jvm-lifecycle-models
  "Managed-state models using explicitly private registry fixtures, never public issuers."
  (:require [clojure.test :refer [deftest is run-tests]]
            [ansatz.lean.jvm.ir :as j] [ansatz.lean.jvm.startup :as startup]
            [ansatz.lean.jvm.capabilities :as caps]))
(def ^:dynamic *basis* nil)
(defn- model-run [state callback]
  (let [token (startup/->Startup) registry @(ns-resolve 'ansatz.lean.jvm.startup 'startup-registry)
        cell (atom (merge {:status :cancelled :lock (java.util.concurrent.locks.ReentrantLock.)
                          :error-slot (object-array 1) :ledger [] :module-index 0} state))]
    ((ns-resolve 'ansatz.lean.jvm.startup 'put-issued!) registry token cell)
    (try (callback token cell) (finally (locking registry (.remove ^java.util.WeakHashMap registry token))))))
(deftest idle-project-can-change-java-threads-under-one-lease
  (model-run {} (fn [token _]
                 (is (= :cancelled (:status (startup/status token))))
                 (is (= :cancelled (deref (future (:status (startup/status token))) 10000 :timeout))))))
(deftest project-lease-serializes-concurrent-borrows
  (model-run {} (fn [token _]
                 (let [active (atom 0) maximum (atom 0) lease (ns-resolve 'ansatz.lean.jvm.startup 'with-lease!)
                       workers (mapv (fn [_] (future (dotimes [_ 40]
                                                       (lease token :observe
                                                              #(let [n (swap! active inc)]
                                                                 (swap! maximum max n) (Thread/yield) (swap! active dec)))) true)) (range 8))]
                   (try
                     (doseq [worker workers] (is (= true (deref worker 10000 :timeout))))
                     (is (= 1 @maximum)) (is (zero? @active))
                     (finally (doseq [worker workers] (future-cancel worker))))))))
(deftest paused-effect-thread-is-pinned-but-stopped-control-can-handoff
  (model-run {:status :running :execution-thread (Thread/currentThread)}
             (fn [token cell]
               (is (= :running (deref (future (:status (startup/status token))) 10000 :timeout)))
               (is (= :refused (deref (future (try (startup/poll! token 1) :unexpected
                                                  (catch Exception _ :refused))) 10000 :timeout)))
               (is (= :running (:status @cell)))
               (is (= :cancelled (deref (future (:status (startup/cancel! token))) 10000 :timeout))))))
(deftest terminal-handle-stays-invalid-without-dereferencing-dropped-engine
  (model-run {:status :closed} (fn [token _]
                                (is (= :closed (:status (startup/status token))))
                                (is (thrown? Exception (startup/with-ready-engine! token (fn [_] :unexpected))))
                                (is (thrown? Exception (startup/poll! token 1))))))
(deftest unprofiled-world-cannot-claim-managed-heap-abandonment
  (model-run {:status :host-failed :prepared {}}
             (fn [token cell]
               (is (thrown? Exception (startup/abandon! token)))
               (is (= :host-failed (:status @cell))))))
(deftest certified-pre-engine-failure-drops-private-roots-without-rc
  (let [ctx (j/prepare-host-program *basis* [] []) descriptor (caps/check-rows! *basis* [])
        prepared {:ctx ctx :headers {} :requirements descriptor} slot (object-array [(Object.)])]
    (model-run {:status :host-failed :prepared prepared :error-slot slot}
               (fn [token cell]
                 (with-redefs [j/release! (fn [& _] (throw (ex-info "Must not DEC" {})))
                               j/close! (fn [& _] (throw (ex-info "Must not close" {})))]
                   (let [receipt (startup/abandon! token)]
                     (is (false? (:guest-rc-unwound receipt)))
                     (is (false? (:abandonment-invoked-engine-close receipt)))))
                 (is (= :abandoned (:status @cell)))
                 (is (nil? (aget slot 0)))
                 (is (= #{:status :lock :abandonment} (set (keys @cell))))))))
(deftest abandoned-failed-close-does-not-deny-the-prior-attempt
  (let [ctx (j/prepare-host-program *basis* [] []) descriptor (caps/check-rows! *basis* [])]
    (model-run {:status :close-started :prepared {:ctx ctx :headers {} :requirements descriptor}}
               (fn [token _]
                 (let [receipt (startup/abandon! token)]
                   (is (true? (:prior-coordinator-close-attempted? receipt)))
                   (is (false? (:abandonment-invoked-engine-close receipt))))))))
(deftest prepared-world-retains-code-not-raw-producer-observations
  (let [marker (Object.) publish (ns-resolve 'ansatz.lean.jvm.startup 'publish-prepared!)
        registry @(ns-resolve 'ansatz.lean.jvm.startup 'prepared-registry)
        token (publish (assoc *basis* :raw-compile-token marker)
                       {:modules [] :rows [marker] :actions [marker]} [] {} (byte-array 0) [])]
    (try
      (let [cell (locking registry (.get ^java.util.WeakHashMap registry token))]
        (is (= {:modules []} (:plan cell)))
        (is (not (contains? (:ctx cell) :raw-compile-token)))
        (is (= [] (:entries cell))))
      (finally (locking registry (.remove ^java.util.WeakHashMap registry token))))))
(deftest checked-entry-observation-is-compacted-with-hashes
  (let [entry {"name" ["str" ["anonymous"] "id"] "actualType" ["large-type-observation"]
               "typeCheck" {"signature" "nat-to-nat" "algorithm" "Lean.Meta.isDefEq"
                              "transparency" "default" "expectedType" ["Nat-arrow-Nat"]}}
        compact ((ns-resolve 'ansatz.lean.jvm.startup 'compact-entry) entry)]
    (is (= "nat-to-nat" (get-in compact ["typeCheck" "signature"])))
    (is (not (contains? compact "actualType")))
    (is (not (contains? (get compact "typeCheck") "expectedType")))
    (is (every? #(re-matches #"[0-9a-f]{64}" %) (vals (get compact "nativeEvidence"))))))
(defn check! [basis] (binding [*basis* basis] (run-tests 'ansatz-lean-jvm-lifecycle-models)))
