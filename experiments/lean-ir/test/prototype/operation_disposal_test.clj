;; Tiny real raw execution and actual public control/wrapper disposal.
;; Compiler/factory transports in imported fixtures are explicitly modeled;
;; these tests grant no genuine full-frontend/source authority.
(ns prototype.operation-disposal-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as machine] [prototype.raw-interop :as raw]
            [prototype.resident-frontend :as resident]
            [prototype.resident-init-prefix :as prefix]
            [prototype.resident-init-prefix-test :as contexts]
            [prototype.resident-init-import-test :as legacy]
            [prototype.native-init-base-test :as native]
            [prototype.source-graph-runtime-test :as publication]
            [prototype.source-graph-staged-test :as staged]
            [prototype.source-import :as source]))
(defn- thrown [f] (try (f) nil (catch Throwable cause cause)))
(defn- boundary [backend effects handler]
  (let [functions {"entry" {:params [] :body [:host "effect" [] 0 [:return [:var 0]]]}}
        binding {:signature {:params [] :return-type "object"}
                 :handler (fn [_ world _] (swap! effects inc) (handler world))}
        session (raw/open-functions functions {"effect" binding} {:backend backend :fuel 1000})]
    (raw/advance-to-boundary session (machine/start (machine/world functions) "entry" []))))
(deftest abandoning-actual-issued-boundary-does-not-run-handler-and-is-terminal
  (doseq [backend [:reference :mutable :jvm]]
    (let [effects (atom 0) event (boundary backend effects #(vector % 0))
          token (:token event) before (:state event)]
      (is (= :boundary (:status event)))
      (is (= {:phase :abandoned :completion-already-attempted false}
             (raw/abandon-host-boundary! token)))
      (is (= {:phase :abandoned :completion-already-attempted false}
             (raw/abandon-host-boundary! token)))
      (is (some? (thrown #(raw/complete-host-boundary token {:helper-fuel 1000}))))
      (is (zero? @effects))
      ;; No mutation/re-admission of the borrowed immutable captured World.
      (is (identical? before (:state event))))))
(deftest abandonment-never-replays-completed-or-failed-handler
  (doseq [backend [:reference :mutable :jvm] fails? [false true]]
    (let [effects (atom 0) selected (ex-info "selected host failure" {})
          event (boundary backend effects (fn [world] (if fails? (throw selected) [world 0])))
          token (:token event)
          result (try (raw/complete-host-boundary token {:helper-fuel 1000})
                      (catch Throwable cause cause))]
      (is (= 1 @effects))
      (is (= {:phase :abandoned :completion-already-attempted true}
             (raw/abandon-host-boundary! token)))
      (is (some? (thrown #(raw/complete-host-boundary token {:helper-fuel 1000}))))
      (is (= 1 @effects))
      (when fails?
        (is (loop [cause result]
              (cond (identical? cause selected) true
                    (nil? cause) false
                    :else (recur (.getCause ^Throwable cause)))))))))
(deftest forged-boundary-data-is-not-disposal-authority
  (is (some? (thrown #(raw/abandon-host-boundary! {:phase :boundary :claim (atom :unstarted)})))))

(deftest raw-running-completion-cannot-be-abandoned-reentrantly
  (let [effects (atom 0) selected (atom nil) captured (atom nil)
        event (boundary :reference effects
                        (fn [world]
                          (reset! selected (thrown #(raw/abandon-host-boundary! @captured)))
                          [world 0]))]
    (reset! captured (:token event))
    (is (= :handler-completed (:status (raw/complete-host-boundary @captured {:helper-fuel 1000}))))
    (is (.contains (.getMessage ^Throwable @selected) "running host boundary"))
    (is (= 1 @effects))))

(deftest managed-context-abandonment-is-wrapper-local-and-idempotent
  (doseq [backend [:reference :mutable :jvm]]
    (contexts/with-fixture backend
      (fn [{:keys [context source]}]
        (let [before (resident/snapshot context) child (resident/fork context) sibling (resident/fork context)]
          (try
            (is (nil? (resident/abandon! child)))
            (is (nil? (resident/abandon! child)))
            ;; The exposed Atom remains a caller-owned diagnostic snapshot;
            ;; retirement is checked separately and never resets that Atom.
            (is (identical? before (:prepared @(.-state ^prototype.resident_frontend.Context child))))
            (is (some? (thrown #(resident/snapshot child))))
            (is (identical? before (resident/snapshot context)))
            (is (identical? before (resident/snapshot sibling)))
            (is (false? @(:closed source)))
            (finally (resident/close! sibling))))))))

(deftest public-state-hooks-never-run-as-hidden-abandonment-callbacks
  (contexts/with-fixture :reference
    (fn [{:keys [context]}]
      (let [child (resident/fork context) state (.-state ^prototype.resident_frontend.Context child)
            before (resident/snapshot child) watch-calls (atom 0) validator-calls (atom 0)]
        (try
          (add-watch state :selected (fn [& _] (swap! watch-calls inc)))
          (is (.contains (.getMessage ^Throwable (thrown #(resident/abandon! child))) "hooks"))
          (is (zero? @watch-calls))
          (is (identical? before (resident/snapshot child)))
          (remove-watch state :selected)
          (set-validator! state (fn [_] (swap! validator-calls inc) true))
          (reset! validator-calls 0)
          (is (.contains (.getMessage ^Throwable (thrown #(resident/abandon! child))) "hooks"))
          (is (zero? @validator-calls))
          (is (identical? before (resident/snapshot child)))
          (set-validator! state nil)
          (is (nil? (resident/abandon! child)))
          (add-watch state :selected (fn [& _] (swap! watch-calls inc)))
          (resident/close! child)
          (is (zero? @watch-calls))
          (is (some? (thrown #(resident/snapshot child))))
          (finally (remove-watch state :selected) (set-validator! state nil) (resident/close! child))))))
  (let [touched (atom 0) holder (reify clojure.lang.IDeref (deref [_] (swap! touched inc)))
        malformed (resident/->Context holder)]
    (is (.contains (.getMessage ^Throwable (thrown #(resident/abandon! malformed))) "holder"))
    (is (zero? @touched))))

(defn- no-heavy-control-roots! [state]
  ;; Retention is part of the lifecycle contract, independently of caller-held
  ;; original exceptions/snapshots. Never assert a process heap/GC outcome here.
  (is (= :disposed (:phase @state)))
  (is (not-any? #(or (instance? Throwable %)
                    (instance? prototype.resident_frontend.Context %)
                    (and (map? %) (or (contains? % :world) (contains? % :functions)
                                     (contains? % :heap) (contains? % :checkpoint)
                                     (contains? % :entry) (contains? % :certificate))))
                (tree-seq coll? seq @state))))

(deftest legacy-prepared-disposal-never-starts-finalizer-or-touches-parent
  (doseq [backend [:reference :mutable :jvm]]
    (legacy/with-fixture backend
      (fn [{:keys [context source finalizer-calls] :as fixture}]
        (let [before (resident/snapshot context) control (:control (legacy/prepare fixture))
              state (#'prefix/import-control! control)]
          (is (some? (thrown #(prefix/dispose-source-graph-import! control))))
          (let [receipt (prefix/dispose-import! control)]
            (is (identical? receipt (prefix/dispose-import! control))))
          (is (zero? @finalizer-calls))
          (is (some? (thrown #(prefix/advance-import! control {:max-operations 1 :wall-ms 1000}))))
          (is (some? (thrown #(prefix/finish-import! control))))
          (is (zero? @finalizer-calls))
          (is (identical? before (resident/snapshot context)))
          (is (false? @(:closed source)))
          (no-heavy-control-roots! state))))))

(deftest busy-import-disposal-rejects-without-poisoning-the-active-owner
  (legacy/with-fixture :reference
    (fn [{:keys [finalizer-calls] :as fixture}]
      (let [control (:control (legacy/prepare fixture)) rejected (atom [])]
        (prefix/advance-import! control {:max-operations 1 :wall-ms 1000
                                        :observe! (fn [_] (swap! rejected conj (thrown #(prefix/dispose-import! control))))})
        (is (seq @rejected))
        (is (every? #(and % (.contains (.getMessage ^Throwable %) "busy")) @rejected))
        (legacy/run-to-io! control)
        (is (= 1 @finalizer-calls))
        (prefix/dispose-import! control)
        (is (= 1 @finalizer-calls))))))

(deftest failed-import-disposal-preserves-original-error-but-retires-library-roots
  (legacy/with-fixture :reference
    (fn [{:keys [context source finalizer-calls] :as fixture}]
      (let [before (resident/snapshot context) control (:control (legacy/prepare fixture))
            _ (legacy/run-to-io! control) original (thrown #(prefix/finish-import! control))
            checkpoint (:checkpoint (ex-data original)) state (#'prefix/import-control! control)]
        (is (some? original))
        (is (identical? original (thrown #(prefix/finish-import! control))))
        (prefix/dispose-import! control)
        (is (not (identical? original (thrown #(prefix/finish-import! control)))))
        (is (identical? checkpoint (:checkpoint (ex-data original))))
        (is (= 1 @finalizer-calls))
        (is (identical? before (resident/snapshot context)))
        (is (false? @(:closed source)))
        (no-heavy-control-roots! state)))
    :finalizer-error? true))

(deftest finished-control-disposal-does-not-revoke-the-transferred-context
  (legacy/with-fixture :reference
    (fn [fixture]
      (let [control (:control (legacy/prepare fixture)) _ (legacy/run-to-io! control)
            result (prefix/finish-import! control) owned (:context result)
            before (resident/snapshot owned)]
        (try
          (prefix/dispose-import! control)
          (is (identical? before (resident/snapshot owned)))
          (finally (resident/close! owned)))))))

(deftest actual-graph-control-disposal-retires-only-its-private-branch
  (publication/with-empty-publication :reference
    (fn [{:keys [context captured source] :as fixture}]
      (let [published (staged/publish! fixture) _ (swap! captured conj (:context published))
            parent (:context published) before (resident/snapshot parent)
            control (:control (staged/prepare! fixture published))
            state (#'prefix/import-control! control)]
        (is (some? (thrown #(prefix/dispose-import! control))))
        (prefix/dispose-source-graph-import! control)
        (is (some? (thrown #(prefix/advance-source-graph-import! control {:max-operations 1 :wall-ms 1000}))))
        (is (some? (thrown #(prefix/finish-source-graph-import! control))))
        (is (identical? before (resident/snapshot parent)))
        (is (false? @(:closed source)))
        (no-heavy-control-roots! state)))
    :local-ci? true :configure staged/configure-staged))

(deftest native-failed-control-disposal-never-replays-readiness-or-finalizer
  (publication/with-empty-publication :reference
    (fn [{:keys [source] :as fixture}]
      (let [token (native/modeled-stage-token fixture)
            parent (native/modeled-guards-context fixture (:context fixture) #{[source/init-module :all]})
            before (resident/snapshot parent)
            control (:control (native/prepare-native! fixture parent token))
            original (thrown #(prefix/advance-native-init-base! control {:max-operations 4 :wall-ms 1000}))
            state (#'prefix/native-control! control)]
        (is (some? original))
        (is (identical? original (thrown #(prefix/finish-native-init-base! control))))
        (let [receipt (prefix/dispose-native-init-base! control)]
          (is (identical? receipt (prefix/dispose-native-init-base! control))))
        (is (not (identical? original (thrown #(prefix/finish-native-init-base! control)))))
        (is (some? (thrown #(prefix/advance-native-init-base! control {:max-operations 1 :wall-ms 1000}))))
        (is (identical? before (resident/snapshot parent)))
        (is (false? @(:closed source)))
        (no-heavy-control-roots! state)))
    :local-ci? true :configure native/configure-native-stage))

(deftest disposing-import-at-actual-boundary-poisons-its-unstarted-handler-token
  (legacy/with-fixture :reference
    (fn [{:keys [context finalizer-calls] :as fixture}]
      (let [before (resident/snapshot context) control (:control (legacy/prepare fixture))
            state (#'prefix/import-control! control)]
        (prefix/advance-import! control {:max-operations 1 :wall-ms 1000})
        (let [event (:event @state) token (:token event)]
          (is (= :boundary (:status event)))
          (is (zero? @finalizer-calls))
          (prefix/dispose-import! control)
          (is (some? (thrown #(raw/complete-host-boundary token {:helper-fuel 1000000}))))
          (is (zero? @finalizer-calls))
          (is (identical? before (resident/snapshot context)))
          (no-heavy-control-roots! state))))))

(deftest native-control-disposal-covers-prepared-paused-completed-and-transferred-owners
  (publication/with-empty-publication :reference
    (fn [{:keys [captured operations source] :as fixture}]
      (let [token (native/modeled-stage-token fixture)]
      (doseq [phase [:prepared :after-readiness :io-completed :finished]]
        (let [context (native/modeled-guards-context fixture (:context fixture) native/complete-guards)
              before (resident/snapshot context)
              prepared (native/prepare-native! fixture context token)
              control (:control prepared) state (#'prefix/native-control! control)
              returned (case phase
                         :prepared nil
                         :after-readiness (do (prefix/advance-native-init-base! control {:max-operations 1 :wall-ms 1000}) nil)
                         :io-completed (do (native/complete-native! control) nil)
                         :finished (do (native/complete-native! control)
                                       (let [result (prefix/finish-native-init-base! control)]
                                         (swap! captured conj (:context result)) result)))
              returned-before (when returned (resident/snapshot (:context returned)))
              operations-before @operations]
          (prefix/dispose-native-init-base! control)
          (is (identical? operations-before @operations))
          (is (some? (thrown #(prefix/advance-native-init-base! control {:max-operations 1 :wall-ms 1000}))))
          (is (some? (thrown #(prefix/finish-native-init-base! control))))
          (is (identical? before (resident/snapshot context)))
          (is (false? @(:closed source)))
          (when returned (is (identical? returned-before (resident/snapshot (:context returned)))))
          (no-heavy-control-roots! state)))))
    :local-ci? true :configure native/configure-native-stage))

(deftest unissued-controls-reject-before-caller-defined-hashing
  (let [hash-calls (atom 0) poison (proxy [Object] []
                                   (hashCode [] (swap! hash-calls inc) (throw (AssertionError. "unvalidated hash"))))]
    (is (some? (thrown #(prefix/dispose-import! poison))))
    (is (some? (thrown #(prefix/dispose-source-graph-import! poison))))
    (is (some? (thrown #(prefix/dispose-native-init-base! poison))))
    (is (zero? @hash-calls))))

(deftest public-boundary-claim-hooks-cannot-run-or-revive-a-retired-token
  (let [effects (atom 0) watches (atom 0) validators (atom 0)
        event (boundary :reference effects #(vector % 0)) token (:token event)
        claim (.-claim ^prototype.raw_interop.HostBoundaryToken token)]
    (try
      (add-watch claim :selected (fn [& _] (swap! watches inc)))
      (set-validator! claim (fn [_] (swap! validators inc) true))
      (reset! validators 0)
      (is (= {:phase :abandoned :completion-already-attempted false}
             (raw/abandon-host-boundary! token)))
      (is (some? (thrown #(raw/complete-host-boundary token {:helper-fuel 1000}))))
      (is (zero? @effects)) (is (zero? @watches)) (is (zero? @validators))
      (remove-watch claim :selected) (set-validator! claim nil)
      (reset! claim :unstarted)
      (is (some? (thrown #(raw/complete-host-boundary token {:helper-fuel 1000}))))
      (is (zero? @effects))
      (finally (remove-watch claim :selected) (set-validator! claim nil)))))

(deftest constructor-and-public-fields-do-not-forge-boundary-issuance
  (let [effects (atom 0) touched (atom 0) event (boundary :reference effects #(vector % 0))
        real (:token event) holder (reify clojure.lang.IDeref (deref [_] (swap! touched inc)))
        forged (prototype.raw_interop.HostBoundaryToken.
                 (.-world ^prototype.raw_interop.HostBoundaryToken real)
                 (.-session ^prototype.raw_interop.HostBoundaryToken real)
                 (.-request ^prototype.raw_interop.HostBoundaryToken real)
                 (.-binding ^prototype.raw_interop.HostBoundaryToken real) holder)]
    (is (some? (thrown #(raw/abandon-host-boundary! forged))))
    (is (some? (thrown #(raw/complete-host-boundary forged {:helper-fuel 1000}))))
    (is (zero? @touched)) (is (zero? @effects))
    (raw/abandon-host-boundary! real)))

(deftest completion-and-abandonment-race-has-no-post-retirement-handler
  (dotimes [_ 4]
    (let [effects (atom 0) event (boundary :reference effects #(vector % 0))
          token (:token event) start (promise)
          completed (future @start (try (raw/complete-host-boundary token {:helper-fuel 1000})
                                        (catch Throwable cause cause)))
          abandoned (future @start (try (raw/abandon-host-boundary! token)
                                        (catch Throwable cause cause)))]
      (deliver start true)
      (try
        (let [a (deref completed 5000 ::timeout) b (deref abandoned 5000 ::timeout)]
          (is (not= ::timeout a)) (is (not= ::timeout b))
          (is (contains? #{0 1} @effects))
          (if (zero? @effects)
            (do (is (instance? Throwable a))
                (is (= {:phase :abandoned :completion-already-attempted false} b)))
            (do (is (= :handler-completed (:status a)))
                (is (or (instance? Throwable b)
                        (= {:phase :abandoned :completion-already-attempted true} b)))))
          (let [before @effects]
            (is (some? (thrown #(raw/complete-host-boundary token {:helper-fuel 1000}))))
            (is (= before @effects))))
        (finally (future-cancel completed) (future-cancel abandoned))))))

(deftest disposal-failure-keeps-original-operation-error-and-pending-private-owners
  (publication/with-empty-publication :reference
    (fn [{:keys [captured operations source] :as fixture}]
      (let [published (staged/publish! fixture) _ (swap! captured conj (:context published))
            before (resident/snapshot (:context published))
            control (:control (staged/prepare! fixture published))
            _ (staged/complete-io! control)
            selected (ex-info "selected failure after actual Context adoption" {})
            ;; Only the post-adoption scalar compaction step is fault-injected;
            ;; compiler/factory transport remains the fixture's explicit model.
            original (with-redefs-fn {#'prefix/finished-import-state (fn [_] (throw selected))}
                       #(thrown (fn [] (prefix/finish-source-graph-import! control))))
            state (#'prefix/import-control! control) owned (:adopted-context @state)
            holder (.-state ^prototype.resident_frontend.Context owned)
            world (:world @state) events @operations watch-calls (atom 0)]
        (try
          (is (identical? selected (.getCause ^Throwable original)))
          (is (some? (resident/snapshot owned)))
          (add-watch holder :selected (fn [& _] (swap! watch-calls inc)))
          (let [failure (thrown #(prefix/dispose-source-graph-import! control))]
            (is (.contains (.getMessage ^Throwable failure) "hooks"))
            (is (identical? failure (:disposal-failure @state))))
          (is (identical? original (:failure @state)))
          (is (identical? world (:world @state)))
          (is (identical? owned (:adopted-context @state)))
          (is (true? (:busy? @state)))
          (is (= :failed (:dispose-state @state)))
          (is (not= :disposed (:phase @state)))
          (is (nil? (:disposal @state)))
          (is (identical? original (thrown #(prefix/finish-source-graph-import! control))))
          (is (identical? original (thrown #(prefix/advance-source-graph-import! control {:max-operations 1 :wall-ms 1000}))))
          (is (some? (thrown #(prefix/dispose-source-graph-import! control))))
          (is (identical? events @operations))
          (is (zero? @watch-calls))
          (is (identical? before (resident/snapshot (:context published))))
          (is (false? @(:closed source)))
          (finally
            (remove-watch holder :selected)
            ;; Test owns this untransferred Context; operation remains terminal.
            (resident/abandon! owned)))))
    :local-ci? true :configure staged/configure-staged))
