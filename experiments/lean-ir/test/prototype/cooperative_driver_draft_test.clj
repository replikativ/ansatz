(ns prototype.cooperative-driver-draft-test
  "Model callback tests only; no full Init compatibility claim."
  (:require [clojure.test :refer [deftest is]]
            [prototype.raw-interop :as raw]
            [prototype.raw-interop-test :as fixture]
            [prototype.machine :as m]))

;; Proposed script is definitions only, and is intentionally not auto-required
;; by production runtime code. Loading it here starts no guest work.
(load-file "scripts/cooperative-full-init-drive.clj")
(alias 'driver 'prototype.cooperative-driver-draft)

(defn failure [f] (try (f) nil (catch clojure.lang.ExceptionInfo e e)))
(def limits {:max-operations 1 :wall-ms 100000})
(defn prepared [handler]
  (let [s (fixture/session :reference "permitted" (fixture/binding-for [] "object" handler) {})]
    [s (m/start (m/world (:functions s)) fixture/root [])]))
(defn options [s source]
  {:allowed-bindings (:bindings s) :helper-fuel 20000000
   :source source :source-open? deref})

(deftest explicit-single-operation-slices-do-not-start-or-replay-owners
  (let [effects (atom 0) records (atom []) source (atom true)
        [s world] (prepared (fn [_ state _] (swap! effects inc) [state 42]))
        d (driver/make-driver s world (assoc (options s source) :observe! #(swap! records conj %)))]
    (is (= :yielded (:status (driver/drive-slice! d limits))))
    (is (= :boundary (get-in (driver/checkpoint d) [:event :status])))
    (is (= 0 @effects))
    (is (= :yielded (:status (driver/drive-slice! d limits))))
    (is (= 1 @effects))
    (is (= :handler-completed (get-in (driver/checkpoint d) [:event :status])))
    (is (= :running (get-in (driver/checkpoint d) [:event :state :status])))
    (is (= :done (:status (driver/drive-slice! d limits))))
    (is (= 42 (get-in (driver/checkpoint d) [:event :value])))
    (is (failure #(driver/drive-slice! d limits)))
    (is (= 1 @effects))
    (is @source)
    (doseq [record @records]
      (is (every? #(or (nil? %) (number? %) (string? %) (keyword? %) (boolean? %)) (vals record)))
      (is (false? (:finish-finalization-called record))))))

(deftest denied-registry-is-rejected-before-any-guest-or-handler-execution
  (let [effects (atom 0) source (atom true)
        [s world] (prepared (fn [_ state _] (swap! effects inc) [state 42]))]
    (is (failure #(driver/make-driver s world (assoc (options s source) :allowed-bindings {}))))
    (is (= 0 @effects))
    (is (= :running (:status world)))
    (is @source)))

(deftest handler-failure-is-never-retried-and-preserves-the-raw-cause
  (let [effects (atom 0) source (atom true)
        [s world] (prepared (fn [_ _ _] (swap! effects inc) (throw (ex-info "effect already happened" {}))))
        d (driver/make-driver s world (options s source))]
    (driver/drive-slice! d limits)
    (let [error (failure #(driver/drive-slice! d limits))
          cause (.getCause error)]
      (is (= 1 @effects))
      (is (true? (:boundary-token-consumed? (ex-data cause))))
      (is (= :failed (:phase (driver/checkpoint d))))
      (is (failure #(driver/drive-slice! d limits)))
      (is (= 1 @effects))
      (is @source))))

(deftest observation-failure-retains-completed-event-without-repeating-handler
  (let [effects (atom 0) source (atom true)
        [s world] (prepared (fn [_ state _] (swap! effects inc) [state 42]))
        d (driver/make-driver s world
            (assoc (options s source) :observe! #(when (= :handler-completed (:status %))
                                                  (throw (ex-info "observer unavailable" {})))))]
    (driver/drive-slice! d limits)
    (is (failure #(driver/drive-slice! d limits)))
    (is (= 1 @effects))
    (is (= :handler-completed (get-in (driver/checkpoint d) [:event :status])))
    (is (= :running (get-in (driver/checkpoint d) [:event :state :status])))
    (is (failure #(driver/drive-slice! d limits)))
    (is (= 1 @effects))))

(deftest adopted-session-is-used-for-the-next-operation
  (let [source (atom true)
        [s world] (prepared (fn [{:keys [switch-backend!]} state _]
                              [(switch-backend! state :mutable) 42]))
        d (driver/make-driver s world (options s source))]
    (driver/drive-slice! d limits)
    (driver/drive-slice! d limits)
    (is (= :mutable (get-in (driver/checkpoint d) [:event :session :backend])))
    (is (= :done (:status (driver/drive-slice! d limits))))
    (is (= 42 (get-in (driver/checkpoint d) [:event :value])))))

(deftest wall-budget-is-checked-between-operations-and-source-is-only-borrowed
  (let [effects (atom 0) source (atom true)
        [s world] (prepared (fn [_ state _] (swap! effects inc) [state 42]))
        d (driver/make-driver s world (options s source))]
    (is (= 0 (:operations (driver/drive-slice! d {:max-operations 100 :wall-ms 0}))))
    (is (= :initial (get-in (driver/checkpoint d) [:event :status])))
    (is (= 0 @effects))
    (reset! source false)
    (is (failure #(driver/drive-slice! d limits)))
    (is (= 0 @effects))
    (is (false? @source))))

(deftest an-allowed-outer-cannot-hide-an-unauthorized-nested-callback
  (let [outer-effects (atom 0) inner-effects (atom 0) source (atom true)
        inner ["str" ["anonymous"] "driver-inner"]
        bindings {"outer" (fixture/binding-for [] "object"
                           (fn [{:keys [invoke]} world _]
                             (swap! outer-effects inc) (invoke world inner [])))
                  "inner" (fixture/binding-for [] "object"
                           (fn [_ world _] (swap! inner-effects inc) [world 42]))}
        inner-row (-> (fixture/row "inner" [] "object")
                      (assoc :name inner) (assoc-in [:ir :extern :f] inner))
        functions {fixture/root (second (raw/lower bindings (fixture/row "outer" [] "object")))
                   inner (second (raw/lower bindings inner-row))}
        session (raw/open-functions functions bindings {:backend :reference})
        world (m/start (m/world functions) fixture/root [])]
    (is (failure #(driver/make-driver session world
                    (assoc (options session source) :allowed-bindings {"outer" (get bindings "outer")}))))
    (is (= [0 0] [@outer-effects @inner-effects]))
    (let [d (driver/make-driver session world (options session source))]
      (is (= :done (:status (driver/drive-slice! d {:max-operations 10 :wall-ms 100000}))))
      (is (= 42 (get-in (driver/checkpoint d) [:event :value])))
      (is (= [1 1] [@outer-effects @inner-effects])))))

(deftest adopted-foreign-registry-is-retained-for-diagnosis-and-never-executed
  (let [effects (atom 0) foreign-effects (atom 0) source (atom true)
        [s world] (prepared (fn [_ state _] (swap! effects inc) [state 42]))
        d (driver/make-driver s world (options s source))
        original-complete raw/complete-host-boundary
        foreign (fixture/binding-for [] "object"
                  (fn [_ state _] (swap! foreign-effects inc) [state 0]))]
    (driver/drive-slice! d limits)
    ;; Model a future session-extension bug. Existing raw scoped capabilities
    ;; preserve the registry; the driver must also reject an adopted foreign one.
    (let [error (with-redefs [raw/complete-host-boundary
                             (fn [token options]
                               (let [event (original-complete token options)]
                                 (assoc-in event [:session :bindings "foreign"] foreign)))]
                  (failure #(driver/drive-slice! d limits)))]
      (is (some? error))
      (is (= :failed (:phase (driver/checkpoint d))))
      (is (= :handler-completed (get-in (driver/checkpoint d) [:event :status])))
      (is (identical? foreign (get-in (driver/checkpoint d) [:event :session :bindings "foreign"])))
      (is (= [1 0] [@effects @foreign-effects]))
      (is (failure #(driver/drive-slice! d limits))))))

(deftest racing-driver-callers-execute-one-handler
  (let [entered (promise) release (promise) effects (atom 0) source (atom true)
        [s world] (prepared (fn [_ state _]
                              (swap! effects inc) (deliver entered true)
                              @release [state 42]))
        d (driver/make-driver s world (options s source))]
    (driver/drive-slice! d limits)
    (let [first-call (future (driver/drive-slice! d limits))]
      (try
        (is (= true (deref entered 10000 :timeout)))
        (let [second-call (future (failure #(driver/drive-slice! d limits)))]
          (is (instance? clojure.lang.ExceptionInfo (deref second-call 10000 :timeout))))
        (finally (deliver release true)))
      (is (= :yielded (:status (deref first-call 10000 {:status :timeout})))))
    (is (= 1 @effects))
    (is (= :done (:status (driver/drive-slice! d limits))))))

(deftest observer-reentrancy-is-rejected-without-corrupting-the-running-driver
  (let [holder (atom nil) rejections (atom 0) effects (atom 0) source (atom true)
        [s world] (prepared (fn [_ state _] (swap! effects inc) [state 42]))
        d (driver/make-driver s world
            (assoc (options s source) :observe!
                   (fn [_]
                     (when (failure #(driver/drive-slice! @holder limits))
                       (swap! rejections inc)))))]
    (reset! holder d)
    (is (= :done (:status (driver/drive-slice! d {:max-operations 10 :wall-ms 100000}))))
    (is (= 3 @rejections))
    (is (= 1 @effects))
    (is (= :done (:phase (driver/checkpoint d))))))

(deftest observer-failure-on-done-preserves-the-owned-finalizer-io-result
  (let [source (atom true)
        [s world] (prepared (fn [_ state _]
                              (let [[state payload] (m/resource state "completed-payload")]
                                (m/allocate state :ctor 0 [payload]))))
        d (driver/make-driver s world
            (assoc (options s source) :observe!
                   (fn [event] (when (= :done (:status event))
                                 (throw (ex-info "done observer failed" {}))))))]
    (is (failure #(driver/drive-slice! d {:max-operations 10 :wall-ms 100000})))
    (let [saved (driver/checkpoint d) state (get-in saved [:event :state]) value (get-in saved [:event :value])]
      (is (= :failed (:phase saved)))
      (is (= :done (get-in saved [:event :status])))
      (is (= 1 (:rc (m/node state value))))
      (is (= 0 (:tag (m/node state value))))
      (is (= [[:released "completed-payload"]] (:events (m/release state value 1))))
      (is (empty? (:heap world))))))

(deftest yielded-summary-belongs-to-its-own-event-despite-an-immediate-next-caller
  (let [effects (atom 0) source (atom true)
        [s world] (prepared (fn [_ state _] (swap! effects inc) [state 42]))
        d (driver/make-driver s world (options s source))
        ledger (.-ledger d) interleaved? (atom false)
        original-reset! reset! original-swap! swap!
        after-publish (fn [target]
                        (when (and (identical? target ledger)
                                   (= :ready (:phase @ledger))
                                   (not @interleaved?))
                          (original-reset! interleaved? true)
                          ;; Deterministically model a second caller scheduled
                          ;; immediately AFTER :ready becomes visible.
                          (driver/drive-slice! d limits)))
        result (with-redefs [clojure.core/reset! (fn [target value]
                                                 (let [r (original-reset! target value)]
                                                   (after-publish target) r))
                            clojure.core/swap! (fn [target f & args]
                                                (let [r (apply original-swap! target f args)]
                                                  (after-publish target) r))]
                 (driver/drive-slice! d limits))]
    (is @interleaved?)
    (is (= :boundary (get-in result [:summary :status])))
    (is (= :ready (get-in result [:summary :driver-phase])))
    (is (= :handler-completed (get-in (driver/checkpoint d) [:event :status])))
    (is (= 1 @effects))))
