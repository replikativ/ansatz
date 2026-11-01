;; Small HOST CONTROL MODELS ONLY: no actual Lean/guest/native execution.
;; cwd research/lean-hosting; load typed-witness-next.clj first, then this file.
(require '[clojure.test :refer [deftest is testing]]
         '[prototype.native-heap :as tw-control-native])

(defn tw-control-model []
  (let [target ["str" ["str" ["anonymous"] "ModuleDataTransport"] "finalizeTransport"]
        functions {target {:params [0 1 2] :body [:return [:imm 0]]}}
        closed (atom false)
        source (reify tw-control-native/NativeSource
                 (contains-id? [_ _] false)
                 (lookup-node [_ _] nil)
                 clojure.lang.ILookup
                 (valAt [_ key] (when (= key :closed) closed))
                 (valAt [_ key fallback] (if (= key :closed) closed fallback)))
        bindings {"model" {:handler identity}}
        world (assoc (tw-m/world functions) :status :done :native-imports [source]
                     :heap {0 {:kind :ctor :tag 0 :fields [] :rc 1}
                            1 {:kind :array :tag 246 :fields [] :rc 1}} :next-id 2)]
    {:status :typed-witness-prepared :world world :source source
     :session {:functions functions :bindings bindings}
     :state (tw-m/->Ref 0) :imports (tw-m/->Ref 1)
     :profile (atom {}) :start-claimed? (atom false)}))

(defn tw-control-open [cache]
  (fn [functions bindings options]
    (merge options {:functions functions :bindings bindings :cache cache})))

(deftest tw-start-and-outer-continuation-never-replay-test
  (let [prepared (tw-control-model) cache (atom {}) invocations (atom 0)
        calls (atom [])]
    (with-redefs [tw-raw/open-functions (tw-control-open cache)
                  tw-raw/continue
                  (fn [session world]
                    (swap! calls conj [session world])
                    (if (= 1 (swap! invocations inc))
                      (throw (ex-info "Raw runtime instruction budget exhausted"
                               {:checkpoint (assoc world :status :paused)
                                :checkpoint-session session}))
                      {:state (assoc world :status :done :result 0) :session session :value 0}))]
      (let [paused (start-full-init-finalizer-slice prepared {:fuel 7 :backend :mutable})]
        (is (= :paused-outer (:outcome paused)))
        (is (= 1 @invocations))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"start already claimed"
                             (start-full-init-finalizer-slice prepared {:fuel 7})))
        (is (= 1 @invocations) "Duplicate start must not call the driver")
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Slice fuel"
                             (continue-full-init-finalizer-slice paused 0)))
        (is (false? @(:continue-claimed? paused)) "Failed preflight must not claim continuation")
        (let [returned (continue-full-init-finalizer-slice paused 11)
              [first-session first-world] (first @calls)
              [next-session next-world] (second @calls)]
          (is (= :guest-io-returned (:outcome returned)))
          (is (= 2 @invocations))
          (is (identical? cache (:cache first-session)))
          (is (identical? cache (:cache next-session)))
          (is (identical? (:bindings first-session) (:bindings next-session)))
          (is (identical? (:functions first-session) (:functions next-session)))
          (is (= 11 (:fuel next-session)))
          (is (identical? (:world paused) next-world) "Resume the exact paused snapshot, not m/start")
          (is (identical? (:source prepared) (:source returned)))
          (is (identical? (:source prepared) (first (:native-imports first-world))))
          (is (identical? (:source prepared) (first (:native-imports next-world))))
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Continuation already claimed"
                               (continue-full-init-finalizer-slice paused 11)))
          (is (= 2 @invocations)))))))

(deftest tw-nested-checkpoint-is-not-an-outer-continuation-test
  (doseq [message ["Raw runtime instruction budget exhausted" "handler already effected IO"]]
    (let [prepared (tw-control-model) invocations (atom 0) cache (atom {})]
      (with-redefs [tw-raw/open-functions (tw-control-open cache)
                    tw-raw/continue
                    (fn [session world]
                      (swap! invocations inc)
                      (throw (ex-info message
                               {:checkpoint (assoc world :status :paused)
                                :checkpoint-session session
                                :host-boundaries [{:checkpoint (assoc world :status :host-call)
                                                   :session session :helper {:target :model-nested}}]})))]
        (let [result (start-full-init-finalizer-slice prepared {:fuel 7})]
          (is (= :blocked-nested (:outcome result)))
          (is (= 1 (get-in result [:summary :host-boundary-depth])))
          (is (nil? (:continue-claimed? result)))
          (is (= message (.getMessage ^Throwable (:failure result))))
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Only a top-level"
                               (continue-full-init-finalizer-slice result 11)))
          (is (= 1 @invocations) "A nested checkpoint must never replay its effected host handler"))))))

(deftest tw-unrelated-failure-is-not-resumable-test
  (let [prepared (tw-control-model)]
    (with-redefs [tw-raw/open-functions (tw-control-open (atom {}))
                  tw-raw/continue (fn [session world]
                                    (throw (ex-info "model validation failure"
                                             {:checkpoint (assoc world :status :paused)
                                              :checkpoint-session session})))]
      (let [result (start-full-init-finalizer-slice prepared {:fuel 7})]
        (is (= :failed (:outcome result)))
        (is (nil? (:continue-claimed? result)))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Only a top-level"
                             (continue-full-init-finalizer-slice result 11)))))))

(deftest tw-closed-source-and-mismatched-session-do-not-claim-test
  (let [prepared (tw-control-model) cache (atom {}) invocations (atom 0)]
    (with-redefs [tw-raw/open-functions (tw-control-open cache)
                  tw-raw/continue
                  (fn [session world]
                    (swap! invocations inc)
                    (throw (ex-info "Raw runtime instruction budget exhausted"
                             {:checkpoint (assoc world :status :paused) :checkpoint-session session})))]
      (let [paused (start-full-init-finalizer-slice prepared {:fuel 7})
            mismatch (assoc-in paused [:session :functions] {})]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"executable mismatch"
                             (continue-full-init-finalizer-slice mismatch 7)))
        (is (false? @(:continue-claimed? paused)))
        (reset! (:closed (:source prepared)) true)
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Source already closed"
                             (continue-full-init-finalizer-slice paused 7)))
        (is (false? @(:continue-claimed? paused)))
        (is (= 1 @invocations))))))

(deftest tw-profile-storage-is-bounded-test
  (let [profile (atom {})]
    (doseq [i (range 100)] (tw-profile! profile [:model i] 1.0 3 false))
    (is (= 64 (count @profile)))
    (is (= 100 (reduce + (map :calls (vals @profile)))))
    (is (= 300 (reduce + (map :completed-guest-steps (vals @profile)))))
    (is (= 37 (get-in @profile [:other :calls])))))

(deftest tw-invalid-assembly-preflight-does-not-claim-or-open-test
  (let [mutations {:running-world #(assoc-in % [:world :status] :running)
                   :active-frames #(assoc-in % [:world :frames] [{}])
                   :pending-host #(assoc-in % [:world :host-request] {:symbol "model"})
                   :mismatched-functions #(assoc-in % [:session :functions] {})
                   :no-attached-source #(assoc-in % [:world :native-imports] [])
                   :multiple-sources #(update-in % [:world :native-imports] conj (:source %))
                   :different-source #(assoc % :source {:closed (atom false)})
                   :dangling-state #(assoc % :state (tw-m/->Ref 10))
                   :dangling-imports #(assoc % :imports (tw-m/->Ref 11))
                   :scalar-root #(assoc % :state 0)}]
    (doseq [[label mutate] mutations]
      (testing (name label)
        (let [prepared (tw-control-model) invalid (mutate prepared) opened (atom 0) driven (atom 0)]
          (with-redefs [tw-raw/open-functions (fn [& _] (swap! opened inc) (throw (Exception. "must not open")))
                        tw-raw/continue (fn [& _] (swap! driven inc) (throw (Exception. "must not drive")))]
            (is (thrown? clojure.lang.ExceptionInfo (start-full-init-finalizer-slice invalid {:fuel 7})))
            (is (false? @(:start-claimed? prepared)))
            (is (zero? @opened))
            (is (zero? @driven))
            ;; Preparation itself must reject invalid capability/world/root
            ;; identity BEFORE any artifact parsing or witness linking.
            (is (thrown? clojure.lang.ExceptionInfo
                         (prepare-full-init-shared-witness (assoc invalid :status :assembled-only))))
            (is (false? @(:start-claimed? prepared)))))))))

(deftest tw-concurrent-claims-execute-driver-once-test
  ;; Host threads test claim linearization, NOT concurrent guest execution.
  ;; Both contenders cross the same latch before trying each single-use API.
  (doseq [operation [:start :continue]]
    (testing (name operation)
      (let [prepared (tw-control-model) cache (atom {}) invocations (atom 0)
            ready (java.util.concurrent.CountDownLatch. 2)
            go (java.util.concurrent.CountDownLatch. 1)
            paused {:outcome :paused-outer :world (assoc (:world prepared) :status :paused)
                    :session (assoc (:session prepared) :cache cache) :source (:source prepared)
                    :profile (:profile prepared) :continue-claimed? (atom false)}
            outcomes [(promise) (promise)]
            run (fn [result]
                  (.countDown ready)
                  (try
                    (when-not (.await go 2 java.util.concurrent.TimeUnit/SECONDS)
                      (throw (Exception. "model race gate timed out")))
                    (deliver result
                      [:returned (if (= operation :start)
                                   (start-full-init-finalizer-slice prepared {:fuel 7})
                                   (continue-full-init-finalizer-slice paused 7))])
                    (catch Throwable e (deliver result [:thrown e]))))
            threads (mapv (fn [result] (doto (Thread. #(run result)) (.setDaemon true))) outcomes)]
        (with-redefs [tw-raw/open-functions (tw-control-open cache)
                      tw-raw/continue (fn [session world]
                                        (swap! invocations inc)
                                        {:state (assoc world :status :done :result 0)
                                         :session session :value 0})]
          (try
            (doseq [thread threads] (.start thread))
            (is (.await ready 2 java.util.concurrent.TimeUnit/SECONDS))
            (.countDown go)
            (let [results (mapv #(deref % 2000 ::timeout) outcomes)
                  returned (filter #(= :returned (first %)) (remove #{::timeout} results))
                  thrown (filter #(= :thrown (first %)) (remove #{::timeout} results))]
              (is (not-any? #{::timeout} results))
              (is (= 1 @invocations) "Exactly one claim may enter the raw driver")
              (is (= 1 (count returned)))
              (is (= :guest-io-returned (:outcome (second (first returned)))))
              (is (= 1 (count thrown)))
              (is (instance? clojure.lang.ExceptionInfo (second (first thrown))))
              (is (re-find #"already claimed" (or (some-> thrown first second .getMessage) ""))))
            (finally
              (.countDown go)
              (doseq [thread threads] (.join thread 2000)))))))))
