(ns prototype.resident-preparation-test
  "Ownership/preflight MODELS using captured IR; no actual Lean frontend claim."
  (:require [clojure.test :refer [deftest is]]
            [prototype.resident-preparation :as preparation]
            [prototype.resident-frontend :as resident]
            [prototype.resident-frontend-test :as model]
            [prototype.hosted-file-test :as hosted-model]
            [prototype.guest-encoding :as encoding]
            [prototype.kernel-host :as kernel]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]
            [prototype.native-heap :as native]))

(defn fixture
  ([] (fixture :reference))
  ([backend]
   (let [p (model/prepared backend true @hosted-model/captured)
         p (assoc-in p [:world :globals preparation/options-empty]
                     {:status :ready :value (:options p)})]
     {:candidate (dissoc p :options)
      :options (:options p)
      :configuration {:catalogue (:catalogue p)
                      :trusted-functions (get-in p [:world :functions])
                      :trusted-bindings (get-in p [:session :bindings])}})))
(defn failure [f] (try (f) nil (catch clojure.lang.ExceptionInfo e e)))
(defn rc [world value] (:rc (m/node world value)))

(deftest checked-opening-acquires-one-options-owner-and-preserves-backend-cache
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [candidate options configuration]} (fixture backend)
          ctx (preparation/open-checked candidate configuration)
          p (resident/snapshot ctx)
          branch (resident/fork ctx)]
      (is (= 1 (rc (:world candidate) options)))
      (is (= 2 (rc (:world p) options)))
      (is (= 2 (rc (:world p) (:environment p))))
      (is (identical? (get-in candidate [:session :cache]) (get-in p [:session :cache])))
      (is (= backend (get-in p [:session :backend])))
      (resident/close! ctx)
      (is (= 2 (rc (:world (resident/snapshot branch)) options)))
      (resident/close! branch)
      (is (= 1 (rc (:world candidate) options))))))

(deftest independent-readiness-fails-before-any-association-or-options-acquisition
  (let [{:keys [candidate configuration]} (fixture)
        associations (atom 0) acquisitions (atom 0)]
    (with-redefs [kernel/inherit-checked-association (fn [& _] (swap! associations inc) (throw (AssertionError. "guest call")))
                  m/initialized-value (fn [& _] (swap! acquisitions inc) (throw (AssertionError. "Options read")))]
      (doseq [[candidate configuration]
              [[candidate (update configuration :trusted-functions dissoc encoding/names-helper)]
               [candidate (assoc configuration :trusted-bindings {"rogue" {}})]
               [(assoc-in candidate [:world :status] :paused) configuration]
               [(update-in candidate [:session :functions] with-meta {:different true}) configuration]]]
        (let [error (failure #(preparation/open-checked candidate configuration))]
          (is (some? error))
          (is (identical? (:world candidate) (:checkpoint (ex-data error))))
          (is (= (select-keys candidate [:world :session :environment])
                 (dissoc (:resident-preparation-entry (ex-data error)) :catalogue))))))
    (is (zero? @associations))
    (is (zero? @acquisitions))))

(deftest certificates-and-phase-flags-cannot-replace-live-association
  (let [{:keys [candidate options configuration]} (fixture)
        candidate (-> candidate (update :world dissoc :kernel-environments)
                      (assoc :phase :checked :certificate {:env :forged}))
        acquisitions (atom 0)
        error (with-redefs [m/initialized-value (fn [& _] (swap! acquisitions inc))]
                (failure #(preparation/open-checked candidate configuration)))]
    (is (some? error))
    (is (zero? @acquisitions))
    (is (= 1 (rc (:world candidate) options)))
    (is (nil? (:resident-preparation-options-entry (ex-data error))))))

(deftest only-a-ready-real-options-global-is-acquired
  (let [{:keys [candidate options configuration]} (fixture)]
    (doseq [world [(update (:world candidate) :globals dissoc preparation/options-empty)
                   (assoc-in (:world candidate) [:globals preparation/options-empty :status] :pending)
                   (assoc-in (:world candidate) [:globals preparation/options-empty :value] 0)]]
      (let [error (failure #(preparation/open-checked (assoc candidate :world world) configuration))
            data (ex-data error)]
        (is (some? error))
        (is (some? (:resident-preparation-associated-entry data)))
        (is (nil? (:resident-preparation-options-entry data)))
        (is (= 1 (rc world options)))))))

(deftest second-association-failure-preserves-owned-entry-and-newest-checkpoint
  (let [{:keys [candidate options configuration]} (fixture)
        inherit kernel/inherit-checked-association
        calls (atom 0) latest (atom nil)
        error (with-redefs [kernel/inherit-checked-association
                            (fn [runtime world environment helpers]
                              (if (= 1 (swap! calls inc))
                                (inherit runtime world environment helpers)
                                (let [world (assoc world :test-newer-checkpoint true)
                                      session (raw/open-functions (:functions world) {} {:backend :reference})]
                                  (reset! latest {:world world :session session})
                                  (throw (ex-info "Second association failed" {:checkpoint world :checkpoint-session session})))))]
                (failure #(preparation/open-checked candidate configuration)))
        data (ex-data error)
        owned (:resident-preparation-options-entry data)]
    (is (= 2 @calls))
    (is (identical? (:world @latest) (:checkpoint data)))
    (is (identical? (:session @latest) (:checkpoint-session data)))
    (is (= owned (:resident-adoption-entry data)))
    (is (= 2 (rc (:world owned) options)))
    (is (= 1 (rc (:world candidate) options)))
    (is (not (:test-newer-checkpoint (:world owned))))
    (is (identical? (:environment candidate) (:environment owned)))))

(deftest aliased-environment-options-keep-two-context-owners
  (let [{:keys [candidate configuration options]} (fixture)
        environment (:environment candidate)
        inherit kernel/inherit-checked-association
        calls (atom 0)
        ctx (with-redefs [kernel/inherit-checked-association
                          (fn [runtime world env helpers]
                            (let [[world checked] (inherit runtime world env helpers)]
                              ;; Model a first association returning a newer view;
                              ;; Options MUST be acquired from that returned world.
                              [(if (= 1 (swap! calls inc))
                                 (assoc-in world [:globals preparation/options-empty :value] environment)
                                 world) checked]))]
              (preparation/open-checked candidate configuration))
        p (resident/snapshot ctx)]
    (is (= options (m/initialized-value (:world candidate) preparation/options-empty)))
    (is (= environment (:options p)))
    (is (= 3 (rc (:world p) environment)))
    (is (= 2 (rc (:world candidate) environment)))
    (resident/close! ctx)
    (is (= 2 (rc (:world candidate) environment)))))

(deftest borrowed-artifact-lease-is-never-closed-by-context-lifetime
  (let [{:keys [candidate configuration]} (fixture)
        closed (atom false)
        source (reify
                 native/NativeSource
                 (contains-id? [_ _] false)
                 (lookup-node [_ _] nil)
                 java.io.Closeable
                 (close [_] (reset! closed true)))
        candidate (update-in candidate [:world :native-imports] (fnil conj []) source)
        ctx (preparation/open-checked candidate configuration)
        branch (resident/fork ctx)]
    (resident/close! ctx)
    (resident/close! branch)
    (is (false? @closed))
    (.close ^java.io.Closeable source)
    (is (true? @closed))))

(deftest direct-adoption-preflight-retains-its-exact-entry-on-failure
  (let [{:keys [candidate configuration options]} (fixture)
        candidate (assoc candidate :options options)
        error (failure #(resident/adopt-prepared candidate (assoc configuration :trusted-functions {})))]
    (is (some? error))
    (is (identical? candidate (:resident-adoption-entry (ex-data error))))
    (is (identical? (:world candidate) (:checkpoint (ex-data error))))
    (is (identical? (:session candidate) (:checkpoint-session (ex-data error))))))
