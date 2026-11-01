(ns prototype.resident-branch-retirement-test
  "Small immutable ownership models; no Source/Init or native resource claim."
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]
            [prototype.resident-frontend :as resident]))

(defn packet []
  (let [functions {}
        [world environment] (m/resource (m/world functions) :environment)
        [world options] (m/resource world :options)]
    {:world world :session {:functions functions :bindings {}}
     :environment environment :options options}))

(defn failure [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo cause cause)))

(deftest closes-only-the-new-branch-without-adoption-or-guest-execution
  (let [{:keys [world session environment options] :as prepared} (packet)
        result (with-redefs [resident/adopt-prepared (fn [& _] (throw (AssertionError. "adoption")))
                             raw/call (fn [& _] (throw (AssertionError. "guest execution")))]
                 (resident/close-prepared-branch! prepared))]
    (is (= [[:released :environment] [:released :options]] (:events result)))
    (is (empty? (:heap result)))
    (is (= 1 (:rc (m/node world environment))))
    (is (= 1 (:rc (m/node world options))))
    (is (identical? world (:world prepared)))
    (is (identical? session (:session prepared)))
    (is (= (:stats world) (:stats result)))
    (is (map? result))
    (is (not (instance? prototype.resident_frontend.Context result)))))

(deftest both-roots-and-aliased-counts-are-checked-before-first-release
  (let [{:keys [environment] :as prepared} (packet) releases (atom 0)]
    (with-redefs [m/release (fn [& _] (swap! releases inc) (throw (AssertionError. "drop")))]
      (doseq [candidate [(assoc prepared :options environment)
                         (assoc prepared :options (m/->Ref 999))
                         (assoc-in prepared [:world :status] :running)]]
        (let [data (ex-data (failure #(resident/close-prepared-branch! candidate)))]
          (is (= :validate-owned-roots (:phase data)))
          (is (= {:environment :owned :options :owned} (:owner-dispositions data)))
          (is (identical? (:world candidate) (:checkpoint data)))
          (is (true? (:terminal data)))))
      (is (zero? @releases)))))

(deftest aliased-two-owners-and-immortal-roots-retire-in-order
  (let [{:keys [world environment] :as prepared} (packet)
        aliased (assoc prepared :options environment)
        finite (m/retain world environment 1)
        closed (resident/close-prepared-branch! (assoc aliased :world finite))]
    (is (nil? (get-in closed [:heap (:id environment)])))
    (is (= [[:released :environment]] (:events closed)))
    (let [[constructor-world root] (m/allocate (m/world (:functions world)) :ctor 0 [])
          immortal (m/mark-persistent constructor-world root)]
      (is (identical? immortal
                      (resident/close-prepared-branch! (assoc aliased :world immortal :environment root :options root)))))
    (let [extra (-> world (m/retain environment 2) (m/retain (:options prepared) 2))
          remaining (resident/close-prepared-branch! (assoc prepared :world extra))]
      (is (= 2 (:rc (m/node remaining environment))))
      (is (= 2 (:rc (m/node remaining (:options prepared))))))))

(deftest partial-failure-reports-completed-owner-and-latest-checkpoint
  (let [{:keys [world session environment options] :as prepared} (packet)
        release m/release after-environment (release world environment 1)]
    (doseq [advanced? [false true]]
      (let [calls (atom [])
            advanced (assoc after-environment :retirement-progress :lower-checkpoint)
            active-session (assoc session :lower-progress true)
            cause (ex-info "Options drop failed"
                           (when advanced? {:checkpoint advanced :checkpoint-session active-session}))
            error (with-redefs [m/release (fn [current value count]
                                          (swap! calls conj value)
                                          (if (= value options) (throw cause)
                                              (release current value count false)))]
                    (failure #(resident/close-prepared-branch! prepared)))
            data (ex-data error)]
        (is (= [environment options] @calls))
        (is (= :release-options (:phase data)))
        (is (= {:environment :released :options :release-failed} (:owner-dispositions data)))
        (is (= (if advanced? advanced after-environment) (:checkpoint data)))
        (is (identical? (if advanced? active-session session) (:checkpoint-session data)))
        (is (identical? cause (.getCause error)))
        (is (true? (:terminal data)))
        (is (= 1 (:rc (m/node world environment))))
        (is (= 1 (:rc (m/node world options))))))))

(deftest ordinary-context-close-retains-its-consumption-contract
  (let [prepared (packet)
        state (atom {:prepared prepared})
        context (prototype.resident_frontend.Context. state)
        calls (atom []) release m/release]
    (with-redefs [m/release (fn [world value count]
                             (swap! calls conj value)
                             (release world value count false))]
      (is (nil? (resident/close! context)))
      (is (nil? @state))
      (is (nil? (resident/close! context)))
      (is (= [(:environment prepared) (:options prepared)] @calls)))))
