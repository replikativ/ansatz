(ns prototype.resident-prefix-retirement-test
  "Tiny verified Source with modeled import helpers; no full Init acceptance."
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]
            [prototype.resident-frontend :as resident]
            [prototype.resident-init-prefix :as prefix]
            [prototype.resident-init-prefix-test :as fixture]
            [prototype.source-import :as source]))

(deftest combined-retirement-matches-old-closed-heap-without-adoption
  (doseq [backend [:reference :mutable :jvm]]
    (fixture/with-fixture backend
      (fn [{:keys [source] :as f}]
        (let [{:keys [context prefix]} (fixture/prepare f)
              entry (resident/snapshot context) sibling (resident/fork context)
              raw-prefix (first (vals (get-in entry [:world :source-import-prefixes])))
              state (:state raw-prefix)
              old (prefix/release-prefix context prefix)
              old-world (volatile! nil) new-world (volatile! nil)
              release m/release close-branch resident/close-prepared-branch!
              make-context (ns-resolve 'prototype.resident-frontend 'make-context)]
          (try
            ;; Capture the old returned Context's final immutable World while
            ;; preserving release's 3 -> 4 arity delegation exactly once.
            (with-redefs [m/release (fn
                                     ([world value count]
                                      (let [result (release world value count false)]
                                        (vreset! old-world result) result))
                                     ([world value count persistent?]
                                      (let [result (release world value count persistent?)]
                                        (vreset! old-world result) result)))]
              (resident/close! (:context old)))
            (let [result
                  (with-redefs-fn
                    {#'resident/adopt-prepared (fn [& _] (throw (AssertionError. "adoption")))
                     make-context (fn [& _] (throw (AssertionError. "Context creation")))
                     #'raw/call (fn [& _] (throw (AssertionError. "guest execution")))
                     #'resident/close-prepared-branch!
                     (fn [prepared]
                       (let [closed (close-branch prepared)] (vreset! new-world closed) closed))}
                    (fn [] (prefix/release-prefix-and-close-branch context prefix)))]
              (is (= :closed (:status result)))
              (is (= (:receipt old) (:receipt result)))
              (is (= (:heap @old-world) (:heap @new-world)))
              (is (empty? (:source-import-prefixes @new-world)))
              (is (not (contains? (:heap @new-world) (:id state))))
              (is (identical? entry (resident/snapshot context)))
              (is (identical? entry (resident/snapshot sibling)))
              (is (= 1 (count (get-in entry [:world :source-import-prefixes]))))
              (is (false? @(:closed source))))
            (finally (resident/close! (:context old))
                     (resident/close! sibling) (resident/close! context))))))))

(deftest bad-owned-roots-reject-before-the-lower-prefix-release
  (fixture/with-fixture :reference
    (fn [f]
      (let [{:keys [context prefix]} (fixture/prepare f)
            state (.-state ^prototype.resident_frontend.Context context)
            original @state entry (:prepared original) environment (:environment entry)
            releases (atom 0)]
        (try
          (with-redefs [source/release-init-prefix
                        (fn [& _] (swap! releases inc) (throw (AssertionError. "lower release")))]
            (doseq [bad [(update-in entry [:world :heap] dissoc (:id (:options entry)))
                         (-> entry (assoc :options environment)
                             (assoc-in [:world :heap (:id environment) :rc] 1))]]
              (reset! state (assoc original :prepared bad))
              (let [error (fixture/error-of #(prefix/release-prefix-and-close-branch context prefix))]
                (is (some? error))
                (is (:resident-init-prefix-terminal? (ex-data error)))
                (is (= :entry (:resident-init-prefix-phase (ex-data error))))
                (is (identical? (:world bad) (:checkpoint (ex-data error))))))
            (is (zero? @releases)))
          (finally (reset! state original) (resident/close! context)))))))

(deftest capabilities-registry-and-live-anchor-remain-required
  (fixture/with-fixture :reference
    (fn [{:keys [source] :as f}]
      (let [{:keys [context prefix]} (fixture/prepare f)
            state (.-state ^prototype.resident_frontend.Context context)
            original @state entry (:prepared original)
            raw-prefix (first (vals (get-in entry [:world :source-import-prefixes])))
            state-id (:id (:state raw-prefix))]
        (try
          (doseq [change [(fn [world] (update world :source-import-prefixes dissoc state-id))
                          (fn [world] (assoc-in world [:heap (:base source)]
                                                {:kind :array :fields [] :rc 1}))]]
            (let [bad (update entry :world change)]
              (reset! state (assoc original :prepared bad))
              (let [error (fixture/error-of #(prefix/release-prefix-and-close-branch context prefix))]
                (is (some? error))
                (is (:resident-init-prefix-terminal? (ex-data error)))
                (is (identical? (:world bad) (:checkpoint (ex-data error)))))))
          (reset! state original)
          (is (some? (fixture/error-of
                       #(prefix/release-prefix-and-close-branch context (prototype.resident_init_prefix.InitPrefix.)))))
          (.close ^java.io.Closeable source)
          (let [error (fixture/error-of #(prefix/release-prefix-and-close-branch context prefix))]
            (is (some? error))
            (is (identical? (:world entry) (:checkpoint (ex-data error))))
            (is (identical? entry (resident/snapshot context))))
          (finally (reset! state original) (resident/close! context)))))))

(deftest options-drop-failure-keeps-advanced-checkpoint-and-completed-owner
  (fixture/with-fixture :reference
    (fn [{:keys [source] :as f}]
      (let [{:keys [context prefix]} (fixture/prepare f)
            entry (resident/snapshot context)
            close-branch resident/close-prepared-branch! release m/release
            advanced (volatile! nil) active (volatile! nil)
            dropped (atom [])]
        (try
          (let [error
                (with-redefs [resident/close-prepared-branch!
                              (fn [{:keys [options session] :as prepared}]
                                (with-redefs [m/release
                                              (fn [world value count]
                                                (swap! dropped conj value)
                                                (if (= value options)
                                                  (let [checkpoint (assoc world :retirement-test-progress true)
                                                        checkpoint-session (assoc session :retirement-test-progress true)]
                                                    (vreset! advanced checkpoint) (vreset! active checkpoint-session)
                                                    (throw (ex-info "Options release failed"
                                                                    {:checkpoint checkpoint :checkpoint-session checkpoint-session})))
                                                  (release world value count false)))]
                                  (close-branch prepared)))]
                  (fixture/error-of #(prefix/release-prefix-and-close-branch context prefix)))
                data (ex-data error)]
            (is (some? error))
            (is (= [(:environment entry) (:options entry)] @dropped))
            (is (= :root-close-started (:resident-init-prefix-phase data)))
            (is (= :release-options (:phase data)))
            (is (= {:environment :released :options :release-failed} (:owner-dispositions data)))
            (is (identical? @advanced (:checkpoint data)))
            (is (identical? @active (:checkpoint-session data)))
            (is (empty? (:source-import-prefixes (:checkpoint data))))
            (is (true? (:resident-init-prefix-terminal? data)))
            (is (identical? entry (resident/snapshot context)))
            (is (false? @(:closed source))))
          (finally (resident/close! context)))))))
