(ns ansatz.wf-supplement-activation-test
  "The explicit strict convenience entry composes actual role admission with
   conditional session installation; toy exports do not prove frontend WF."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.session :as session]
            [ansatz.state :as state]
            [ansatz.wf-supplement :as supplement]
            [ansatz.wf-supplement-test :as fixture]
            [ansatz.bundle-test :as bundle-fixtures]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]))

(defn- same-state? [expected]
  (empty? (#'session/changed-leaves (#'session/leaves expected)
                                    (#'session/leaves (session/capture)))))

(use-fixtures :each
  (fn [f]
    (let [before (session/capture)]
      (try (session/activate! (fixture/context)) (f)
           (finally (session/activate! before))))))

(deftest strict-convenience-prepares-and-activates-the-complete-context
  (let [selected (fixture/fixture)
        installed (supplement/activate-strict-role! :lex (fixture/options selected))]
    (is (some? (env/lookup (:env installed) (name/from-string "Prod.Lex.right'"))))
    (is (contains? (env/get-extension (:env installed) :simp-unfold #{}) "Prod.Lex.right'"))
    (is (same-state? installed))))

(deftest missing-strict-authority-or-options-never-enters-installation
  (doseq [options [{} (let [legacy (#'bundle-fixtures/fixture)]
                        (assoc (fixture/options (fixture/fixture)) :bundle-options
                               {:manifest (:manifest legacy) :read-resource (:resources legacy)}))]]
    (let [before (session/capture) attempts (atom 0)
          error (with-redefs [session/activate-if-unchanged! (fn [& _] (swap! attempts inc))]
                  (fixture/error #(supplement/activate-strict-role! :lex options)))]
      (is (some? error))
      (is (zero? @attempts))
      (is (same-state? before)))))

(deftest preparation-failure-retains-the-original-error-and-never-installs
  (let [before (session/capture) cause (ex-info "preparation failed" {}) attempts (atom 0)
        observed (with-redefs [supplement/prepare-strict-role (fn [& _] (throw cause))
                               session/activate-if-unchanged! (fn [& _] (swap! attempts inc))]
                   (fixture/error #(supplement/activate-strict-role! :lex {})))]
    (is (identical? cause observed))
    (is (zero? @attempts))
    (is (same-state? before))))

(deftest session-switch-remains-responsive-and-stale-preparation-does-not-retry
  (let [entered (promise) release (promise) attempts (atom 0)
        prepared (fixture/context) foreign (fixture/context)]
    (with-redefs [supplement/prepare-strict-role
                  (fn [& _] (swap! attempts inc) (deliver entered true) @release prepared)]
      (let [operation (future (fixture/error #(supplement/activate-strict-role! :lex {})))
            switched (promise) switch (atom nil)]
        (try
          (is (= true (deref entered 5000 ::timeout)))
          ;; This normal cooperative switch must finish while preparation is
          ;; still waiting; preparation must not hold session-lock around replay.
          (reset! switch (future (session/activate! foreign) (deliver switched true)))
          (is (= true (deref switched 5000 ::timeout)))
          (deliver release true)
          (let [error (deref operation 5000 ::timeout)]
            (is (instance? clojure.lang.ExceptionInfo error))
            (is (= :rejected (get-in (ex-data error) [:outcome :status])))
            (is (= :stale (get-in (ex-data error) [:outcome :stage])))
            (is (same-state? foreign))
            (is (= 1 @attempts)))
          (finally
            ;; Release first, then join BOTH workers before the outer fixture
            ;; restores globals. Cancellation alone cannot join a thread blocked
            ;; on the cooperative monitor after an earlier assertion timeout.
            (deliver release true)
            (doseq [worker (remove nil? [operation @switch])]
              (let [result (deref worker 5000 ::timeout)]
                (is (not= ::timeout result) "worker completed before fixture restoration")
                (when (= ::timeout result) (future-cancel worker))))))))))

(deftest installation-failure-retains-original-cause-and-restoration-report
  (let [before (session/capture) selected (fixture/fixture)
        actual-prepare supplement/prepare-strict-role prepared (atom nil)
        cause (ex-info "post-CAS installation watch" {})]
    (try
      (add-watch state/ansatz-env ::failure
                 (fn [_ _ _ value]
                   (when (identical? value (:env @prepared)) (throw cause))))
      (let [error (with-redefs [supplement/prepare-strict-role
                                (fn [& args] (let [result (apply actual-prepare args)] (reset! prepared result) result))]
                    (fixture/error #(supplement/activate-strict-role! :lex (fixture/options selected))))]
        (is (instance? clojure.lang.ExceptionInfo error))
        (is (identical? cause (.getCause error)))
        (is (identical? cause (get-in (ex-data error) [:outcome :cause])))
        (is (= :restored (get-in (ex-data error) [:outcome :restoration :status])))
        (is (same-state? before)))
      (finally (remove-watch state/ansatz-env ::failure)))))
