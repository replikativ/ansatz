(ns prototype.resident-prefix-warm-validation-test
  "Warm-code-proof controls on the tiny Source fixture; no full Init acceptance."
  (:require [clojure.test :refer [deftest is]]
            [prototype.eval-const :as eval]
            [prototype.resident-frontend :as resident]
            [prototype.resident-init-prefix :as prefix]
            [prototype.resident-init-prefix-test :as fixture]))

(def capability (ns-resolve 'prototype.resident-init-prefix 'capability!))

(deftest warm-code-proofs-do-not-replace-live-readiness-or-prefix-validation
  (fixture/with-fixture :reference
    (fn [{:keys [source] :as f}]
      (let [{:keys [context prefix]} (fixture/prepare f)
            state (.-state ^prototype.resident_frontend.Context context)
            original @state entry (:prepared original)
            raw-prefix (first (vals (get-in entry [:world :source-import-prefixes])))
            prefix-id (:id (:state raw-prefix))
            original-validation eval/validate-executables! walks (atom 0)]
        (try
          (with-redefs [eval/validate-executables!
                        (fn [& args] (swap! walks inc) (apply original-validation args))]
            ;; Seed under this exact validator Fn: changing semantic rules after
            ;; issuance intentionally invalidates a proof, even on the same image.
            (is (= :closed (:status (prefix/release-prefix-and-close-branch context prefix))))
            (let [proofs (:retirement-code-proofs (capability prefix))]
              (is (some? (:adoption proofs)))
              (is (some? (:preparation proofs))))
            (reset! walks 0)
            (is (= :closed (:status (prefix/release-prefix-and-close-branch context prefix))))
            (doseq [[label alter]
                    [[:binding (fn [p]
                                 (let [symbol (first (keys (get-in p [:session :bindings])))]
                                   (update-in p [:session :bindings symbol] assoc :handler (fn [& _] nil))))]
                     [:manifest (fn [p] (assoc-in p [:catalogue :manifests 0 :runtimeProfile :wordBits] 32))]
                     [:dead-options (fn [p] (update-in p [:world :heap] dissoc (:id (:options p))))]
                     [:aliased-root-owners (fn [p] (-> p (assoc :options (:environment p))
                                                       (assoc-in [:world :heap (:id (:environment p)) :rc] 1)))]
                     [:registry (fn [p] (update-in p [:world :source-import-prefixes] dissoc prefix-id))]
                     [:native-anchor (fn [p] (assoc-in p [:world :heap (:base source)]
                                                       {:kind :array :fields [] :rc 1}))]]]
              (let [changed (alter entry)]
                (reset! state (assoc original :prepared changed))
                (let [error (fixture/error-of #(prefix/release-prefix-and-close-branch context prefix))]
                  (is (some? error) (name label))
                  (is (:resident-init-prefix-terminal? (ex-data error)) (name label))
                  (is (identical? (:world changed) (:checkpoint (ex-data error))) (name label))
                  (is (identical? changed (resident/snapshot context)) (name label)))
                (reset! state original)))
            ;; Source liveness is a lower native-prefix check even on a code hit.
            (.close ^java.io.Closeable source)
            (let [error (fixture/error-of #(prefix/release-prefix-and-close-branch context prefix))]
              (is (some? error))
              (is (identical? (:world entry) (:checkpoint (ex-data error)))))
            (is (zero? @walks)))
          (finally (reset! state original) (resident/close! context)))))))

(deftest changed-configured-root-selection-misses-a-warm-code-proof
  (fixture/with-fixture :reference
    (fn [f]
      (let [{:keys [context prefix]} (fixture/prepare f)
            entry (resident/snapshot context)
            original-capability @capability
            original-validation eval/validate-executables! walks (atom 0)
            missing ["str" ["anonymous"] "MissingWarmRetirementCompiler"]]
        (try
          (with-redefs [eval/validate-executables!
                        (fn [& args] (swap! walks inc) (apply original-validation args))]
            (is (= :closed (:status (prefix/release-prefix-and-close-branch context prefix))))
            (reset! walks 0)
            ;; Alter only configured root selection; the validator Fn and code
            ;; maps remain identical to those used when seeding the proof slots.
            (with-redefs-fn
              {capability (fn [token]
                            (assoc-in (original-capability token)
                                      [:configuration :frontend-configuration :compile-target] missing))}
              (fn []
                (let [error (fixture/error-of #(prefix/release-prefix-and-close-branch context prefix))]
                  (is (some? error))
                  (is (re-find #"differs from authorized" (.getMessage ^Throwable (.getCause error))))
                  (is (= 1 @walks))
                  (is (identical? (:world entry) (:checkpoint (ex-data error))))))))
          (is (identical? entry (resident/snapshot context)))
          (finally (resident/close! context)))))))
