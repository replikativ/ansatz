(ns prototype.resident-executor-test
  "Executor-boundary MODEL using captured identity IR; no hosted frontend claim."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.string :as str]
            [prototype.resident-frontend :as resident]
            [prototype.resident-frontend-test :as model]
            [prototype.hosted-file-test :as hosted]
            [prototype.interop-codec :as codec]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]))

(def bytes-signature {:arguments [:erased :bytes] :result :bytes})
(defn failure [f] (try (f) nil (catch clojure.lang.ExceptionInfo e e)))
(defn with-loaded [bundle f]
  (let [base (model/context :reference true bundle)
        loaded (model/load-identity base)]
    (try (f loaded)
         (finally (resident/close! (:context loaded)) (resident/close! base)))))
(defn invoke [loaded values signature selector]
  (resident/call-with-executor (:context loaded) (:file loaded)
                               hosted/answer-name values signature selector))
(defn ordinary-selection [{:keys [prepared]}]
  {:prepared prepared :invoke raw/call})

(deftest decline-precedes-encoding-and-preserves-default-call
  (with-loaded @hosted/captured
    (fn [loaded]
      (let [events (atom []) encode codec/encode-boxed
            called (with-redefs [codec/encode-boxed
                                 (fn [& args] (swap! events conj :encode) (apply encode args))]
                     (invoke loaded [nil 42] model/identity-signature
                             (fn [request]
                               (swap! events conj :select)
                               (is (= model/identity-signature (:signature request)))
                               (is (= 2 (count (get-in request [:abi :params]))))
                               nil)))]
        (is (= [:select :encode :encode] @events))
        (is (= 42 (:value called)))
        (resident/close! (:context called))))))

(deftest selected-execution-uses-canonical-completion-and-codecs
  (with-loaded @hosted/captured
    (fn [loaded]
      (let [executions (atom 0)
            called (invoke loaded [nil [0 128 255]] bytes-signature
                           (fn [{:keys [prepared source-name target]}]
                             (is (= ["str" ["anonymous"] "answer"] source-name))
                             (is (= target (get-in prepared [:world :eval-const-authorizations
                                                            :declarations target :name])))
                             {:prepared prepared
                              :invoke (fn [session world target args]
                                        (swap! executions inc)
                                        (raw/call session world target args))}))]
        (is (= 1 @executions))
        (is (= [0 128 255] (:value called)))
        (is (= 0 (get-in (resident/snapshot (:context called)) [:world :result])))
        (resident/close! (:context called))))))

(deftest invalid-selection-rejects-before-argument-ownership
  (with-loaded @hosted/captured
    (fn [loaded]
      (doseq [select [(constantly false)
                     (fn [{:keys [prepared]}]
                       {:prepared (assoc prepared :environment 42) :invoke raw/call})
                     (fn [{:keys [prepared]}] {:prepared prepared :invoke :not-an-executor})]]
        (let [error (with-redefs [codec/encode-boxed
                                  (fn [& _] (throw (AssertionError. "encoding started")))]
                      (failure #(invoke loaded [nil 42] model/identity-signature select)))]
          (is (re-find #"changed resident authority" (.getMessage error)))
          (is (= [] (:resident-temporary-owners (ex-data error)))))))))

(deftest inconsistent-reply-is-evidence-not-a-promoted-checkpoint
  (with-loaded @hosted/captured
    (fn [loaded]
      (let [input-world (atom nil) actual (atom nil)
            error (failure #(invoke loaded [nil [1 2]] bytes-signature
                                    (fn [{:keys [prepared]}]
                                      {:prepared prepared
                                       :invoke (fn [session world target args]
                                                 (reset! input-world world)
                                                 (let [reply (raw/call session world target args)]
                                                   (reset! actual reply)
                                                   (assoc reply :value -1)))})))
            data (ex-data error)]
        (is (re-find #"inconsistent completion" (.getMessage error)))
        (is (identical? @input-world (:checkpoint data)))
        (is (= -1 (get-in data [:resident-executor-reply :value])))
        (is (= (:state @actual) (get-in data [:resident-executor-reply :state])))
        (is (not (contains? data :resident-completed-invocation)))
        (is (not (contains? data :resident-owned-result)))))))

(deftest executor-error-keeps-actual-owned-arguments-and-never-falls-back
  (with-loaded @hosted/captured
    (fn [loaded]
      (let [entries (atom 0)
            error (with-redefs [raw/call (fn [& _] (throw (AssertionError. "fallback entered")))]
                    (failure #(invoke loaded [nil [7 8]] bytes-signature
                                      (fn [{:keys [prepared]}]
                                        {:prepared prepared
                                         :invoke (fn [session world _ args]
                                                   (swap! entries inc)
                                                   (throw (ex-info "selected execution failed"
                                                                   {:checkpoint world :checkpoint-session session
                                                                    :executor-owned-arguments args})))}))))
            data (ex-data error) argument (second (:executor-owned-arguments data))]
        (is (= 1 @entries))
        (is (re-find #"selected execution failed" (.getMessage error)))
        (is (= [] (:resident-temporary-owners data)))
        (is (= [7 8] (:bytes (m/node (:checkpoint data) argument))))
        (is (= 1 (:rc (m/node (:checkpoint data) argument))))
        (is (identical? (get-in data [:checkpoint :functions])
                        (get-in data [:checkpoint-session :functions])))))))

(defn borrowed-bundle []
  ;; The emitted boxed wrapper normally consumes x2. This boundary model instead
  ;; borrows it, while the original inner identity retains its result owner.
  (str (str/join "\n"
                 (for [line (str/split-lines @hosted/captured)
                       :let [row (json/read-str line :key-fn keyword)]]
                   (json/write-str
                     (if (= "_boxed" (last (:name row)))
                       (let [body (get-in row [:ir :fdecl :body])]
                         (-> row
                             (assoc-in [:ir :fdecl :xs 1 :borrow] true)
                             (assoc-in [:ir :fdecl :body] (assoc body 4 (last (nth body 4))))))
                       row)))) "\n"))

(deftest discharged-result-is-not-reissued-after-context-construction-failure
  (with-loaded @hosted/captured
    (fn [loaded]
      (let [result-ref (atom nil)
            error (with-redefs-fn
                    {(ns-resolve 'prototype.resident-frontend 'make-context)
                     (fn [_] (throw (ex-info "context construction failed" {})))}
                    #(failure (fn []
                                (invoke loaded [nil [5 6]] bytes-signature
                                        (fn [{:keys [prepared]}]
                                          {:prepared prepared
                                           :invoke (fn [session world target args]
                                                     (let [reply (raw/call session world target args)]
                                                       (reset! result-ref (:value reply)) reply))})))))
            data (ex-data error)]
        (is (re-find #"context construction failed" (.getMessage error)))
        (is (= [] (:resident-temporary-owners data)))
        (is (not (contains? data :resident-owned-result)))
        (is (= 0 (get-in data [:checkpoint :result])))
        (is (thrown? clojure.lang.ExceptionInfo (m/node (:checkpoint data) @result-ref)))))))

(deftest cleanup-failure-retains-latest-world-and-only-remaining-owners
  (with-loaded (borrowed-bundle)
    (fn [loaded]
      (let [result-ref (atom nil) after-borrow (atom nil) releases (atom 0)
            release m/release
            error (with-redefs [m/release
                                (fn [world value n]
                                  (if (= value @result-ref)
                                    (case (swap! releases inc)
                                      1 (let [next (release world value n false)] (reset! after-borrow next) next)
                                      2 (throw (ex-info "result cleanup failed" {})))
                                    (release world value n false)))]
                    (failure #(invoke loaded [nil [3 4]] bytes-signature
                                      (fn [{:keys [prepared]}]
                                        {:prepared prepared
                                         :invoke (fn [session world target args]
                                                   (let [reply (raw/call session world target args)]
                                                     (reset! result-ref (:value reply)) reply))}))))
            data (ex-data error)]
        (is (re-find #"result cleanup failed" (.getMessage error)))
        (is (= 2 @releases))
        (is (identical? @after-borrow (:checkpoint data)))
        (is (= [] (:resident-temporary-owners data)))
        (is (= @result-ref (:resident-owned-result data)))
        (is (= 1 (:rc (m/node (:checkpoint data) @result-ref))))
        (is (= 2 (:rc (m/node (get-in data [:resident-completed-invocation :state]) @result-ref))))))))
