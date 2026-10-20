(ns prototype.compact-import-check-test
  "Compact consumer parity over genuine native CIs and modeled guest helpers."
  (:require [clojure.test :refer [deftest is]]
            [prototype.compact-import-check :as compact]
            [prototype.imported-kernel :as kernel]
            [prototype.machine :as m]
            [prototype.restored-import-check-test :as fixture]
            [prototype.restored-import-check :as original]))

(defn- shapes [certificate]
  (update certificate :projected #(into {} (map (fn [[name ci]] [name (kernel/checking-shape ci)])) %)))

(deftest compact-consumer-produces-the-same-complete-checked-map
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [entry configuration environment root]} (fixture/fixture backend)
          old (original/check! (original/prepare entry configuration))
          control (compact/prepare entry configuration)
          result (compact/check! control)
          selected [:constants :projected :axioms :order]]
      (is (= :ok (:status result)))
      (is (= (select-keys (shapes (:certificate old)) selected)
             (select-keys (shapes (:certificate result)) selected)))
      (is (= 17 (count (get-in result [:certificate :constants]))))
      (is (= environment (:environment result)))
      (is (identical? (get-in result [:certificate :env])
                      (get-in result [:world :kernel-environments (:id root) :env])))
      (is (= 1 (:rc (m/node (:world result) environment))))
      (is (not (contains? (get-in result [:world :heap]) (:id (:io-result entry)))))
      (is (= 1 (:rc (m/node (:world entry) (:io-result entry)))))
      (is (= :checked (:phase (compact/summary control))))
      (is (= :association (get-in (compact/summary control) [:verification-progress :phase])))
      (is (fixture/failure #(compact/check! control))))))

(deftest compact-consumer-keeps-real-kernel-policy-rejection
  (doseq [policy [{:allow-axioms? false :allow-unsafe? true}
                  {:allow-axioms? true :allow-unsafe? false}]]
    (let [{:keys [entry configuration]} (fixture/fixture)
          configuration (assoc configuration :kernel-policy policy)
          control (compact/prepare entry configuration)
          failure (fixture/failure #(compact/check! control))]
      (is (some? failure))
      (is (= :failed (:phase (compact/summary control))))
      (is (identical? (:world entry) (get-in (ex-data failure) [:restored-check-entry :world])))
      (is (nil? (:result (compact/checkpoint control)))))))

(deftest fresh-verifier-rejects-duplicates-missing-quotients-and-certificate-injection
  (let [{:keys [entry values configuration]} (fixture/fixture)
        world (:world entry) policy (:kernel-policy configuration)
        quotient (first (filter #(.isQuot ^ansatz.kernel.ConstantInfo
                                  (kernel/project-constant world %)) values))]
    (is (some? quotient))
    (doseq [candidate [(conj values (first values)) [quotient]]]
      (is (some? (fixture/failure #(kernel/verify-constants world candidate policy))))
      (is (some? (fixture/failure #(compact/verify-constants world candidate policy)))))
    (is (some? (fixture/failure
                #(compact/verify-constants world values
                                           (assoc policy :projection-certificate {:env nil})))))))

(deftest observer-failure-preserves-the-actual-checked-owner
  (let [{:keys [entry configuration environment]} (fixture/fixture)
        control (compact/prepare entry
                                 (assoc configuration :observe! (fn [_] (throw (ex-info "observer" {})))))
        failure (fixture/failure #(compact/check! control))
        result (:result (compact/checkpoint control))]
    (is (some? failure))
    (is (= :ok (:status result)))
    (is (= environment (:environment result)))
    (is (identical? result (:restored-check-result (ex-data failure))))
    (is (= :failed (:phase (compact/summary control))))
    (is (true? (:checking-completed (compact/summary control))))))

(deftest io-error-is-preserved-without-projection-or-helper-execution
  (let [{:keys [entry configuration]} (fixture/fixture)
        [world error] (m/resource (:world entry) "model IO error")
        [world io] (m/allocate world :ctor 1 [error])
        world (assoc world :result io)
        control (compact/prepare (assoc entry :world world :io-result io) configuration)
        result (compact/check! control)]
    (is (= :io-error (:status result)))
    (is (identical? world (:world result)))
    (is (= io (:io-result result)))
    (is (nil? (:verification-progress (compact/checkpoint control))))
    (is (= :guest-io-error (:phase (compact/summary control))))))
