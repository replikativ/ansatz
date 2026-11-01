(ns prototype.compact-import-check-test
  "Compact consumer parity over genuine native CIs and modeled guest helpers."
  (:require [clojure.test :refer [deftest is]]
            [prototype.compact-import-check :as compact]
            [prototype.compact-kernel-projection :as projection]
            [prototype.imported-kernel :as kernel]
            [prototype.imported-kernel-test :as native]
            [prototype.kernel-bridge-test :as guest]
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

(deftest compact-first-pass-preserves-dependency-failure-details
  (let [loaded (native/loaded) world (:world loaded) values (native/values loaded)
        alias (get (native/by-name loaded) "aliasA")
        [changed missing] (guest/constant world "Missing")
        payload (native/payload world alias)
        failure (fn [verify world values]
                  (when-let [cause (fixture/failure #(verify world values native/policy))]
                    [(.getMessage cause) (ex-data cause)]))]
    ;; Missing dependencies and a two-definition cycle must fail before
    ;; admission rather than producing a partial or seeded checked environment.
    (let [candidate (assoc-in changed [:heap (:id payload) :fields 1] missing)
          expected (failure kernel/verify-constants candidate values)]
      (is (= "Unresolved imported kernel dependencies" (first expected)))
      (is (= expected (failure compact/verify-constants candidate values))))
    (let [[cyclic level] (guest/ctor (m/world {}) 1 [guest/nil-tag] 8)
          [cyclic type] (guest/ctor cyclic 3 [level] 8)
          [cyclic a] (guest/constant cyclic "a") [cyclic b] (guest/constant cyclic "b")
          [cyclic da] (guest/declaration cyclic "a" type b)
          [cyclic db] (guest/declaration cyclic "b" type a)
          expected (failure kernel/verify-constants cyclic [da db])]
      (is (= "Unsupported recursive imported kernel dependency group" (first expected)))
      (is (= expected (failure compact/verify-constants cyclic [da db]))))))

(deftest compact-first-pass-reports-the-actual-admission-group-count
  (let [loaded (native/loaded) world (:world loaded) values (native/values loaded)
        entries (native/entries loaded) expected (count (#'kernel/groups entries))
        stages (atom [])
        certificate (with-bindings {#'compact/*stage!* #(swap! stages conj %)}
                      (compact/verify-constants world values native/policy))
        admission (filter #(= :kernel-admission (:phase %)) @stages)]
    (is (= 17 (count (:constants certificate))))
    (is (= expected (count (:order certificate))))
    (is (seq admission))
    (is (every? #(= expected (:groups-total %)) admission))
    (is (some #(= :dependency-construction (:phase %)) @stages))))

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

(deftest scoped-public-verifier-freshly-admits-native-cis-in-both-orders
  (let [loaded (native/loaded) world (:world loaded) values (native/values loaded)]
    (doseq [ordered [values (vec (reverse values))]]
      (let [before world
            expected (kernel/verify-constants world ordered native/policy)
            result (compact/verify-constants world ordered native/policy)
            selected [:constants :projected :axioms :order :projection-sources]
            environment-shapes
            (fn [certificate]
              (into {} (map (fn [ci] [(.name ^ansatz.kernel.ConstantInfo ci) (kernel/checking-shape ci)]))
                    (.allConstants ^ansatz.kernel.Env (:env certificate))))]
        (is (= 17 (count (:constants result))))
        (is (= (select-keys (shapes expected) selected) (select-keys (shapes result) selected)))
        (is (= (environment-shapes expected) (environment-shapes result)))
        (is (= (.isQuotEnabled ^ansatz.kernel.Env (:env expected))
               (.isQuotEnabled ^ansatz.kernel.Env (:env result))))
        (is (identical? before world))))))

(deftest scoped-public-verifier-still-rejects-closed-but-ill-typed-declarations
  (let [loaded (native/loaded) world (:world loaded) values (native/values loaded)
        alias (get (native/by-name loaded) "aliasA")
        payload (native/payload world alias)
        base (first (:fields (m/node world payload)))
        [world sort-zero] (guest/ctor world 3 [guest/nil-tag] 8)
        [world successor] (guest/ctor world 1 [guest/nil-tag] 8)
        [world sort-one] (guest/ctor world 3 [successor] 8)
        malformed-type (assoc-in world [:heap (:id base) :fields 2] sort-zero)
        malformed-body (assoc-in world [:heap (:id payload) :fields 1] sort-one)]
    ;; aliasA : Sort 1 := A. Sort 0 as its type, or Sort 1 as its body, is closed
    ;; and projects successfully; the fresh Java checker must reject the mismatch.
    (doseq [changed [malformed-type malformed-body]]
      (let [{:keys [project-constant]} (projection/make-scoped-projector changed)
            projected (mapv #(project-constant changed %) values)
            ;; Java rejection is RuntimeException, not the facade's ExceptionInfo.
            rejected (fn [f] (try (f) nil (catch RuntimeException cause cause)))
            expected (rejected #(kernel/verify-constants changed values native/policy))
            actual (rejected #(compact/verify-constants changed values native/policy))]
        (is (= 17 (count projected)))
        (is (some? expected))
        (is (some? actual))
        (is (= (.getMessage expected) (.getMessage actual)))
        (is (re-find #"Declaration value type does not match" (.getMessage actual)))))))

(deftest failed-item-progress-is-bounded-accurate-and-frozen
  (doseq [where [:projection :kernel-admission]]
    (let [{:keys [entry configuration]} (fixture/fixture)
          control (compact/prepare entry configuration) original (ex-info "modeled item failure" {})
          replacements (if (= where :projection)
                         {#'projection/make-scoped-projector (fn [_] {:project-constant (fn [& _] (throw original))})}
                         {(ns-resolve 'prototype.compact-import-check 'validate-quot-bootstrap) (fn [_] (throw original))})
          failure (with-redefs-fn replacements #(fixture/failure (fn [] (compact/check! control))))
          first-progress (:verification-progress (compact/summary control))]
      (is (some #(identical? original %) (take-while some? (iterate #(.getCause ^Throwable %) failure))))
      (is (= :failed (:phase (compact/summary control))))
      (is (= where (:phase first-progress)))
      (is (integer? (:item-elapsed-ns first-progress)))
      (Thread/sleep 2)
      (is (= (:item-elapsed-ns first-progress)
             (get-in (compact/summary control) [:verification-progress :item-elapsed-ns])))
      (if (= where :projection)
        (do (is (= 0 (:projected-constants first-progress))) (is (integer? (:guest-id first-progress))))
        (do (is (< (:groups-checked first-progress) (:groups-total first-progress)))
            (is (<= (count (:group-name first-progress)) 256))))
      (is (nil? (:result (compact/checkpoint control)))))))
