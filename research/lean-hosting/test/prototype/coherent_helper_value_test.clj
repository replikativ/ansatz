(ns prototype.coherent-helper-value-test
  "Small helper/controller MODEL. Private source escrow is staged explicitly over
   the 17-CI fixture; actual five-instruction helper execution remains real. This
   is not full Init/source preparation or provider acceptance."
  (:require [clojure.test :refer [deftest is]]
            [prototype.coherent-source-preparation :as source]
            [prototype.coherent-source-preparation-test :as model]
            [prototype.coherent-helper-value :as helper]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]))

(defn with-prepared [artifact? f]
  (model/with-model artifact?
    (fn [{:keys [input result checking preparation baseline] :as model}]
      (let [functions (assoc (get-in result [:world :functions])
                             helper/pure-value-target {:params [] :body [:global helper/pure-value-target helper/initializer-target]}
                             helper/initializer-target {:params [] :body [:let 1 [:literal 0]
                                                                         [:let 2 [:box "uint32" [:var 1]] [:return [:var 2]]]]})
            world (assoc (:world result) :functions functions)
            session (raw/open-functions functions {} {:backend :reference :fuel 500000000})
            support (assoc (:support input) :session session)
            projection (get result (if artifact? :checked-result :certificate))
            prepared ((model/private-var 'retain-base-projection)
                      {:profile source/profile-id :actual-factory (:factory input)
                       :consumer-contract-sha256 "model-contract" :world world :session session
                       :environment (:environment result) :support support
                       :original-support (:support input) :trusted-functions functions
                       :runnable? false :missing-helper-values [helper/pure-value-target]}
                      (if artifact? :trusted-artifact :strict-fresh) result projection)
            escrow {:phase :prepared-missing-helper-values :prepared prepared
                    :evidence {:missing-helper-values [helper/pure-value-target]
                               :new-initialization-actions 0 :existing-value-actions 1}}
            helper-state (atom nil)]
        (reset! checking {:phase (if artifact? :admitted :checked) :entry input :result result})
        (reset! preparation escrow)
        (reset! baseline ((model/private-var 'initialization-snapshot) world))
        (with-redefs-fn {(ns-resolve 'prototype.coherent-helper-value 'state) helper-state}
          #(f (assoc model :prepared prepared :escrow escrow :helper-state helper-state)))))))

(deftest actual-helper-value-preserves-both-strict-and-artifact-prepared-contracts
  (doseq [artifact? [false true]]
    (with-prepared artifact?
      (fn [{:keys [prepared preparation escrow helper-state result]}]
        (let [summary (helper/initialize!)
              completed (:prepared @helper-state)]
          (is (= :initialized (:phase summary)))
          (is (= 1 (:guest-invocation-count summary) (:result-release-count summary)))
          (is (= 5 (:guest-steps-delta summary)))
          (is (identical? escrow @preparation))
          (is (true? (:runnable? completed)))
          (is (identical? (:kernel-projection prepared) (:kernel-projection completed)))
          (if artifact?
            (do (is (not (contains? completed :certificate)))
                (is (identical? (:admission result) (:admission completed)))
                (is (identical? result (:original-admitted completed))))
            (is (identical? (:certificate result) (:certificate completed))))
          (is (thrown-with-msg? Exception #"already claimed" (helper/initialize!))))))))

(deftest substituted-basis-result-does-not-execute-the-helper
  (with-prepared true
    (fn [{:keys [preparation helper-state]}]
      (let [calls (atom 0)]
        ;; This is an advanced private-state invariant model. No public map flag
        ;; is used as an issuer or a replacement for the original constructor.
        (swap! preparation update :prepared assoc :checked-result {:env :forged})
        (with-redefs [raw/call (fn [& _] (swap! calls inc) (throw (AssertionError. "Must not execute")))]
          (is (= :failed (:phase (helper/initialize!)))))
        (is (zero? @calls))
        (is (= 0 (:guest-invocation-count @helper-state)))))))

(deftest source-lifetime-remains-a-pre-execution-requirement
  (with-prepared true
    (fn [{:keys [prepared helper-state]}]
      (let [calls (atom 0) source (get-in prepared [:support :source])]
        (.close ^java.io.Closeable source)
        (with-redefs [raw/call (fn [& _] (swap! calls inc) (throw (AssertionError. "Must not execute")))]
          (is (= :failed (:phase (helper/initialize!)))))
        (is (zero? @calls))
        (is (= 0 (:guest-invocation-count @helper-state)))))))
