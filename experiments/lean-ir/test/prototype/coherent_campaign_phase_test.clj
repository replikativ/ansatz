(ns prototype.coherent-campaign-phase-test
  "Host-only controller models; no Source, checkpoint read or guest execution."
  (:require [clojure.test :refer :all] [prototype.coherent-campaign :as campaign]
            [prototype.restore-consumer :as restore] [prototype.coherent-source-preparation :as source]
            [prototype.coherent-stage-guards :as guards] [prototype.raw-interop :as raw]))
(defn v [name] (ns-resolve 'prototype.coherent-campaign name))
(defn model [f]
  (let [lease (Object.) checked (Object.) calls (atom [])
        restored {:session {:compile-threshold 1} :world {:functions {}} :trusted-bindings {} :resource-lease lease}
        state (atom {:phase :constructed :factory :factory :options {:producer-preparation :producer}
                     :bootstrap {:resolve-input identity :implementation-sha256 :implementation
                                 :execution {:backend :mutable :fuel 500000000 :compile-threshold 1}
                                 :manifest {:direct-inputs [{:id "checkpoint/manifest" :sha256 :manifest}]}}})]
    (with-redefs-fn {(v 'state) state
                    #'restore/restore! (fn [& _] (swap! calls conj :restore) restored)
                    #'raw/open-functions (fn [functions _ options]
                                           (is (= :restoring (:phase @state)))
                                           (is (identical? restored (:restored @state)))
                                           (is (thrown? clojure.lang.ExceptionInfo ((v 'check-and-prepare!))))
                                           {:functions functions :compile-threshold (:compile-threshold options)})
                    #'source/prepare-bootstrap-support (fn [_ r _] (swap! calls conj :support) {:candidate r :support :support})
                    #'source/check-restored! (fn [_] (swap! calls conj :check) checked)
                    #'source/prepare! (fn [input] (is (identical? checked (:checked input))) (swap! calls conj :prepare) :summary)
                    #'source/checkpoint (fn [] :preparation-escrow)
                    #'source/checking-checkpoint (fn [] :checking-escrow)
                    #'guards/preparation-phase! (fn [& _] :helper-value-required)}
      #(binding [*out* (java.io.StringWriter.)]
         (f {:state state :calls calls :lease lease :restored restored :checked checked})))))
(deftest restore-returns-before-check-with-one-canonical-lease
  (model (fn [{:keys [state calls lease]}]
           (is (= {:phase :restored} ((v 'restore-only!))))
           (is (= [:restore] @calls)) (is (= :restored (:phase @state)))
           (is (identical? lease (get-in @state [:restored :resource-lease])))
           (is (thrown? clojure.lang.ExceptionInfo ((v 'restore-only!))))
           (is (= :summary ((v 'check-and-prepare!))))
           (is (= [:restore :support :check :prepare] @calls))
           (is (= :helper-value-required (:phase @state)))
           (is (thrown? clojure.lang.ExceptionInfo ((v 'check-and-prepare!)))))))
(deftest compatibility-driver-keeps-the-same-stage-order
  (model (fn [{:keys [calls]}]
           (is (= :summary ((v 'restore-and-prepare!))))
           (is (= [:restore :support :check :prepare] @calls)))))
(deftest failure-keeps-source-and-original-checking-escrow
  (model (fn [{:keys [state lease calls]}]
           ((v 'restore-only!))
           (let [failure (ex-info "model check failure" {})]
             (with-redefs [source/check-restored! (fn [_] (throw failure))]
               (is (identical? failure (try ((v 'check-and-prepare!)) (catch Throwable e e)))))
             (is (= :failed (:phase @state))) (is (= :checking-escrow (:checking-escrow @state)))
             (is (identical? lease (get-in @state [:restored :resource-lease])))
             (is (= [:restore :support] @calls))
             (is (thrown? clojure.lang.ExceptionInfo ((v 'check-and-prepare!))))))))
