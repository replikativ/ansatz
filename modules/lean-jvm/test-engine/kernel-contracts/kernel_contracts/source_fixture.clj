(ns kernel-contracts.source-fixture
  "Native theorem fixture construction used by carrier checking contracts."
  (:require [kernel-support.imported-kernel :as imported]
            [kernel-support.module-data :as data]
            [kernel-support.carrier :as m]
            [kernel-contracts.kernel-bridge-test :as guest])
  (:import [ansatz.kernel ConstantInfo Env TypeChecker]))

(defn fixture []
  (let [loaded (data/load-file (m/world {}) "fixtures/imported-kernel-native.jsonl")
        entries (imported/module-constants (:world loaded) (first (:roots loaded)))]
    {:world (:world loaded)
     :values (into {} (map (fn [{:keys [guest ^ConstantInfo constant]}] [(str (.name constant)) guest])) entries)}))
(defn base-env [{:keys [world values]}]
  (TypeChecker/checkConstant (Env.) (imported/project-constant world (get values "A")) 1000000))
(defn guest-list [world values]
  (reduce (fn [[world tail] value] (guest/ctor world 1 [value tail] 0))
          [world guest/nil-tag] (reverse values)))
