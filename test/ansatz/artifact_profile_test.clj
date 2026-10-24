(ns ansatz.artifact-profile-test
  "Small immutable profile models; no DB/kernel corpus/native work. Profile data
   is descriptive and never substitutes for actual supplement admission."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.artifact-profile :as profile]
            [ansatz.kernel.env :as env])
  (:import [ansatz.kernel Env]))
(def legacy
  {:artifact/cohort "legacy-test-cohort" :bundle/co-generation :unrecorded
   :producer {:lean {:version "4.29.0-rc2"}}
   :resources [{:role :init :resource "init" :sha256 "init-digest" :provenance/status :header-recorded}
               {:role :lex :resource "lex" :sha256 "lex-digest" :provenance/status :header-recorded}
               {:role :sizeof :resource "sizeof" :sha256 "sizeof-digest" :provenance/status :header-recorded}
               {:role :attrs :resource "attrs" :sha256 "attrs-digest" :provenance/status :unrecorded}
               {:role :matchers :resource "matchers" :sha256 "matcher-digest" :provenance/status :unrecorded}
               {:role :instances :resource "instances" :sha256 "instance-digest" :provenance/status :unrecorded}]})
(def store-manifest
  {:store/format 1 :branch "mathlib" :provenance {:lean/toolchain "leanprover/lean4:v4.33.1"}
   :artifacts {:declarations 707508}})

(deftest base-provenance-keeps-legacy-and-prepared-modes-distinct
  (let [bundled (profile/bundled legacy) stored (profile/prepared-store store-manifest)]
    (is (= :trust (get-in bundled [:base :kernel-admission])))
    (is (= :unrecorded (get-in bundled [:roles :attrs :provenance/status])))
    (is (nil? (get-in bundled [:roles :attrs :producer])))
    (is (= :prepared-trust (get-in stored [:base :kernel-admission])))
    (is (= 1 (get-in stored [:base :store-format])))
    (is (nil? (get-in stored [:base :capabilities])))
    (is (= :unrecorded (get-in stored [:roles :matchers :provenance/status])))
    (is (nil? (get-in stored [:roles :matchers :producer])))
    (is (= 2 (get-in (profile/prepared-store (assoc store-manifest :store/format 2)) [:base :store-format])))))

(deftest role-plan-never-promotes-a-matching-version-to-compatibility-authority
  (doseq [base [nil (profile/prepared-store store-manifest)
                (profile/external-export {:lean {:version "4.33.1"}} true {})]]
    (let [plan (profile/plan-supplement base legacy :lex)]
      (is (= {} (:requirements plan)))
      (is (= :lex (:kernel-role plan)))
      (is (= "lex" (get-in plan [:resource :resource])))
      (is (some #{:exact-full-ci-overlap} (:required-checks plan)))
      (is (some #{:selected-role-metadata-closure} (:required-checks plan)))
      (is (some #{:prepared-session-activation} (:required-checks plan)))
      (is (not (contains? plan :accepted?)))
      (is (nil? (get-in plan [:companion-producers :matchers :producer])))))
  (is (thrown? clojure.lang.ExceptionInfo
               (profile/plan-supplement (profile/bundled legacy) (assoc legacy :artifact/cohort "other") :lex)))
  (let [stored (assoc (profile/prepared-store store-manifest) :supplements [{:cohort "legacy-test-cohort"}])]
    (is (= {:artifact/cohort "legacy-test-cohort"} (profile/supplemental-requirements stored)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (profile/plan-supplement stored (assoc legacy :artifact/cohort "other") :sizeof)))))

(deftest profile-branches-with-env-and-retains-recorded-matcher-fallback
  (let [source {:source :bundled-by-name :cohort "legacy-test-cohort" :producer-status :unrecorded}
        a (profile/prepared-store (assoc store-manifest :derived-provenance {:matchers source}))
        before (env/with-extension (Env.) profile/extension-key a)
        after (env/with-extension before profile/extension-key (assoc a :supplements [{:kernel-role :lex}]))]
    (is (identical? source (get-in a [:roles :matchers])))
    (is (= [] (:supplements (env/get-extension before profile/extension-key nil))))
    (is (= [{:kernel-role :lex}] (:supplements (env/get-extension after profile/extension-key nil)))))
  (let [explicit (profile/external-export nil false {:matchers {:source :bundled-by-name :provenance/status :unrecorded}})]
    (is (= :trust (get-in explicit [:base :kernel-admission])))
    (is (nil? (get-in explicit [:base :producer])))
    (is (= :unrecorded (get-in explicit [:roles :matchers :provenance/status])))))
