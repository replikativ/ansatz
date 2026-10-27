(ns prototype.resident-code-validation-boundary-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.resident-frontend :as resident]
            [prototype.resident-frontend-test :as fixture]
            [prototype.hosted-file-test :as hosted]
            [prototype.module-import :as imports]))

(def proof-key :prototype.resident-frontend/code-proof)

(deftest returned-children-inherit-the-same-code-proof
  (let [base (fixture/context :jvm) loaded (fixture/load-identity base)
        context (:context loaded) proof (get @(.-state ^prototype.resident_frontend.Context context) proof-key)
        validator (ns-resolve 'prototype.resident-code-validation 'validate-mappings!) scans (atom 0)]
    (try
      (is proof)
      (with-redefs-fn {validator (fn [& _] (swap! scans inc) (throw (AssertionError. "Unexpected rescan")))}
        #(let [called (resident/call context (:file loaded) hosted/answer-name [nil 42] fixture/identity-signature)
               child (:context called) fork (resident/fork child)]
           (try
             (is (= 42 (:value called)))
             (is (identical? proof (get @(.-state ^prototype.resident_frontend.Context child) proof-key)))
             (is (identical? proof (get @(.-state ^prototype.resident_frontend.Context fork) proof-key)))
             (is (zero? @scans))
             (finally (resident/close! fork) (resident/close! child)))))
      (finally (resident/close! context) (resident/close! base)))))

(deftest warmed-proof-keeps-all-live-root-and-session-checks
  (let [context (fixture/context :jvm) state (.-state ^prototype.resident_frontend.Context context)
        original @state prepared (:prepared original) environment (:environment prepared)]
    (try
      (is (get original proof-key))
      (doseq [alter [(fn [p] (assoc-in p [:session :functions] (with-meta (get-in p [:world :functions]) {:different true})))
                    (fn [p] (assoc-in p [:world :status] :running))
                    (fn [p] (assoc-in p [:world :frames] [{}]))
                    (fn [p] (assoc-in p [:world :host-request] {:pending true}))
                    (fn [p] (update-in p [:world :heap] dissoc (:id environment)))
                    (fn [p] (-> p (assoc :options environment)
                                (assoc-in [:world :heap (:id environment) :rc] 1)))]]
        (reset! state (assoc original :prepared (alter prepared)))
        (is (thrown? clojure.lang.ExceptionInfo (resident/fork context)))
        (reset! state original))
      ;; Public Atom replacement must not preserve a hit for a changed image.
      (let [functions (assoc (get-in prepared [:world :functions]) (:root imports/helpers)
                             {:params [1] :body [:return [:imm 0]]})]
        (reset! state (assoc original :prepared (-> prepared (assoc-in [:world :functions] functions)
                                                   (assoc-in [:session :functions] functions))))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"protected executable" (resident/fork context))))
      (finally (reset! state original) (resident/close! context)))
    ;; A cached proof does not keep a consumed wrapper open.
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"closed" (resident/fork context)))))
