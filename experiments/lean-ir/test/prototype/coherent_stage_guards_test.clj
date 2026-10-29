(ns prototype.coherent-stage-guards-test
  "Bounded protocol models only: no actual kernel, Source, Factory, restore or
   loaded-cohort evidence follows from these tests. Source-only until sole lane."
  (:require [clojure.test :refer [deftest is]] [prototype.coherent-stage-guards :as g]))

(def execution {:backend :mutable :fuel 500000000 :compile-threshold 1})
(def target ["reviewed-pure-value"])
(def facts
  {:status :ok :constants 65994 :projected 65994 :axioms g/expected-axioms
   :association-count 1 :projection-source-count 1 :owned-environment? true :java-env? true
   :same-association-env? true :single-open-source? true :same-projection-source? true
   :matching-functions? true :inactive-init? true})
(def stages [:fresh-init :graph-helpers :panic :ordinary-helpers :typed-eio :cases-on :seal :helper-value :project
             :typed-io :ordinary-module :chain :diamond :reload])

(deftest caught-preparation-failure-keeps-original-terminal-cause
  (let [cause (ex-info "original terminal cause" {:owner :canonical})]
    (is (identical? cause (try (g/preparation-phase! {:phase :failed} {:phase :failed :failure cause} target)
                              (catch Throwable actual actual))))))
(deftest missing-known-helper-is-a-required-stage-never-prepared
  (is (= :helper-value-required
         (g/preparation-phase! {:phase :prepared-missing-helper-values}
           {:phase :prepared-missing-helper-values :prepared {:runnable? false :missing-helper-values [target]}
            :evidence {:missing-helper-values [target]}} target))))
(deftest nonrunnable-or-mismatched-summary-never-advances
  (doseq [[summary escrow] [[{:phase :prepared} {:phase :prepared :prepared {:runnable? false}}]
                            [{:phase :prepared} {:phase :failed}]
                            [{:phase :preparing} {:phase :preparing}]]]
    (is (thrown? clojure.lang.ExceptionInfo (g/preparation-phase! summary escrow target)))))
(deftest fresh-init-requires-both-counts-and-the-exact-axiom-set
  (is (= facts (g/init-facts! facts)))
  (doseq [bad [(assoc facts :projected 65993) (assoc facts :constants 65995)
               (update facts :axioms disj "propext") (update facts :axioms conj "injectedAxiom")]]
    (is (thrown? clojure.lang.ExceptionInfo (g/init-facts! bad)))))

(deftest artifact-init-observations-keep-the-admission-basis-explicit
  (let [admitted (assoc facts :base-basis :trusted-artifact :artifact-admission? true)]
    (is (identical? admitted (g/admitted-init-facts! admitted)))
    (doseq [bad [(dissoc admitted :base-basis) (assoc admitted :base-basis :strict-fresh)
                 (assoc admitted :artifact-admission? false) (assoc admitted :constants 17)
                 (assoc admitted :single-open-source? false)]]
      (is (thrown? clojure.lang.ExceptionInfo (g/admitted-init-facts! bad))))))
(deftest live-source-and-checked-association-origin-cannot-be-substituted
  (doseq [bad [(assoc facts :same-projection-source? false) (assoc facts :single-open-source? false)
               (assoc facts :same-association-env? false) (assoc facts :association-count 2)
               (assoc facts :owned-environment? false) (assoc facts :matching-functions? false)
               (assoc facts :inactive-init? false)]]
    (is (thrown? clojure.lang.ExceptionInfo (g/init-facts! bad)))))
(deftest actual-emitted-helper-value-stage-has-exact-work-and-owner-disposition
  (let [good {:phase :initialized :runnable? true :guest-invocation-count 1 :result-release-count 1
              :guest-steps-delta 5 :result-owner-state :released :host-value-seeded false :native-initializers-replayed false}]
    (is (= good (g/helper-value-facts! good)))
    (doseq [bad [(assoc good :phase :failed) (assoc good :guest-steps-delta 0)
                 (assoc good :guest-invocation-count 2) (assoc good :result-release-count 0)
                 (assoc good :host-value-seeded true) (assoc good :native-initializers-replayed true)]]
      (is (thrown? clojure.lang.ExceptionInfo (g/helper-value-facts! bad))))))
(deftest missing-helper-stage-and-role-fail-before-restore
  (is (seq (g/stage-prefix! stages true)))
  (is (thrown? clojure.lang.ExceptionInfo (g/stage-prefix! (vec (remove #{:helper-value} stages)) true)))
  (is (thrown? clojure.lang.ExceptionInfo (g/stage-prefix! (vec (remove #{:graph-helpers} stages)) true)))
  (is (true? (g/helper-roles! [{:id "cases-on" :entrypoints ["KernelCasesOnRaw.construct"]}]
                              {"cases-on" ["KernelCasesOnRaw.construct"]})))
  (doseq [helpers [[] [{:id "cases-on" :entrypoints ["wrong.construct"]}]]]
    (is (thrown? clojure.lang.ExceptionInfo (g/helper-roles! helpers {"cases-on" ["KernelCasesOnRaw.construct"]})))))
(deftest constructor-smoke-rejects-unbounded-or-wrong-status-and-resource-claims
  (let [good (merge execution {:status :constructed :consumer-contract-sha256 "contract" :consumer-implementation-sha256 "implementation"
              :compatibility-profile "ansatz-producer50f-coherent-frontend-consumer/1"
              :native-resources-acquired false :guest-executed false :strictly-checked? false})]
    (is (= good (g/constructor-result! good "contract" "implementation" execution)))
    (doseq [bad [(assoc good :status :prepared) (assoc good :world {})
                 (assoc good :native-resources-acquired true) (assoc good :consumer-contract-sha256 "another")]]
      (is (thrown? clojure.lang.ExceptionInfo (g/constructor-result! bad "contract" "implementation" execution))))))
