(ns prototype.coherent-stage-guards
  "Small state/protocol checks, not kernel/capability authority. Production callers
   compute facts from actual issued operations; model facts in tests prove only
   these fail-closed transitions, never execution or a checked Environment.")

(def expected-axioms
  #{"Classical.choice" "Lean.ofReduceBool" "Lean.ofReduceNat" "Lean.trustCompiler"
    "Quot.lcInv" "Quot.sound" "isScalarObj" "lcAny" "lcCast" "lcErased" "lcProof"
    "lcUnreachable" "lcVoid" "propext" "sorryAx"})
(defn check! [ok message] (when-not ok (throw (ex-info message {}))))
(defn preparation-phase!
  "Classify the ACTUAL source-controller escrow. Failure/nonrunnable cannot be
   promoted to prepared. A pending exact helper value is its own required stage."
  [summary escrow target]
  (check! (= (:phase summary) (:phase escrow)) "Preparation summary/escrow phase mismatch")
  (case (:phase escrow)
    :failed (throw (or (:failure escrow) (ex-info "Source preparation failed without cause" {})))
    :prepared (do (check! (and (true? (get-in escrow [:prepared :runnable?]))
                              (empty? (get-in escrow [:prepared :missing-helper-values])))
                         "Prepared packet is not runnable") :prepared)
    :prepared-missing-helper-values
    (do (check! (and (false? (get-in escrow [:prepared :runnable?]))
                    (= [target] (get-in escrow [:prepared :missing-helper-values]))
                    (= [target] (get-in escrow [:evidence :missing-helper-values])))
               "Unsupported missing helper values") :helper-value-required)
    (throw (ex-info "Source preparation did not complete" {:phase (:phase escrow)}))))

(defn init-facts!
  [facts]
  (check! (and (= :ok (:status facts)) (= 65994 (:constants facts) (:projected facts))
               (= expected-axioms (:axioms facts)) (= 1 (:association-count facts) (:projection-source-count facts))
               (every? true? (map facts [:owned-environment? :java-env? :same-association-env?
                                        :single-open-source? :same-projection-source? :matching-functions? :inactive-init?])))
          "Fresh strict Init did not meet the exact checked/live-source acceptance gate")
  facts)

(defn helper-value-facts! [facts]
  (check! (and (= :initialized (:phase facts)) (true? (:runnable? facts))
               (= 1 (:guest-invocation-count facts) (:result-release-count facts))
               (= 5 (:guest-steps-delta facts)) (= :released (:result-owner-state facts))
               (false? (:host-value-seeded facts)) (false? (:native-initializers-replayed facts)))
          "Reviewed emitted helper value did not complete its exact one-call/five-step/one-release stage")
  facts)

(defn stage-prefix! [stages typed?]
  (let [prefix (cond-> [:fresh-init :graph-helpers :panic :ordinary-helpers]
                 typed? (conj :typed-eio))
        prefix (into prefix [:cases-on :seal :helper-value :project])]
    (check! (and (vector? stages) (<= (count prefix) (count stages))
                 (= prefix (subvec stages 0 (count prefix)))) "Missing/misordered required coherent preparation stages")
    prefix))

(def jvm-stages
  [:fresh-init :graph-helpers :panic :ordinary-helpers :typed-eio :cases-on :seal :helper-value
   :init-prefix :load-a :select-a :call-a :callback :load-b :select-b :call-b-a :dispose])
(defn jvm-stage-prefix! [stages typed?]
  (check! (and (true? typed?) (= jvm-stages stages)) "Exact finite JVM application stage program required")
  (subvec stages 0 9))
(defn profile-stage-prefix! [profile stages typed?]
  (case profile
    "ansatz-producer50f-coherent-frontend-consumer/1" (stage-prefix! stages typed?)
    "ansatz-producer50f-coherent-jvm-application-consumer/1" (jvm-stage-prefix! stages typed?)
    (throw (ex-info "Unknown coherent composition profile" {}))))

(defn helper-roles! [helpers expected]
  (doseq [[id entries] expected]
    (let [rows (filter #(= id (:id %)) helpers)]
      (check! (and (= 1 (count rows)) (= (sort entries) (sort (:entrypoints (first rows)))))
              "Missing/misdeclared required helper role before restore")))
  true)

(defn constructor-result! [result expected-contract expected-implementation expected-execution]
  (check! (and (map? result)
               (= #{:status :consumer-contract-sha256 :consumer-implementation-sha256 :compatibility-profile
                    :native-resources-acquired :guest-executed :strictly-checked? :backend :fuel :compile-threshold} (set (keys result)))
               (= expected-execution (select-keys result [:backend :fuel :compile-threshold]))
               (= :constructed (:status result)) (= expected-contract (:consumer-contract-sha256 result))
               (= expected-implementation (:consumer-implementation-sha256 result))
               (= "ansatz-producer50f-coherent-frontend-consumer/1" (:compatibility-profile result))
               (false? (:native-resources-acquired result)) (false? (:guest-executed result))
               (false? (:strictly-checked? result))) "Constructor smoke result is not exact bounded construction evidence")
  result)
