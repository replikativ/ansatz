(ns prototype.resident-preparation
  "Explicit adapter from an actually checked guest Environment to a resident
   Context. Bootstrap, imports, code preparation and native leases stay external."
  (:require [prototype.resident-frontend :as resident]
            [prototype.kernel-host :as kernel]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]))

(def options-empty
  ["str" ["str" ["str" ["anonymous"] "Lean"] "Options"] "empty"])

(defn- open*
  "Adopt the owned ENVIRONMENT in candidate {:world :session :environment}.
   CONFIGURATION supplies an independent :catalogue, :trusted-functions and
   :trusted-bindings, plus resident :kernel-helpers/:frontend-configuration and
   optional application extern admission. Certificates and phase flags are not
   authority: selected frontend/guest Name-encoder closures and the actual live
   checked association are verified BEFORE retaining initialized Options.empty.

   On success one Options owner is acquired and Environment/Options transfer into
   the returned Context in that immutable branch. Failure never guesses cleanup:
   exact named entry/associated/options-owned packets and latest helper session
   are preserved in ex-data. No imports, initializer, markers or code linking run;
   the native ResourceLease remains caller-owned and must outlive every borrower."
  [basis {:keys [world session environment]} configuration admission]
  (let [entry {:world world :session session :environment environment :catalogue (:catalogue configuration)}
        active (atom session) progress (volatile! world)
        associated-entry (volatile! nil) options-entry (volatile! nil)
        invoke (fn [world target args]
                 (vreset! progress world)
                 (let [result (raw/call @active world target args)]
                   (reset! active (:session result)) (vreset! progress (:state result))
                   [(:state result) (:value result)]))]
    (try
      (let [{:keys [kernel-helpers]} (resident/adoption-readiness! entry configuration)
            [world checked] (if (= :trusted-artifact basis)
                              (resident/resolve-admitted-association {:invoke invoke} world environment kernel-helpers admission)
                              (kernel/inherit-checked-association {:invoke invoke} world environment kernel-helpers))
            _ (vreset! progress world)
            _ (when-not checked (throw (ex-info "Resident Environment has no existing checked association" {})))
            associated (assoc entry :world world :session @active)
            _ (vreset! associated-entry associated)
            options (m/initialized-value world options-empty)
            _ (when-not (m/ref? options) (throw (ex-info "Initialized Options.empty is not a guest reference" {})))
            _ (m/node world options)
            world (m/retain world options 1)
            prepared (assoc associated :world world :options options)
            _ (vreset! progress world)
            _ (vreset! options-entry prepared)]
        ;; Adoption deliberately rechecks live association; no prechecked boolean
        ;; or caller-provided certificate bypasses its normal authority boundary.
        (if (= :trusted-artifact basis)
          (resident/adopt-admitted prepared (dissoc configuration :catalogue) admission)
          (resident/adopt-prepared prepared (dissoc configuration :catalogue))))
      (catch Throwable cause
        (let [data (ex-data cause)]
          (throw (ex-info (or (.getMessage cause) "Resident checked preparation failed")
                          (cond-> (merge {:checkpoint @progress :checkpoint-session @active}
                                         data
                                         {:resident-preparation-entry entry
                                          :resident-operation (if (= :trusted-artifact basis) :open-admitted :open-checked)})
                            @associated-entry (assoc :resident-preparation-associated-entry @associated-entry)
                            @options-entry (assoc :resident-preparation-options-entry @options-entry)) cause)))))))

(defn open-checked
  "Adopt an owned candidate Environment with initialized Options.empty. Requires
   the existing independent readiness checks and live STRICT association; options
   acquisition/checkpoint ownership follow the original preparation contract."
  [candidate configuration]
  (open* :strict-fresh candidate configuration nil))

(defn open-admitted
  "Explicit artifact counterpart. ACTUAL-ARTIFACT-TOKEN must be issued and match
   the current live descendant. Full readiness/Java auditing precedes Options
   acquisition and adoption rechecks the association. The Store remains borrowed;
   named entry/associated/options owner packets preserve failures without replay."
  [candidate configuration actual-artifact-token]
  (open* :trusted-artifact candidate configuration actual-artifact-token))
