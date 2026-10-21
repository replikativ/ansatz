(ns prototype.resident-source
  "Optional, explicit resident source publication. This consumer uses only public
   resident APIs. Inputs and artifact leases stay borrowed; failures are terminal
   operation checkpoints, not retry/resumption capabilities."
  (:require [prototype.resident-frontend :as resident]
            [prototype.hosted-file :as hosted]
            [prototype.source-import :as source]
            [prototype.source-module :as export]
            [prototype.guest-encoding :as encoding]
            [prototype.eval-const :as eval]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]
            [prototype.module-import :as imports]))

(defn- fail [message data] (throw (ex-info message data)))
(def publication-roots
  "Fixed guest publication/Name-encoding roots. Caller independently authenticates
   these and their transitive closures; this namespace never loads or relinks code."
  (into [export/export-helper encoding/names-helper]
        (concat (vals export/ir-export-targets)
                (map imports/helpers [:root :constant-map :quot-init?]))))

(defn publication-readiness!
  "Host-only validation against an EXPLICIT independent resident configuration.
   Checks the whole binding registry and selected compiler/export/alias closures.
   Does not create a checked association or acquire guest/resource owners."
  [prepared configuration]
  (resident/adoption-readiness! prepared configuration)
  (eval/validate-executables! (:world prepared) (:trusted-functions configuration)
                              publication-roots))

(defn load-and-publish
  "Compile exactly once in a NEW persistent branch, then publish its actual packet.
   REQUEST must explicitly select :initialization :defer; both publication profiles
   require zero source initializer actions. Example:
     (load-and-publish context (assoc request :initialization :defer)
                       {:profile :standalone :configuration independent})
   PUBLICATION requires {:profile :standalone|:over-init :configuration independent}.
   On success returns a context, ordinary resident FileHandle and borrowed scalar
   publication descriptor. Failed compilation never publishes. Adoption still
   requires a live checked association, including for a diagnostic Environment;
   if absent the exact completed packet is preserved in terminal failure evidence.
   Publication adds registry owners; closing contexts does not unregister them or
   close borrowed Stores/catalogues/leases. Original input context stays open and
   unchanged. Publication is not an import loader; assembly/finalization are separate."
  [context request {:keys [profile configuration] :as publication}]
  (locking context
    (let [entry (resident/snapshot context)
          active (atom (:session entry)) progress (volatile! (:world entry))
          phase (volatile! :entry) completed (volatile! nil) registered (volatile! nil)
          last-call (volatile! nil)
          owners (volatile! {:input-environment :borrowed :input-options :borrowed})
          invoke (fn [world target args]
                   (vreset! progress world)
                   (let [result (raw/call @active world target args)]
                     (vreset! last-call {:target target :arguments args :returned result})
                     (reset! active (:session result)) (vreset! progress (:state result))
                     [(:state result) (:value result)]))]
      (try
        (when-not (and (map? publication) (contains? #{:standalone :over-init} profile)
                       (map? configuration))
          (fail "Resident publication requires explicit profile and independent configuration" {}))
        (when-not (= :defer (:initialization request))
          (fail "Resident source publication requires deferred initialization" {}))
        (when (contains? request :calls)
          (fail "Use resident calls separately from source publication" {}))
        (publication-readiness! entry configuration)
        (vreset! phase :compile-started)
        (let [compiled (hosted/run-file entry request (:frontend-configuration configuration))]
          ;; Keep the real envelope/world before any postcondition or export.
          (vreset! completed compiled)
          (reset! active (:session compiled)) (vreset! progress (:world compiled))
          (vswap! owners assoc :compiled-environment (:environment compiled)
                              :compiled-environment-state :owned)
          (vreset! phase :compiled)
          (publication-readiness! (merge entry (select-keys compiled [:world :session :environment])) configuration)
          (when (:success compiled)
            (vreset! phase :encode-module-started)
            (let [[world name] (encoding/encode-name @progress invoke (:module-name request))]
              (vreset! progress world)
              (vswap! owners assoc :module-name name :module-name-state :owned)
              (vreset! phase :register-started)
              (let [result ((case profile :standalone source/register-compiled
                                           :over-init source/register-compiled-over-init)
                            world invoke compiled name)]
                (vreset! registered result) (vreset! progress (:world result))
                (vswap! owners assoc :registry-environment (:environment (:entry result))
                                    :registry-module-data (:data (:entry result))
                                    :registry-state :owned-by-world)
                (vreset! progress (m/release @progress name 1))
                (vswap! owners assoc :module-name-state :released))))
          (vreset! phase :adopt-started)
          ;; Only this NEW branch drops the former context's Environment owner.
          (vreset! progress (m/release @progress (:environment entry) 1))
          (vswap! owners assoc :prior-environment-in-new-branch :released)
          (let [prepared (merge entry (select-keys compiled [:environment])
                                {:world @progress :session @active})
                digest (get-in compiled [:handle :unit-digest])
                unit (get-in prepared [:world :eval-const-authorizations :units digest])
                _ (when (and (:success compiled) (not unit))
                    (fail "Successful resident publication has no admitted unit" {}))
                next-context (resident/adopt-prepared prepared configuration)]
            {:context next-context :success (:success compiled) :diagnostics (:diagnostics compiled)
             :file (when (:success compiled)
                     (resident/->FileHandle digest unit (:module-name request)))
             :publication (when-let [published (:entry @registered)]
                            (select-keys published [:module :unit-digest :profile]))}))
        (catch Throwable cause
          (throw (ex-info (or (.getMessage cause) "Resident source publication failed")
                          (merge {:checkpoint @progress :checkpoint-session @active}
                                 (ex-data cause)
                                 {:resident-source-input context :resident-source-entry entry
                                  :resident-source-compiled @completed
                                  :resident-source-registration @registered
                                  :resident-source-last-call @last-call
                                  :resident-source-ownership @owners
                                  :resident-source-phase @phase
                                  :resident-source-terminal? true
                                  :resident-operation :load-and-publish}) cause)))))))
