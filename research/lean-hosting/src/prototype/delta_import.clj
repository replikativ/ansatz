(ns prototype.delta-import
  "Explicit strict-base delta completion of an actual guest finalizer IO.Result.
   A live checked-base capability and current independent helper authority are
   required. No artifact certificate, finalizer replay, or whole-base checking."
  (:require [prototype.machine :as m]
            [prototype.checked-delta :as delta]
            [prototype.module-import :as import]
            [prototype.imported-kernel :as kernel]
            [prototype.kernel-artifact :as artifact]
            [prototype.kernel-projection-snapshot :as snapshot]
            [prototype.helper-authority :as authority]))

(defn- fail [message data] (throw (ex-info message data)))
(defn- array-values [world value]
  (let [node (when (m/ref? value) (m/node world value))]
    (when-not (and (= :array (:kind node)) (vector? (:fields node)))
      (fail "Expected final checked ConstantInfo array" {}))
    (:fields node)))

(defn- finish-finalization*
  "Consume actual owned finalizer IO.Result, check only additions to CAPABILITY,
   then associate the exact final guest map with the strict-compatible result.
   CONTEXT is the current independently authorized checked-delta helper context;
   its :invoke borrows Environment and returns owned helper results. OPTIONS has
   the same :helpers/:kernel-policy/:finalizer-attestation as module-import.
   :io-error returns the original World/result without invoking any helper.
   Success owns :environment. Failure retains the latest child checkpoint and
   session, outstanding helper owners, and this layer's constants-array owner.
   :finalizer-result and :finalization-entry are alternative diagnostic snapshots,
   never permission to replay finalizer effects. :finalization-owners pairs this
   layer's still-owned Environment/constants with the actual latest checkpoint.
   This API accepts only a previously strictly checked live base."
  [basis context world result capability options]
   (let [targets (merge import/helpers (:helpers options))
         roots (cond-> (mapv targets [:root :constants :quot-init?])
                 (:constant-map targets) (conj (:constant-map targets))
                 (:finalizer-attestation options) (conj (get-in options [:finalizer-attestation :header-helper])))
         helper-code (volatile! nil)
         snapshot {:checkpoint world :io-result result}
         node (when (m/ref? result) (m/node world result))]
     (when-not (and (= :ctor (:kind node)) (contains? #{0 1} (:tag node))
                    (= 1 (count (:fields node))))
       (fail "Malformed guest import IO.Result"
             {:checkpoint world :io-result result :finalizer-result snapshot}))
     (if (= 1 (:tag node))
       {:status :io-error :world world :io-result result}
       (let [environment (first (:fields node))]
         (when-not (m/ref? environment)
           (fail "Guest import did not return an Environment reference"
                 {:checkpoint world :io-result result :finalizer-result snapshot}))
         (try
           (vreset! helper-code (authority/capture context world roots))
           (catch Throwable cause
             (throw (ex-info "Final guest helpers lack current independent authority"
                             (merge (ex-data cause)
                                    {:checkpoint world :io-result result :finalizer-result snapshot
                                     :phase :kernel-association :stage :helper-authority}) cause))))
         (let [entry (-> world (m/retain environment 1) (m/release result 1) (assoc :result 0))
               checkpoint (volatile! entry)
               constants-owner (volatile! nil)
               stage (volatile! :final-constants)]
           (try
             (let [[world constants] ((:invoke context) @checkpoint (:constants targets) [environment])
                   _ (vreset! checkpoint world)
                   _ (vreset! constants-owner constants)
                   values (array-values world constants)
                   _ (vreset! stage :delta-check)
                   certificate ((if (= :trusted-artifact basis)
                                  delta/verify-artifact-extension delta/verify-extension)
                                context world values capability (:kernel-policy options))
                   world (:world certificate)
                   _ (vreset! checkpoint world)
                   _ (vreset! stage :final-constants-release)
                   world (m/release world constants 1)
                   _ (vreset! checkpoint world)
                   _ (vreset! constants-owner nil)
                   _ (vreset! stage :finalizer-attestation)
                   [world certificate] (import/project-finalizer-flag-progress
                                        world environment (:invoke context) targets certificate
                                        (:finalizer-attestation options))
                   _ (vreset! checkpoint world)
                   _ (vreset! stage :final-association)
                   world (if (= :trusted-artifact basis)
                           (kernel/associate-projection-progress
                            context world environment targets certificate
                            (fn [world]
                              (let [admission (get-in certificate [:kernel-provenance :artifact-admission])
                                    admitted (artifact/inspect-for-world world admission)]
                                (when-not (= (:kernel-provenance admitted) (:kernel-provenance certificate))
                                  (fail "Artifact extension provenance differs from issued base" {}))
                                (authority/check context world roots @helper-code)
                                (snapshot/validate-segments (:env certificate) (:java-guard-segments certificate)))))
                           (kernel/associate-checked-progress context world environment targets certificate))]
               {:status :ok :world (assoc world :result 0) :environment environment
                :kernel-provenance (:kernel-provenance certificate) :new-order (:new-order certificate)
                (if (= :trusted-artifact basis) :checked-result :certificate) (dissoc certificate :world)})
             (catch Throwable cause
               (let [data (ex-data cause)
                     latest (or (:checkpoint data) @checkpoint)
                     owned (cond-> {:checkpoint latest :environment environment}
                             @constants-owner (assoc :constants @constants-owner))
                     child-owners (vec (concat (:temporary-owners data)
                                               (:association-temporary-owners data)
                                               (:finalizer-temporary-owners data)))]
                 (throw (ex-info "Guest import delta kernel association failed"
                                 (cond-> (merge {:phase :kernel-association :stage @stage} data
                                                {:checkpoint latest :finalizer-result snapshot
                                                 :finalization-entry {:checkpoint entry :environment environment}
                                                 :finalization-owners owned
                                                 :temporary-owners (cond-> (vec child-owners)
                                                                     @constants-owner (conj @constants-owner))})
                                   (nil? (:checkpoint data)) (assoc :environment environment)
                                   (:checkpoint-session data) (assoc :session (:checkpoint-session data)))
                                 cause))))))))))

(defn finish-finalization
  "Consume actual finalizer IO.Result and check only additions to a strictly
   checked live base. Returns :certificate; artifact capabilities are rejected.
   Latest-world/owner/session packets and IO-error ownership are preserved."
  ([context world result capability] (finish-finalization context world result capability {}))
  ([context world result capability options]
   (finish-finalization* :strict-fresh context world result capability options)))

(defn finish-artifact-finalization
  "Explicit artifact-relative counterpart consuming the actual finalizer IO once.
   Returns :checked-result, original :kernel-provenance and checked :new-order;
   no strict certificate or base order is invented. Final guest association is
   exact and all prior/new Java guard segments are revalidated across helpers."
  ([context world result capability] (finish-artifact-finalization context world result capability {}))
  ([context world result capability options]
   (finish-finalization* :trusted-artifact context world result capability options)))
