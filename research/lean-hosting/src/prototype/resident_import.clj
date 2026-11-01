(ns prototype.resident-import
  "Optional public resident preparation for ONE published standalone source import.
   No B compilation, generic resolver, native Init prefix or cached projection
   certificate. Inputs/resources remain borrowed; output owns a new branch."
  (:require [prototype.resident-frontend :as resident]
            [prototype.frontend :as frontend]
            [prototype.source-import :as source]
            [prototype.module-import :as imports]
            [prototype.guest-encoding :as encoding]
            [prototype.eval-const :as eval]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]
            [ansatz.kernel.name :as name]
            [clojure.string :as str])
  (:import [ansatz.kernel Name]))

(defn- fail [message data] (throw (ex-info message data)))
(def import-roots
  "Fixed parser/encoding/assembly/finalizer/checking helpers. They and their static
   closures must already match the independent preparation registry."
  (into [frontend/header-target encoding/names-helper]
        (concat (map source/helpers [:assemble :finalize :header])
                (map imports/helpers [:root :constants :constant-map :quot-init?]))))

(defn- policy! [policy]
  (when-not (and (map? policy)
                 (every? #{:allow-axioms? :allow-unsafe? :allow-compiler-markers? :fuel} (keys policy)))
    (fail "Resident import requires explicit allowlisted kernel policy; projection certificates are not accepted" {}))
  (doseq [key [:allow-axioms? :allow-unsafe? :allow-compiler-markers?]
          :when (contains? policy key)]
    (when-not (boolean? (get policy key)) (fail "Resident import policy flags must be Boolean" {:key key})))
  (when (and (contains? policy :fuel)
             (not (and (integer? (:fuel policy)) (<= 1 (:fuel policy) Long/MAX_VALUE))))
    (fail "Invalid imported checker fuel" {}))
  policy)

(defn import-readiness!
  "Host-only closure/binding checks; does not mint a checked Environment."
  [prepared configuration]
  (resident/adoption-readiness! prepared configuration)
  (eval/validate-executables! (:world prepared) (:trusted-functions configuration) import-roots))

(defn- capture-request [request]
  (when-not (and (map? request)
                 (every? #{:path :text :file-name :module-name :roots :initialization} (keys request))
                 (not= (contains? request :path) (contains? request :text))
                 (instance? Name (:module-name request))
                 (vector? (:roots request)) (every? #(instance? Name %) (:roots request))
                 (= :defer (:initialization request)))
    (fail "Resident import requires an explicit deferred source request with exactly one text or path and no calls" {}))
  (let [path (:path request) filename (or (:file-name request) path)]
    (when-not (and (string? filename) (seq filename)
                   (if (contains? request :path) (and (string? path) (seq path)) (string? (:text request))))
      (fail "Resident import requires source text/path and file name" {}))
    ;; No later stage reopens PATH. Returned request is directly usable by load-source.
    (-> request (dissoc :path) (assoc :text (if (contains? request :path) (slurp path :encoding "UTF-8") (:text request))
                                    :file-name filename))))

(defn prepare-source-import
  "Prepare one actual header-requested published standalone module in a NEW branch.
   OPTIONS is exactly {:profile :standalone :configuration independent-resident
                       :kernel-policy explicit-map}. Policy permits only explicit
   Boolean assumption/marker flags and positive checker :fuel; every CI is freshly
   strictly checked. REQUEST uses resident source shape, :initialization :defer,
   and no calls; source is captured once and returned for later load-source.

   Return {:context :request captured-request :header actual-parsed-header
           :import-receipt {:module :unit-digest :constant-count}}. Descriptor is
   descriptive, not checking authority. Registry owns import region anchors.
   The input context remains unchanged/open; no Store/lease is acquired or closed.
   Failures retain exact named packets/owners as terminal diagnostic evidence,
   never authorize retrying effects, guessing cleanup, or splicing checkpoints."
  [context request {:keys [profile configuration kernel-policy] :as options}]
  (locking context
    (let [entry (resident/snapshot context)
          active (atom (:session entry)) progress (volatile! (:world entry))
          phase (volatile! :entry) captured (volatile! nil) header (volatile! nil)
          assembly (volatile! nil) finished (volatile! nil) last-call (volatile! nil)
          owners (volatile! {:input-environment :borrowed :input-options :borrowed})
          invoke (fn [world target args]
                   (vreset! progress world)
                   (let [called (raw/call @active world target args)]
                     (vreset! last-call {:target target :arguments args :returned called})
                     (reset! active (:session called)) (vreset! progress (:state called))
                     [(:state called) (:value called)]))]
      (try
        (when-not (and (map? options) (= :standalone profile) (map? configuration)
                       (contains? options :kernel-policy)
                       (every? #{:profile :configuration :kernel-policy} (keys options)))
          (fail "Resident source import supports only the explicit standalone profile" {}))
        (policy! kernel-policy)
        (import-readiness! entry configuration)
        (vreset! phase :capture-source)
        (vreset! captured (capture-request request))
        (vreset! phase :header-started)
        (let [parsed (frontend/inspect-file-header @active @progress (:text @captured) (:file-name @captured))]
          (vreset! header parsed) (reset! active (:session parsed)) (vreset! progress (:world parsed))
          (let [actual (:header parsed) requests (:requestedImports actual)
                module (:module (first requests))
                expected [{:module module :importAll false :isExported true :isMeta false}]]
            (when-not (and (false? (:hasErrors actual)) (false? (:moduleSystem actual))
                           (= expected requests))
              (fail "Resident import requires a classic header with exactly one ordinary exported source import" {}))
            (let [module-name (reduce name/mk-str (name/anonymous)
                                      (str/split (imports/module-string module) #"\."))
                  _ (vreset! phase :encode-module-started)
                  [world encoded] (encoding/encode-name @progress invoke module-name)]
              (vreset! progress world)
              (vswap! owners assoc :module-name encoded :module-name-state :owned)
              (vreset! phase :assemble-started)
              ;; Public assemble checks actual registry unit and executable identities.
              (let [assembled (source/assemble world invoke module encoded)]
                (vreset! assembly assembled) (vreset! progress (:world assembled))
                (vswap! owners assoc :assembly-state (:state assembled) :assembly-imports (:imports assembled)
                                    :assembly-owner-state :owned-at-assembly-checkpoint)
                (vreset! phase :finalize-started)
                (let [result (source/finalize assembled invoke (:options entry) {:kernel-policy kernel-policy})]
                  (vreset! finished result) (vreset! progress (:world result))
                  (when-not (= :ok (:status result))
                    (fail "Resident source import finalizer failed" {:checkpoint (:world result) :io-result (:io-result result)}))
                  (vswap! owners assoc :final-environment (:environment result) :final-environment-state :owned
                                      :assembly-owner-state :consumed-by-successful-finalizer)
                  (let [receipt (:source-import-receipt result)]
                    (when-not (and receipt (identical? (:checked-env receipt) (get-in result [:certificate :env])))
                      (fail "Resident source import has no exact fresh checked receipt" {}))
                    (vreset! phase :adopt-started)
                    (vreset! progress (m/release @progress encoded 1))
                    (vswap! owners assoc :module-name-state :released)
                    (vreset! progress (m/release @progress (:environment entry) 1))
                    (vswap! owners assoc :prior-environment-in-new-branch :released)
                    (let [prepared {:world @progress :session @active :environment (:environment result)
                                    :options (:options entry) :catalogue (:catalogue entry)}
                          next-context (resident/adopt-prepared prepared configuration)]
                      {:context next-context :request @captured :header actual
                       :import-receipt {:module module :unit-digest (:unit-digest receipt)
                                        :constant-count (count (:constants receipt))}})))))))
        (catch Throwable cause
          (throw (ex-info (or (.getMessage cause) "Resident source import preparation failed")
                          (merge {:checkpoint @progress :checkpoint-session @active}
                                 (ex-data cause)
                                 {:resident-import-input context :resident-import-entry entry
                                  :resident-import-request @captured :resident-import-header @header
                                  :resident-import-assembly @assembly :resident-import-finalization @finished
                                  :resident-import-last-call @last-call :resident-import-ownership @owners
                                  :resident-import-phase @phase :resident-import-terminal? true
                                  :resident-operation :prepare-source-import}) cause)))))))
