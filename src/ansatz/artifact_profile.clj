(ns ansatz.artifact-profile
  "Immutable descriptive base/role provenance. These records grant no checking
   authority, runtime capability, matching-version shortcut or proof-validity bit.
   Unknown legacy evidence stays unknown. Supplement execution and session
   activation must validate actual declarations/companions independently.")
(def schema "ansatz-env-artifact-profile/1")
(def extension-key :artifact-profile)
(def ^:private kernel-roles #{:init :lex :sizeof})
(def ^:private companion-roles [:attrs :matchers :instances])
(defn- fail [message] (throw (ex-info message {})))

(defn bundled
  "Describe the actual verified manifest snapshot selected for bundle loading.
   Kernel admission records the caller's replay mode, independently of provenance."
  ([manifest] (bundled manifest false))
  ([manifest checked?]
   (when-not (and (map? manifest) (string? (:artifact/cohort manifest))
                  (vector? (:resources manifest))) (fail "Invalid bundle profile input"))
   {:schema schema
    :base {:kind :bundle :cohort (:artifact/cohort manifest) :producer (:producer manifest)
           :generation-status (:bundle/co-generation manifest) :kernel-admission (if checked? :checked-export :trust)}
    :roles (into {} (map (fn [row]
                           [(:role row) (select-keys row [:resource :sha256 :producer :provenance/status])]))
                 (:resources manifest))
    :supplements []}))

(defn prepared-store
  "Describe a readable prepared-store manifest without opening the DB. Import
   completion, readable format and kernel verification remain distinct. Older
   absent derived provenance is never inferred from library/toolchain strings."
  [manifest]
  (when-not (and (map? manifest) (contains? #{1 2} (:store/format manifest))
                 (string? (:branch manifest))) (fail "Invalid prepared store profile input"))
  {:schema schema
   :base {:kind :prepared-store :branch (:branch manifest) :store-format (:store/format manifest)
          :cohort (:artifact/cohort manifest) :provenance (:provenance manifest)
          :capabilities (:store/capabilities manifest) :kernel-admission :prepared-trust}
   :roles (into {} (map (fn [role]
                          [role (or (get-in manifest [:derived-provenance role])
                                    {:source :persisted-derived :provenance/status :unrecorded})]))
                companion-roles)
   :supplements []})

(defn external-export
  "Describe observed CI producer metadata and the actual explicit replay mode.
   Companion sources are descriptive caller/loader evidence, never assumed to
   share a producer with the CI header. No companion producer is synthesized."
  [producer checked? companion-sources]
  {:schema schema
   :base {:kind :external-export :producer producer
          :kernel-admission (if checked? :checked-export :trust)}
   :roles companion-sources :supplements []})

(defn supplemental-requirements
  "Keep a known bundle base/previous supplement on its captured cohort. Unknown
   or store/external bases have no implicit matching cohort: their compatibility
   MUST be established by exact overlap, strict missing admission and role
   evidence, not an empty requirement map or matching version string alone."
  [profile]
  (when (and profile (not= schema (:schema profile))) (fail "Unknown Env artifact profile"))
  (let [cohort (or (some-> profile :supplements peek :cohort)
                   (when (= :bundle (get-in profile [:base :kind]))
                     (get-in profile [:base :cohort])))]
    (if cohort {:artifact/cohort cohort} {})))

(defn plan-supplement
  "Descriptive role plan only. It never marks a candidate accepted or skips full
   overlap/companion checks; generation history can remain explicitly unknown."
  [base manifest role]
  (when-not (contains? #{:lex :sizeof} role) (fail "Invalid supplemental kernel role"))
  (let [requirements (supplemental-requirements base)
        cohort (:artifact/cohort manifest)
        selected (first (filter #(= role (:role %)) (:resources manifest)))]
    (when-not (and (string? cohort) selected) (fail "Supplement manifest lacks selected role"))
    (when-let [expected (:artifact/cohort requirements)]
      (when-not (= expected cohort) (fail "Supplement cohort differs from retained base profile")))
    {:kernel-role role :cohort cohort :requirements requirements
     :resource (select-keys selected [:resource :sha256 :producer :provenance/status])
     :required-checks [:exact-full-ci-overlap :complete-packages :strict-missing-admission
                       :selected-role-metadata-closure :prepared-session-activation]
     :companion-producers (into {} (map (fn [r]
                                          [(:role r) (select-keys r [:producer :provenance/status])]))
                                (filter #(contains? (set companion-roles) (:role %)) (:resources manifest)))}))
