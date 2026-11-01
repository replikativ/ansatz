(ns prototype.source-inductive-preparation
  "Explicit HOST-ONLY ordinary inductive code/profile preparation.
   Borrow candidate/configuration/Source/lease; acquire no guest owners. The
   caller supplies authenticated expected digests as trusted configuration, not
   provenance read from a candidate or an artifact's descriptive manifest.
   Run BEFORE sealing graph/evaluator profiles or opening a NEW Context."
  (:require [clojure.string :as str]
            [clojure.data.json :as json]
            [prototype.checkpoint-wire :as wire]
            [prototype.declaration-store :as declarations]
            [prototype.import-ir :as ir]
            [prototype.preparation :as preparation]
            [prototype.eval-const :as eval]
            [prototype.runtime-abi :as abi]
            [prototype.raw-interop :as raw]
            [prototype.kernel-host :as kernel]))

(def profile-id "ansatz-source-inductive-ordinary/1")
(def generated ["str" ["str" ["anonymous"] "KernelSourceInductivePublication"] "postCheckGeneratedFamily"])
(def encoder ["str" ["str" ["str" ["anonymous"] "KernelEncoding"] "decodeFamily"] "_boxed"])
(def ^:private symbol "lean_elab_add_decl")
(def ^:private ordinary-helpers {:generated generated :encode-family encoder})
(def ^:private object-types #{"object" "tobject"})
(defn- check! [p message] (when-not p (throw (ex-info message {}))))
(defn- row [catalogue name]
  (if-let [read! (:read-declaration catalogue)] (read! name) (get-in catalogue [:declarations name])))

(defn authenticated-index
  "Authenticate BOTH source and IR bytes before parsing. This does not establish
   compiler trust: expected digests/toolchain identity belong to the enclosing
   reviewed host profile. Never accept expected digests from the loaded bytes."
  [{:keys [source-bytes source-sha256 ir-bytes ir-sha256 max-bytes max-declarations]}]
  (check! (and (integer? max-bytes) (<= 1 max-bytes 67108864)
               (integer? max-declarations) (<= 1 max-declarations 1000000))
          "Explicit finite helper artifact limits required")
  (doseq [[bytes sha] [[source-bytes source-sha256] [ir-bytes ir-sha256]]]
    (check! (and (bytes? bytes) (<= (alength ^bytes bytes) max-bytes)
                 (wire/hash? sha) (= sha (wire/sha256 bytes)))
            "Source inductive artifact digest/bound mismatch"))
  (let [text (wire/utf8-string ir-bytes)
        lines (str/split-lines text)
        _ (check! (<= 2 (count lines) (inc max-declarations)) "Helper declaration bound exceeded")
        parsed (mapv #(json/read-str % :key-fn keyword) lines)
        _ (check! (and (= "manifest" (:kind (first parsed)))
                       (every? #(= "decl" (:kind %)) (rest parsed)))
                  "Helper artifact contains missing/non-declaration rows")
        index (ir/index-bundles [(java.io.StringReader. text)])
        _ (check! (and (= 1 (count (:manifests index)))
                       (= (dec (count parsed)) (count (:declarations index))))
                  "Duplicate helper names or invalid manifest inventory")
        manifest (first (:manifests index))
        plan (:initializationPlan manifest)]
    (ir/validate-manifest! manifest)
    (check! (and (= {:target "x86_64-unknown-linux-gnu" :wordBits 64} (:runtimeProfile manifest))
                 (or (not (contains? manifest :leanCommit))
                     (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (:leanCommit manifest))))
            "Helper toolchain/target mismatch")
    (check! (and (= "initialization-plan" (:kind plan)) (= "lean-init-plan/1" (:schema plan))
                 (false? (:moduleSystem plan)) (vector? (:module plan))
                 (vector? (:imports plan)) (= [] (:actions plan)))
            "Ordinary helper profile requires an explicit classic initializer-free plan")
    index))

(defn- validate-abi! [catalogue name borrows expected]
  (let [f (get-in (row catalogue name) [:ir :fdecl])]
    ;; Expected FULL ABI is independently pinned profile input after native IR
    ;; inspection; object/tobject are not silently identified.
    (check! (and (= expected {:params (mapv #(select-keys % [:ty :borrow]) (:xs f)) :return-type (:type f)})
                 f (= name (:f f)) (= (count borrows) (count (:xs f)))
                 (= borrows (mapv :borrow (:xs f)))
                 (every? object-types (map :ty (:xs f)))
                 (object-types (:type f)))
            "Source inductive helper arity/type/ownership mismatch")))

(defn- options [session]
  (cond-> (select-keys session [:backend :fuel :compile-threshold])
    (or (:cache session) (get-in session [:program :cache]))
    (assoc :cache (or (:cache session) (get-in session [:program :cache])))))

(def ^:private policy-keys
  #{:allow-axioms? :allow-compiler-markers? :allow-unsafe? :allow-nested? :checker-fuel})
(defn- effective-policy [policy]
  (check! (and (map? policy) (every? policy-keys (keys policy))) "Unsupported kernel policy fields")
  (let [policy (merge {:allow-axioms? false :allow-compiler-markers? false
                       :allow-unsafe? false :allow-nested? false :checker-fuel 1000000} policy)]
    (check! (and (every? boolean? (map policy [:allow-axioms? :allow-compiler-markers? :allow-unsafe? :allow-nested?]))
                 (integer? (:checker-fuel policy)) (<= 1 (:checker-fuel policy) Long/MAX_VALUE))
            "Malformed effective kernel policy")
    policy))
(defn- unsealed! [candidate configuration]
  ;; Existing callbacks close over their original catalogue/registry. Editing
  ;; adjacent maps cannot update them or validate a prefix issued from them.
  (doseq [packet [candidate configuration]
          key [:graph-profile :graph-install-options :prefix :context]]
    (check! (not (contains? packet key)) "Ordinary helpers must be linked before graph/profile/prefix sealing"))
  (doseq [packet [candidate configuration]]
    (check! (nil? (get-in packet [:frontend-configuration :install-options]))
            "Ordinary helpers cannot extend a sealed evaluator installation profile")))

(defn prepare-ordinary
  "Return {:candidate :configuration :profile} on a NEW immutable code branch.
   CANDIDATE includes independently retained original :support and the actual
   checked pre-user packet. CONFIGURATION is independently
   retained trusted preparation (catalogue/functions/bindings/helpers); never
   reconstruct that authority by copying the candidate registry. ARTIFACTS is
   exactly {:publication <bytes+expected-pins> :encoding <bytes+expected-pins>}.
   The three-argument form derives effective policy from the identity-trusted
   original binding; the optional fourth argument must normalize identically.
   Invoke before creating evaluator/graph profiles, Contexts and prefixes. No widening of axioms/unsafe/markers/checker-fuel is performed.
   Success does not admit a Context; resident-preparation/open-checked still
   checks its real association. Failure escrows original packets and cause;
   there are no acquired owners, effect retries or initializer execution."
  ([candidate configuration artifacts]
   (prepare-ordinary candidate configuration artifacts
                     (:kernel-policy (get-in configuration [:trusted-bindings symbol]))))
  ([candidate configuration artifacts policy]
  (try
    (let [world (:world candidate) actual (:session candidate)
          trusted (:trusted-functions configuration) bindings (:trusted-bindings configuration)
          helpers (:kernel-helpers configuration) support (:support candidate) original-kernel (get bindings symbol)
          _ (unsealed! candidate configuration)
          inherited-policy (effective-policy (:kernel-policy original-kernel))
          _ (check! (= inherited-policy (effective-policy policy))
                    "Explicit policy differs from identity-trusted original kernel binding")
          _ (check! (= #{:publication :encoding} (set (keys artifacts))) "Exact ordinary artifact pair required")
          _ (check! (and (not (:allow-nested? inherited-policy))
                         (not-any? #(contains? helpers %) [:generated :generated-nested :encode-family]))
                    "Ordinary preparation requires unextended helpers and nested disabled")
          _ (check! (and (= :done (:status world)) (empty? (:frames world)) (nil? (:host-request world))
                         (identical? (:functions world) (:functions actual))
                         (identical? (:catalogue candidate) (:catalogue configuration))
                         (map? trusted) (seq trusted) (map? helpers) original-kernel
                         (empty? (get-in world [:eval-const-authorizations :units])))
                    "Original checked pre-user preparation packet required")
          _ (check! (= (set (keys bindings)) (set (keys (:bindings actual)))) "Original binding set differs")
          _ (doseq [[s binding] bindings]
              (check! (identical? binding (get-in actual [:bindings s])) "Independent original binding identity drift"))
          _ (doseq [[name f] trusted]
              (check! (identical? f (get-in world [:functions name])) "Independent original executable identity drift"))
          _ (check! (map? support) "Independently retained original support required")
          _ (do
              (check! (and (identical? trusted (get-in support [:session :functions]))
                           (identical? bindings (get-in support [:session :bindings]))
                           (= helpers (:kernel-helpers support))
                           (= inherited-policy (effective-policy (:kernel-policy support)))
                           (or (not (contains? configuration :kernel-policy))
                               (= inherited-policy (effective-policy (:kernel-policy configuration)))))
                      "Prepared support differs from independent configuration/policy"))
          indexes (mapv #(authenticated-index (get artifacts %)) [:publication :encoding])
          catalogue (reduce declarations/overlay (:catalogue configuration) indexes)
          ;; Force every overlap through reconciliation even when an existing
          ;; executable means the linker would otherwise never read its row.
          _ (doseq [index indexes name (keys (:declarations index))] (row catalogue name))
          _ (validate-abi! catalogue generated [false true true] (get-in artifacts [:publication :expected-root-abi]))
          _ (validate-abi! catalogue encoder [false false false false] (get-in artifacts [:encoding :expected-root-abi]))
          extended (merge helpers ordinary-helpers)
          roots (vec (vals extended))
          lower (fn [r]
                  (if (contains? bindings (some-> r :ir :extern abi/symbol-for))
                    (raw/lower bindings r) (abi/lower-deferred-catalogue catalogue r)))
          derived (preparation/complete-functions catalogue trusted roots lower)
          functions (reduce-kv
                      (fn [out name f]
                        (when-let [existing (get out name)]
                          (check! (identical? existing f) "Independent helper closure collides with original executable"))
                        (assoc out name f)) (:functions world) derived)
          prepared-world (assoc world :functions functions)
          closure (eval/validate-executables! prepared-world derived roots)
          _ (doseq [[_ f] closure]
              (check! (not (or (:deferred-extern f) (:deferred-declaration f)))
                      "Ordinary helper closure has an unresolved runtime frontier"))
          _ (doseq [[name f] closure :when (:runtime-initializer f)]
              (check! (= :ready (get-in world [:globals name :status]))
                      "Helper closure needs an uninitialized imported global; no replay allowed"))
          ;; make-binding closes exactly this helper map/policy. One object is
          ;; shared by the independently derived config and actual candidate.
          binding (kernel/make-binding extended inherited-policy)
          _ (check! (= (:signature original-kernel) (:signature binding)) "Kernel callback ABI changed")
          next-bindings (assoc bindings symbol binding)
          session (raw/open-functions functions next-bindings (options actual))
          next-support (when support
                         (assoc support :catalogue catalogue :kernel-helpers extended :kernel-policy inherited-policy
                                :session (raw/open-functions derived next-bindings (options (:session support)))))
          next-candidate (cond-> (assoc candidate :world prepared-world :session session :catalogue catalogue
                                                        :trusted-functions derived)
                           next-support (assoc :support next-support))
          next-configuration (assoc configuration :catalogue catalogue :trusted-functions derived
                                    :trusted-bindings next-bindings :kernel-helpers extended :kernel-policy inherited-policy)]
      {:candidate next-candidate :configuration next-configuration
       :profile {:id profile-id :allow-nested? false :guest-executed false :new-initialization-actions 0
                 :added-functions (- (count derived) (count trusted))
                 :binding-replacements [symbol] :stage :before-profile-sealing}})
    (catch Throwable cause
      (throw (ex-info "Ordinary source inductive preparation failed"
                      {:source-inductive-preparation-entry candidate
                       :source-inductive-preparation-configuration configuration
                       :source-inductive-preparation-policy policy} cause))))))
