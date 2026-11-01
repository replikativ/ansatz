(ns prototype.full-init-admission
  "One-shot trusted-controller admission of the exact restored full Init map.
   The controller supplies its ACTUAL restore return and opaque Factory/support;
   this is not an API authenticating arbitrary caller-created restore maps. No
   source acquisition, initializer/finalizer replay or base proof checking."
  (:require [prototype.machine :as m]
            [prototype.native-scalar :as native]
            [prototype.module-store :as store]
            [prototype.raw-interop :as raw]
            [prototype.restore-consumer]
            [prototype.globals-consumer-factory :as factory]
            [prototype.coherent-stage-guards :as guards]
            [prototype.helper-authority :as authority]
            [prototype.compact-kernel-projection :as compact]
            [prototype.kernel-artifact :as artifact])
  (:import [ansatz.kernel Env ConstantInfo]
           [java.util WeakHashMap]))

(def supported-profile artifact/full-init-profile)
(def ^:private profile
  {:id supported-profile
   :manifest "a848092bdd6753f2737a954907747e1bad900c11506ad371fcb8460b576c46d6"
   ;; The fixed manifest authenticates these data bytes; admission never reopens it.
   :data "26282492007e48f6ba06466f0dea2c203c62d918da5ca283aee2db30449e773f"
   :archive "21acd0e8e735f46232dcb64ea3071600a2b2b0973167d46517e91b0db58b8129"
   :descriptor "62b168762b4ef900ac783589d4e8b4df4fa4712f120722190fbe4b3cfc0de144"
   :index "148b2b9aecaf8b8b4bfd856b92b1ca3f85246ac7b40303ae035538b3878e3b1c"
   :source "d3563f566d0eb70b76b4b7d148d7e28ee6f8464ad856288d762ffbb22bdff8d9"
   :base 352932 :nodes 11233359 :source-bytes 1858263589 :index-bytes 494267796
   :count 65994 :axioms guards/expected-axioms})

;; Values are constant and never retain a lease, input map, World or token.
(def ^:private claimed (WeakHashMap.))
(defn- require! [condition message data]
  (when-not condition (throw (ex-info message data))))

(defn- attached! [world source]
  (let [attached (store/describe-attached world source)]
    (require! (and (= 1 (count (:native-imports world)))
                   (identical? source (first (:native-imports world)))
                   (= (:source profile) (:digest source))
                   (= (:base profile) (:base source)) (= (:nodes profile) (:size source))
                   (= "4.33.1" (get-in attached [:manifest :input :leanVersion]))
                   (= factory/lean-commit (get-in attached [:manifest :input :leanCommit])))
              "Full Init admission requires the exact attached supported Store" {})
    attached))

(defn- preflight! [{:keys [factory restored support] :as input}]
  (require! (= #{:factory :restored :support} (set (keys input)))
            "Exact actual Factory/restore/support admission inputs required" {})
  ;; Accessors authenticate an issued opaque Factory before descriptive fields
  ;; are considered. The Factory already authenticates runtime companions.
  (let [{:keys [contract sha256]} (factory/coherent-contract factory)
        descriptor (factory/descriptor factory)
        recipe (get-in descriptor [:producer-preparation :catalogue-recipe])
        {:keys [world session io-result resource-lease]} restored
        source (:source support) trusted-session (:session support)
        node (when (m/ref? io-result) (m/node world io-result))
        lease-sources (when (instance? prototype.restore_consumer.ResourceLease resource-lease)
                        @(.-sources ^prototype.restore_consumer.ResourceLease resource-lease))]
    (require! (= {:basis :trusted-artifact :profile (:id profile)} (:kernel-base-admission contract))
              "Authenticated consumer contract does not select full Init artifact admission" {})
    (require! (and (= (:archive profile) (get-in recipe [:artifacts :archive :sha256]))
                   (= (:descriptor profile) (get-in recipe [:artifacts :transport-descriptor :sha256]))
                   (= (:producer-preparation descriptor) (:producer-preparation restored))
                   (= (:consumer-implementation-sha256 descriptor) (:consumer-implementation-sha256 restored))
                   (= (:compatibility-profile descriptor) (:compatibility-profile restored))
                   (= sha256 (:consumer-contract-sha256 restored))
                   (= (:manifest profile) (:manifest-sha256 restored)))
              "Actual Factory/restored checkpoint differs from the supported producer cohort" {})
    (require! (and (= :restored-precheck (:status restored)) (false? (:strictly-checked? restored))
                   (= :done (:status world)) (empty? (:frames world))
                   (nil? (:host-request world)) (nil? (:resume-var world))
                   (not (:initializing? world)) (not (:initialization-scope world))
                   (empty? (:kernel-environments world))
                   (= io-result (:result world) (get-in restored [:roots :io-result]))
                   (= :ctor (:kind node)) (= 0 (:tag node)) (= 1 (count (:fields node)))
                   (integer? (:rc node)) (<= 0 (:rc node)) (m/ref? (first (:fields node)))
                   (identical? (:functions world) (:functions session))
                   (map? (:functions trusted-session)) (map? (:bindings trusted-session))
                   (= (set (keys (:bindings session))) (set (keys (:bindings trusted-session)))))
              "Full Init admission requires the actual idle successful precheck IO/session" {})
    (require! (and (= 1 (count lease-sources)) (identical? source (first lease-sources)))
              "Full Init admission requires the actual open restore ResourceLease" {})
    (doseq [[symbol binding] (:bindings trusted-session)]
      (require! (identical? binding (get-in session [:bindings symbol]))
                "Full Init admission host binding differs from independent support" {:symbol symbol}))
    (require! (= (select-keys factory/helpers [:root :constants :constant-map :quot-init?])
                 (select-keys (:kernel-helpers support) [:root :constants :constant-map :quot-init?]))
              "Full Init admission requires the fixed independently prepared helpers" {})
    (let [attached (attached! world source)]
      ;; Length checks borrow the already authenticated open handles. Source and
      ;; private index hashes were checked by restore; do not repeat those scans.
      (require! (and (= (:source-bytes profile) (.size ^java.nio.channels.FileChannel (:channel source)))
                     (= (:index-bytes profile) (.length ^java.io.RandomAccessFile (:index source))))
                "Full Init admission source/index extent differs from the supported cohort" {})
      (authority/capture {:invoke (fn [& _] (throw (ex-info "Preflight cannot execute guest code" {})))
                          :trusted-functions (:functions trusted-session)
                          :bindings (:bindings session) :trusted-bindings (:bindings trusted-session)}
                         world (mapv (:kernel-helpers support) [:root :constants :constant-map :quot-init?]))
      {:attached attached :environment (first (:fields node)) :lease resource-lease})))

(defn- projection [world values source attached]
  ;; The large scoped memo dies before snapshotting and guest association.
  (let [project (:project-constant (compact/make-scoped-projector world))
        entries (reduce (fn [out guest]
                          (let [^ConstantInfo ci (project world guest) name (.name ci)]
                            (require! (not (contains? out name)) "Duplicate full Init map declaration" {:name name})
                            (assoc out name {:guest guest :constant ci}))) {} values)
        projected (into {} (map (fn [[name entry]] [name (:constant entry)])) entries)
        axioms (set (for [[name ^ConstantInfo ci] projected :when (.isAxiom ci)] name))
        _ (require! (= (:axioms profile) (set (map str axioms)))
                    "Full Init artifact axiom assumptions differ from the supported cohort" {})
        environment (reduce (fn [^Env environment ^ConstantInfo ci] (.addConstant environment ci))
                            (Env.) (vals projected))]
    {:basis :trusted-artifact :profile (:id profile)
     :provenance {:sha256 (:source profile) :lean-version "4.33.1" :lean-commit factory/lean-commit
                  :checkpoint-manifest (:manifest profile) :checkpoint-data (:data profile)
                  :producer-archive (:archive profile) :descriptor (:descriptor profile) :index (:index profile)}
     :base-assumptions {:basis :trusted-artifact :scope :full-init-restored-map
                       :declarations (set (keys projected)) :axioms axioms
                       :unsafe (set (for [[name ^ConstantInfo ci] projected
                                          :when (or (.isUnsafe ci) (and (.isDef ci) (not= 0 (.safety ci))))] name))
                       :quot-enabled? true}
     :env (.enableQuot environment) :source source :roots (:roots attached) :projection-sources [source]
     :constants (into {} (map (fn [[name entry]] [name (:guest entry)])) entries) :projected projected}))

(defn admit-restored!
  "Claim the ACTUAL controller-held supported restore return once and admit its
   exact native Init map. Factory and independent support authenticate code and
   bindings; the fixed checkpoint authenticates finalizer selection. This trusted
   host constructor does not authenticate arbitrary caller-created restore maps.
   Pure preflight failures do not claim the lease; after claim no retry is allowed.
   Returns owned :environment, latest :world/:session and :checked-result with an
   issued artifact token/provenance, never a strict certificate or checked order.
   The caller retains its ResourceLease/Store. Failure never closes either."
  [{:keys [restored support] :as input}]
  (let [{:keys [attached environment lease]} (preflight! input)
        _ (locking claimed
            (require! (not (.containsKey claimed lease)) "Full Init admission already claimed; no retry" {})
            (.put claimed lease true))
        entry (:world restored) active (atom (:session restored)) progress (volatile! entry)
        owners (volatile! []) environment-owned? (volatile! false) stage (volatile! :consume-io)
        invoke (fn [world target args]
                 (vreset! stage [:helper target])
                 (let [called (raw/call @active world target args)]
                   (reset! active (:session called)) (vreset! progress (:state called))
                   [(:state called) (:value called)]))
        context {:invoke invoke :trusted-functions (get-in support [:session :functions])
                 :bindings (get-in restored [:session :bindings])
                 :trusted-bindings (get-in support [:session :bindings])}
        helpers (:kernel-helpers support)
        roots (mapv helpers [:root :constants :constant-map :quot-init?])]
    (try
      ;; Independent authority is checked before IO ownership is consumed.
      (let [code (authority/capture context entry roots)
            world (-> entry (m/retain environment 1) (m/release (:io-result restored) 1) (assoc :result 0))
            _ (vreset! progress world) _ (vreset! environment-owned? true)
            [world constants] (invoke world (:constants helpers) [environment])
            _ (vswap! owners conj constants)
            node (when (m/ref? constants) (m/node world constants))
            values (:fields node)
            _ (require! (and (= :array (:kind node)) (vector? values)
                             (= (:count profile) (count values) (count (set values)))
                             (every? #(and (m/ref? %) (m/native-reference? world %)) values))
                        "Full Init admission requires the complete unique native CI map" {})
            _ (vreset! stage :project-actual-map)
            projected (projection world values (:source support) attached)
            world (m/release world constants 1)
            _ (vreset! progress world) _ (vreset! owners [])
            [world flag] (invoke world (:quot-init? helpers) [environment])
            _ (vswap! owners conj flag)
            _ (require! (= 1 (native/nat-value {:ref? m/ref? :node m/node} world flag))
                        "Supported restored Init must have initialized quotient metadata" {})
            world (m/release world flag 1)
            _ (vreset! progress world) _ (vreset! owners [])
            _ (attached! world (:source support))
            _ (authority/check context world roots code)
            _ (vreset! stage :issue-artifact)
            admission (artifact/issue-admitted-projection world projected)
            _ (vreset! stage :associate-actual-map)
            world (artifact/associate-admitted-progress context world environment helpers admission)
            _ (vreset! progress world)
            checked (artifact/inspect-for-world world admission)]
        {:status :ok :world (assoc world :result 0) :session @active :environment environment
         :admission admission :checked-result checked :kernel-provenance (:kernel-provenance checked)})
      (catch Throwable cause
        (let [data (ex-data cause) latest (or (:checkpoint data) @progress)]
          (throw (ex-info (or (.getMessage cause) "Full Init artifact admission failed")
                          (merge {:checkpoint latest :checkpoint-session @active :full-init-admission-stage @stage}
                                 data
                                 {:full-init-admission-entry {:checkpoint entry :io-result (:io-result restored)}
                                  :full-init-admission-owners (cond-> {:checkpoint latest}
                                                               @environment-owned? (assoc :environment environment))
                                  :full-init-admission-temporary-owners @owners
                                  :temporary-owners (vec (concat @owners (:temporary-owners data)
                                                                 (:association-temporary-owners data)))})
                          cause)))))))
