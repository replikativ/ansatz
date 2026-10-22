(ns prototype.native-init-base-test
  "Native-only host query/finalization tests. Tiny Source is real; large producer
   byte/closure validation is an explicit model where noted, never a genuine
   full-frontend construction or completed-Init receipt claim."
  (:require [clojure.test :refer [deftest is]]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.data.json :as json]
            [prototype.globals-consumer-factory :as factory]
            [prototype.globals-consumer-profile :as profile]
            [prototype.bootstrap-archive :as archive]
            [prototype.declaration-store :as ds]
            [prototype.runtime-abi :as abi]
            [prototype.eval-const :as eval]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]
            [prototype.module-init-capabilities :as init]
            [prototype.source-import :as source]
            [prototype.source-import-test :as tiny]
            [prototype.runtime-prim :as prim]
            [prototype.resident-init-prefix :as resident-prefix]
            [prototype.resident-frontend :as resident]
            [prototype.source-graph-runtime-test :as publication]
            [prototype.source-graph-staged-test :as staged])
  (:import [java.util ArrayList HashMap]
           [java.lang.ref WeakReference]
           [prototype.globals_consumer_factory Factory]))

(def init-plan {:kind "initialization-plan" :schema "lean-init-plan/1" :module source/init-module
                :moduleSystem true :imports [] :actions []})
(def init-symbol "initialize_Init")
(defn witness [symbols]
  {:schema "lean-module-initializer-symbols/1" :leanVersion "4.33.1"
   :leanCommit (get prim/pinned-build "lean_get_githash") :nativeEnvironmentTransported false
   :runtimeProfile {:wordBits 64 :target "x86_64-unknown-linux-gnu"} :symbols symbols})
(def init-witness (witness [{:module source/init-module :phase "all" :symbol init-symbol}]))
(def plans {source/init-module init-plan})
(def complete-guards (set (map #(vector source/init-module %) [:all :runtime :comptime])))
(defn failure [f] (try (f) nil (catch Exception e e)))
(defn model-options []
  (let [recipe (edn/read-string (slurp (io/resource "fixtures/producer50f-catalogue-recipe.edn")))]
    {:producer-preparation {:factory-id factory/shared-linear-factory-id
                            :implementation-sha256 profile/producer-implementation-sha256
                            :catalogue-recipe recipe :kernel-policy factory/kernel-policy
                            :trusted-roots (vec (concat factory/assembly-roots [factory/shared-linear-target factory/exporter]))}
     :producer-resolve-artifact (constantly "unused-modeled-producer") :store-root "unused-modeled-store"
     :expected-consumer-implementation-sha256 "modeled-consumer"}))
(defn with-modeled-producer
  "Only the existing archive/build/closure IO is modeled. Public factory dispatch,
   actual attached Source identity/descriptor comparison, real canonical native
   handler construction, opt-in preprocessing and final provenance issuance run."
  [loaded body & {:keys [reject-final? wrong-source?] :or {reject-final? false wrong-source? false}}]
  (let [source (:source loaded) options (model-options)
        functions {} world (assoc (:world loaded) :functions functions :sharecommon-profile :immutable-text-v1)
        catalogue {:manifests [{:initializationPlan init-plan}] :declarations {}}
        captured (atom nil) original-bindings init/make-bindings
        descriptor {:manifest (:manifest source) :sourceSha256 (if wrong-source? "wrong-source" (:digest source)) :nodes (:size source)}
        auth (fn [_] {:compatibility-profile profile/source-graph-frontend-reconstruction-profile-id})
        parsed {:preparation (:producer-preparation options) :world world :functions functions
                :prepared-functions functions :resources [source]}]
    (with-redefs-fn
      {#'profile/authenticate! auth #'profile/authenticate-reconstruction! auth
       #'profile/authenticate-runtime-ops-reconstruction! auth #'profile/authenticate-heap-net-dirty-reconstruction! auth
       #'profile/authenticate-source-graph-reconstruction! auth #'profile/authenticate-source-graph-frontend-reconstruction! auth
       #'factory/authenticate-build! (fn [& _] true)
       #'factory/checked-bytes (fn [_ _ id] (.getBytes (json/write-str (case id :transport-descriptor descriptor :initializer-witness init-witness)) "UTF-8"))
       #'factory/catalogue-bytes (fn [& _] catalogue)
       #'ds/open-index-verified-stream (fn [& _] catalogue) #'ds/overlay (fn [base _] base)
       #'abi/with-export-aliases (fn [base _] base)
       #'archive/verify-function-rows (fn [& _] {:functions functions :header {:declaration-index (:declaration-index @#'factory/pinned)}
                                               :next-id (:base source)})
       #'factory/complete (fn [cat funcs & _] {:catalogue cat :functions funcs})
       #'factory/witnesses (fn [_ assembly & _] assembly)
       #'eval/validate-executables! (fn [& _] (when reject-final? (throw (ex-info "Selected final authentication failure" {}))) true)
       #'init/make-bindings (fn [options] (let [made (original-bindings options)] (reset! captured made) made))}
      #(body {:factory-options options :parsed parsed :captured captured :source source :world world}))))

(deftest opted-in-public-factory-authenticates-source-before-issuing-provenance
  (tiny/with-tiny-init
    (fn [loaded]
      (with-modeled-producer loaded
        (fn [{:keys [factory-options parsed source world]}]
          (let [f (factory/make-source-graph-native-base-factory factory-options)
                rebuilt (factory/invoke! f parsed)
                binding (get-in rebuilt [:bindings "lean_run_mod_init_core"])
                cap (factory/native-init-readiness f source binding)
                coverage (factory/native-init-coverage cap source binding)]
            (is (= 1 (:query-count coverage)))
            (is (= [source/init-module] (:modules coverage)))
            (is (nil? (:native-init-readiness rebuilt))) ;; normal result contract unchanged
            (let [proof (#'factory/native-binding-proof! binding nil)
                  values (tree-seq coll? seq proof)]
              (is (not-any? #(identical? binding %) values))
              (is (not-any? #(identical? (:handler binding) %) values))
              (is (not-any? #(identical? world %) values)))
            (is (some? (failure #(factory/native-init-readiness f {:closed (atom false)} binding))))
            (is (some? (failure #(factory/native-init-readiness f source (into {} (map identity binding))))))
            (let [before (assoc world :status :done :frames [] :initialized-modules complete-guards)
                  [after io] (factory/query-native-init cap before binding 0)]
              (is (= [1] (:fields (m/node after io))))
              (is (= (get-in before [:stats :steps]) (get-in after [:stats :steps])))
              (is (identical? (:functions before) (:functions after)))
              (is (not (contains? (:heap before) (:id io))))
              (is (not (contains? (:heap (m/release after io 1)) (:id io)))))
            (doseq [missing complete-guards]
              (let [before (assoc world :status :done :frames [] :initialized-modules (disj complete-guards missing))
                    [after io] (factory/query-native-init cap before binding 0)]
                (is (= [0] (:fields (m/node after io))))
                (is (identical? (:initialized-modules before) (:initialized-modules after)))
                (is (not (contains? (:heap (m/release after io 1)) (:id io))))))
            (doseq [bad-binding [nil {} (assoc binding :handler (fn [& _] (throw (AssertionError. "Must not dispatch foreign handler"))))]]
              (is (some? (failure #(factory/query-native-init cap world bad-binding 0)))))
            (is (some? (failure #(factory/query-native-init cap world binding -1))))
            (is (some? (failure #(factory/query-native-init cap world binding 1))))))))))

(deftest failed-authentication-never-records-native-binding-provenance
  (tiny/with-tiny-init
    (fn [loaded]
      (doseq [mode [:source-mismatch :late-validation]]
        (with-modeled-producer loaded
          (fn [{:keys [factory-options parsed source captured]}]
            (let [f (factory/make-source-graph-native-base-factory factory-options)]
              (is (some? (failure #(factory/invoke! f parsed))))
              (is (some? (failure #(factory/native-init-readiness f source (get @captured "lean_run_mod_init_core")))))))
          :reject-final? (= mode :late-validation) :wrong-source? (= mode :source-mismatch))))))

(deftest all-six-original-factories-skip-opt-in-readiness-preprocessing
  (tiny/with-tiny-init
    (fn [loaded]
      (with-modeled-producer loaded
        (fn [{:keys [factory-options parsed source]}]
          (with-redefs-fn {#'factory/native-init-metadata! (fn [& _] (throw (AssertionError. "Original factory gained readiness work")))}
            #(doseq [make! [factory/make-factory factory/make-reconstruction-factory
                            factory/make-runtime-ops-reconstruction-factory factory/make-heap-net-dirty-reconstruction-factory
                            factory/make-source-graph-reconstruction-factory factory/make-source-graph-frontend-reconstruction-factory]]
               (let [f (make! factory-options) result (factory/invoke! f parsed)]
                 (is (:bindings result))
                 (is (some? (failure (fn [] (factory/native-init-readiness f source (get-in result [:bindings "lean_run_mod_init_core"]))))))))))))))

(deftest identity-buckets-never-hash-or-compare-caller-bindings
  (let [poison (proxy [java.util.AbstractMap] []
                 (entrySet [] (throw (AssertionError. "Caller entrySet")))
                 (hashCode [] (throw (AssertionError. "Caller hashCode")))
                 (equals [_] (throw (AssertionError. "Caller equals"))))
        a {:signature init/signature :handler (fn [& _] nil)} b (into {} (map identity a))
        proof-a {:marker (Object.)} proof-b {:marker (Object.)}]
    (with-redefs-fn {#'factory/native-binding-hash (constantly (int 123456789))}
      #(do
         (#'factory/native-binding-proof! a proof-a)
         (#'factory/native-binding-proof! b proof-b)
         (is (identical? proof-a (#'factory/native-binding-proof! a nil)))
         (is (identical? proof-b (#'factory/native-binding-proof! b nil)))
         (is (nil? (#'factory/native-binding-proof! poison nil)))
         (is (nil? (#'factory/native-binding-proof! (into {} (map identity a)) nil)))
         ;; Deterministic queue cleanup, without GC timing or live-entry eviction.
         (let [registry @#'factory/native-binding-provenance
               ^HashMap buckets (:buckets registry)]
           (locking registry
             (let [^ArrayList bucket (.get buckets (int 123456789))
                   ^WeakReference reference (first (first (filter (fn [[^WeakReference r _]] (identical? a (.get r))) (seq bucket))))]
               (.clear reference) (.enqueue reference)))
           (is (nil? (#'factory/native-binding-proof! a nil)))
           (is (identical? proof-b (#'factory/native-binding-proof! b nil))))))))

(deftest native-preprocessing-rejects-aggregate-and-coverage-drift
  (let [poison (proxy [Object] [] (hashCode [] (throw (AssertionError. "Unvalidated Name tag hashed"))))]
    (is (some? (failure #(#'factory/native-module-name! [poison ["anonymous"] "x"])))))
  (let [metadata (#'factory/native-init-metadata! plans init-witness)]
    (is (= 1 (get-in metadata [:counts :queries])))
    (is (= 5 (:host-units-per-query metadata)))
    (is (nil? (:module-plans metadata)))
    (is (nil? (:initialized-symbols metadata)))
    (is (some? (failure #(#'factory/native-init-metadata! plans (assoc init-witness :symbols [])))))
    (is (some? (failure #(#'factory/native-init-metadata! plans (update init-witness :symbols into (:symbols init-witness))))))
    (is (some? (failure #(#'factory/native-init-metadata! {source/init-module (assoc init-plan :imports (vec (repeat 16385 {:module source/init-module})))} init-witness))))
    (is (some? (failure #(#'factory/native-init-metadata! {source/init-module (assoc init-plan :module ["str" ["anonymous"] (apply str (repeat 16385 "x"))])} init-witness))))))

(defn configure-native-stage [input]
  (let [configured (staged/configure-chain (assoc input :independent-b? true))
        binding (get (init/make-bindings (init/options-from-witness plans init-witness)) "lean_run_mod_init_core")]
    (assoc-in configured [:bindings "lean_run_mod_init_core"] binding)))

(defn modeled-stage-token
  "Constructor consumer/build authentication AND post-invocation provenance are
   explicit models here. Source descriptor/auth ordering is separately exercised
   by with-modeled-producer above. Public readiness identity checks remain real;
   no caller-supplied provenance is accepted by the production operation."
  [fixture]
  (let [f (with-redefs-fn
            {#'profile/authenticate-source-graph-frontend-reconstruction!
             (constantly {:compatibility-profile profile/source-graph-frontend-reconstruction-profile-id})
             #'factory/authenticate-build! (fn [& _] true)}
            #(factory/make-source-graph-native-base-factory (model-options)))
        binding (get-in (resident/snapshot (:context fixture)) [:session :bindings "lean_run_mod_init_core"])
        proof (assoc (#'factory/native-init-metadata! plans init-witness)
                     :source (:source fixture) :owner (:native-owner (#'factory/capability! f)))]
    (#'factory/native-binding-proof! binding proof)
    (factory/native-init-readiness f (:source fixture) binding)))

(defn modeled-guards-context [fixture context guards]
  (let [entry (resident/snapshot context)
        next (resident/adopt-prepared (assoc-in entry [:world :initialized-modules] guards) (:configuration fixture))]
    (swap! (:captured fixture) conj next) next))

(defn prepare-native! [fixture context token]
  (swap! (get-in fixture [:transport :state]) update :headers conj source/init-requests)
  (resident-prefix/prepare-native-init-base context (staged/graph-request staged/module-b [] [staged/answer-b])
    (:prefix fixture) (:profile fixture) token {:kernel-policy staged/policy :budgets staged/budgets}))

(defn complete-native! [control]
  (loop [remaining 100]
    (when (zero? remaining) (throw (ex-info "Tiny native-base fixture exceeded slice bound" {})))
    (let [result (resident-prefix/advance-native-init-base! control {:max-operations 4 :wall-ms 1000})
          phase (get-in result [:progress :phase])]
      (if (= :io-completed phase) result (recur (dec remaining))))))

(deftest independent-leaves-reset-and-refresh-one-exact-graph-union
  ;; The compiler/header/native-finalizer envelopes are explicit models. The
  ;; fixed readiness handler, native finishing check/adoption, actual G1 graph
  ;; assembler, new B declaration kernel admission/decoder/installer, and whole
  ;; [A,B] fresh checking/authority run through production APIs on all backends.
  (doseq [backend [:reference :mutable :jvm]]
    (publication/with-empty-publication backend
      (fn [{:keys [captured transport] :as fixture}]
        (let [token (modeled-stage-token fixture)
              a (staged/publish! fixture) _ (swap! captured conj (:context a))
              completed-a (staged/import-roots! fixture (:context a) [(:graph-node a)] [staged/module-a])
              old-a (:context completed-a) old-packet (resident/snapshot old-a)
              ready (modeled-guards-context fixture old-a complete-guards)
              before (resident/snapshot ready)
              prepared (prepare-native! fixture ready token)
              control (:control prepared)
              _ (complete-native! control)
              finished (resident-prefix/finish-native-init-base! control)
              _ (swap! captured conj (:context finished))
              reset-packet (resident/snapshot (:context finished))
              denied (failure #(staged/graph-eval-answer! fixture (:context finished) (:graph-node a) staged/answer-a))
              b (staged/publish-child! fixture (:context finished) staged/module-b [] [] [staged/answer-b])
              union (staged/import-roots! fixture (:context b) [(:graph-node a) (:graph-node b)] [staged/module-a staged/module-b])
              union-packet (resident/snapshot (:context union))
              a-receipt (staged/receipt-in union-packet staged/module-a)
              b-receipt (staged/receipt-in union-packet staged/module-b)]
          (is (= :finished (get-in finished [:progress :phase])))
          (is (= 1 (get-in finished [:progress :readiness-queries])))
          (is (= 5 (get-in finished [:progress :host-work])))
          (is (= 0 (get-in finished [:native-base :source-receipts])))
          (is (nil? (:graph-import-receipts finished)))
          (is (some? denied))
          (is (identical? (get-in before [:world :source-modules]) (get-in reset-packet [:world :source-modules])))
          (is (identical? (get-in before [:world :eval-const-authorizations])
                          (get-in reset-packet [:world :eval-const-authorizations])))
          (is (identical? (:functions (:world before)) (:functions (:world reset-packet))))
          (is (= 2 (count (:graph-import-receipts union))))
          (is (identical? (:checked-env a-receipt) (:checked-env b-receipt)))
          (is (= [source/init-module staged/module-a staged/module-b] (:module-order a-receipt)))
          (is (= 41 (:value (staged/graph-eval-answer! fixture (:context union) (:graph-node a) staged/answer-a))))
          (is (= 41 (:value (staged/graph-eval-answer! fixture (:context union) (:graph-node b) staged/answer-b))))
          (is (= 41 (:value (staged/graph-eval-answer! fixture old-a (:graph-node a) staged/answer-a))))
          (is (identical? old-packet (resident/snapshot old-a)))
          (is (some? (failure #(resident-prefix/finish-native-init-base! control))))))
      :local-ci? true :configure configure-native-stage)))

(deftest partial-readiness-fails-terminally-before-finalizer-with-owned-false-result
  (publication/with-empty-publication :reference
    (fn [fixture]
      (let [token (modeled-stage-token fixture)
            context (modeled-guards-context fixture (:context fixture) #{[source/init-module :all]})
            before (resident/snapshot context)
            prepared (prepare-native! fixture context token)
            control (:control prepared)
            cause (failure #(resident-prefix/advance-native-init-base! control {:max-operations 4 :wall-ms 1000}))
            state (:native-init-base-state (ex-data cause))
            value (get-in state [:native-owners :readiness-result :value])]
        (is (some? cause))
        (is (nil? (:finalizer-started? state)))
        (is (= [0] (:fields (m/node (:world state) value))))
        (is (= :owned (get-in state [:native-owners :readiness-result :state])))
        (is (= 5 (:host-work state)))
        (is (identical? cause (failure #(resident-prefix/advance-native-init-base! control {:max-operations 1 :wall-ms 1000}))))
        (is (identical? cause (failure #(resident-prefix/finish-native-init-base! control))))
        (is (identical? before (resident/snapshot context)))))
    :local-ci? true :configure configure-native-stage))

(defn prepare-ready-native! [fixture]
  (let [token (modeled-stage-token fixture)
        context (modeled-guards-context fixture (:context fixture) complete-guards)]
    {:context context :before (resident/snapshot context)
     :prepared (prepare-native! fixture context token)}))

(deftest wrong-native-index-rejects-shared-const-extra-attribution-path
  ;; The wrong answer is encountered at the first native constant. Both Name
  ;; inventories use this shared guard; this is not an extra-only injection.
  (publication/with-empty-publication :reference
    (fn [fixture]
      (let [{:keys [context before prepared]} (prepare-ready-native! fixture)
            control (:control prepared) _ (complete-native! control)
            cause (failure #(resident-prefix/finish-native-init-base! control))
            state (:native-init-base-state (ex-data cause))]
        (is (some? cause))
        (is (= "Native finalizer has another const/extra module attribution" (.getMessage ^Throwable (.getCause ^Throwable cause))))
        (is (= :ok (get-in state [:finished :status])))
        (is (:native-observation state))
        (is (= :owned (get-in state [:native-owners :attribution-result :state])))
        (is (nil? (:adoption-entry state)))
        (is (identical? before (resident/snapshot context)))))
    :local-ci? true
    :configure (fn [input]
                 (let [configured (configure-native-stage input)
                       symbol (str "graph_staged_model_" (pr-str @#'resident-prefix/module-index-helper))]
                   (assoc-in configured [:bindings symbol :handler]
                     (fn [_ world _] (m/allocate world :ctor 1 [1])))))))

(deftest late-adoption-failure-retains-actual-checked-environment-and-owner-packet
  (publication/with-empty-publication :reference
    (fn [fixture]
      (let [{:keys [context before prepared]} (prepare-ready-native! fixture)
            control (:control prepared) _ (complete-native! control)
            selected (ex-info "Selected native-base adoption failure" {})
            cause (with-redefs [resident/adopt-prepared (fn [& _] (throw selected))]
                    (failure #(resident-prefix/finish-native-init-base! control)))
            state (:native-init-base-state (ex-data cause))]
        (is (identical? selected (.getCause ^Throwable cause)))
        (is (= :ok (get-in state [:finished :status])))
        (is (identical? (:world state) (get-in state [:adoption-entry :world])))
        (is (= :owned (get-in state [:native-owners :final-environment :state])))
        (is (= :released (get-in state [:native-owners :prior-environment :state])))
        (is (nil? (:adopted-context state)))
        (is (identical? cause (failure #(resident-prefix/finish-native-init-base! control))))
        (is (identical? before (resident/snapshot context)))))
    :local-ci? true :configure configure-native-stage))

(deftest partial-outer-and-boundary-guest-failures-charge-their-real-categories
  ;; Inject transport failure only AFTER the original raw operation publishes a
  ;; genuine event. Host-only finalization has effects but zero guest work; a
  ;; separate captured nested helper provides positive boundary guest work.
  ;; The adapter sees only the thrown call's checkpoint and retains the residual.
  (doseq [kind [:outer :boundary :boundary-helper]]
    (publication/with-empty-publication :reference
      (fn [fixture]
        (let [{:keys [context before prepared]} (prepare-ready-native! fixture)
              control (:control prepared) observed (atom nil)
              category (if (= :outer kind) :outer-steps :helper-steps)
              target (if (= :outer kind) #'raw/advance-to-boundary #'raw/complete-host-boundary)
              original @target selected (ex-info "Selected post-event transport failure" {})
              wrapper (fn [& args]
                        (let [entry @(#'resident-prefix/native-control! control)
                              event (apply original args)]
                          (reset! observed {:entry entry :event event})
                          (throw (ex-info "Selected post-event transport failure"
                                   {:checkpoint (:state event) :checkpoint-session (:session event)
                                    :native-diagnostic-event event} selected))))
              cause (with-redefs-fn {target wrapper} #(failure (fn [] (complete-native! control))))
              state (:native-init-base-state (ex-data cause))
              child (ex-data (.getCause ^Throwable cause))
              entry (:entry @observed) event (:event @observed)
              delta (- (get-in event [:state :stats :steps]) (get-in entry [:world :stats :steps]))
              bound (get-in entry [:guest-entry :bound])]
          (is (some? cause))
          (is (:finalizer-started? state))
          (case kind
            :outer (is (pos? delta))
            :boundary (do (is (zero? delta)) (is (zero? (:helper-steps event)))
                          (is (= :handler-completed (:status event)))
                          (is (not (identical? (get-in entry [:world :heap]) (get-in event [:state :heap])))))
            :boundary-helper (do (is (pos? delta)) (is (pos? (:helper-steps event)))))
          (is (= delta (- (category state) (category entry))))
          (is (= delta (- (:used state) (:used entry))))
          (is (= (:used state) (+ (:helper-steps state) (:outer-steps state))))
          (is (= (- bound delta) (:reserved state)))
          (is (identical? (:state event) (:world state)))
          (is (identical? (:session event) (:session state)))
          (is (identical? (:checkpoint child) (:world state)))
          (is (identical? (:checkpoint-session child) (:session state)))
          (is (identical? before (resident/snapshot context)))))
      :local-ci? true
      :configure (fn [input]
                   (let [configured (configure-native-stage input)]
                     (if (not= :boundary-helper kind) configured
                       (let [target (publication/str-name "NativeAccountingNestedGuest")
                             symbol (str "graph_staged_model_" (pr-str (:finalize source/helpers)))
                             original (get-in configured [:bindings symbol :handler])]
                         ;; Fixed test helper and handler are captured BEFORE
                         ;; profile/configuration/prefix. No hot code replacement.
                         (-> configured
                             (assoc-in [:functions target] {:params [] :body [:let 91 [:literal 0] [:return [:var 91]]]})
                             (assoc-in [:bindings symbol :handler]
                               (fn [context world args]
                                 (let [[world value] (original context world args)
                                       [world _] ((:invoke context) world target [])]
                                   [world value])))))))))))

(deftest unpublished-backend-instructions-retain-the-unknown-reservation
  ;; run-boundary does not publish intermediate machine steps. The real let
  ;; executes internally, then unreachable throws without a later checkpoint;
  ;; no assertion invents that hidden work or treats the entry as a fresh result.
  (publication/with-empty-publication :reference
    (fn [fixture]
      (let [{:keys [context before prepared]} (prepare-ready-native! fixture)
            control (:control prepared)
            cause (failure #(complete-native! control))
            state (:native-init-base-state (ex-data cause))
            child (ex-data (.getCause ^Throwable cause))]
        (is (some? cause))
        (is (:finalizer-started? state))
        (is (= (get-in prepared [:progress :outer-steps]) (:outer-steps state)))
        (is (= (get-in prepared [:progress :guest-steps]) (:used state)))
        (is (= (:outer-fuel staged/budgets) (:reserved state)))
        (is (identical? (:checkpoint child) (:world state)))
        (is (identical? (:checkpoint-session child) (:session state)))
        (is (identical? cause (failure #(resident-prefix/finish-native-init-base! control))))
        (is (identical? before (resident/snapshot context)))))
    :local-ci? true
    :configure (fn [input]
                 (assoc-in (configure-native-stage input) [:functions (:finalize source/helpers) :body]
                   [:let 91 [:literal 0] [:unreachable]]))))
