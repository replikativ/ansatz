(ns prototype.resident-frontend
  "Explicit resident contexts over the proven hosted frontend. Contexts own one
   Environment and Options owner in their immutable branch; artifact Store lifetime
   remains external. Returned contexts preserve the actual execution session/cache.
   Forks isolate guest state, not host effects. No native per-file compiler."
  (:refer-clojure :exclude [load-file])
  (:require [prototype.machine :as m]
            [prototype.binding-dependencies :as dependencies]
            [prototype.frontend :as frontend]
            [prototype.hosted-file :as hosted]
            [prototype.guest-encoding :as encoding]
            [prototype.raw-interop :as raw]
            [prototype.interop-codec :as codec]
            [prototype.import-ir :as ir]
            [prototype.kernel-host :as kernel]
            [prototype.module-import :as imports]
            [prototype.eval-const :as eval]
            [prototype.runtime-prim :as prim]
            [prototype.runtime-abi :as abi]
            [clojure.string :as str])
  (:import [ansatz.kernel Name]))

(declare close!)
(deftype Context [state]
  java.io.Closeable
  (close [this] (close! this)))
(deftype FileHandle [digest unit module])

(defn- fail [message data] (throw (ex-info message data)))
(defn- context-data [context]
  (when-not (instance? Context context) (fail "Expected resident context" {}))
  (or @(.-state ^Context context) (fail "Resident context is closed" {})))
(defn- matching-world! [{:keys [world session] :as prepared}]
  (when-not (and (map? world) (map? session) (map? (:functions world))
                 (identical? (:functions world) (:functions session)))
    (fail "Resident world and session must share executable identity" {}))
  (when-not (and (contains? #{nil :done} (:status world)) (empty? (:frames world))
                 (nil? (:host-request world)))
    (fail "Resident contexts require idle guest execution" {}))
  prepared)
(defn- matching! [{:keys [world environment options] :as prepared}]
  (matching-world! prepared)
  (doseq [[label value] [[:environment environment] [:options options]]]
    (when-not (m/ref? value) (fail "Resident context requires owned guest roots" {:root label}))
    (m/node world value))
  (doseq [[value owners] (frequencies [environment options])
          :let [rc (:rc (m/node world value))]]
    (when-not (or (zero? rc) (<= owners rc))
      (fail "Insufficient resident root owners" {:owners owners :rc rc})))
  prepared)
(defn- valid-context! [data]
  (let [{:keys [world session]} (matching! (:prepared data))]
    (doseq [[name function] (:protected-functions data)]
      (when-not (identical? function (get-in world [:functions name]))
        (fail "Resident protected executable changed" {:name name})))
    (doseq [[symbol binding] (:protected-bindings data)]
      (when-not (identical? binding (get-in session [:bindings symbol]))
        (fail "Resident protected host capability changed" {:symbol symbol})))
    data))
(defn- make-context [data]
  (valid-context! data)
  (Context. (atom data)))

(defn snapshot
  "Borrow the explicit prepared snapshot for diagnostics/advanced orchestration.
   Returned roots are borrowed; this is not a serialized checking capability."
  [context]
  (:prepared (context-data context)))

(defn- guest-encoder-roots [configuration]
  ;; hosted/run-file supplies these defaults, while frontend/compile-file passes
  ;; encoder-options unchanged to BOTH encoders. Any selected default encoder
  ;; can invoke the selected guest decodeNames helper; custom host callbacks are
  ;; an explicit trust decision and cannot be introspected for dependencies.
  (let [configuration (or configuration {})
        encode-name (get configuration :encode-name encoding/encode-name)
        encode-names (get configuration :encode-names encoding/encode-names)
        options (:encoder-options configuration)]
    (when-not (and (map? configuration) (fn? encode-name) (fn? encode-names)
                   (or (nil? options) (map? options)))
      (fail "Invalid resident Name encoder configuration" {}))
    (when (or (identical? encode-name encoding/encode-name)
              (identical? encode-names encoding/encode-names))
      [(get options :helper encoding/names-helper)])))

(defn adoption-readiness!
  "Validate the independent host registry/catalogue and selected frontend/helper
   closures without guest execution or Options acquisition. ENVIRONMENT must be
   a live owned root in an idle matching world/session. This does not validate a
   checked association or mint authority; adoption/open-checked still invoke the
   identity-authorized live kernel helpers. Custom host encoders/lowering remain
   explicit trusted code, not dependencies inferred from a callback's behavior.
   Declared fixed helper roots are read only from identity-authenticated trusted
   bindings and become protected with their full independent executable closure.
   Legacy callbacks without such metadata remain explicitly trusted host code."
  [prepared configuration]
  (matching-world! prepared)
  (let [environment (:environment prepared) world (:world prepared)]
    (when-not (m/ref? environment) (fail "Resident context requires owned Environment" {}))
    (let [rc (:rc (m/node world environment))]
      (when-not (and (integer? rc) (<= 0 rc)) (fail "Invalid resident Environment owner" {}))))
  (when-not (and (map? (:trusted-functions configuration))
                 (map? (:trusted-bindings configuration)))
    (fail "Resident adoption requires explicit trusted preparation registries" {}))
  (when-not (= (set (keys (:trusted-bindings configuration)))
               (set (keys (get-in prepared [:session :bindings]))))
    (fail "Resident bindings differ from trusted preparation" {}))
  (doseq [[symbol binding] (:trusted-bindings configuration)]
    (when-not (identical? binding (get-in prepared [:session :bindings symbol]))
      (fail "Resident host capability differs from trusted preparation" {:symbol symbol})))
  (when-not (seq (get-in prepared [:catalogue :manifests]))
    (fail "Resident context requires producer manifests" {}))
  (doseq [manifest (get-in prepared [:catalogue :manifests])]
    (ir/validate-manifest! manifest)
    (when-not (and (or (not (contains? manifest :leanCommit))
                       (= (get prim/pinned-build "lean_get_githash") (:leanCommit manifest)))
                   (= {:target "x86_64-unknown-linux-gnu" :wordBits 64} (:runtimeProfile manifest)))
      (fail "Resident frontend requires pinned runtime profile" {})))
  (let [binding-roots (dependencies/declared-roots (:trusted-bindings configuration))
        helpers (or (:kernel-helpers configuration) imports/helpers)
        _ (doseq [key [:root :constant-map :quot-init?]]
            (when-not (vector? (get helpers key)) (fail "Missing resident kernel helper" {:helper key})))
        frontend-configuration (:frontend-configuration configuration)
        compile-target (or (:compile-target frontend-configuration) frontend/compile-target)
        default-witness ["str" ["str" ["anonymous"] "RuntimeCompileShim"] "exportEvalConstWitness"]
        witness (or (get-in frontend-configuration [:install-options :witness])
                    (when (or (get-in frontend-configuration [:install-options :authorize-source-import])
                              (contains? (get-in prepared [:world :functions]) default-witness))
                      default-witness))
        protected (eval/validate-executables! (:world prepared) (:trusted-functions configuration)
                                              (concat binding-roots
                                                      (map helpers [:root :constant-map :quot-init?])
                                                      [compile-target frontend/header-target]
                                                      (when witness [witness])
                                                      (guest-encoder-roots frontend-configuration)))]
    {:kernel-helpers helpers :protected-functions protected}))

(defn adopt-prepared
  "Adopt ONE existing owned Environment/Options pair in this branch. No implicit
   retain/import/bootstrap. The original immutable snapshot remains independent.
   Configuration requires independently captured trusted functions/bindings and
   an explicit catalogue. Actual live association and selected compiler/witness/
   guest Name-encoder closures are checked; certificates/phase flags grant none.
   Custom host callbacks remain trusted host code. Failures preserve the exact
   owned entry packet plus latest named helper checkpoint/session alternatives."
  ([prepared] (adopt-prepared prepared {}))
  ([prepared configuration]
   (let [active (atom (:session prepared)) progress (volatile! (:world prepared))
         invoke (fn [world target args]
                  (vreset! progress world)
                  (let [result (raw/call @active world target args)]
                    (reset! active (:session result)) (vreset! progress (:state result))
                    [(:state result) (:value result)]))]
     (try
       (matching! prepared)
       (let [{:keys [kernel-helpers protected-functions]} (adoption-readiness! prepared configuration)
             [world checked] (kernel/inherit-checked-association
                              {:invoke invoke} (:world prepared) (:environment prepared) kernel-helpers)]
         (vreset! progress world)
         (when-not checked (fail "Resident Environment has no existing checked association" {}))
         (make-context {:prepared (assoc prepared :world world :session @active)
                        :configuration configuration :protected-functions protected-functions
                        :protected-bindings (get-in prepared [:session :bindings])}))
       (catch Throwable cause
         (let [data (ex-data cause)]
           (throw (ex-info (or (.getMessage cause) "Resident adoption failed")
                           (merge {:checkpoint @progress :checkpoint-session @active} data
                                  {:resident-adoption-entry prepared :resident-operation :adopt-prepared}) cause))))))))

(defn fork
  "Fork guest state with inherited code authority and shared optimization caches.
   Artifact resources stay borrowed from the caller; external effects are shared."
  [context]
  (locking context (make-context (context-data context))))

(defn close!
  "Consume this context's Environment/Options owners once. Does not close a shared
   artifact Store, invalidate children, or replay/undo host effects."
  [context]
  (when-not (instance? Context context) (fail "Expected resident context" {}))
  (locking context
    (when-let [data @(.-state ^Context context)]
      (let [{:keys [world environment options]} (:prepared data)]
        (-> world (m/release environment 1) (m/release options 1))
        (reset! (.-state ^Context context) nil))))
  nil)

(defn load-source
  "Load source with explicit module, roots and initialization policy. Returns
   {:context :diagnostics :success :file}; diagnostic failures preserve the actual
   partial Environment, without an executable handle. No inline calls accepted."
  [context request]
  (locking context
    (let [{:keys [prepared configuration] :as data} (context-data context)
          completed (volatile! nil)]
      (valid-context! data)
      (when (contains? request :calls) (fail "Use resident call separately from source loading" {}))
      (try
        (let [compiled (hosted/run-file prepared request (:frontend-configuration configuration))
              _ (vreset! completed compiled)
              _ (matching! (merge prepared (select-keys compiled [:world :session :environment])))
              world (m/release (:world compiled) (:environment prepared) 1)
              prepared (merge prepared (select-keys compiled [:session :environment]) {:world world})
              digest (get-in compiled [:handle :unit-digest])
              unit (get-in world [:eval-const-authorizations :units digest])]
          (when (and (:success compiled) (not unit))
            (fail "Successful resident compilation has no admitted unit" {}))
          {:context (make-context (assoc data :prepared prepared))
           :success (:success compiled) :diagnostics (:diagnostics compiled)
           :file (when (:success compiled) (FileHandle. digest unit (:module-name request)))})
        (catch Throwable cause
          ;; Lower layers own precise partial-result/temporary-owner evidence.
          ;; Do not invent a checked context or splice owners across checkpoints.
          (throw (ex-info (or (.getMessage cause) "Resident source load failed")
                          (merge (when-let [compiled @completed]
                                   {:checkpoint (:world compiled) :checkpoint-session (:session compiled)
                                    :resident-completed-load compiled})
                                 (ex-data cause)
                                 {:resident-input context :resident-operation :load-source}) cause)))))))

(defn- structured-name [^Name name]
  (when-not (instance? Name name) (fail "Resident calls require kernel Names" {}))
  (loop [name name parts []]
    (if (.isAnonymous name)
      (reduce (fn [prefix [kind value]] [kind prefix value]) ["anonymous"] (rseq parts))
      (recur (.-prefix name) (conj parts (if (.isStr name) ["str" (.-str name)] ["num" (str (.-num name))]))))))

(defn- file-unit! [prepared file]
  (when-not (instance? FileHandle file) (fail "Expected admitted resident file handle" {}))
  (let [digest (.-digest ^FileHandle file)
        unit (get-in prepared [:world :eval-const-authorizations :units digest])]
    (when-not (and unit (identical? unit (.-unit ^FileHandle file)))
      (fail "Resident file handle belongs to a different context generation" {}))
    [digest unit]))

(defn initialize
  "Run only the admitted unit's explicit initializer plan; never recompile source.
   Actual guest guards/evidence prevent replay of completed or failed effects."
  [context file]
  (locking context
    (let [{:keys [prepared] :as data} (valid-context! (context-data context))
          [digest unit] (file-unit! prepared file)
          active (atom (:session prepared))
          progress (volatile! (:world prepared))
          completed (volatile! nil)
          invoke (fn [world target args]
                   (let [called (raw/call @active world target args)]
                     (reset! active (:session called))
                     (vreset! progress (:state called))
                     [(:state called) (:value called)]))]
      (try
        (let [world (eval/run-initializers {:invoke invoke} (:world prepared)
                                           {:unit-digest digest :initialization-plan (get-in unit [:manifest :initializationPlan])})
              _ (vreset! completed {:world world :session @active})]
          (make-context (assoc data :prepared (assoc prepared :world world :session @active))))
        (catch Throwable cause
          (let [cause-data (ex-data cause)]
            (throw (ex-info (or (.getMessage cause) "Resident initialization failed")
                            (merge {:checkpoint @progress :checkpoint-session @active}
                                   (when-let [done @completed]
                                     {:checkpoint (:world done) :resident-completed-initialization done})
                                   cause-data
                                   {:checkpoint-session (or (:checkpoint-session cause-data) @active)
                                    :resident-input context :resident-operation :initialize}) cause))))))))

(defn- target! [prepared file name]
  (let [[digest _] (file-unit! prepared file)]
    (eval/assert-unit-ready! (:world prepared) digest)
    (let [target (eval/boxed-entrypoint! (:world prepared) digest (structured-name name))
          function (get-in prepared [:world :functions target])
          row (get-in prepared [:world :eval-const-authorizations :declarations target])
          decl (get-in row [:ir :fdecl])
          signature (or (when decl {:params (mapv #(select-keys % [:ty :borrow]) (:xs decl)) :return-type (:type decl)})
                        (when-let [ext (:raw-extern function)]
                          {:params (mapv #(select-keys % [:ty :borrow]) (get-in ext [:signature :params]))
                           :return-type (get-in ext [:signature :return-type])}))]
      (when-not (and signature (= (count (:params signature)) (count (:params function)))
                     (every? #(and (boolean? (:borrow %))
                                   (contains? #{"object" "tobject" "tagged" "erased" "void"} (:ty %)))
                             (:params signature))
                     (contains? #{"object" "tobject" "tagged"} (:return-type signature)))
        (fail "Resident calls require an admitted boxed entrypoint ABI" {:target target}))
      [target function signature])))

(defn call
  "Call an admitted boxed entrypoint with explicit :arguments vector/:result codec.
   Erased polymorphic arguments use :erased with nil; use call-io for the IO world.
   Returns decoded :value and matching :context. Decode borrows, then the result
   owner is released once. On failure retain the exact completed result evidence."
  [context file name values {:keys [arguments result] :as signature}]
  (locking context
    (let [{:keys [prepared] :as data} (context-data context)
          _ (valid-context! data)
          [target function abi] (target! prepared file name)
          _ (when-not (and (vector? arguments) (vector? values)
                           (= (count arguments) (count values) (count (:params function)))
                           (contains? signature :result))
              (fail "Resident call needs explicit matching codecs and arity" {}))
          _ (doseq [descriptor arguments]
              (when (= :world descriptor) (fail "Use call-io for the IO world argument" {}))
              (codec/validate-descriptor! descriptor :encode))
          _ (doseq [[param descriptor] (map vector (:params abi) arguments)]
              (when (and (contains? #{"void" "erased"} (:ty param)) (not= :erased descriptor))
                (fail "Erased ABI parameter requires an explicit erased codec" {})))
          _ (codec/validate-descriptor! result :decode)
          progress (volatile! (:world prepared))
          owned (volatile! [])
          completed (volatile! nil)]
      (try
        (let [[world args]
              (reduce (fn [[world args] [descriptor value]]
                        (when (= :world descriptor)
                          (fail "Use call-io for the IO world argument" {}))
                        (let [[world encoded] (codec/encode-boxed world descriptor value)]
                          (vreset! progress world) (vswap! owned conj encoded)
                          [world (conj args encoded)]))
                      [(:world prepared) []] (map vector arguments values))
              ;; Borrowed ABI parameters keep their facade owner while the guest
              ;; runs. Owned parameters transfer at invocation start.
              borrowed (into [] (keep (fn [[param value]] (when (:borrow param) value)))
                             (map vector (:params abi) args))
              _ (vreset! owned borrowed)
              invoked (raw/call (:session prepared) world target args)
              _ (vreset! completed invoked)
              _ (matching! (assoc prepared :world (:state invoked) :session (:session invoked)))
              value (codec/decode-boxed (:state invoked) result (:value invoked))
              world (reduce #(m/release %1 %2 1) (:state invoked) borrowed)
              world (assoc (m/release world (:value invoked) 1) :result 0)]
          {:context (make-context (assoc data :prepared (assoc prepared :world world :session (:session invoked))))
           :value value})
        (catch Throwable cause
          (let [invoked @completed]
            (throw (ex-info (or (.getMessage cause) "Resident guest call failed")
                            (merge {:checkpoint @progress :checkpoint-session (:session prepared)
                                    :resident-temporary-owners @owned}
                                   (ex-data cause)
                                   {:resident-input context :resident-operation :call}
                                   (when invoked {:checkpoint (:state invoked) :checkpoint-session (:session invoked)
                                                  :resident-owned-result (:value invoked)})) cause))))))))

(defn call-io
  "Explicit IO call; append the erased world token and decode the owned IO wrapper.
   User argument codecs must describe only the explicit Lean arguments."
  [context file name values signature]
  ;; :erased and :world share the carrier, not the API obligation.
  (call context file name (conj values nil)
        {:arguments (conj (:arguments signature) :erased) :result [:io (:result signature)]}))

(defn with-externs
  "Add new application raw extern bindings. Existing runtime/kernel bindings cannot
   be replaced. New symbols require :application-extern-symbols in independent
   trusted preparation; runtime symbols remain reserved even when not yet linked.
   Exact ABI checking happens in raw session opening and compilation. Passed
   new binding objects are explicit trusted host capabilities. Their declared
   guest dependencies must match the EXISTING independent executable registry;
   they are added to Context protection, never authorized from candidate code."
  [context bindings]
  (locking context
    (let [{:keys [prepared] :as data} (context-data context)
          _ (valid-context! data)
          session (:session prepared)]
      (when-not (map? bindings) (fail "Resident extern bindings must be a map" {}))
      (doseq [symbol (keys bindings)]
        (when-not (contains? (get-in data [:configuration :application-extern-symbols] #{}) symbol)
          (fail "Application extern was not admitted by trusted preparation" {:symbol symbol}))
        (when (or (str/starts-with? symbol "lean_")
                  (contains? prim/supported-symbols symbol)
                  (contains? @abi/signatures symbol)
                  (some #(= symbol (:symbol %)) (mapcat :exports (get-in prepared [:catalogue :manifests]))))
          (fail "Application extern collides with a reserved runtime capability" {:symbol symbol}))
        (when (contains? (:bindings session) symbol)
          (fail "Resident extern configuration cannot replace an existing capability" {:symbol symbol})))
      (let [next-session (raw/open-functions (:functions session) (merge (:bindings session) bindings)
                                             (assoc (select-keys session [:backend :fuel :compile-threshold])
                                                    :cache (or (get-in session [:program :cache]) (:cache session))))
            ;; The complete retained/admitted binding registry shares one root
            ;; budget; repeated additions cannot bypass aggregate bounds.
            roots (dependencies/declared-roots (:bindings next-session))
            protected (eval/validate-executables! (:world prepared)
                                                  (get-in data [:configuration :trusted-functions]) roots)]
        (make-context (assoc data :prepared (assoc prepared :session next-session)
                             :protected-functions (merge (:protected-functions data) protected)
                             :protected-bindings (:bindings next-session)))))))
