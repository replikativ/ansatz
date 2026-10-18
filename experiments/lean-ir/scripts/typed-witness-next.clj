;; DRAFT: definitions only. Working directory: experiments/lean-ir.
;; First load scripts/prepare-ir-witness.clj and
;; scripts/prepare-shared-names-witness.clj (both definitions only).
;; No finalizer, native command, archive restore or source closure on load.
(require '[clojure.java.io :as tw-io]
         '[prototype.import-ir :as tw-ir]
         '[prototype.declaration-store :as tw-store]
         '[prototype.runtime-abi :as tw-abi]
         '[prototype.raw-interop :as tw-raw]
         '[prototype.preparation :as tw-prep]
         '[prototype.eval-const :as tw-eval]
         '[prototype.machine :as tw-m])

(def full-init-witness-artifacts
  {"target/runtime-compile-shim-json-value-source.jsonl"
   "45dcd510324bdff6d0d95ac1093d26a087ad1d6e513e7fec1ea2d07f6a8873fd"
   "target/runtime-compile-shim-ir-value-source.jsonl"
   "731bb72ce9928e0d46d50728c675df21a3d073c6d0f3c1dde96816af89c09cad"
   "target/runtime-compile-shim-ir-linear-source.jsonl"
   "a78a10859db267efa952f12b2635c6cdc3dfa32ce713f98f04f6a8ea6e2f9e98"
   "target/runtime-compile-shim-ir-shared-names-source.jsonl"
   "9864fa3afbf521fa541ef0a00931c34e237ea6538582ddad0746acf5e8e5bed8"})
(def tw-json-target ["str" ["str" ["anonymous"] "RuntimeCompileShim"] "exportEvalConstWitnessValue"])
(def tw-exporter ["str" ["str" ["anonymous"] "RuntimeCompileShim"] "exportCompiled"])

(defn- tw-check [ok message]
  (when-not ok (throw (ex-info message {:scope :full-init-typed-witness-draft}))))
(defn- tw-assembly-preflight! [assembled]
  ;; Liveness/identity checks only, before opening or claiming an execution.
  ;; This does not prove that external callers have observed affine ownership.
  (let [world (:world assembled) session (:session assembled) source (:source assembled)
        attached (:native-imports world)]
    (tw-check (and (= :done (:status world)) (empty? (:frames world)) (nil? (:host-request world)))
              "Assembly world must be idle")
    (tw-check (and (map? (:functions session)) (identical? (:functions session) (:functions world)))
              "Assembly/session executable identity mismatch")
    (tw-check (and source (instance? clojure.lang.IDeref (:closed source)) (false? @(:closed source)))
              "Expected original open source")
    (tw-check (and (= 1 (count attached)) (identical? source (first attached)))
              "Assembly world must attach the same singleton source")
    (doseq [root [(:state assembled) (:imports assembled)]]
      (tw-check (tw-m/ref? root) "Missing owned assembly roots")
      (tw-check (map? (tw-m/node world root)) "Assembly root has no live guest node"))
    assembled))
(defn- tw-heap []
  (let [r (Runtime/getRuntime)] {:used (- (.totalMemory r) (.freeMemory r)) :committed (.totalMemory r) :max (.maxMemory r)}))
(defn- tw-measure [phases phase f]
  (let [before (tw-heap) started (System/nanoTime) result (f)]
    (swap! phases conj {:phase phase :elapsed-ms (/ (- (System/nanoTime) started) 1e6)
                       :heap-before before :heap-after (tw-heap)}) result))
(defn- tw-pinned [path expected]
  (let [bytes (java.nio.file.Files/readAllBytes (.toPath (tw-io/file path)))
        actual (.formatHex (java.util.HexFormat/of)
                 (.digest (java.security.MessageDigest/getInstance "SHA-256") bytes))]
    (tw-check (= actual expected) (str "Witness artifact mismatch: " path))
    ;; Parse the same checked bytes, with no verify/reopen race.
    (tw-ir/index-bundles [(java.io.StringReader. (String. bytes java.nio.charset.StandardCharsets/UTF_8))])))
(defn- tw-preserved-functions! [before after]
  (doseq [[name function] before]
    (tw-check (identical? function (get after name)) "Witness preparation replaced an executable")))
(defn- tw-stage-json [catalogue functions bindings]
  ;; Equivalent additive/no-refresh policy to prepare-json-witness, but parses
  ;; authenticated bytes rather than its path reopening. Existing rows win.
  (let [path "target/runtime-compile-shim-json-value-source.jsonl"
        candidate (tw-pinned path (get full-init-witness-artifacts path))
        _ (doseq [manifest (:manifests candidate)]
            (tw-ir/validate-manifest! manifest)
            (tw-check (and (= "lean-init-plan/1" (get-in manifest [:initializationPlan :schema]))
                           (= ["str" ["anonymous"] "RuntimeCompileShim"] (get-in manifest [:initializationPlan :module]))
                           (false? (get-in manifest [:initializationPlan :moduleSystem]))
                           (= [] (get-in manifest [:initializationPlan :actions])))
                      "Stage1 witness may not introduce initializer actions"))
        additions (into {} (remove (fn [[name _]] (contains? (:declarations catalogue) name))) (:declarations candidate))
        _ (tw-check (contains? additions tw-json-target) "Expected fresh stage1 witness preparation")
        _ (doseq [name (keys additions)]
            (tw-check (not (contains? functions name)) "Witness row collides with unbacked executable"))
        catalogue (tw-store/overlay catalogue {:manifests (:manifests candidate) :declarations additions})
        lower #(if (contains? bindings (some-> % :ir :extern tw-abi/symbol-for))
                 (tw-raw/lower bindings %) (tw-abi/lower-deferred-catalogue catalogue %))
        linked (tw-ir/load-closure catalogue [tw-json-target] lower {:existing-functions functions})]
    (tw-preserved-functions! functions linked)
    {:catalogue catalogue :functions linked :target tw-json-target
     :added-declarations (count additions) :added-functions (- (count linked) (count functions))}))

(defn- tw-profile! [profile key elapsed-ms steps failed?]
  ;; Bounded scalar telemetry only. No guest worlds, IO values, exceptions or
  ;; closures retained; inclusive nested times/steps must NEVER be summed.
  (swap! profile
    (fn [p]
      (let [key (if (or (contains? p key) (< (count (dissoc p :other)) 63)) key :other)
            old (get p key {:calls 0 :failures 0 :inclusive-ms 0.0 :max-ms 0.0 :completed-guest-steps 0})]
        (assoc p key (-> old (update :calls inc) (update :failures + (if failed? 1 0))
                         (update :inclusive-ms + elapsed-ms) (update :max-ms max elapsed-ms)
                         (update :completed-guest-steps + (or steps 0))))))))
(defn- tw-profile-call [profile key world f result-world]
  (let [started (System/nanoTime)]
    (try
      (let [result (f)]
        (tw-profile! profile key (/ (- (System/nanoTime) started) 1e6)
                     (- (get-in (result-world result) [:stats :steps]) (get-in world [:stats :steps])) false)
        result)
      (catch Throwable e
        (tw-profile! profile key (/ (- (System/nanoTime) started) 1e6) nil true)
        (throw e)))))
(defn- tw-profile-binding [binding profile]
  (assoc binding :handler
    (fn [context world args]
      (let [invoke (:invoke context)
            context (assoc context :invoke
                      (fn [w target arguments]
                        (tw-profile-call profile [:eval-helper target] w #(invoke w target arguments) first)))]
        (tw-profile-call profile :eval-const world #((:handler binding) context world args) first)))))

(defn prepare-full-init-shared-witness
  "PREPARATION ONLY, on a fresh assemble-full-init-only result. Link additions,
   finish closures, THEN capture exact catalogue/functions in new evalConst cap.
   Preserve all other binding objects, source, roots and guest world fields.
   No guest instructions, initializers, finalizer or kernel association execute.
   Load the two existing defs-only helper scripts before invoking this function."
  [assembled]
  (tw-check (= :assembled-only (:status assembled)) "Expected fresh assembled-only result")
  (tw-assembly-preflight! assembled)
  (let [world (:world assembled) source (:source assembled)
        session (:session assembled) functions (:functions session) bindings (:bindings session)
        phases (atom []) profile (atom {})
        stage2 (resolve 'prepare-ir-witness) stage3 (resolve 'prepare-shared-names-witness)]
    (tw-check (and stage2 stage3) "Load both witness preparation helper scripts first")
    (tw-check (and (= :done (:status world)) (empty? (:frames world)) (nil? (:host-request world))) "Assembly world must be idle")
    (tw-check (and source (false? @(:closed source)) (identical? source (get-in assembled [:loaded :source]))) "Expected original open source")
    (tw-check (identical? functions (:functions world)) "Assembly/session executable identity mismatch")
    (tw-check (empty? (:kernel-environments world)) "Expected assembly without checking association")
    (tw-check (every? tw-m/ref? [(:state assembled) (:imports assembled)]) "Missing owned assembly roots")
    (let [s1 (tw-measure phases :json-additive #(tw-stage-json (:catalogue assembled) functions bindings))
          s2 (tw-measure phases :typed-additive #(stage2 (:catalogue s1) (:functions s1) bindings))
          s3 (tw-measure phases :shared-names-additive #(stage3 (:catalogue s2) (:functions s2) bindings))
          catalogue (:catalogue s3) target (:target s3)
          lower #(if (contains? bindings (some-> % :ir :extern tw-abi/symbol-for))
                   (tw-raw/lower bindings %) (tw-abi/lower-deferred-catalogue catalogue %))
          linked (tw-measure phases :complete-actual-bodies
                   #(tw-prep/complete-functions catalogue (:functions s3) [target tw-exporter] lower))
          _ (tw-preserved-functions! functions linked)
          ;; Only NOW bind final authority; a stale catalogue causes the actual
          ;; evalConst profile check to fail, even if helper code was loaded.
          binding (tw-measure phases :capture-final-eval-capability
                    #(tw-eval/make-binding tw-exporter {:witness target :witness-format :typed-ir
                                                       :catalogue catalogue :trusted-functions linked
                                                       :research-traps? true}))
          _ (tw-check (= (:signature binding) (get-in bindings ["lean_eval_const" :signature])) "evalConst ABI drift")
          new-bindings (assoc bindings "lean_eval_const" (tw-profile-binding binding profile))
          new-session (tw-measure phases :open-mutable-session
                        #(tw-raw/open-functions linked new-bindings {:backend :mutable :fuel 20000000}))]
      (doseq [[symbol original] bindings :when (not= symbol "lean_eval_const")]
        (tw-check (identical? original (get new-bindings symbol)) "Preparation changed another capability"))
      {:status :typed-witness-prepared :world (assoc world :functions linked)
       :state (:state assembled) :imports (:imports assembled) :source source
       :loaded (update (:loaded assembled) :world assoc :functions linked)
       :catalogue catalogue :session new-session :kernel-helpers (:kernel-helpers assembled)
       :kernel-policy (:kernel-policy assembled) :profile profile :start-claimed? (atom false)
       :summary {:scope :full-init-witness-preparation-only :phases @phases
                 :functions-before (count functions) :functions-after (count linked)
                 :stage-additions (mapv #(select-keys % [:added-declarations :added-functions]) [s1 s2 s3])
                 :witness target :format :typed-ir :artifacts full-init-witness-artifacts
                 :original-functions-preserved true :other-capabilities-preserved true
                 :guest-steps-delta 0 :finalizer-executed false :strict-association false}})))

(defn- tw-run-one-slice [session world source profile continue-claimed?]
  (let [started (System/nanoTime) before (tw-heap) steps (get-in world [:stats :steps])]
    (try
      (let [called (tw-raw/continue session world)]
        {:outcome :guest-io-returned :world (:state called) :session (:session called) :value (:value called)
         :source source :profile profile
         :summary {:elapsed-ms (/ (- (System/nanoTime) started) 1e6)
                   :guest-steps (- (get-in called [:state :stats :steps]) steps)
                   :heap-before before :heap-after (tw-heap) :profile @profile
                   :strict-association false :io-result-unconsumed true}})
      (catch Throwable e
        (let [data (ex-data e) checkpoint (:checkpoint data)
              outer? (and (= "Raw runtime instruction budget exhausted" (.getMessage e))
                          (= :paused (:status checkpoint)) (empty? (:host-boundaries data)))
              outcome (cond outer? :paused-outer (seq (:host-boundaries data)) :blocked-nested :else :failed)]
          {:outcome outcome :world checkpoint :session (:checkpoint-session data) :source source :profile profile
           :continue-claimed? (when outer? continue-claimed?)
           :failure e ;; Keep ALL named alternative checkpoints; never print this whole map.
           :summary {:elapsed-ms (/ (- (System/nanoTime) started) 1e6)
                     :guest-steps (when checkpoint (- (get-in checkpoint [:stats :steps]) steps))
                     :heap-before before :heap-after (tw-heap) :profile @profile
                     :host-boundary-depth (count (:host-boundaries data))
                     :strict-association false :automatic-retry false}})))))

(defn start-full-init-finalizer-slice
  "EXPLICIT guest work, once per prepared object. No automatic loop or checking.
   Default 1M instructions; max20M. Guard wall/RSS externally. Ownership of
   :state/:imports transfers in this branch. Prepared input is a diagnostic fork,
   not an additional owner in the returned branch. :blocked-nested is terminal
   for this draft: JVM host continuations have unwound and cannot be resumed."
  [prepared {:keys [backend fuel] :or {backend :mutable fuel 1000000} :as options}]
  (tw-check (every? #{:backend :fuel} (keys options)) "Unknown slice option")
  (tw-check (= :typed-witness-prepared (:status prepared)) "Expected typed witness preparation")
  (tw-check (contains? #{:mutable :jvm} backend) "Choose measured backend explicitly")
  (tw-check (and (integer? fuel) (<= 1 fuel 20000000)) "Slice fuel must be1..20M")
  (tw-assembly-preflight! prepared)
  (tw-check (instance? clojure.lang.Atom (:start-claimed? prepared)) "Missing start claim token")
  (let [session (:session prepared)
        session (tw-raw/open-functions (:functions session) (:bindings session)
                  {:backend backend :fuel fuel :compile-threshold 64})
        target ["str" ["str" ["anonymous"] "ModuleDataTransport"] "finalizeTransport"]
        _ (tw-check (contains? (:functions session) target) "Finalizer missing from prepared functions")
        world (tw-m/start (:world prepared) target [(:state prepared) (:imports prepared) tw-m/erased])
        continue-claimed? (atom false)
        _ (tw-check (compare-and-set! (:start-claimed? prepared) false true) "Finalizer start already claimed; do not replay IO")]
    (tw-run-one-slice session world (:source prepared) (:profile prepared) continue-claimed?)))

(defn continue-full-init-finalizer-slice
  "One EXPLICIT continuation of a proven top-level fuel pause, never a nested
   helper or host-call checkpoint. Matching session/cache/bindings preserved.
   Input is single-use to guard accidental duplicate continuation/effects."
  [paused fuel]
  (tw-check (= :paused-outer (:outcome paused)) "Only a top-level fuel pause is continuable")
  (tw-check (and (integer? fuel) (<= 1 fuel 20000000)) "Slice fuel must be1..20M")
  (tw-check (false? @(:closed (:source paused))) "Source already closed")
  (tw-check (= :paused (get-in paused [:world :status])) "Expected actual paused world")
  (tw-check (identical? (get-in paused [:session :functions]) (get-in paused [:world :functions])) "Checkpoint/session executable mismatch")
  (tw-check (instance? clojure.lang.Atom (:continue-claimed? paused)) "Missing continuation claim token")
  (let [session (assoc (:session paused) :fuel fuel)
        continue-claimed? (atom false)]
    (tw-check (compare-and-set! (:continue-claimed? paused) false true) "Continuation already claimed; do not replay effects")
    ;; No generic snapshot serialization: source/resources and code identities are
    ;; intentionally live capabilities, unsupported by bootstrap-archive.
    (tw-run-one-slice session (:world paused) (:source paused) (:profile paused) continue-claimed?)))
