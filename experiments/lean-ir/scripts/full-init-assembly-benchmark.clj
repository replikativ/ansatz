;; DRAFT: load from experiments/lean-ir; definitions only, no guest work on load.
;; Pass a FRESH, still-open result of assemble-full-init-only. This never calls
;; finalizeTransport, verifies constants, creates an association, or closes source.
(require '[prototype.machine :as bench-m]
         '[prototype.raw-interop :as bench-raw]
         '[prototype.lazy-runtime :as bench-lazy]
         '[prototype.module-import :as bench-import])

(defn assembly-benchmark-check [condition message]
  (when-not condition (throw (ex-info message {:scope :full-init-assembly-benchmark}))))

(defn assembly-benchmark-heap []
  (let [runtime (Runtime/getRuntime)]
    {:used (- (.totalMemory runtime) (.freeMemory runtime))
     :committed (.totalMemory runtime) :maximum (.maxMemory runtime)}))

(defn assembly-benchmark-source-cache [source]
  (let [cache (:cache source)]
    (locking cache
      {:policy :preserve-shared-derived-cache :entries (.size ^java.util.Map cache)
       :limit (:cache-limit source) :shared-between-forks true
       :operating-system-file-cache :uncontrolled})))

(defn- assembly-map-delta [before after]
  {:changed (into {} (filter (fn [[key value]] (not= value (get before key ::absent)))) after)
   :removed (into [] (keep (fn [[key _]] (when-not (contains? after key) key))) before)})

(defn- assembly-local-topology [base result]
  ;; Never recursively hydrate native ModuleData: immutable source-range edges
  ;; remain Ref values. Compare exact local node maps/RCs, global differences,
  ;; roots and allocator identity against the SAME initial immutable world.
  (let [world (:world result)]
    {:roots [(:state result) (:imports result)]
     :next-id (:next-id world)
     :heap (assembly-map-delta (:heap base) (:heap world))
     :globals (assembly-map-delta (:globals base) (:globals world))
     :initialized-modules (:initialized-modules world)
     :initializing? (:initializing? world)
     :initialization-scope (:initialization-scope world)}))

(defn- assembly-benchmark-one
  [loaded original-session source backend cache label expected-topology gc-between?]
  (let [base (:world loaded)
        functions (:functions base)
        bindings (:bindings original-session)
        session (atom (bench-raw/open-functions functions bindings
                         (cond-> {:backend backend :fuel 20000000}
                           (= :jvm backend) (assoc :compile-threshold 64 :cache cache))))
        last-helper-boundary (atom nil)
        owned (atom nil)]
    (when gc-between? (System/gc))
    (let [heap-before (assembly-benchmark-heap)
          cache-before (count @cache)
          source-before (assembly-benchmark-source-cache source)
          invoke (fn [world target arguments]
                   (reset! last-helper-boundary {:phase :entry :world world :session @session :target target})
                   (let [called (bench-raw/call @session world target arguments)]
                     (reset! session (:session called))
                     (reset! last-helper-boundary {:phase :returned :world (:state called)
                                                  :session @session :value (:value called) :target target})
                     [(:state called) (:value called)]))]
      (try
        (let [_ (do (println {:assembly-benchmark-run label :phase :start}) (flush))
              started (System/nanoTime)
              result (bench-import/assemble loaded invoke {:assembly :bulk})
              elapsed-ms (/ (- (System/nanoTime) started) 1e6)
              world (:world result)
              _ (reset! owned {:world world :session @session :state (:state result) :imports (:imports result)})
              heap-after (assembly-benchmark-heap)
              steps (- (get-in world [:stats :steps]) (get-in base [:stats :steps]))
              _ (assembly-benchmark-check (identical? functions (:functions world)) "Assembly changed executable map")
              _ (assembly-benchmark-check (identical? functions (:functions @session)) "Assembly changed session executable map")
              _ (assembly-benchmark-check (identical? bindings (:bindings @session)) "Assembly changed host capability map")
              _ (assembly-benchmark-check (empty? (:kernel-environments world)) "Assembly unexpectedly acquired checking authority")
              topology (assembly-local-topology base result)
              _ (when expected-topology
                  (assembly-benchmark-check (= (:topology expected-topology) topology)
                                            "Assembly tiers differ in exact local/root topology")
                  (assembly-benchmark-check (= (:guest-steps expected-topology) steps)
                                            "Assembly tiers differ in exact guest step count"))
              record {:run label :backend backend :compile-threshold (when (= backend :jvm) 64)
                      :fuel-per-call 20000000 :elapsed-ms elapsed-ms :guest-steps steps
                      :root-ids (mapv :id (:roots topology)) :next-id (:next-id topology)
                      :local-topology-equal? (when expected-topology true)
                      :same-functions-and-bindings true
                      :local-heap-objects (count (:heap world))
                      :changed-local-nodes (count (get-in topology [:heap :changed]))
                      :removed-local-nodes (count (get-in topology [:heap :removed]))
                      :changed-globals (count (get-in topology [:globals :changed]))
                      :source-cache-before source-before
                      :source-cache-after (assembly-benchmark-source-cache source)
                      :heap-before heap-before :heap-after-assembly heap-after
                      :host-gc-between-runs-requested gc-between?
                      :code-cache-before cache-before :code-cache-after (count @cache)
                      :program (when (= :jvm backend) (bench-lazy/summary (:program @session)))}
              ;; Update recovery ownership after EACH successful release. No
              ;; cleanup guesses or automatic source closure on an exception.
              world (bench-m/release world (:state result) 1)
              _ (swap! owned #(-> % (assoc :world world) (dissoc :state)))
              world (bench-m/release world (:imports result) 1)
              _ (swap! owned #(-> % (assoc :world world) (dissoc :imports)))
              remaining (count (:heap world))]
          (reset! last-helper-boundary nil)
          (reset! owned nil)
          (println {:assembly-benchmark-run label :phase :released :elapsed-ms elapsed-ms
                    :guest-steps steps :code-cache-count (count @cache)})
          (flush)
          ;; Released branch world is discarded on return; only its local delta
          ;; is retained temporarily for exact comparison, not the whole world.
          (when gc-between? (System/gc))
          {:comparison {:topology topology :guest-steps steps}
           :record (assoc record :after-release-local-heap-objects remaining
                                 :heap-after-release (assembly-benchmark-heap)
                                 :released-owned-roots 2 :source-left-open true)})
        (catch Throwable failure
          (throw (ex-info "Full Init assembly benchmark branch failed"
                         (assoc (ex-data failure)
                                :scope :full-init-assembly-benchmark :run label
                                :source source :source-entry loaded
                                :last-helper-boundary @last-helper-boundary
                                :owned-branch @owned :benchmark-session @session)
                         failure)))))))

(defn benchmark-full-init-assembly
  "Sequential mutable, JVM64 code-cold and JVM64 code-warm forks from the same
   loaded idle world/functions/bindings/source. Successful branches release both
   owned roots and discard their worlds before the next branch. Input assembly's
   own roots are untouched. Source cache and OS cache are shared, NOT code-cold;
   cache occupancy is reported, so this is no isolated disk/cache benchmark.
   Use the external process-group RSS/system/time guard. The20M guest budget is
   per helper call and does not bound wall time, JIT compilation, or code cache.
   Failures retain named owned/checkpoint alternatives; never blindly retry them."
  ([assembled] (benchmark-full-init-assembly assembled {:gc-between? true}))
  ([assembled {:keys [gc-between?] :as options}]
   (assembly-benchmark-check (= #{:gc-between?} (set (keys options))) "Unknown assembly benchmark options")
   (assembly-benchmark-check (boolean? gc-between?) "gc-between? must be an explicit Bool")
   (assembly-benchmark-check (= :assembled-only (:status assembled)) "Expected assembly-only preparation result")
   (let [loaded (:loaded assembled) source (:source assembled)
         base (:world loaded) original-session (:session assembled)
         cache (bench-lazy/code-cache)]
     (assembly-benchmark-check (= :done (:status base)) "Expected idle loaded bootstrap world")
     (assembly-benchmark-check (and source (false? @(:closed source))) "Verified source must remain open")
     (assembly-benchmark-check (identical? source (:source loaded)) "Different verified source identity")
     (assembly-benchmark-check (and (= 1 (count (:native-imports base)))
                                    (identical? source (first (:native-imports base)))) "Different world source identity")
     (assembly-benchmark-check (identical? (:functions base) (:functions original-session)) "Different prepared executable map")
     (assembly-benchmark-check (empty? (:kernel-environments base)) "Expected unassociated assembly-only world")
     (loop [runs [[:mutable :mutable] [:jvm-cold :jvm] [:jvm-warm :jvm]]
            expected nil records []]
       (if-let [[label backend] (first runs)]
         (let [result (assembly-benchmark-one loaded original-session source backend cache label expected gc-between?)]
           (recur (next runs) (or expected (:comparison result)) (conj records (:record result))))
         {:scope :full-init-assembly-benchmark :status :passed :runs records
          :source-cache-policy :preserve-shared-derived-cache :source-left-open true
          :comparison :exact-local-topology-root-ids-next-id-and-guest-step-delta
          :finalizer-executed false :strict-association false
          :limits ["Sequential fixed-order observation; code-cold is not source/OS/JVM-cold"
                   "Elapsed times cover assemble only; preparation and comparison/release/GC are excluded"
                   "Heap used includes live input assembly and temporary comparison deltas"
                   "No source-cache hit/miss telemetry or allocation profiler is installed"
                   "No full-Init finalizer or strict whole-map timing is inferred"]})))))
