(ns prototype.guarded-kernel-view
  "Private, bounded, full-value kernel lookup over captured store roots.
   This layer grants no artifact, checking, guest-association or replay authority.
   The trusted host retains Env descendants privately and brackets EVERY checker,
   helper and publication operation with guard!/with-view!: local Env lookups
   precede external lookup and cannot be revoked by an external closure."
  (:require [ansatz.export.storage :as storage]
            [prototype.kernel-projection-snapshot :as snapshot])
  (:import [ansatz.kernel Env Name ConstantInfo]
           [java.util UUID]))

(def root-fields
  #{:env-root :env-count :names-root :names-count :levels-root :levels-count
    :exprs-root :exprs-count :dag-storage? :quot-enabled})
(def ^:private evidence-fields
  #{:declarations :shell-items :expr-nodes :expr-edges :expr-depth :raw-bytes
    :name-nodes :name-chars :name-depth :level-nodes :level-depth :level-visits})
(deftype View [holder])
(defn- require! [condition message data]
  (when-not condition (throw (ex-info message data))))
(defn- holder [view]
  (require! (instance? View view) "Actual guarded kernel View required" {})
  (.-holder ^View view))
(defn- live! [cell]
  (let [state @cell]
    (require! (= :open (:status state)) "Guarded kernel view is closed or failed" {})
    (require! (identical? (:thread state) (Thread/currentThread))
              "Guarded kernel view belongs to another thread" {})
    (try ((:lease! state))
         (catch Throwable cause
           (swap! cell assoc :status :failed)
           (throw cause)))
    state))
(defn- fail-view! [cell cause]
  (swap! cell #(if (= :open (:status %)) (assoc % :status :failed) %))
  (throw cause))
(defn- validate-ledger! [state]
  (doseq [[_ segment] (:ledger state)] (snapshot/validate-segment-values segment)))
(defn guard!
  "Validate lifecycle/borrowed-source lease and ALL historical materialized values.
   No new snapshots are taken over changed values. Does not consult Env.lookup."
  [view]
  (let [cell (holder view) state (live! cell)]
    (try (validate-ledger! state) (live! cell) view
         (catch Throwable cause (fail-view! cell cause)))))
(defn- positive-limits? [m expected-keys]
  (and (map? m) (= expected-keys (set (keys m)))
       (every? #(and (integer? %) (<= 1 % Long/MAX_VALUE)) (vals m))))
(defn- domain! [domain]
  (require! (and (set? domain) (<= 1 (count domain) 10000)
                 (every? #(instance? Name %) domain)) "Exact bounded typed Name domain required" {})
  ;; The persistent store comparator uses display keys. For this fixed domain,
  ;; reject every collision instead of treating a rendered Name as its identity.
  (doseq [^Name name domain]
    (loop [^Name current name depth 0 chars 0]
      (require! (and (<= depth 256) (<= chars 4096)) "Typed Name domain exceeds bounds" {})
      (when current
        (recur (.prefix current) (inc depth) (+ chars (if (.str current) (count (.str current)) 0))))))
  (require! (= (count domain) (count (set (map str domain))))
            "Typed Name domain has display-key collisions" {})
  domain)
(defn- charge-usage [state usage]
  (require! (and (map? usage) (every? evidence-fields (keys usage))
                 (every? #(and (integer? %) (<= 0 %)) (vals usage))) "Invalid bounded resolver usage" {})
  (let [total (merge-with +' (:usage state) usage)]
    (doseq [[key amount] total]
      (require! (<= amount (get (:max-total-usage state) key))
                "Guarded kernel view total evidence budget exceeded" {:limit key}))
    total))
(defn- lookup! [cell name]
  (let [state (live! cell)]
    (require! (instance? Name name) "Typed Java Name lookup required" {})
    (try
      (require! (not (:hydrating state)) "Reentrant guarded kernel hydration is unsupported" {})
      (if-not (contains? (:domain state) name) nil
        (if-let [ci (get (:memo state) name)]
          (do (snapshot/validate-segment-values (get (:ledger state) name))
              (live! cell) ci)
          (do
            (require! (< (count (:memo state)) (:max-materialized state))
                      "Guarded kernel materialization count exceeded" {})
            (swap! cell assoc :hydrating name)
            (let [result ((:resolve! state) name (:evidence-limits state))
                  constants (:constants result)
                  _ (require! (and (map? constants) (= #{name} (set (keys constants))))
                              "Bounded source is missing the exact typed domain member" {:name name})
                  ^ConstantInfo ci (get constants name)
                  _ (require! (and (instance? ConstantInfo ci) (= name (.name ci)))
                              "Bounded source returned the wrong typed Name" {:name name})
                  usage (charge-usage state (:usage result))
                  segment (snapshot/snapshot-segment {name ci})]
              ;; Capture BEFORE the host's semantic comparison, and refuse any
              ;; mutation during it. Its return value is never an admission flag.
              ((:authenticate-ci! state) name ci)
              (snapshot/validate-segment-values segment)
              (live! cell)
              (swap! cell #(-> % (assoc-in [:memo name] ci) (assoc-in [:ledger name] segment)
                               (assoc :usage usage :hydrating nil)))
              ci))))
      (catch Throwable cause (fail-view! cell cause)))))
(defn ^:no-doc open-resolver-view!
  "Internal pure backing-resolver seam for tests/adapters, NOT artifact authority.
   RESOLVE! returns storage/full-ci-evidence's {:constants :usage} for ONE Name.
   The trusted caller must supply bounded raw evidence, not ordinary Env.lookup."
  [{:keys [domain quot-enabled? lease! authenticate-ci! evidence-limits max-materialized max-total-usage resolve!]}]
  (domain! domain)
  (require! (and (boolean? quot-enabled?) (fn? lease!) (fn? authenticate-ci!) (fn? resolve!)
                 (positive-limits? evidence-limits evidence-fields)
                 (every? #(<= (get evidence-limits %) 256) [:expr-depth :name-depth :level-depth])
                 (integer? max-materialized) (<= 1 max-materialized (count domain))
                 (positive-limits? max-total-usage evidence-fields))
            "Explicit bounded guarded kernel view policy required" {})
  (lease!)
  (let [cell (atom {:status :open :thread (Thread/currentThread) :domain domain
                    :lease! lease! :authenticate-ci! authenticate-ci! :resolve! resolve!
                    :evidence-limits evidence-limits :max-materialized max-materialized
                    :max-total-usage max-total-usage :memo {} :ledger {} :usage {}})
        external (fn [name] (lookup! cell name))
        seed (if quot-enabled? (.enableQuot (Env.)) (Env.))
        environment (.withExternalLookupUncached ^Env seed external (int (count domain)))]
    (swap! cell assoc :environment environment)
    (View. cell)))
(defn open-view!
  "Capture a borrowed actual store branch once. EXPECTED-ROOTS must be the exact
   root/count/DAG/quot metadata from the caller's authenticated paired evidence.
   No branch-head reread, ordinary lazy hydration, store close or proof replay.
   Public maps/digests do not grant authority; authenticate-ci! must independently
   compare every actual materialized CI to the accepted guest/producer evidence."
  [store-map branch {:keys [expected-roots domain] :as policy}]
  (require! (fn? (:lease! policy)) "Borrowed source/store lease guard required" {})
  ((:lease! policy))
  (domain! domain)
  (require! (and (map? store-map) (:store store-map) (:storage store-map)
                 (map? expected-roots) (= root-fields (set (keys expected-roots)))
                 (every? #(instance? UUID (get expected-roots %)) [:env-root :names-root :levels-root :exprs-root])
                 (every? #(and (integer? (get expected-roots %)) (pos? (get expected-roots %)))
                         [:env-count :names-count :levels-count :exprs-count])
                 (true? (:dag-storage? expected-roots)) (boolean? (:quot-enabled expected-roots)))
            "Actual store and complete captured PSS root evidence required" {})
  (let [loader (#'storage/branch-loader store-map branch :value-policy :full)
        metadata (select-keys (:branch-meta loader) root-fields)]
    (require! (= expected-roots metadata) "Captured store branch roots differ from expected evidence" {})
    (require! (= (count domain) (:env-count metadata)) "Captured store domain count differs" {})
    (require! (:evidence-sources loader) "Captured store lacks bounded raw DAG evidence" {})
    (let [backing (storage/load-env store-map branch :loader loader :value-policy :full)
          view (open-resolver-view!
                 (assoc policy :quot-enabled? (:quot-enabled metadata)
                        :resolve! (fn [name limits] (storage/full-ci-evidence backing [name] limits))))]
      (guard! view)
      view)))
(defn with-view!
  "Borrow the private Env during one trusted serialized operation. Validate lease
   and historical values before AND after, including local-only checker calls.
   Keep every returned Env/descendant private and bracket later use the same way."
  [view f]
  (guard! view)
  (try
    (let [result (f (:environment @(holder view)))]
      (guard! view)
      result)
    (catch Throwable cause
      (try (guard! view)
           (catch Throwable guard-cause
             (when-not (identical? cause guard-cause) (.addSuppressed cause guard-cause))))
      (throw cause))))
(defn inspect!
  "Guarded metadata only; never exposes the backing resolver, memo or ledger."
  [view]
  (guard! view)
  (let [state @(holder view)]
    {:domain-count (count (:domain state)) :materialized-count (count (:memo state))
     :snapshot-count (count (:ledger state)) :usage (:usage state)}))
(defn close!
  "Revoke first, drop all retained store/CI/snapshot closures. Borrowed store and
   producer/source leases remain the owning host's responsibility. Idempotent."
  [view]
  (let [cell (holder view) state @cell]
    (when-not (= :closed (:status state))
      (require! (identical? (:thread state) (Thread/currentThread)) "Guarded kernel view belongs to another thread" {})
      (reset! cell {:status :closed})))
  nil)
