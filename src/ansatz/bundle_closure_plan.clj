(ns ansatz.bundle-closure-plan
  "Bounded pure role-local metadata closure requests. No native execution or authority."
  (:require [ansatz.bundle-metadata :as metadata])
  (:import [clojure.lang PersistentVector PersistentArrayMap PersistentHashMap]))

(def ^:private roles [:init :lex :sizeof])
(def ^:private companion-roles [:attrs :matchers :instances])
(def ^:private planner-options {:metadata-profile "ansatz-global-companions/2"})
(def ^:private cap-keys
  #{:items :scalar-bytes :depth :rounds :observations :roots :reasons :edges :names})
(deftype ^:private PlanState [capture limits value])

(defn- fail [reason data]
  (throw (ex-info "Bundle closure planning refused"
                  (assoc data :type ::planning-refused :reason reason))))
(defn- vector! [x]
  (when-not (identical? PersistentVector (class x)) (fail :unsupported-vector {})) x)
(defn- map! [x]
  (when-not (or (identical? PersistentArrayMap (class x))
                (identical? PersistentHashMap (class x)))
    (fail :unsupported-map {})) x)
(defn- keys! [x expected]
  (map! x)
  (when-not (and (= (count x) (count expected))
                 (every? #(and (keyword? %) (contains? expected %)) (keys x)))
    (fail :unexpected-fields {})) x)
(defn- sha? [x] (and (string? x) (boolean (re-matches #"[0-9a-f]{64}" x))))
(defn- integer-value? [x]
  (or (instance? Long x) (instance? Integer x) (instance? Short x) (instance? Byte x)))
(defn- charge [usage limits key amount]
  (let [total (+' (get usage key 0) amount)]
    (when (> total (get limits key))
      (fail :limit {:limit key :maximum (get limits key) :actual total}))
    (assoc usage key total)))

(defn- data-budget
  "Only standard finite data. Count child slots before walking or hashing them."
  [root usage limits]
  (loop [pending [[root 1]] usage usage]
    (if (empty? pending) usage
        (let [[x depth] (peek pending) pending (pop pending)]
          (when (> depth (:depth limits))
            (fail :limit {:limit :depth :maximum (:depth limits) :actual depth}))
          (cond
            (string? x) (recur pending (charge usage limits :scalar-bytes (*' 2 (.length ^String x))))
            (keyword? x) (recur pending (charge usage limits :scalar-bytes
                                                (*' 2 (+ (count (name x)) (count (namespace x))))))
            (or (nil? x) (boolean? x) (integer-value? x)) (recur pending usage)
            (identical? PersistentVector (class x))
            (let [usage (charge usage limits :items (count x))]
              (recur (reduce #(conj %1 [%2 (inc depth)]) pending x) usage))
            (or (identical? PersistentArrayMap (class x)) (identical? PersistentHashMap (class x)))
            (let [usage (charge usage limits :items (*' 2 (count x)))]
              (recur (reduce-kv (fn [p k v] (conj p [k (inc depth)] [v (inc depth)])) pending x) usage))
            :else (fail :unsupported-data {}))))))

(defn- descriptor! [row]
  (keys! row #{:text :name})
  (let [{:keys [text name]} row]
    (vector! name)
    (when-not (and (string? text) (seq text) (seq name)
                   (not (.startsWith ^String text "--")) (neg? (.indexOf ^String text (int 0))))
      (fail :invalid-native-descriptor {}))
    (doseq [segment name]
      (vector! segment)
      (when-not (= 2 (count segment)) (fail :invalid-native-descriptor {}))
      (let [[tag value] segment]
        (when-not
         (case tag
           "str" (string? value)
           "num" (and (string? value) (<= (count value) 19)
                      (boolean (re-matches #"0|[1-9][0-9]*" value))
                      (or (< (count value) 19) (not (pos? (compare value "9223372036854775807")))))
           false)
          (fail :invalid-native-descriptor {}))))
    row))

(defn- native-index [rows]
  (vector! rows)
  (reduce (fn [{:keys [texts identities]} row]
            (descriptor! row)
            (when (or (contains? texts (:text row)) (contains? identities (:name row)))
              (fail :ambiguous-native-descriptor {}))
            {:texts (assoc texts (:text row) row) :identities (conj identities (:name row))})
          {:texts {} :identities #{}} rows))
(defn- names! [values index]
  (vector! values)
  (reduce (fn [seen text]
            (when-not (and (string? text) (contains? index text)) (fail :missing-native-descriptor {}))
            (when (contains? seen text) (fail :duplicate-name {}))
            (conj seen text)) #{} values))

(defn- reference-slots [companions]
  (reduce + 0 (for [role companion-roles row (get companions role)]
                (case role :attrs (case (:kind row) "csimp" 2 "impl" 1
                                         "unfold-thms" (count (vector! (:theorems row))) 0)
                      :instances 1 :matchers 0))))

(defn- initial [captured limits usage]
  (keys! captured #{:capture-id :native-names :companions :original-roots})
  (when-not (sha? (:capture-id captured)) (fail :invalid-capture {}))
  (keys! (:original-roots captured) (set roles))
  (keys! (:companions captured) (set companion-roles))
  (let [index (:texts (native-index (:native-names captured)))
        originals (:original-roots captured) companions (:companions captured)
        _ (doseq [role companion-roles] (vector! (get companions role)))
        slots (reference-slots companions)
        usage (charge usage limits :edges slots)]
    (doseq [role roles]
      (when-not (seq (get originals role)) (fail :empty-original-roots {:role role}))
      (names! (get originals role) index))
    ;; Existing planner validates each complete corpus, even unselected rows.
    ;; Resolve every GLOBAL reference; matcher binder annotations are excluded.
    (doseq [role companion-roles]
      (vector! (get companions role))
      (doseq [row (get companions role)]
        (when-not (contains? index (:name row)) (fail :missing-native-descriptor {})))
      (doseq [edge (metadata/references role (get companions role) planner-options)]
        (when-not (contains? index (:target edge)) (fail :missing-native-descriptor {}))))
    {:index index :originals originals :companions companions :reference-slots slots :usage usage :round 0
     :effective originals :derived (zipmap roles (repeat [])) :reasons (zipmap roles (repeat {}))
     :reason-addresses (zipmap roles (repeat {}))
     :snapshots {} :awaiting roles :status :needs-export}))

(defn- issue [value limits]
  (let [usage (charge (:usage value) limits :roots
                      (reduce + 0 (map #(count (get (:effective value) %)) (:awaiting value))))
        requests (mapv
                  (fn [role]
                    (let [original-indices (zipmap (get (:originals value) role) (range))]
                    {:role role :round (:round value)
                     :roots (mapv (fn [text]
                                    (assoc (get (:index value) text) :provenance
                                           (if-let [original-index (get original-indices text)]
                                             [{:origin :configured :original-index original-index}]
                                             (get-in value [:reasons role text]))))
                                  (get (:effective value) role))})) (:awaiting value))]
    (assoc value :requests requests :usage usage)))

(defn- observe [captured value observations limits]
  (keys! observations (set (:awaiting value)))
  (let [usage (data-budget observations (:usage value) limits)
        usage (charge usage limits :observations (count observations))
        _ (doseq [row (vals observations)] (keys! row #{:capture-id :roots :names :raw-sha256}) (vector! (:names row)))
        usage (charge usage limits :names (reduce + 0 (map #(count (:names %)) (vals observations))))
        snapshots
        (reduce (fn [snapshots role]
                  (let [row (get observations role)]
                    (keys! row #{:capture-id :roots :names :raw-sha256})
                    (when-not (and (= (:capture-id captured) (:capture-id row))
                                   (= (get (:effective value) role) (:roots row)) (sha? (:raw-sha256 row)))
                      (fail :stale-observation {:role role}))
                    (let [names (names! (:names row) (:index value))]
                      (when-not (every? names (:roots row)) (fail :requested-root-omitted {:role role}))
                      (when-not (every? names (get-in snapshots [role :names]))
                        (fail :export-closure-shrank {:role role}))
                      (assoc snapshots role {:names names :raw-sha256 (:raw-sha256 row)
                                             :round (:round value) :ordered-names (:names row)
                                             :requested (:roots row)})))) (:snapshots value) (:awaiting value))]
    (assoc value :snapshots snapshots :usage usage)))

(defn- advance [value limits]
  (let [usage (charge (:usage value) limits :edges (*' 3 (:reference-slots value)))
        plans (into {} (map (fn [role]
                            [role (metadata/plan-role role (:companions value)
                                                      (get-in value [:snapshots role :names]) planner-options)]) roles))
        result
        (reduce
         (fn [acc role]
           (let [plan (get plans role) names (get-in value [:snapshots role :names])
                 additions (:missing-roots plan)
                 effective (into (get-in acc [:effective role]) additions)
                 derived (into (get-in acc [:derived role]) additions)
                 derived-set (set derived)
                 indices (into {} (map (fn [cr]
                                        [cr (into [] (keep-indexed (fn [i row] (when (contains? names (:name row)) i)))
                                                  (get-in value [:companions cr]))]) companion-roles))
                 reason-result
                 (reduce (fn [{:keys [reasons addresses usage] :as current} edge]
                           (let [target (:target edge)]
                             (if-not (contains? derived-set target) current
                                 (let [reason {:origin :metadata :kernel-role role :companion-role (:role edge)
                                               :global-row-index (nth (get indices (:role edge)) (:row-index edge))
                                               :selected-row-index (:row-index edge) :edge-kind (:kind edge)
                                               :source (:source edge) :target target}
                                       old (get reasons target [])
                                       address [(:role edge) (:global-row-index reason) (:kind edge)]]
                                   (if (contains? (get addresses target #{}) address)
                                     current
                                     {:usage (charge usage limits :reasons 1)
                                      :addresses (update addresses target (fnil conj #{}) address)
                                      :reasons (assoc reasons target (conj old (assoc reason :round (:round value))))})))))
                         {:reasons (get-in acc [:reasons role])
                          :addresses (get-in acc [:reason-addresses role]) :usage (:usage acc)} (:edges plan))]
           (-> acc (assoc-in [:effective role] effective) (assoc-in [:derived role] derived)
                 (assoc-in [:reasons role] (:reasons reason-result))
                 (assoc-in [:reason-addresses role] (:addresses reason-result))
                 (assoc :usage (:usage reason-result))))) (assoc value :usage usage) roles)
        result (assoc result :selection-provenance
                      (into {} (for [role roles]
                                 [role (into {} (for [cr companion-roles]
                                                  [cr (into [] (keep-indexed (fn [i row]
                                                                             (when (contains? (get-in value [:snapshots role :names]) (:name row)) i)))
                                                            (get-in value [:companions cr]))]))])))
        changed (filterv #(not= (get-in value [:effective %]) (get-in result [:effective %])) roles)]
    (if (empty? changed) (assoc result :awaiting [] :requests [] :status :closure-planned)
        (issue (assoc result :round (inc (:round value)) :awaiting changed) limits))))

(defn next-round
  "Pure deterministic closure transition over trusted materialized data.
   nil state + {} observations emits three initial requests. Awaiting states
   accept exactly requested roles. Reuse the IDENTICAL captured/limits objects.
   Observations: role -> {:capture-id sha :roots [opaque-native-text ...]
                         :names [actual-exported-native-text ...] :raw-sha256 sha}.
   Typed descriptors are {:text native-text :name [[\"str\" text]|[\"num\" decimal] ...]}.

   Limits require positive :items :scalar-bytes :depth :rounds :observations
   :roots :reasons :edges :names. Count/data limits apply before planner walks.
   Cumulative budgets belong to ONE IMMUTABLE STATE LINEAGE. Branches/retries
   reuse old state; their aggregate/native-invocation budget belongs to the host.
   This function establishes no native evidence authenticity or kernel judgment."
  [captured state observations limits]
  (keys! limits cap-keys)
  (when-not (and (every? #(and (integer-value? %) (pos? %)) (vals limits)) (<= (:depth limits) 256))
    (fail :explicit-finite-limits-required {}))
  (map! observations)
  (let [value
        (if (nil? state)
          (do (when (seq observations) (fail :initial-observations-forbidden {}))
              (let [usage (data-budget captured {} limits)
                    usage (charge usage limits :rounds 1)]
                (issue (initial captured limits usage) limits)))
          (do
            (when-not (instance? PlanState state) (fail :unsupported-state {}))
            (when-not (and (identical? captured (.-capture ^PlanState state))
                           (identical? limits (.-limits ^PlanState state)))
              (fail :different-lineage-inputs {}))
            (let [value (.-value ^PlanState state)]
              (when-not (= :needs-export (:status value)) (fail :terminal-state {}))
              (advance (observe captured (update value :usage charge limits :rounds 1) observations limits) limits))))]
    {:state (PlanState. captured limits value) :status (:status value) :requests (:requests value)
     :original-roots (:originals value) :derived-roots (:derived value)
     :effective-roots (:effective value) :selection-provenance (:selection-provenance value)
     :observed-kernel-closure
     (into {} (for [[role snapshot] (:snapshots value)]
                [role {:raw-sha256 (:raw-sha256 snapshot) :round (:round snapshot)
                       :names (filterv (complement (set (:requested snapshot))) (:ordered-names snapshot))}]))
     :usage (:usage value) :authority :none :promotion :not-performed
     :pending-gates #{:native-preflight :captured-producer :native-ci-binding :kernel-replay
                      :axiom-types :proof-assumptions :implemented-by :serialization}}))
