(ns prototype.heap-hint
  "Storage-shape hints ONLY, not deep immutability or checking authority.
   Cached roots/nodes are standard persistent maps with exact PersistentVector
   field storage. Existing COW already shares vector elements and metadata;
   this memo does not strengthen their semantics. No machine dependency."
  (:import [java.lang.ref WeakReference] [java.util HashMap ArrayList]
           [clojure.lang PersistentHashMap PersistentArrayMap PersistentVector]))

(def ^:private entry-limit 256)
(defonce ^:private hints {:buckets (HashMap.) :count (atom 0)})
(def ^:private map-classes #{PersistentHashMap PersistentArrayMap})
(defn standard-map? [value]
  (and value (contains? map-classes (class value))))

(defn storage-node? [node]
  (and (standard-map? node) (= PersistentVector (class (:fields node)))))

(defn clear-cache! []
  (locking hints (.clear ^HashMap (:buckets hints)) (reset! (:count hints) 0)) nil)
(defn cache-summary []
  (locking hints {:entries @(:count hints) :limit entry-limit}))
(defn proof
  "Return a scalar proof only for this exact previously attested heap identity."
  [heap]
  (when (standard-map? heap)
    (locking hints
      (when-let [^ArrayList bucket (.get ^HashMap (:buckets hints) (System/identityHashCode heap))]
        (some (fn [[^WeakReference reference long-keys?]]
                (when (identical? heap (.get reference)) {:long-keys? long-keys?})) bucket)))))
(defn remember!
  "INTERNAL: caller has validated every node, or derived its proof from an
   attested immutable base plus ALL changed frozen nodes. Stores no strong root."
  [heap long-keys?]
  (when (standard-map? heap)
    (locking hints
      (when-not (proof heap)
        (when (>= @(:count hints) entry-limit) (clear-cache!))
        (let [key (System/identityHashCode heap) ^HashMap buckets (:buckets hints)
              ^ArrayList bucket (or (.get buckets key) (ArrayList.))]
          (.add bucket [(WeakReference. heap) (boolean long-keys?)])
          (.put buckets key bucket)
          (swap! (:count hints) inc)))))
  heap)

(defn derive!
  "Propagate an attested base through ONE actual persistent cell update/removal.
   Unknown bases or noncanonical replacement storage produce no hint."
  [base result id node]
  (when-let [prior (proof base)]
    (when (or (and (nil? node) (not (contains? result id)))
              (storage-node? node))
      (remember! result (and (:long-keys? prior) (or (nil? node) (instance? Long id))))))
  result)
