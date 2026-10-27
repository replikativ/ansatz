(ns prototype.mutable
  "JVM-only mutable execution of the reference instruction set.
   Snapshots share immutable heap nodes and copy changed storage; writable arrays stay private."
  (:refer-clojure :exclude [run!])
  (:require [prototype.machine :as m]
            [prototype.heap-overlay :as overlay]
            [prototype.heap-snapshot :as heap-snapshot]
            [prototype.slot-count :as slots]
            [prototype.continuation-layout :as continuation-layout]
            [prototype.scalar :as scalar]
            [prototype.native-scalar :as native]
            [prototype.entropy :as entropy]
            [prototype.runtime-prim :as runtime]
            [prototype.runtime-task :as task]
            [prototype.leaf-compile :as leaf])
  (:import [ansatz.runtime GlobalsOverlay]
           [java.util HashMap Map ArrayDeque Arrays]
           [java.lang.ref WeakReference]))

(def ^:private unbound (Object.))
(defrecord Machine [functions slots control heap frames events counters])
;; control: body, locals, joins, next-id, status, result, resume-var
;; counters: allocations, field-stores, steps, max-frames
(defn- ctl [s i] (aget ^objects (:control s) i))
(defn- put! [s i v] (aset ^objects (:control s) i v))
(defn- bump! [s i n] (let [a ^longs (:counters s)] (aset-long a i (+ (aget a i) (long n)))))
(defn- registers [n bindings]
  (let [a (object-array n)]
    (Arrays/fill a unbound)
    (doseq [[k v] bindings] (aset a (int k) v)) a))
(defn- bind-params! [locals params args]
  ;; IR parameter/argument vectors are already indexed. Avoid constructing an
  ;; intermediate map or a lazy sequence of pairs on every guest transfer.
  (dotimes [i (count params)]
    (aset ^objects locals (int (nth params i)) (nth args i)))
  locals)
(defn- bindings [a]
  (into {} (keep-indexed (fn [i v] (when-not (identical? unbound v) [i v])) a)))
(defn- joins-out [joins]
  (into {} (map (fn [[k j]]
                  [k {:params (aget ^objects j 0) :body (aget ^objects j 1)
                      :locals (bindings (aget ^objects j 2))}]) joins)))
(defn- ids-slots [ids]
  (inc (reduce max 0 (filter integer? ids))))
(defn- operand-slots [[op id]]
  (if (= :var op) (ids-slots [id]) 1))
(defn- operands-slots [operands]
  (reduce (fn [n operand] (max n (operand-slots operand))) 1 operands))
(defn- expression-slots [[op a b] fallback]
  ;; Snapshot-generated continuations can contain runtime values in :imm and
  ;; :literal positions. They are data, never code/register-layout evidence.
  (case op
    :literal 1
    (:ctor :scalar-ctor :closure :runtime :prim) (operands-slots b)
    (:project :shared? :scalar-get) (operand-slots a)
    (:box :unbox) (operand-slots b)
    fallback))
(defn- measure-continuation-slots [body fallback]
  ;; Walk future instructions, including every branch and newly captured join.
  ;; Existing captured joins have their OWN arrays and are sized independently.
  ;; Do not inspect callees, module Names, scalar layouts, or literal payloads.
  (loop [pending (if body [body] []) n 1]
    (if (empty? pending) n
      (let [[op a b c d] (peek pending) pending (pop pending)]
        (case op
          :let (recur (conj pending c) (max n (ids-slots [a]) (expression-slots b fallback)))
          :call (recur (conj pending d)
                       (max n (ids-slots [a]) (operands-slots c)
                            (if (= :closure (first b)) (operand-slots (second b)) 1)))
          :tail (recur pending (max n (operands-slots b)
                                   (if (= :closure (first a)) (operand-slots (second a)) 1)))
          :return (recur pending (max n (operand-slots a)))
          (:read-global :global :unreachable) (recur pending n)
          :begin-init (recur pending (max n (operands-slots c)))
          :publish-global (recur pending (max n (operand-slots b)))
          :publish-io-global (recur pending (max n (operand-slots c)))
          :join (recur (conj pending c d) (max n (ids-slots b)))
          :jump (recur pending (max n (operands-slots b)))
          :case (recur (into pending (map second b)) (max n (operand-slots a)))
          :trap (recur pending (max n (operands-slots b)))
          :del (recur (conj pending b) (max n (operand-slots a)))
          (:set-tag :inc :dec) (recur (conj pending c) (max n (operand-slots a)))
          (:set :scalar-set) (recur (conj pending d) (max n (operand-slots a) (operand-slots c)))
          :suspend (recur (conj pending b) (max n (ids-slots [a])))
          :host (recur (conj pending d) (max n (operands-slots b) (ids-slots [c])))
          ;; Preserve the legacy global allocation bound for unknown forms.
          (recur pending (max n fallback)))))))
(def ^:private continuation-layout-generation (Object.))
(def ^:private continuation-layout-rules
  (mapv #(WeakReference. %) [measure-continuation-slots expression-slots operands-slots operand-slots ids-slots]))
(defn- builtin-continuation-layout? []
  (and (identical? (.get ^WeakReference (nth continuation-layout-rules 0)) measure-continuation-slots)
       (identical? (.get ^WeakReference (nth continuation-layout-rules 1)) expression-slots)
       (identical? (.get ^WeakReference (nth continuation-layout-rules 2)) operands-slots)
       (identical? (.get ^WeakReference (nth continuation-layout-rules 3)) operand-slots)
       (identical? (.get ^WeakReference (nth continuation-layout-rules 4)) ids-slots)))

(defn- restored-registers [cache fallback body locals extra-ids]
  (let [^java.util.IdentityHashMap cache cache
        body-width (or (.get cache body)
                       (let [n (continuation-layout/width body fallback measure-continuation-slots
                                                          builtin-continuation-layout? continuation-layout-generation)]
                         (.put cache body n) n))
        n (max body-width (slots/local-slots locals) (ids-slots extra-ids))]
    (when (> n 1000000) (m/fail "Register limit" {:slots n}))
    (registers n locals)))
(defn- joins-in [cache n joins]
  (let [result (HashMap.)]
    (doseq [[k j] joins]
      (.put result k (object-array [(:params j) (:body j)
                                   (restored-registers cache n (:body j) (:locals j) (:params j))])))
    result))
(defn- frame-in [cache n frame]
  (object-array [(:body frame) (:dest frame)
                 (restored-registers cache n (:body frame) (:locals frame) [(:dest frame)])
                 (joins-in cache n (:joins frame))]))
(defn- frame-out [frame]
  {:body (aget ^objects frame 0) :dest (aget ^objects frame 1)
   :locals (bindings (aget ^objects frame 2)) :joins (joins-out (aget ^objects frame 3))})
(defn- slot-count [s]
  (max (slots/program-slots (:functions s)) (slots/local-slots (:locals s))))
(defn function-slots [function]
  ;; Reuse the weak function cache without evicting the execution program cache.
  (slots/function-slots function))
(defn- callee-slots [s target function]
  (if-some [layouts (:register-layouts s)]
    ;; Preserve explicit layouts, including their global fallback for omissions.
    (get layouts target (:slots s))
    (if-let [cache (:function-slot-cache s)]
      (or (.get ^java.util.IdentityHashMap cache function)
          (let [n (function-slots function)]
            (.put ^java.util.IdentityHashMap cache function n)
            n))
      ;; Machines already alive before function-only adoption have no local cache.
      (function-slots function))))

(defn- dirty! [s id]
  (when-let [ids (:heap-dirty s)] (.add ^java.util.HashSet ids id)))
(defn- heap-put! [s id node]
  (dirty! s id)
  (.put ^Map (:heap s) id node))
(defn- heap-remove! [s id]
  (dirty! s id)
  (.remove ^Map (:heap s) id))

(defn- thaw-node [node]
  ;; Frozen vectors and node maps are immutable, regardless of RC. First field
  ;; writes acquire private arrays; RC/tag/scalar updates can keep the vector.
  ;; Defensive copying also covers externally supplied rc0 Object[] snapshots.
  (if (vector? (:fields node)) node (update node :fields object-array)))
(defn- freeze-node [node]
  (if (vector? (:fields node)) node
    ;; vec can adopt short arrays, so clone mutable storage first.
    (update node :fields #(vec (aclone ^objects %)))))

(defn- thaw-heap [heap dirty-ids]
  (if (instance? clojure.lang.IPersistentMap heap)
    (if-let [proof (heap-snapshot/proof heap)]
      (overlay/overlay heap dirty-ids (:long-keys? proof))
      (let [scan (object-array [true [] (heap-snapshot/standard-map? heap)])]
        (reduce-kv (fn [_ id node]
                     (when-not (instance? Long id) (aset scan 0 false))
                     (when-not (heap-snapshot/storage-node? node) (aset scan 2 false))
                     (when-not (vector? (:fields node))
                       (aset scan 1 (conj (aget scan 1) [id (thaw-node node)])))
                     nil)
                   nil heap)
        (when (aget scan 2) (heap-snapshot/remember! heap (aget scan 0)))
        (let [result (overlay/overlay heap dirty-ids (aget scan 0))]
          (doseq [[id node] (aget scan 1)] (.put ^Map result id node))
          result)))
    ;; Nonpersistent external input cannot be the immutable base of an overlay.
    (let [result (HashMap.)]
      (doseq [[id node] heap]
        (.put result id (thaw-node node))
        (when-not (vector? (:fields node))
          (.add ^java.util.HashSet dirty-ids id)))
      result)))
(defn- freeze-heap [s]
  (let [base (:heap-base s) ids (:heap-dirty s) heap ^Map (:heap s)]
    (cond
      (and base ids (.isEmpty ^java.util.HashSet ids)) base
      ;; Full reconstruction also attests its output during this existing pass.
      (or (nil? base) (nil? ids) (> (.size ^java.util.HashSet ids) (quot (.size heap) 2)))
      (let [scan (object-array [true true])
            result (persistent!
                     (reduce (fn [out [id node]]
                               (let [frozen (freeze-node node)]
                                 (when-not (instance? Long id) (aset scan 0 false))
                                 (when-not (heap-snapshot/storage-node? frozen) (aset scan 1 false))
                                 (assoc! out id frozen))) (transient {}) heap))]
        (when (aget scan 1) (heap-snapshot/remember! result (aget scan 0)))
        result)
      :else
      (let [proof (heap-snapshot/proof base)
            scan (object-array [(boolean (:long-keys? proof)) (boolean proof)])
            result (reduce (fn [out id]
                             (if-let [node (.get heap id)]
                               (let [frozen (freeze-node node)]
                                 (when-not (instance? Long id) (aset scan 0 false))
                                 (when-not (heap-snapshot/storage-node? frozen) (aset scan 1 false))
                                 (assoc out id frozen))
                               (dissoc out id))) base ids)]
        (when (aget scan 1) (heap-snapshot/remember! result (aget scan 0)))
        result))))

(defn thaw [snapshot]
  (let [n (slot-count snapshot)
        ;; Memoize code identity only for this restoration. No body/value or
        ;; mutable register array is retained in a snapshot or global cache.
        body-widths (java.util.IdentityHashMap.)
        pending-dest (case (:status snapshot)
                       :host-call (get-in snapshot [:host-request :dest])
                       :suspended (:resume-var snapshot)
                       nil)
        dirty-ids (java.util.HashSet.)]
    (when (> n 1000000) (m/fail "Register limit" {:slots n}))
    (assoc (->Machine (:functions snapshot) n
               (object-array [(:body snapshot)
                              (restored-registers body-widths n (:body snapshot) (:locals snapshot) [pending-dest])
                              (joins-in body-widths n (:joins snapshot)) (:next-id snapshot)
                              (:status snapshot) (:result snapshot) (or (:host-request snapshot) (:resume-var snapshot))])
               (thaw-heap (:heap snapshot) dirty-ids)
               (ArrayDeque. ^java.util.Collection
                            (mapv #(frame-in body-widths n %) (:frames snapshot)))
               (java.util.ArrayList. ^java.util.Collection (:events snapshot))
               (long-array (map (:stats snapshot) [:allocations :field-stores :steps :max-frames])))
           :heap-base (when (instance? clojure.lang.IPersistentMap (:heap snapshot)) (:heap snapshot))
           :heap-dirty dirty-ids
           :function-slot-cache (java.util.IdentityHashMap.)
           :globals (GlobalsOverlay/open (or (:globals snapshot) {}))
           :entropy-state (when (contains? snapshot :entropy) (object-array [(:entropy snapshot)]))
           :task-runtime-state (object-array [(get snapshot :task-runtime ::unset)])
           :stdio-runtime-state (object-array [(get snapshot :stdio-runtime ::unset)])
           :world-context (select-keys snapshot [:initializing? :initialization-scope :initialized-modules :environment :kernel-environments :native-imports :eval-const-authorizations :heartbeat-allocation-offset :runtime-build :runtime-build-overrides :sharecommon-profile :source-modules :source-regions :source-import-prefixes]))))

(defn- freeze-globals [s]
  (let [globals ^Map (:globals s)]
    (or (GlobalsOverlay/unchangedBase globals)
        (let [frozen (into {} globals)]
          (GlobalsOverlay/rememberSnapshot globals frozen)
          frozen))))

(defn freeze [s]
  (cond-> (merge (:world-context s) {:functions (:functions s)
           :heap (freeze-heap s)
           :globals (freeze-globals s)
           :next-id (ctl s 3) :events (vec (:events s))
           :stats (zipmap [:allocations :field-stores :steps :max-frames] (vec (aclone ^longs (:counters s))))
           :body (ctl s 0) :locals (bindings (ctl s 1)) :joins (joins-out (ctl s 2))
           :frames (mapv frame-out (:frames s))
           :status (ctl s 4)})
    (:entropy-state s) (assoc :entropy (aget ^objects (:entropy-state s) 0))
    (not= ::unset (aget ^objects (:task-runtime-state s) 0))
    (assoc :task-runtime (aget ^objects (:task-runtime-state s) 0))
    (not= ::unset (aget ^objects (:stdio-runtime-state s) 0))
    (assoc :stdio-runtime (aget ^objects (:stdio-runtime-state s) 0))
    (= :done (ctl s 4)) (assoc :result (ctl s 5))
    (= :suspended (ctl s 4)) (assoc :resume-var (ctl s 6))
    (= :host-call (ctl s 4)) (assoc :host-request (ctl s 6))))

(defn- node [s r]
  ;; Imported vectors stay immutable and are never inserted in the local heap.
  ;; Pure/mutable worlds therefore share only the source's immutable cache.
  (if (m/native-reference? s r)
    (do
      (when (.containsKey ^Map (:heap s) (:id r))
        (m/fail "Imported guest reference is shadowed by mutable heap storage" {:ref r}))
      (m/node s r))
    (or (.get ^Map (:heap s) (:id r)) (m/fail "Dangling guest reference" {:ref r}))))

(defn- writable-fields! [s r current]
  ;; Call only after validating a write, using the CURRENT node after any RC
  ;; effects. Never restore an earlier node merely to install copied fields.
  (let [fields (:fields current)]
    (if (vector? fields)
      (let [owned (object-array fields)]
        (heap-put! s (:id r) (assoc current :fields owned))
        owned)
      fields)))

(defn- replace-node! [s r n]
  (when (m/native-reference? s r)
    (m/fail "Cannot mutate immutable imported guest node" {:ref r}))
  (heap-put! s (:id r) (update n :fields object-array)) s)

(defn assert-persistent! [s v]
  (when (and (m/ref? v) (not (m/native-reference? s v)) (not (zero? (:rc (node s v)))))
    (m/fail "Persistent RC invariant violated" {:ref v}))
  v)

(defn mark-persistent! [s root]
  ;; Validate before mutating RC, visiting only the reachable graph. Module
  ;; initialization must not copy the complete guest heap for each global.
  (let [ids (loop [pending [root] seen #{}]
              (if (empty? pending) seen
                (let [v (peek pending) pending (pop pending)]
                  (if (or (not (m/ref? v)) (contains? seen (:id v)) (m/native-reference? s v))
                    (recur pending seen)
                    (let [{:keys [kind fields]} (node s v)]
                      (when-not (contains? #{:ctor :closure :array :ref :task :byte-array :float-array :thunk :promise
                                             :string :mpz :scalar-array :mutex} kind)
                        (m/fail "Unsupported persistent object kind" {:kind kind}))
                      (recur (into pending fields) (conj seen (:id v))))))))]
    (doseq [id ids]
      (heap-put! s id (assoc (.get ^Map (:heap s) id) :rc 0))))
  root)

(defn retain!
  ([s v n] (retain! s v n false))
  ([s v n persistent?]
   (when persistent? (assert-persistent! s v))
   (when (and (m/ref? v) (not (m/native-reference? s v)) (not (zero? (:rc (node s v)))))
     (heap-put! s (:id v) (update (node s v) :rc + n)))))
(defn release!
  ([s v n] (release! s v n false))
  ([s v n persistent?]
   (when persistent? (assert-persistent! s v))
   (when (m/ref? v)
     (let [pending (ArrayDeque.)]
       (.addLast pending [v n])
       (while (not (.isEmpty pending))
         (let [[v n] (.removeLast pending)]
           (when (and (m/ref? v) (not (m/native-reference? s v)))
             (let [initial (node s v)
                   [_ n] (if (and (= :task (:kind initial)) (:queued? initial))
                           (task/prepare-release
                            {:ref? m/ref? :node node
                             :replace-node replace-node!
                             :get-task-runtime (fn [s] (let [v (aget ^objects (:task-runtime-state s) 0)] (when-not (= ::unset v) v)))
                             :set-task-runtime (fn [s c] (aset ^objects (:task-runtime-state s) 0 c) s)}
                            s v n) [s n])
                   {:keys [rc kind tag fields] :as node} (node s v) left (- rc n)]
               (cond
                 (zero? rc) nil
                 (neg? left) (m/fail "Reference count underflow" {:ref v :rc rc :drop n})
                 (pos? left) (heap-put! s (:id v) (assoc node :rc left))
                 :else (do (when (= kind :promise)
                             (task/deactivate-promise
                              {:ref? m/ref? :node (fn [s r] (.get ^Map (:heap s) (:id r)))
                               :replace-node replace-node!}
                              s node))
                           (heap-remove! s (:id v))
                           (when (= :resource kind) (.add ^java.util.ArrayList (:events s) [:released tag]))
                           (doseq [f fields]
                             (when (m/ref? f) (.addLast pending [f 1])))))))))))))
(defn delete-shell! [s r]
  (when (m/ref? r)
    (let [n (node s r)]
      (when-not (and (= :ctor (:kind n)) (= 1 (:rc n)))
        (m/fail "Invalid unique constructor deletion" {:ref r :node n}))
      (heap-remove! s (:id r))))
  s)

(defn set-constructor-tag! [s r tag]
  (let [n (node s r)]
    (when-not (and (= :ctor (:kind n)) (= 1 (:rc n)) (integer? tag) (<= 0 tag 243))
      (m/fail "Invalid unique constructor tag store" {:ref r :tag tag}))
    (heap-put! s (:id r) (assoc n :tag tag))))

(defn read-local [locals x]
  (let [v (aget ^objects locals (int x))]
    (if (identical? unbound v) (m/fail "Unbound variable" {:variable x}) v)))
(defn- value [s [op x]]
  (case op
    :imm x
    :var (read-local (ctl s 1) x)
    (m/fail "Unknown operand" {:op op})))
(defn- allocate! [s kind tag fields function]
  (let [id (ctl s 3) r (m/->Ref id)]
    (when (m/native-reference? s r)
      (m/fail "Allocation collides with reserved imported guest range" {:id id}))
    (put! s 3 (inc id))
    (heap-put! s id (cond-> {:kind kind :tag tag :fields (object-array fields) :rc 1}
                                function (assoc :function function)))
    (bump! s 0 1) r))

(defn scalar-constructor! [s tag fields layout]
  (scalar/layout! layout)
  (when-not (= (:objects layout) (count fields)) (m/fail "Scalar constructor object count mismatch" {}))
  (let [r (allocate! s :ctor tag fields nil)]
    (heap-put! s (:id r) (assoc (node s r) :layout layout :scalar-bytes {})) r))

(defn scalar-get [s r slot] (m/read-scalar-node (node s r) slot))
(defn scalar-store! [s r slot v]
  (heap-put! s (:id r) (m/write-scalar-node (node s r) slot v)) (bump! s 1 1))
(defn box! [s type x]
  (let [x (scalar/value! type x)]
    (if-let [layout (scalar/box-layout type)]
      (let [r (scalar-constructor! s 0 [] layout)]
        ;; Boxing initializes storage, but isn't a separate IR field-store step.
        (heap-put! s (:id r) (m/write-scalar-node (node s r) (scalar/box-slot type) x)) r)
      x)))
(defn unbox [s type x] (m/unbox-value s type x))

(defn take-entropy! [s n]
  (let [tape (:entropy-state s)
        [world bytes] (entropy/take-bytes {:entropy (when tape (aget ^objects tape 0))} n)]
    (aset ^objects tape 0 (:entropy world))
    [s bytes]))

;; Every operation receives its actual machine explicitly. This immutable table
;; captures no machine/world; runtime-value! checks the five function values that
;; the old per-call map read directly, preserving redefinition/reload semantics.
(def ^:private runtime-ops
  {:get-stdio-runtime (fn [s] (let [v (aget ^objects (:stdio-runtime-state s) 0)] (when-not (= ::unset v) v)))
   :set-stdio-runtime (fn [s c] (aset ^objects (:stdio-runtime-state s) 0 c) s)
   :get-task-runtime (fn [s] (let [v (aget ^objects (:task-runtime-state s) 0)] (when-not (= ::unset v) v)))
   :set-task-runtime (fn [s c] (aset ^objects (:task-runtime-state s) 0 c) s)
   :get-env (fn [s name]
              [s (second (m/environment-entry {:environment (get-in s [:world-context :environment])} name))])
   :runtime-build (fn [s symbol] (m/runtime-build-entry (:world-context s) symbol))
   :allocation-count (fn [s] (- (aget ^longs (:counters s) 0)
                                (get (:world-context s) :heartbeat-allocation-offset 0)))
   :pointer-address m/pointer-address
   :take-entropy take-entropy!
   :initializing? (fn [s] (boolean (get-in s [:world-context :initializing?])))
   :ref? m/ref?
   :node (fn [s r] (update (node s r) :fields vec))
   :borrow-node node
   :store-array-field! (fn [s ref index value]
                         ;; The runtime establishes exclusivity and bounds
                         ;; before releasing the old field. Preserve any RC
                         ;; changes caused by that release.
                         (when (m/native-reference? s ref)
                           (m/fail "Cannot mutate imported array" {:ref ref}))
                         (let [current (node s ref)]
                           (when-not (and (= :array (:kind current)) (= 1 (:rc current))
                                          (< -1 index (count (:fields current))))
                             (m/fail "Invalid unique array store" {:ref ref :index index}))
                           (let [fields (writable-fields! s ref current)]
                             (dirty! s (:id ref))
                             (aset ^objects fields (int index) value)))
                         s)
   :allocate (fn [s kind tag fields] [s (allocate! s kind tag fields nil)])
   :retain (fn [s v n] (retain! s v n) s)
   :release (fn [s v n] (release! s v n) s)
   :replace-node replace-node!})

(defn runtime-value! [s symbol args]
  ;; Read function values once at call entry, as the original ops map did. Using
  ;; Vars as table entries would instead observe a redefinition inside evaluate.
  (let [pointer-address m/pointer-address take-entropy take-entropy! ref? m/ref?
        borrow-node node replace-node replace-node!
        ops (if (and (identical? pointer-address (:pointer-address runtime-ops))
                     (identical? take-entropy (:take-entropy runtime-ops))
                     (identical? ref? (:ref? runtime-ops))
                     (identical? borrow-node (:borrow-node runtime-ops))
                     (identical? replace-node (:replace-node runtime-ops)))
              runtime-ops
              (assoc runtime-ops :pointer-address pointer-address :take-entropy take-entropy
                     :ref? ref? :borrow-node borrow-node :replace-node replace-node))]
    (second (runtime/evaluate ops s symbol args))))

(defn- field-at [fields i]
  (if (vector? fields) (nth fields (int i)) (aget ^objects fields (int i))))

(defn- expr! [s [op a b c]]
  (case op
    :literal a
    :ctor (if (empty? b) (m/->Tag a) (allocate! s :ctor a (mapv #(value s %) b) nil))
    :project (field-at (:fields (node s (value s a))) b)
    :shared? (let [r (value s a)] (if (and (m/ref? r) (not= (:rc (node s r)) 1)) 1 0))
    :scalar-ctor (scalar-constructor! s a (mapv #(value s %) b) c)
    :scalar-get (scalar-get s (value s a) b)
    :box (box! s a (value s b))
    :unbox (unbox s a (value s b))
    :closure (allocate! s :closure nil (mapv #(value s %) b) a)
    :runtime (runtime-value! s a (mapv #(value s %) b))
    :prim (m/scalar a (mapv #(value s %) b))
    (m/fail "Unsupported expression" {:op op})))
(defn deliver! [s result]
  (if (.isEmpty ^ArrayDeque (:frames s))
    (do (put! s 4 :done) (put! s 5 result))
    (let [frame ^objects (.removeLast ^ArrayDeque (:frames s))
          locals ^objects (aget frame 2)]
      (aset locals (int (aget frame 1)) result)
      (put! s 0 (aget frame 0)) (put! s 1 locals) (put! s 2 (aget frame 3)))))
(defn- push-frame! [s body dest locals joins]
  (.addLast ^ArrayDeque (:frames s) (object-array [body dest locals joins]))
  (let [a ^longs (:counters s)]
    (aset-long a 3 (max (aget a 3) (.size ^ArrayDeque (:frames s))))))

(defn call-values! [s target args dest continuation]
  (let [application
        (if (= :direct (first target)) {:target (second target) :args args}
          (let [closure (second target)]
            (when (empty? args) (m/fail "Empty boxed closure application" {}))
            (cond
              (instance? prototype.machine.Builtin closure)
              (do (when-not (= :inc (:name closure))
                    (m/fail "Unsupported pure host callback" {:target closure}))
                  {:target closure :args [(first args)] :surplus (subvec (vec args) 1)})
              (m/ref? closure)
              (let [{:keys [kind function fields]} (node s closure)]
                (when-not (= :closure kind) (m/fail "Expected guest closure" {:value closure}))
                (let [{:keys [partial? args surplus]}
                      (m/application-shape (:functions s) function (vec fields) args)]
                  (doseq [v fields] (retain! s v 1))
                  (release! s closure 1)
                  (if partial?
                    {:result (allocate! s :closure nil args function)}
                    {:target function :args args :surplus surplus})))
              (m/erased-callee? closure)
              (do (doseq [v args] (release! s v 1)) {:result closure})
              :else (m/fail "Expected closure" {:value closure}))))
        {:keys [target args surplus]} application]
    (when continuation (push-frame! s continuation dest (ctl s 1) (ctl s 2)))
    (when (seq surplus)
      (push-frame! s [:tail [:closure [:var 0]] (mapv #(vector :imm %) surplus)]
                   0 (registers 1 nil) (HashMap.)))
    (cond
      (contains? application :result) (deliver! s (:result application))
      (instance? prototype.machine.Builtin target)
      (do (when-not (and (= :inc (:name target)) (= 1 (count args)) (number? (first args)))
            (m/fail "Unsupported pure host callback" {:target target :args args}))
          (deliver! s (m/small-integer! (inc (m/small-integer! (first args))))))
      :else
      (let [{:keys [params body] :as f} (get (:functions s) target)]
        (when-not f (m/fail "Unresolved function" {:target target}))
        (when-not (= (count params) (count args))
          (m/fail "Guest arity mismatch" {:target target :expected (count params) :actual (count args)}))
        (let [slots (callee-slots s target f)]
          (put! s 0 body)
          (if continuation
            (do (put! s 1 (bind-params! (registers slots nil) params args))
                (put! s 2 (HashMap.)))
            (let [old ^objects (ctl s 1)
                  ;; Tail transfers discard the caller's registers. Reuse only
                  ;; the exact required width; a global-sized initial array must
                  ;; shrink too. New arrays are already cleared by registers.
                  ^objects locals (if (= (alength old) slots)
                                    (do (Arrays/fill old unbound) old)
                                    (registers slots nil))]
              (bind-params! locals params args)
              (put! s 1 locals)
              (.clear ^HashMap (ctl s 2)))))))))

(defn start! [s target args]
  (.clear ^ArrayDeque (:frames s))
  (put! s 4 :running)
  (put! s 5 nil)
  (put! s 6 nil)
  (call-values! s [:direct target] args nil nil)
  s)

(defn global-enter! [s name initializer]
  (let [entry (.get ^Map (:globals s) name)]
    (case (:status entry)
      :ready (deliver! s (:value entry))
      :initializing (m/fail "Recursive global initialization" {:name name})
      (do (.put ^Map (:globals s) name {:status :initializing})
          (call-values! s [:direct initializer] [] 0 [:publish-global name [:var 0]])))))

(defn publish-global! [s name v]
  (mark-persistent! s v)
  (.put ^Map (:globals s) name {:status :ready :value v})
  (deliver! s v))

(defn initialized-value [s name]
  (let [entry (.get ^Map (:globals s) name)]
    (when-not (= :ready (:status entry))
      (m/fail "Module global has not been initialized" {:name name :status (:status entry)}))
    (:value entry)))

(defn begin-init! [s name initializer args type]
  (let [entry (.get ^Map (:globals s) name)]
    (case (:status entry)
      :ready (deliver! s (:value entry))
      :initializing (m/fail "Recursive global initialization" {:name name})
      (do (.put ^Map (:globals s) name {:status :initializing})
          (call-values! s [:direct initializer] args 0 [:publish-io-global name type [:var 0]])))))

(defn publish-io-global! [s name type result]
  (let [{:keys [kind tag fields]} (node s result)]
    (when-not (and (= :ctor kind) (= tag 0) (= 1 (count fields)))
      (m/fail "Lean module initializer did not return IO success" {:name name :result result :tag tag}))
    (let [v (field-at fields 0)
          v (if (contains? #{"uint8" "uint16" "uint32" "uint64" "usize" "float" "float32"} type) (unbox s type v) v)]
      (mark-persistent! s v)
      (release! s result 1)
      (.put ^Map (:globals s) name {:status :ready :value v})
      (deliver! s v))))

(defn- complete-leaf! [s result steps]
  (let [a ^longs (:counters s)]
    (aset-long a 3 (max (aget a 3) (inc (.size ^ArrayDeque (:frames s))))))
  (bump! s 2 steps)
  result)

(defn try-leaf! [s target args]
  ;; A miss has no guest-visible effects. Plans come from the current program,
  ;; not a block's constant pool, so reused callers see edited callees.
  (let [closure (when (= :closure (first target)) (second target))]
    (if (instance? prototype.machine.Builtin closure)
      ;; This is the one existing pure host callback, not arbitrary host interop.
      (when (and (= :inc (:name closure)) (= 1 (count args)) (leaf/small-integer? (first args)))
        (let [result (try (m/small-integer! (inc (first args)))
                          (catch clojure.lang.ExceptionInfo _ nil))]
          (when (some? result) (complete-leaf! s result 0))))
      (let [capture (when (m/ref? closure) (node s closure))
            name (if (= :direct (first target)) (second target)
                     (when (= :closure (:kind capture)) (:function capture)))
            plan (when (or (= :direct (first target)) (= :closure (:kind capture)))
                   (get (:leaf-plans s) name))]
        (when (and plan (= (:definition plan) (get (:functions s) name)))
          (let [fields (:fields capture)
                args (if (seq fields) (into (vec fields) args) args)]
            (when (and (= (count (:params (:definition plan))) (count args))
                       (every? leaf/small-integer? args))
              (let [result (try ((:invoke plan) args)
                                (catch clojure.lang.ExceptionInfo _ nil))]
                (when (some? result)
                  (when capture
                    (doseq [v fields] (retain! s v 1))
                    (release! s closure 1))
                  (complete-leaf! s result (:steps plan)))))))))))

(defn- call! [s target operands dest continuation]
  (call-values! s (if (= :closure (first target))
                   [:closure (value s (second target))] target)
                (mapv #(value s %) operands) dest continuation))

;; Experimental ABI shared by the instruction interpreter and generated blocks.
;; Helpers own heap/control transitions; compiled code owns operand resolution.
(defn body-of [s] (ctl s 0))
(defn set-body! [s body] (put! s 0 body))
(defn locals-array [s] (ctl s 1))
(defn has-frames? [s] (not (.isEmpty ^ArrayDeque (:frames s))))
(defn status [s] (ctl s 4))
(defn steps [s] (aget ^longs (:counters s) 2))
(defn add-steps! [s n] (bump! s 2 n))
(defn pause! [s] (put! s 4 :paused) s)
(defn constructor! [s tag fields]
  (if (empty? fields) (m/->Tag tag) (allocate! s :ctor tag fields nil)))
(defn closure! [s function fields] (allocate! s :closure nil fields function))
(defn project [s r i] (field-at (:fields (node s r)) i))
(defn shared? [s r] (if (and (m/ref? r) (not= (:rc (node s r)) 1)) 1 0))
(defn tag-of [s v]
  (cond (m/ref? v) (:tag (node s v))
        (native/native-scalar? v) (native/unsigned-value 32 v)
        (instance? prototype.machine.Tag v) (:tag v)
        (number? v) v :else (m/fail "Value has no constructor tag" {:value v})))
(defn capture-join! [s id params body locals]
  ;; Takes ownership of a fresh, fully materialized register array.
  (.put ^HashMap (ctl s 2) id (object-array [params body locals])))
(defn join! [s id params body]
  (capture-join! s id params body (aclone ^objects (ctl s 1))))
(defn jump-values! [s id args]
  (let [join ^objects (.get ^HashMap (ctl s 2) id)]
    (when-not (and join (= (count (aget join 0)) (count args))) (m/fail "Invalid join" {:join id}))
    (let [locals (aclone ^objects (aget join 2))]
      (bind-params! locals (aget join 0) args)
      (put! s 1 locals) (put! s 0 (aget join 1)))))
(defn store! [s r i v]
  (let [n (node s r)]
    (when-not (and (= :ctor (:kind n)) (= 1 (:rc n)) (< -1 i (count (:fields n))))
      (m/fail "Invalid unique field store" {:ref r :field i}))
    (let [fields (writable-fields! s r n)]
      (dirty! s (:id r))
      (aset ^objects fields (int i) v))
    (bump! s 1 1)))
(defn suspend! [s dest body]
  (put! s 4 :suspended) (put! s 6 dest) (put! s 0 body))

(defn host! [s symbol args dest body]
  (put! s 4 :host-call) (put! s 6 {:symbol symbol :arguments args :dest dest}) (put! s 0 body))

(defn step! [s]
  (when-not (= :running (ctl s 4)) (m/fail "Machine is not running" {:status (ctl s 4)}))
  (bump! s 2 1)
  (let [[op a b c d] (ctl s 0)]
    (case op
      :let (do (aset ^objects (ctl s 1) (int a) (expr! s b)) (put! s 0 c))
      :call (call! s b c a d)
      :tail (call! s a b nil nil)
      :return (deliver! s (value s a))
      :read-global (deliver! s (initialized-value s a))
      :begin-init (begin-init! s a b (mapv #(value s %) c) d)
      :publish-io-global (publish-io-global! s a b (value s c))
      :global (global-enter! s a b)
      :publish-global (publish-global! s a (value s b))
      :join (do (join! s a b c) (put! s 0 d))
      :jump (jump-values! s a (mapv #(value s %) b))
      :case (let [tag (tag-of s (value s a))
                  branch (or (some (fn [[k body]] (when (= k tag) body)) b)
                             (some (fn [[k body]] (when (= k :default) body)) b))]
              (when-not branch (m/fail "Missing case" {:tag tag})) (put! s 0 branch))
      :trap (m/fail "Reached unsupported guest declaration" {:declaration a :arguments (mapv #(value s %) b)})
      :unreachable (m/fail "Reached Lean unreachable instruction" {})
      :del (do (delete-shell! s (value s a)) (put! s 0 b))
      :set-tag (do (set-constructor-tag! s (value s a) b) (put! s 0 c))
      :inc (do (retain! s (value s a) b (boolean d)) (put! s 0 c))
      :dec (do (release! s (value s a) b (boolean d)) (put! s 0 c))
      :set (do (store! s (value s a) b (value s c)) (put! s 0 d))
      :scalar-set (do (scalar-store! s (value s a) b (value s c)) (put! s 0 d))
      :suspend (suspend! s a b)
      :host (host! s a (mapv #(value s %) b) c d)
      (m/fail "Unsupported instruction" {:op op}))) s)

(defn run!
  ([s] (run! s 10000000))
  ([s fuel]
   (when-not (and (integer? fuel) (not (neg? fuel))) (m/fail "Invalid step budget" {:fuel fuel}))
   (loop [n fuel]
     (cond (not= :running (ctl s 4)) s
           (zero? n) (do (put! s 4 :paused) s)
           :else (do (step! s) (recur (dec n)))))))
(defn resume! [s x]
  (case (ctl s 4)
    :suspended (do (aset ^objects (ctl s 1) (int (ctl s 6)) x) (put! s 6 nil) (put! s 4 :running))
    :paused (put! s 4 :running)
    :host-call (do (aset ^objects (ctl s 1) (int (:dest (ctl s 6))) x) (put! s 6 nil) (put! s 4 :running))
    (m/fail "State is not resumable" {:status (ctl s 4)})) s)

;; Private storage may cross an unchanged host boundary only while its original
;; readers/layout semantics remain valid. No Machine is exposed to a handler.
(declare boundary-storage-token)
(defn- boundary-arrays-fit? [s snapshot]
  (when-let [program-width (slots/cached-program-slots (:functions snapshot))]
    (let [fallback (:slots s)
          required-global (max program-width (slots/local-slots (:locals snapshot)))
          seen (java.util.IdentityHashMap.)
          fits? (fn [array body extra]
                  (when-not (.containsKey seen array)
                    (.put seen array true)
                    (when-let [width (continuation-layout/proven-width body fallback continuation-layout-generation)]
                      (<= (max width (ids-slots extra)) (alength ^objects array)))))
          joins-fit? (fn [joins]
                       (every? (fn [^objects join]
                                 (fits? (aget join 2) (aget join 1) (aget join 0)))
                               (.values ^HashMap joins)))
          dest (get-in snapshot [:host-request :dest])]
      (and (= fallback required-global)
           (integer? dest) (<= 0 dest) (< dest (alength ^objects (ctl s 1)))
           (fits? (ctl s 1) (ctl s 0) [dest])
           (joins-fit? (ctl s 2))
           (every? (fn [^objects frame]
                     (and (fits? (aget frame 2) (aget frame 0) [(aget frame 1)])
                          (joins-fit? (aget frame 3)))) (:frames s))))))

(defn clean-host-storage?
  "Internal cheap candidate test; never retain dirty private heap copies through
   a handler when unchanged-boundary reuse is already impossible."
  [s snapshot token]
  (and (some? token) (identical? token (boundary-storage-token))
       (= :host-call (ctl s 4)) (= :host-call (:status snapshot))
       (identical? (:functions s) (:functions snapshot))
       (instance? java.util.HashSet (:heap-dirty s))
       (.isEmpty ^java.util.HashSet (:heap-dirty s))
       (identical? (:heap-base s) (:heap snapshot))
       (instance? java.util.IdentityHashMap (:function-slot-cache s))))

(defn resume-unchanged-host!
  "Internal optional resume over private storage after an IDENTICAL host World
   return. TOKEN must have been captured before the stock Machine was restored.
   This never replaces the caller's ordinary immutable resumed checkpoint.
   Missing proof/capacity or any changed storage/layout rule returns nil without
   mutation or speculative code walks. Successful reuse resets interval caches."
  [s snapshot value token]
  (when (and (clean-host-storage? s snapshot token)
             (boundary-arrays-fit? s snapshot)
             (identical? token (boundary-storage-token)))
    (.clear ^java.util.IdentityHashMap (:function-slot-cache s))
    ;; These are per-backend-entry caches, not semantic state or World fields.
    (let [s (dissoc s :leaf-plans :register-layouts :prototype.typed-tail-execution/context)]
      (put! s 5 nil)
      (resume! s value))))

(def ^:private boundary-storage-generation (Object.))
(def ^:private boundary-program-layout (WeakReference. (slots/program-layout-token)))
(def ^:private boundary-storage-roots
  (mapv #(WeakReference. %) [thaw freeze resume! run! step! restored-registers frame-in joins-in frame-out joins-out bindings registers slot-count function-slots callee-slots freeze-heap freeze-node freeze-globals thaw-heap thaw-node ctl put! boundary-arrays-fit? resume-unchanged-host! slots/program-slots slots/local-slots slots/cached-program-slots continuation-layout/proven-width measure-continuation-slots expression-slots operands-slots operand-slots ids-slots overlay/overlay heap-snapshot/proof heap-snapshot/remember! heap-snapshot/storage-node? clean-host-storage? continuation-layout/width slots/program-layout-token]))
(defn boundary-storage-token
  "Internal generation only while stock restore/freeze/layout rules are intact."
  []
  (when (and (identical? (.get ^WeakReference (nth boundary-storage-roots 0)) thaw)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 1)) freeze)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 2)) resume!)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 3)) run!)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 4)) step!)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 5)) restored-registers)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 6)) frame-in)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 7)) joins-in)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 8)) frame-out)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 9)) joins-out)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 10)) bindings)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 11)) registers)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 12)) slot-count)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 13)) function-slots)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 14)) callee-slots)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 15)) freeze-heap)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 16)) freeze-node)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 17)) freeze-globals)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 18)) thaw-heap)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 19)) thaw-node)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 20)) ctl)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 21)) put!)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 22)) boundary-arrays-fit?)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 23)) resume-unchanged-host!)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 24)) slots/program-slots)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 25)) slots/local-slots)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 26)) slots/cached-program-slots)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 27)) continuation-layout/proven-width)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 28)) measure-continuation-slots)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 29)) expression-slots)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 30)) operands-slots)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 31)) operand-slots)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 32)) ids-slots)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 33)) overlay/overlay)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 34)) heap-snapshot/proof)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 35)) heap-snapshot/remember!)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 36)) heap-snapshot/storage-node?)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 37)) clean-host-storage?)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 38)) continuation-layout/width)
             (identical? (.get ^WeakReference (nth boundary-storage-roots 39)) slots/program-layout-token)
             (some? (.get ^WeakReference boundary-program-layout))
             (identical? (.get ^WeakReference boundary-program-layout) (slots/program-layout-token)))
    boundary-storage-generation))

;; Selected pure-wrapper guards compose definition-owner baselines, including
;; reference classification that runtime-value! otherwise reads at call entry.
(def ^:private scalar-wrapper-generation (Object.))
(def ^:private scalar-wrapper-roots
  [runtime-value! runtime-ops node take-entropy! replace-node! step! expr! value
   read-local ctl put! bump! locals-array add-steps! set-body!])
(defn scalar-wrapper-token []
  scalar-wrapper-generation)
(defn builtin-scalar-wrapper? [symbol operation]
  (let [[r ops n entropy replace step expr value-root read ctl-root put bump locals steps body] scalar-wrapper-roots]
    (and (identical? r runtime-value!) (identical? ops runtime-ops) (identical? n node)
         (identical? entropy take-entropy!) (identical? replace replace-node!)
         (identical? step step!) (identical? expr expr!) (identical? value-root value)
         (identical? read read-local) (identical? ctl-root ctl) (identical? put put!)
         (identical? bump bump!) (identical? locals locals-array) (identical? steps add-steps!)
         (identical? body set-body!) (m/builtin-scalar-reference?)
         (runtime/builtin-scalar-arithmetic? symbol operation))))

(defn scalar-wrapper-tokens []
  [(scalar-wrapper-token) (m/scalar-reference-token) (runtime/scalar-arithmetic-token)
   (scalar/scalar-integer-token) (native/scalar-carrier-token)])
(defn current-scalar-wrapper? [tokens symbol operation]
  (and (identical? (nth tokens 0) (scalar-wrapper-token))
       (identical? (nth tokens 1) (m/scalar-reference-token))
       (identical? (nth tokens 2) (runtime/scalar-arithmetic-token))
       (identical? (nth tokens 3) (scalar/scalar-integer-token))
       (identical? (nth tokens 4) (native/scalar-carrier-token))
       (builtin-scalar-wrapper? symbol operation)))

(defn tail-frame-depth
  "Current caller depth, read from this invocation rather than compiled code."
  ^long [s]
  (long (.size ^ArrayDeque (:frames s))))

(defn tail-entry-state?
  "Internal guard: valid caller peak, no joins, and exactly the parameter locals."
  [s params]
  (let [^objects locals (ctl s 1)]
    (and (<= (tail-frame-depth s) (aget ^longs (:counters s) 3))
         (.isEmpty ^HashMap (ctl s 2))
         (nil? (:leaf-plans s)) (nil? (:register-layouts s))
         (every? (fn [id] (and (< -1 id (alength locals)) (not (identical? unbound (aget locals (int id)))))) params)
         (= (count params) (loop [i 0 n 0]
                             (if (= i (alength locals)) n
                                 (recur (inc i) (if (identical? unbound (aget locals i)) n (inc n)))))))))

(defn- tail-peak! [s peak]
  (let [^longs counters (:counters s)]
    (aset-long counters 3 (max (aget counters 3) (long peak)))))

(defn materialize-tail-entry!
  "Internal exit ABI. Values are canonical carriers, steps already account for
   logical tail transfer; call-values! adds no extra instruction charge."
  [s name arguments logical-steps peak]
  (call-values! s [:direct name] arguments nil nil)
  (add-steps! s logical-steps)
  (tail-peak! s peak)
  s)

(defn materialize-tail-return!
  "Restore every visible local and exact return PC before ordinary delivery."
  [s name arguments return-body all-locals result logical-steps peak]
  (materialize-tail-entry! s name arguments logical-steps peak)
  (let [^objects locals (ctl s 1)]
    (doseq [[id value] all-locals] (aset locals (int id) value)))
  (put! s 0 return-body)
  (deliver! s result)
  s)

(def ^:private tail-region-generation (Object.))
(def ^:private tail-region-roots
  [call-values! callee-slots bind-params! registers deliver! push-frame!
   tail-entry-state? tail-peak! materialize-tail-entry! materialize-tail-return!
   has-frames? status steps function-slots tail-frame-depth])
(def ^:private nat-rc-generation (Object.))
(def ^:private nat-rc-roots [retain! release! assert-persistent!])
(defn- builtin-nat-rc? []
  (let [[retain release persistent] nat-rc-roots]
    (and (identical? retain retain!) (identical? release release!)
         (identical? persistent assert-persistent!) (m/builtin-scalar-reference?))))

(defn tail-region-tokens
  ([] (tail-region-tokens false))
  ([nat?]
   (cond-> [(scalar-wrapper-tokens) tail-region-generation (slots/tail-layout-token)]
     nat? (conj [nat-rc-generation (runtime/nat-arithmetic-token) (native/native-number-token)]))))
(defn current-tail-region?
  ([tokens symbols] (current-tail-region? tokens symbols false))
  ([tokens symbols nat?]
  (let [[call layout bind registers-root deliver push entry peak entry! return! frames status-root steps-root function-slots-root depth-root] tail-region-roots]
    (and (identical? (nth tokens 1) tail-region-generation)
         (= (nth tokens 2) (slots/tail-layout-token)) (slots/builtin-tail-layout?)
         (identical? call call-values!) (identical? layout callee-slots) (identical? bind bind-params!)
         (identical? registers-root registers) (identical? deliver deliver!) (identical? push push-frame!)
         (identical? entry tail-entry-state?) (identical? peak tail-peak!)
         (identical? entry! materialize-tail-entry!) (identical? return! materialize-tail-return!)
         (identical? frames has-frames?) (identical? status-root status) (identical? steps-root steps) (identical? function-slots-root function-slots)
         (identical? depth-root tail-frame-depth)
         (current-scalar-wrapper? (nth tokens 0) "lean_uint64_add" :add)
         (or (not nat?)
             (and (= (nth tokens 3 nil) [nat-rc-generation (runtime/nat-arithmetic-token) (native/native-number-token)])
                  (builtin-nat-rc?) (runtime/builtin-nat-arithmetic? "lean_nat_add" :add)))
         (every? (fn [[symbol operation domain runtime-operation]]
                   (if (= :nat domain)
                     (runtime/builtin-nat-arithmetic? symbol runtime-operation)
                     (current-scalar-wrapper? (nth tokens 0) symbol operation))) symbols)))))
