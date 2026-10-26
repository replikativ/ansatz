(ns prototype.machine
  "Experimental persistent guest machine. Not a public Ansatz API.
   RC is logical; heap updates use host persistent maps. Native resources excluded."
  (:require #?(:clj [prototype.heap-hint :as heap-hint])
            [prototype.scalar :as scalar]
            [prototype.native-scalar :as native]
            [prototype.native-heap :as native-heap]
            [prototype.entropy :as entropy]
            [prototype.runtime-prim :as runtime]
            [prototype.runtime-task :as task]))

(defrecord Ref [id])
(defrecord Tag [tag])
(defrecord Builtin [name])
(def erased ::erased)
(defn ref? [x] (instance? Ref x))
(defn fail [message data] (throw (ex-info message data)))

(defn world [functions]
  {:functions functions :globals {} :heap {} :next-id 0 :events []
   :stats {:allocations 0 :field-stores 0 :steps 0 :max-frames 0}})

(defn native-reference?
  "Verified imported ranges are immutable RC0 roots; membership never decodes."
  [s r]
  (and (ref? r)
       (native-heap/imported? (or (:native-imports s) (get-in s [:world-context :native-imports])) (:id r))))

(defn node [s r]
  (if (native-reference? s r)
    (do
      (when (contains? (:heap s) (:id r))
        (fail "Imported guest reference is shadowed by mutable heap storage" {:ref r}))
      (let [n (or (native-heap/lookup (or (:native-imports s) (get-in s [:world-context :native-imports])) (:id r))
                  (fail "Missing verified imported guest node" {:ref r}))]
        (when-not (and (map? n) (= 0 (:rc n)) (vector? (:fields n))
                       (case (:kind n)
                         :ctor (and (integer? (:tag n)) (<= 0 (:tag n) 243))
                         :array (= 246 (:tag n))
                         (:byte-array :float-array :scalar-array) (= 248 (:tag n))
                         :string (= 249 (:tag n))
                         :mpz (= 250 (:tag n))
                         false))
          (fail "Malformed immutable imported guest node" {:ref r}))
        n))
    (or (get-in s [:heap (:id r)]) (fail "Dangling guest reference" {:ref r}))))

(defn- heap-assoc [s id node]
  (let [base (:heap s) result (assoc base id node)]
    (assoc s :heap #?(:clj (heap-hint/derive! base result id node) :cljs result))))
(defn- heap-dissoc [s id]
  (let [base (:heap s) result (dissoc base id)]
    (assoc s :heap #?(:clj (heap-hint/derive! base result id nil) :cljs result))))
(defn- heap-update [s id f & args]
  (heap-assoc s id (apply f (get (:heap s) id) args)))

(defn replace-node
  "Runtime updates may replace only local heap storage, never imported nodes."
  [s r n]
  (when (native-reference? s r)
    (fail "Cannot mutate immutable imported guest node" {:ref r}))
  (heap-assoc s (:id r) n))

(defn allocate [s kind tag fields]
  (let [id (:next-id s) r (->Ref id)]
    (when (native-reference? s r)
      (fail "Allocation collides with reserved imported guest range" {:id id}))
    [(-> s (update :next-id inc)
         (heap-assoc id {:kind kind :tag tag :fields (vec fields) :rc 1})
         (update-in [:stats :allocations] inc))
     r]))

(defn assert-persistent [s v]
  (when (and (ref? v) (not (native-reference? s v)) (not (zero? (:rc (node s v)))))
    (fail "Persistent RC invariant violated" {:ref v}))
  v)

(defn mark-persistent [s root]
  ;; Validate the entire reachable graph first: unsupported external objects must
  ;; not leave a partially persistent heap if validation fails.
  (let [ids (loop [todo [root] seen #{}]
              (if (empty? todo) seen
                (let [v (peek todo) todo (pop todo)]
                  (if (or (not (ref? v)) (contains? seen (:id v)) (native-reference? s v))
                    (recur todo seen)
                    (let [{:keys [kind fields]} (node s v)]
                      (when-not (contains? #{:ctor :closure :array :ref :task :byte-array :float-array :thunk :promise
                                             :string :mpz :scalar-array :mutex} kind)
                        (fail "Unsupported persistent object kind" {:kind kind}))
                      (recur (into todo fields) (conj seen (:id v))))))))]
    (reduce #(heap-update %1 %2 assoc :rc 0) s ids)))

(defn retain
  ([s v n] (retain s v n false))
  ([s v n persistent?]
   (when persistent? (assert-persistent s v))
   (if (and (ref? v) (not (native-reference? s v)) (not (zero? (:rc (node s v)))))
     (heap-update s (:id v) update :rc + n) s)))

(defn release
  ([s value n] (release s value n false))
  ([s value n persistent?]
   (when persistent? (assert-persistent s value))
   (loop [s s pending [[value n]]]
     (if (empty? pending) s
       (let [[v n] (peek pending) pending (pop pending)]
         (if (or (not (ref? v)) (native-reference? s v)) (recur s pending)
           (let [initial (node s v)
                 [s n] (if (and (= :task (:kind initial)) (:queued? initial))
                         (task/prepare-release
                          {:ref? ref? :node node :replace-node replace-node
                           :get-task-runtime :task-runtime :set-task-runtime (fn [s c] (assoc s :task-runtime c))}
                          s v n) [s n])
                 {:keys [rc fields kind tag]} (node s v) left (- rc n)]
             (cond
               (zero? rc) (recur s pending)
               (neg? left) (fail "Reference count underflow" {:ref v :rc rc :drop n})
               (pos? left) (recur (heap-update s (:id v) assoc :rc left) pending)
               :else (recur (cond-> (heap-dissoc (if (= kind :promise)
                                                    (task/deactivate-promise
                                                     {:ref? ref? :node node :replace-node replace-node}
                                                     s (node s v)) s)
                                                  (:id v))
                              (= kind :resource) (update :events conj [:released tag]))
                            (into pending (map #(vector % 1) fields)))))))))))

(defn delete-shell [s r]
  ;; lean_del_object checks lean_is_scalar before freeing. Erased reset shells
  ;; and immediate constructors legitimately reach this instruction.
  (if-not (ref? r) s
    (let [n (node s r)]
      (when-not (and (= :ctor (:kind n)) (= 1 (:rc n)))
        (fail "Invalid unique constructor deletion" {:ref r :node n}))
      (heap-dissoc s (:id r)))))

(defn set-constructor-tag [s r tag]
  (let [n (node s r)]
    (when-not (and (= :ctor (:kind n)) (= 1 (:rc n)) (integer? tag) (<= 0 tag 243))
      (fail "Invalid unique constructor tag store" {:ref r :tag tag}))
    (heap-update s (:id r) assoc :tag tag)))

(defn resource [s label] (allocate s :resource label []))

(defn value [s [op x]]
  (case op :imm x :var (if (contains? (:locals s) x) (get-in s [:locals x])
                         (fail "Unbound variable" {:variable x}))
        (fail "Unknown operand" {:operand [op x]})))

(defn tag [s x]
  (cond (ref? x) (:tag (node s x))
        ;; lean_obj_tag returns C unsigned (32 bits), including immediates.
        (native/native-scalar? x) (native/unsigned-value 32 x)
        (instance? Tag x) (:tag x)
        (number? x) x
        :else (fail "Value has no constructor tag" {:value x})))

(defn pointer-address [s v]
  ;; Guest addresses preserve identity and immediate tagging, not host addresses.
  ;; Heap IDs never collide with odd native boxed immediates and survive forks.
  (let [n (cond
            (ref? v) (do (node s v) #?(:clj (+' 4096 (*' 8 (:id v))) :cljs (+ 4096 (* 8 (:id v)))))
            (native/native-scalar? v) (native/pointer-word v)
            (instance? Tag v) #?(:clj (inc' (*' 2 (:tag v))) :cljs (inc (* 2 (:tag v))))
            (and (integer? v) (<= 0 v #?(:clj 9223372036854775807N :cljs 9007199254740991)))
            #?(:clj (inc' (*' 2 v)) :cljs (inc (* 2 v)))
            :else (fail "Pointer identity unavailable for this runtime representation" {:value v}))]
    (scalar/integer! "usize" n)))

(defn small-integer! [x]
  (when-not (and (integer? x) (<= -9007199254740991 x 9007199254740991))
    (fail "Prototype arithmetic requires an exact small integer" {:value x}))
  x)

(defn scalar [op args]
  (let [args (mapv small-integer! args)
        arity (case op :add 2 (:dec :inc :zero?) 1 (fail "Unknown scalar primitive" {:op op}))]
    (when-not (= arity (count args)) (fail "Scalar primitive arity" {:op op}))
    (small-integer!
     (case op :add (+ (first args) (second args)) :dec (dec (first args))
           :inc (inc (first args)) :zero? (if (zero? (first args)) 1 0)))))

(defn scalar-constructor [s tag fields layout]
  (scalar/layout! layout)
  (when-not (= (:objects layout) (count fields)) (fail "Scalar constructor object count mismatch" {}))
  (let [[s r] (allocate s :ctor tag fields)]
    [(heap-update s (:id r) assoc :layout layout :scalar-bytes {}) r]))

(defn read-scalar-node [n slot]
  (when-not (and (= :ctor (:kind n)) (:layout n)) (fail "Expected scalar constructor storage" {:node n}))
  (scalar/read-bytes (:layout n) (:scalar-bytes n) slot))

(defn write-scalar-node [n slot value]
  (when-not (and (= :ctor (:kind n)) (= 1 (:rc n)) (:layout n))
    (fail "Invalid unique scalar store" {:node n}))
  (assoc n :scalar-bytes (scalar/write-bytes (:layout n) (:scalar-bytes n) slot value)))

(defn box-value [s type x]
  (let [x (scalar/value! type x)]
    (if-let [layout (scalar/box-layout type)]
      (let [[s r] (scalar-constructor s 0 [] layout)]
        [(heap-update s (:id r) write-scalar-node (scalar/box-slot type) x) r])
      [s x])))

(defn unbox-value [s type x]
  (if (scalar/box-layout type)
    (read-scalar-node (node s x) (scalar/box-slot type))
    (scalar/integer! type (if (instance? Tag x) (:tag x) x))))

(defn environment-entry [s name]
  (when-not (map? (:environment s))
    (fail "Missing guest environment-variable input" {}))
  [s (get (:environment s) name)])

(defn runtime-build-entry
  "Read explicitly captured producer build metadata; overrides are snapshot-local.
   No installed host library is queried, and absent capabilities fail closed."
  [s symbol]
  (doseq [key [:runtime-build :runtime-build-overrides]
          :when (contains? s key)]
    (when-not (map? (get s key))
      (fail "Invalid guest runtime build capability" {:key key})))
  (let [overrides (:runtime-build-overrides s) profile (:runtime-build s)]
    (cond
      (contains? overrides symbol) (get overrides symbol)
      (contains? profile symbol) (get profile symbol)
      :else (fail "Missing explicit guest runtime build capability" {:symbol symbol}))))

(defn heartbeat-allocation-count [s]
  (- (get-in s [:stats :allocations]) (get s :heartbeat-allocation-offset 0)))

(defn expr [s [op a b c]]
  (case op
    :literal [s a]
    :ctor (let [fields (mapv #(value s %) b)]
            (if (empty? fields) [s (->Tag a)] (allocate s :ctor a fields)))
    :project (let [r (value s a)] [s (nth (:fields (node s r)) b)])
    :shared? (let [r (value s a)] [s (if (and (ref? r) (not= (:rc (node s r)) 1)) 1 0)])
    :scalar-ctor (scalar-constructor s a (mapv #(value s %) b) c)
    :scalar-get [s (read-scalar-node (node s (value s a)) b)]
    :box (box-value s a (value s b))
    :unbox [s (unbox-value s a (value s b))]
    :closure (let [[s r] (allocate s :closure nil (mapv #(value s %) b))]
               [(heap-update s (:id r) assoc :function a) r])
    :runtime (runtime/evaluate {:get-stdio-runtime :stdio-runtime :set-stdio-runtime (fn [s c] (assoc s :stdio-runtime c))
                                :get-task-runtime :task-runtime :set-task-runtime (fn [s c] (assoc s :task-runtime c))
                                :get-env environment-entry :runtime-build runtime-build-entry :allocation-count heartbeat-allocation-count :take-entropy entropy/take-bytes :pointer-address pointer-address :initializing? #(boolean (:initializing? %)) :ref? ref? :node node :allocate allocate :retain retain :release release
                                :replace-node replace-node}
                               s a (mapv #(value s %) b))
    :prim [s (scalar a (mapv #(value s %) b))]
    (fail "Unsupported expression" {:op op})))

(defn enter [s target args]
  (let [{:keys [params body] :as f} (get-in s [:functions target])]
    (when-not f (fail "Unresolved function" {:target target}))
    (when-not (= (count params) (count args))
      (fail "Guest arity mismatch" {:target target :expected (count params) :actual (count args)}))
    (assoc s :body body :locals (zipmap params args) :joins {})))

(defn start [s target args]
  (-> s (dissoc :result :resume-var :host-request) (assoc :frames [] :status :running) (enter target args)))

(defn deliver-result [s result]
  (if-let [frame (peek (:frames s))]
    (-> s (assoc :frames (pop (:frames s)) :body (:body frame)
                 :locals (assoc (:locals frame) (:dest frame) result) :joins (:joins frame)))
    (assoc s :status :done :result result)))

(defn erased-callee? [v]
  ;; lean_apply_n accepts scalar erased proofs and drops all supplied owners.
  (or (= erased v) (native/native-scalar? v) (instance? Tag v)
      (and (integer? v) (<= 0 v #?(:clj 9223372036854775807N :cljs 9007199254740991)))))

(defn application-shape [functions function fields args]
  (let [f (get functions function)]
    (when-not f (fail "Unresolved function" {:target function}))
    (let [arity (count (:params f)) fixed (count fields)
          all (into (vec fields) args)]
      (when-not (< fixed arity)
        (fail "Invalid closure capture count" {:target function :arity arity :fixed fixed}))
      {:partial? (< (count all) arity)
       :args (subvec all 0 (min arity (count all)))
       :surplus (subvec all (min arity (count all)))})))

(defn apply-target
  "Resolve one boxed application. Transfers argument owners, returning either
   :result for underapplication/erased proofs, or a callee plus owned :surplus.
   Surplus must remain in an explicit guest continuation until the callee returns."
  [s target args]
  (if (= :direct (first target)) {:state s :target (second target) :args args}
    (let [closure (value s (second target))]
      (when (empty? args) (fail "Empty boxed closure application" {}))
      (cond
        (instance? Builtin closure)
        (do (when-not (= :inc (:name closure))
              (fail "Unsupported pure host callback" {:target closure}))
            {:state s :target closure :args [(first args)] :surplus (subvec (vec args) 1)})
        (ref? closure)
        (let [{:keys [kind function fields]} (node s closure)]
          (when-not (= kind :closure) (fail "Expected guest closure" {:value closure}))
          (let [{:keys [partial? args surplus]} (application-shape (:functions s) function fields args)
                ;; Retain then release implements both native exclusive transfer
                ;; and shared/persistent capture copying without dangling owners.
                s (release (reduce #(retain %1 %2 1) s fields) closure 1)]
            (if partial?
              (let [[s r] (allocate s :closure nil args)]
                {:state (heap-update s (:id r) assoc :function function) :result r})
              {:state s :target function :args args :surplus surplus})))
        (erased-callee? closure)
        {:state (reduce #(release %1 %2 1) s args) :result closure}
        :else (fail "Expected closure" {:value closure})))))

(defn- push-frame [s frame]
  (let [frames (conj (:frames s) frame)]
    (-> s (assoc :frames frames)
        (update-in [:stats :max-frames] max (count frames)))))

(defn call [s target operands dest continuation]
  (let [application (apply-target s target (mapv #(value s %) operands))
        {:keys [target args surplus]} application
        s (:state application)
        s (if continuation
            (push-frame s (assoc (select-keys s [:locals :joins]) :dest dest :body continuation)) s)
        s (if (seq surplus)
            (push-frame s {:body [:tail [:closure [:var 0]] (mapv #(vector :imm %) surplus)]
                           :dest 0 :locals {} :joins {}}) s)]
    (cond
      (contains? application :result) (deliver-result s (:result application))
      (instance? Builtin target)
      (do (when-not (and (= :inc (:name target)) (= 1 (count args))
                         (number? (first args)))
            (fail "Unsupported pure host callback" {:target target :args args}))
          (deliver-result s (small-integer! (inc (small-integer! (first args))))))
      :else (enter s target args))))

(defn initialized-value [s name]
  (let [entry (get-in s [:globals name])]
    (when-not (= :ready (:status entry))
      (fail "Module global has not been initialized" {:name name :status (:status entry)}))
    (:value entry)))

(defn publish-io-global [s name type result]
  (let [{:keys [kind tag fields]} (node s result)]
    (when-not (and (= :ctor kind) (= tag 0) (= 1 (count fields)))
      (fail "Lean module initializer did not return IO success" {:name name :result result :tag tag}))
    (let [v (first fields)
          v (if (contains? #{"uint8" "uint16" "uint32" "uint64" "usize" "float" "float32"} type)
              (unbox-value s type v) v)]
      (-> s (mark-persistent v) (release result 1)
          (assoc-in [:globals name] {:status :ready :value v})
          (deliver-result v)))))

(defn step [s]
  (when-not (= :running (:status s)) (fail "Machine is not running" {:status (:status s)}))
  (let [s (update-in s [:stats :steps] inc)
        [op a b c d e] (:body s)]
    (case op
      :let (let [[s x] (expr s b)] (-> s (assoc-in [:locals a] x) (assoc :body c)))
      :call (call s b c a d)
      :tail (call s a b nil nil)
      :return (deliver-result s (value s a))
      :read-global (deliver-result s (initialized-value s a))
      :begin-init (let [entry (get-in s [:globals a])]
                    (case (:status entry)
                      :ready (deliver-result s (:value entry))
                      :initializing (fail "Recursive global initialization" {:name a})
                      (call (assoc-in s [:globals a] {:status :initializing})
                            [:direct b] c 0 [:publish-io-global a d [:var 0]])))
      :publish-io-global (publish-io-global s a b (value s c))
      :global (let [entry (get-in s [:globals a])]
                (case (:status entry)
                  :ready (deliver-result s (:value entry))
                  :initializing (fail "Recursive global initialization" {:name a})
                  (call (assoc-in s [:globals a] {:status :initializing})
                        [:direct b] [] 0 [:publish-global a [:var 0]])))
      :publish-global (let [v (value s b)]
                        (-> s (mark-persistent v)
                            (assoc-in [:globals a] {:status :ready :value v})
                            (deliver-result v)))
      :join (-> s (assoc-in [:joins a] {:params b :body c :locals (:locals s)}) (assoc :body d))
      :jump (let [{:keys [params body locals] :as join} (get-in s [:joins a])
                  args (mapv #(value s %) b)]
              (when-not (and join (= (count params) (count args)))
                (fail "Invalid join" {:join a}))
              (assoc s :body body :locals (merge locals (zipmap params args))))
      :case (let [t (tag s (value s a))
                  branch (or (some (fn [[key body]] (when (= key t) body)) b)
                             (some (fn [[key body]] (when (= :default key) body)) b))]
              (when-not branch (fail "Missing case" {:tag t})) (assoc s :body branch))
      :trap (fail "Reached unsupported guest declaration" {:declaration a :arguments (mapv #(value s %) b)})
      :unreachable (fail "Reached Lean unreachable instruction" {})
      :del (-> s (delete-shell (value s a)) (assoc :body b))
      :set-tag (-> s (set-constructor-tag (value s a) b) (assoc :body c))
      :inc (-> (retain s (value s a) b (boolean d)) (assoc :body c))
      :dec (-> (release s (value s a) b (boolean d)) (assoc :body c))
      :set (let [r (value s a) n (node s r)]
             (when-not (and (= :ctor (:kind n)) (= 1 (:rc n))
                            (< -1 b (count (:fields n))))
               (fail "Invalid unique field store" {:ref r :node n :field b}))
             (-> s (heap-update (:id r) assoc-in [:fields b] (value s c))
                 (update-in [:stats :field-stores] inc) (assoc :body d)))
      :scalar-set (let [r (value s a)]
                    (-> s (heap-update (:id r) write-scalar-node b (value s c))
                        (update-in [:stats :field-stores] inc) (assoc :body d)))
      :suspend (assoc s :status :suspended :resume-var a :body b)
      :host (assoc s :status :host-call :host-request {:symbol a :arguments (mapv #(value s %) b) :dest c}
                   :body d)
      (fail "Unsupported instruction" {:op op}))))

(defn run
  ([s] (run s 10000000))
  ([s fuel]
   (when-not (and (integer? fuel) (not (neg? fuel))) (fail "Invalid step budget" {:fuel fuel}))
   (loop [s s n fuel]
     (cond (not= :running (:status s)) s
           (zero? n) (assoc s :status :paused)
           :else (recur (step s) (dec n))))))

(defn resume [s x]
  (case (:status s)
    :suspended (-> s (assoc :status :running) (assoc-in [:locals (:resume-var s)] x)
                   (dissoc :resume-var))
    :paused (assoc s :status :running)
    :host-call (-> s (assoc :status :running) (assoc-in [:locals (get-in s [:host-request :dest])] x)
                   (dissoc :host-request))
    (fail "State is not resumable" {:status (:status s)})))

(defn guest-list [s xs]
  (reduce (fn [[s tail] x] (allocate s :ctor 1 [x tail])) [s (->Tag 0)] (reverse xs)))

(defn list-values [s root]
  (loop [r root xs []]
    (if (= 0 (tag s r)) xs
      (let [[head tail] (:fields (node s r))] (recur tail (conj xs head))))))

#?(:clj
   (do
     (def ^:private scalar-reference-generation (Object.))
     (def ^:private scalar-reference-roots [ref? node native-reference?])
     (defn scalar-reference-token [] scalar-reference-generation)
     (defn builtin-scalar-reference? []
       (let [[r n nr] scalar-reference-roots]
         (and (identical? r ref?) (identical? n node) (identical? nr native-reference?))))))
