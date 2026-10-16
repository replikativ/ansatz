(ns prototype.machine
  "Experimental persistent guest machine. Not a public Ansatz API.
   RC is logical; heap updates use host persistent maps. Native resources excluded.")

(defrecord Ref [id])
(defrecord Tag [tag])
(defrecord Builtin [name])
(def erased ::erased)
(defn ref? [x] (instance? Ref x))
(defn fail [message data] (throw (ex-info message data)))

(defn world [functions]
  {:functions functions :heap {} :next-id 0 :events []
   :stats {:allocations 0 :field-stores 0 :steps 0 :max-frames 0}})

(defn node [s r]
  (or (get-in s [:heap (:id r)]) (fail "Dangling guest reference" {:ref r})))

(defn allocate [s kind tag fields]
  (let [id (:next-id s)]
    [(-> s (update :next-id inc)
         (assoc-in [:heap id] {:kind kind :tag tag :fields (vec fields) :rc 1})
         (update-in [:stats :allocations] inc))
     (->Ref id)]))

(defn retain [s v n]
  (if (ref? v)
    (do (node s v) (update-in s [:heap (:id v) :rc] + n)) s))

(defn release [s value n]
  (loop [s s pending [[value n]]]
    (if (empty? pending) s
        (let [[v n] (peek pending) pending (pop pending)]
          (if-not (ref? v) (recur s pending)
            (let [{:keys [rc fields kind tag]} (node s v) left (- rc n)]
              (when (neg? left) (fail "Reference count underflow" {:ref v :rc rc :drop n}))
              (if (pos? left)
                (recur (assoc-in s [:heap (:id v) :rc] left) pending)
                (recur (cond-> (update s :heap dissoc (:id v))
                         (= kind :resource) (update :events conj [:released tag]))
                       (into pending (map #(vector % 1) fields))))))))))

(defn resource [s label] (allocate s :resource label []))

(defn value [s [op x]]
  (case op :imm x :var (if (contains? (:locals s) x) (get-in s [:locals x])
                         (fail "Unbound variable" {:variable x}))
        (fail "Unknown operand" {:operand [op x]})))

(defn tag [s x]
  (cond (ref? x) (:tag (node s x))
        (instance? Tag x) (:tag x)
        (number? x) x
        :else (fail "Value has no constructor tag" {:value x})))

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

(defn expr [s [op a b]]
  (case op
    :literal [s a]
    :ctor (let [fields (mapv #(value s %) b)]
            (if (empty? fields) [s (->Tag a)] (allocate s :ctor a fields)))
    :project (let [r (value s a)] [s (nth (:fields (node s r)) b)])
    :shared? (let [r (value s a)] [s (if (and (ref? r) (> (:rc (node s r)) 1)) 1 0)])
    :closure (let [[s r] (allocate s :closure nil (mapv #(value s %) b))]
               [(assoc-in s [:heap (:id r) :function] a) r])
    :prim [s (scalar a (mapv #(value s %) b))]
    (fail "Unsupported expression" {:op op})))

(defn enter [s target args]
  (let [{:keys [params body] :as f} (get-in s [:functions target])]
    (when-not f (fail "Unresolved function" {:target target}))
    (when-not (= (count params) (count args))
      (fail "Guest arity mismatch" {:target target :expected (count params) :actual (count args)}))
    (assoc s :body body :locals (zipmap params args) :joins {})))

(defn start [s target args]
  (-> s (dissoc :result :resume-var) (assoc :frames [] :status :running) (enter target args)))

(defn deliver-result [s result]
  (if-let [frame (peek (:frames s))]
    (-> s (assoc :frames (pop (:frames s)) :body (:body frame)
                 :locals (assoc (:locals frame) (:dest frame) result) :joins (:joins frame)))
    (assoc s :status :done :result result)))

(defn apply-target [s target args]
  (if (= :direct (first target)) [s (second target) args]
    (let [closure (value s (second target))]
      (cond
        (instance? Builtin closure) [s closure args]
        (ref? closure)
        (let [{:keys [kind function fields]} (node s closure)]
          (when-not (= kind :closure) (fail "Expected guest closure" {:value closure}))
          ;; Applying consumes the closure and transfers fresh ownership of captures.
          (let [s (reduce #(retain %1 %2 1) s fields)]
            [(release s closure 1) function (into fields args)]))
        :else (fail "Expected closure" {:value closure})))))

(defn call [s target operands dest continuation]
  (let [args (mapv #(value s %) operands)
        [s target args] (apply-target s target args)
        tail? (nil? continuation)
        s (if tail? s
            (let [frames (conj (:frames s) (assoc (select-keys s [:locals :joins])
                                                 :dest dest :body continuation))]
              (-> s (assoc :frames frames)
                  (update-in [:stats :max-frames] max (count frames)))))]
    (if (instance? Builtin target)
      (do (when-not (and (= :inc (:name target)) (= 1 (count args))
                         (number? (first args)))
            (fail "Unsupported pure host callback" {:target target :args args}))
          (deliver-result s (small-integer! (inc (small-integer! (first args))))))
      (enter s target args))))

(defn step [s]
  (when-not (= :running (:status s)) (fail "Machine is not running" {:status (:status s)}))
  (let [s (update-in s [:stats :steps] inc)
        [op a b c d] (:body s)]
    (case op
      :let (let [[s x] (expr s b)] (-> s (assoc-in [:locals a] x) (assoc :body c)))
      :call (call s b c a d)
      :tail (call s a b nil nil)
      :return (deliver-result s (value s a))
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
      :inc (-> (retain s (value s a) b) (assoc :body c))
      :dec (-> (release s (value s a) b) (assoc :body c))
      :set (let [r (value s a) n (node s r)]
             (when-not (and (= :ctor (:kind n)) (= 1 (:rc n))
                            (< -1 b (count (:fields n))))
               (fail "Invalid unique field store" {:ref r :node n :field b}))
             (-> s (assoc-in [:heap (:id r) :fields b] (value s c))
                 (update-in [:stats :field-stores] inc) (assoc :body d)))
      :suspend (assoc s :status :suspended :resume-var a :body b)
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
    (fail "State is not resumable" {:status (:status s)})))

(defn guest-list [s xs]
  (reduce (fn [[s tail] x] (allocate s :ctor 1 [x tail])) [s (->Tag 0)] (reverse xs)))

(defn list-values [s root]
  (loop [r root xs []]
    (if (= 0 (tag s r)) xs
      (let [[head tail] (:fields (node s r))] (recur tail (conj xs head))))))
