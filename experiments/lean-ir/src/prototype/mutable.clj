(ns prototype.mutable
  "JVM-only mutable execution of the reference instruction set.
   Snapshots copy all live guest storage; no shared mutable pages or native resources."
  (:refer-clojure :exclude [run!])
  (:require [prototype.machine :as m]
            [prototype.leaf-compile :as leaf])
  (:import [java.util HashMap ArrayDeque Arrays]))

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
(defn- joins-in [n joins]
  (let [result (HashMap.)]
    (doseq [[k j] joins]
      (.put result k (object-array [(:params j) (:body j) (registers n (:locals j))])))
    result))
(defn- frame-in [n frame]
  (object-array [(:body frame) (:dest frame) (registers n (:locals frame))
                 (joins-in n (:joins frame))]))
(defn- frame-out [frame]
  {:body (aget ^objects frame 0) :dest (aget ^objects frame 1)
   :locals (bindings (aget ^objects frame 2)) :joins (joins-out (aget ^objects frame 3))})
(defn- slot-count [s]
  (let [forms (tree-seq coll? seq (:functions s))
        ids (concat (mapcat :params (vals (:functions s)))
                    (mapcat (fn [x]
                              (when (vector? x)
                                (case (first x)
                                  (:var :let :call :suspend) [(second x)]
                                  :join (nth x 2)
                                  []))) forms)
                    (keys (:locals s)))]
    (inc (reduce max 0 (filter integer? ids)))))
(defn function-slots [function]
  (slot-count {:functions {:callee function}}))

(defn thaw [snapshot]
  (let [n (slot-count snapshot)]
    (when (> n 1000000) (m/fail "Register limit" {:slots n}))
    (->Machine (:functions snapshot) n
               (object-array [(:body snapshot) (registers n (:locals snapshot))
                              (joins-in n (:joins snapshot)) (:next-id snapshot)
                              (:status snapshot) (:result snapshot) (:resume-var snapshot)])
               (HashMap. ^java.util.Map
                         (update-vals (:heap snapshot) #(update % :fields object-array)))
               (ArrayDeque. ^java.util.Collection
                            (mapv #(frame-in n %) (:frames snapshot)))
               (java.util.ArrayList. ^java.util.Collection (:events snapshot))
               (long-array (map (:stats snapshot) [:allocations :field-stores :steps :max-frames])))))

(defn freeze [s]
  (cond-> {:functions (:functions s)
           ;; vec may adopt a short Object[] instead of copying it.
           :heap (into {} (map (fn [[k v]] [k (update v :fields #(vec (aclone ^objects %)))]) (:heap s)))
           :next-id (ctl s 3) :events (vec (:events s))
           :stats (zipmap [:allocations :field-stores :steps :max-frames] (vec (aclone ^longs (:counters s))))
           :body (ctl s 0) :locals (bindings (ctl s 1)) :joins (joins-out (ctl s 2))
           :frames (mapv frame-out (:frames s))
           :status (ctl s 4)}
    (= :done (ctl s 4)) (assoc :result (ctl s 5))
    (= :suspended (ctl s 4)) (assoc :resume-var (ctl s 6))))

(defn- node [s r]
  (or (.get ^HashMap (:heap s) (:id r)) (m/fail "Dangling guest reference" {:ref r})))
(defn retain! [s v n]
  (when (m/ref? v)
    (.put ^HashMap (:heap s) (:id v) (update (node s v) :rc + n))))
(defn release! [s v n]
  (when (m/ref? v)
   (let [pending (ArrayDeque.)]
    (.addLast pending [v n])
    (while (not (.isEmpty pending))
      (let [[v n] (.removeLast pending)]
        (when (m/ref? v)
          (let [{:keys [rc kind tag fields] :as node} (node s v) left (- rc n)]
            (when (neg? left) (m/fail "Reference count underflow" {:ref v :rc rc :drop n}))
            (if (pos? left)
              (.put ^HashMap (:heap s) (:id v) (assoc node :rc left))
              (do (.remove ^HashMap (:heap s) (:id v))
                  (when (= :resource kind) (.add ^java.util.ArrayList (:events s) [:released tag]))
                  (doseq [f fields]
                    (when (m/ref? f) (.addLast pending [f 1]))))))))))))
(defn read-local [locals x]
  (let [v (aget ^objects locals (int x))]
    (if (identical? unbound v) (m/fail "Unbound variable" {:variable x}) v)))
(defn- value [s [op x]]
  (case op
    :imm x
    :var (read-local (ctl s 1) x)
    (m/fail "Unknown operand" {:op op})))
(defn- allocate! [s kind tag fields function]
  (let [id (ctl s 3)]
    (put! s 3 (inc id))
    (.put ^HashMap (:heap s) id (cond-> {:kind kind :tag tag :fields (object-array fields) :rc 1}
                                function (assoc :function function)))
    (bump! s 0 1) (m/->Ref id)))
(defn- expr! [s [op a b]]
  (case op
    :literal a
    :ctor (if (empty? b) (m/->Tag a) (allocate! s :ctor a (mapv #(value s %) b) nil))
    :project (aget ^objects (:fields (node s (value s a))) (int b))
    :shared? (let [r (value s a)] (if (and (m/ref? r) (> (:rc (node s r)) 1)) 1 0))
    :closure (allocate! s :closure nil (mapv #(value s %) b) a)
    :prim (m/scalar a (mapv #(value s %) b))
    (m/fail "Unsupported expression" {:op op})))
(defn deliver! [s result]
  (if (.isEmpty ^ArrayDeque (:frames s))
    (do (put! s 4 :done) (put! s 5 result))
    (let [frame ^objects (.removeLast ^ArrayDeque (:frames s))
          locals ^objects (aget frame 2)]
      (aset locals (int (aget frame 1)) result)
      (put! s 0 (aget frame 0)) (put! s 1 locals) (put! s 2 (aget frame 3)))))
(defn call-values! [s target args dest continuation]
  (let [[target args]
        (if (= :direct (first target)) [(second target) args]
          (let [closure (second target)]
            (cond
              (instance? prototype.machine.Builtin closure) [closure args]
              (m/ref? closure)
              (let [{:keys [kind function fields]} (node s closure)]
                (when-not (= :closure kind) (m/fail "Expected guest closure" {:value closure}))
                (doseq [v fields] (retain! s v 1))
                (let [args (into (vec fields) args)]
                  (release! s closure 1) [function args]))
              :else (m/fail "Expected closure" {:value closure}))))]
    (when continuation
      (.addLast ^ArrayDeque (:frames s) (object-array [continuation dest (ctl s 1) (ctl s 2)]))
      (let [a ^longs (:counters s)]
        (aset-long a 3 (max (aget a 3) (.size ^ArrayDeque (:frames s))))))
    (if (instance? prototype.machine.Builtin target)
      (do (when-not (and (= :inc (:name target)) (= 1 (count args)) (number? (first args)))
            (m/fail "Unsupported pure host callback" {:target target :args args}))
          (deliver! s (m/small-integer! (inc (m/small-integer! (first args))))))
      (let [{:keys [params body] :as f} (get (:functions s) target)
            slots (get (:register-layouts s) target (:slots s))]
        (when-not f (m/fail "Unresolved function" {:target target}))
        (when-not (= (count params) (count args)) (m/fail "Guest arity mismatch" {:target target}))
        (put! s 0 body)
        (if continuation
          (do (put! s 1 (bind-params! (registers slots nil) params args))
              (put! s 2 (HashMap.)))
          (let [old ^objects (ctl s 1)
                ^objects locals (if (< (alength old) slots) (registers slots nil) old)]
            (Arrays/fill locals unbound)
            (bind-params! locals params args)
            (put! s 1 locals)
            (.clear ^HashMap (ctl s 2))))))))

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
(defn project [s r i] (aget ^objects (:fields (node s r)) (int i)))
(defn shared? [s r] (if (and (m/ref? r) (> (:rc (node s r)) 1)) 1 0))
(defn tag-of [s v]
  (cond (m/ref? v) (:tag (node s v)) (instance? prototype.machine.Tag v) (:tag v)
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
  (let [n (node s r) fields ^objects (:fields n)]
    (when-not (and (= :ctor (:kind n)) (= 1 (:rc n)) (< -1 i (alength fields)))
      (m/fail "Invalid unique field store" {:ref r :field i}))
    (aset fields (int i) v) (bump! s 1 1)))
(defn suspend! [s dest body]
  (put! s 4 :suspended) (put! s 6 dest) (put! s 0 body))

(defn step! [s]
  (when-not (= :running (ctl s 4)) (m/fail "Machine is not running" {:status (ctl s 4)}))
  (bump! s 2 1)
  (let [[op a b c d] (ctl s 0)]
    (case op
      :let (do (aset ^objects (ctl s 1) (int a) (expr! s b)) (put! s 0 c))
      :call (call! s b c a d)
      :tail (call! s a b nil nil)
      :return (deliver! s (value s a))
      :join (do (join! s a b c) (put! s 0 d))
      :jump (jump-values! s a (mapv #(value s %) b))
      :case (let [tag (tag-of s (value s a))
                  branch (or (some (fn [[k body]] (when (= k tag) body)) b)
                             (some (fn [[k body]] (when (= k :default) body)) b))]
              (when-not branch (m/fail "Missing case" {:tag tag})) (put! s 0 branch))
      :inc (do (retain! s (value s a) b) (put! s 0 c))
      :dec (do (release! s (value s a) b) (put! s 0 c))
      :set (do (store! s (value s a) b (value s c)) (put! s 0 d))
      :suspend (suspend! s a b)
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
    (m/fail "State is not resumable" {:status (ctl s 4)})) s)
