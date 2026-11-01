(defn benchmark-baseline-runtime-value! [s symbol args]
  (second
   (runtime/evaluate
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
     :replace-node replace-node!}
    s symbol args)))
