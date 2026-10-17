(ns prototype.runtime-expr-replace
  "Lean4.33.1 kernel/replace_fn.cpp replace_fn. Callback FIRST, Expr SECOND;
   both borrowed. The generated guest calls consume fresh retained arguments.
   Some stops descent; None rebuilds in native order. Shared nodes memoize,
   including leaves; no-op preserves exact original pointers/cache/annotations.
   Heap work fields own callback/root/all intermediate results across pauses."
  (:require [prototype.native-scalar :as native] [prototype.runtime-expr-transform :as transform]))
(def supported-symbols {"lean_replace_expr" {:arity 2}})
(def internal-symbols
  {"prototype_expr_replace_begin" {:arity 2} "prototype_expr_replace_advance" {:arity 1}
   "prototype_expr_replace_callback" {:arity 1} "prototype_expr_replace_candidate" {:arity 1}
   "prototype_expr_replace_got" {:arity 2} "prototype_expr_replace_finish" {:arity 1}})
(defn body [params dest]
  (let [state dest status (inc dest) callback (+ dest 2) candidate (+ dest 3)
        response (+ dest 4) ignored (+ dest 5) result (+ dest 6) loop-id (+ dest 20)
        v #(vector :var %)
        resume [:let ignored [:runtime "prototype_expr_replace_got" [(v state) (v response)]] [:jump loop-id []]]
        request [:let callback [:runtime "prototype_expr_replace_callback" [(v state)]]
                 [:let candidate [:runtime "prototype_expr_replace_candidate" [(v state)]]
                  [:call response [:closure (v callback)] [(v candidate)] resume]]]
        finish [:let result [:runtime "prototype_expr_replace_finish" [(v state)]] [:return (v result)]]
        step [:let status [:runtime "prototype_expr_replace_advance" [(v state)]]
              [:case (v status) [[0 finish] [1 request]]]]]
    [:let state [:runtime "prototype_expr_replace_begin" (mapv v params)]
     [:join loop-id [] step [:jump loop-id []]]]))
(defn- fail [s d] (throw (ex-info s d)))
(defn- expr-node [ops w v]
  (when-not ((:ref? ops) v) (fail "Expected replace Expr reference" {}))
  (let [n ((:node ops) w v) cnt ({0 1 1 1 2 1 3 1 4 2 5 2 6 3 7 3 8 4 9 1 10 2 11 3} (:tag n))]
    (when-not (and (= :ctor (:kind n)) (some? cnt) (= cnt (count (:fields n))))
      (fail "Malformed replacement Expr" {:tag (:tag n)})) n))
(defn- work-node [ops w r]
  (let [n ((:node ops) w r)]
    (when-not (and (= :ctor (:kind n)) (= 3 (count (:fields n))) (map? (:expr-replace n)))
      (fail "Invalid expression replacement work state" {})) n))
(defn- at [n id] (assoc (second (:fields n)) :id id))
(defn- retain [ops w v] ((:retain ops) w v 1))
(defn- release [ops w v] ((:release ops) w v 1))
(defn- write-state [ops w ref state]
  ((:replace-node ops) w ref (assoc (work-node ops w ref) :expr-replace state)))
(defn- save-result [ops w ref state id shared? result]
  ;; RESULT owned, transferred into an owning list. All tables contain only IDs.
  (let [node (work-node ops w ref) [callback root prior] (:fields node)
        w (retain ops w prior) [w list] ((:allocate ops) w :ctor 1 [result prior])
        state (cond-> (update state :results conj (:id result)) shared? (assoc-in [:memo id] (:id result)))
        w ((:replace-node ops) w ref (assoc node :fields [callback root list] :expr-replace state))]
    (release ops w prior)))
(defn- child-indices [tag] (case tag 5 [0 1] (6 7) [1 2] 8 [1 2 3] 10 [1] 11 [2] []))
(defn- none?* [value]
  (and (not (nil? value)) (or (= 0 value) (and (native/native-scalar? value) (= 0 (native/payload value)))
                             (and (map? value) (= #{:tag} (set (keys value))) (= 0 (:tag value))))))
(defn evaluate [ops w symbol args]
  (when-not (= (get-in internal-symbols [symbol :arity]) (count args))
    (fail "Expr replacement requires generated guest-call lowering" {:symbol symbol}))
  (if (= symbol "prototype_expr_replace_begin")
    (let [[callback root] args n (expr-node ops w root)
          w (retain ops w callback)]
      ;; Keep the retain calls explicit: callback/root are borrowed extern args.
      (let [w (retain ops w root) [w ref] ((:allocate ops) w :ctor 0 [callback root 0])]
        [((:replace-node ops) w ref
           (assoc ((:node ops) w ref) :expr-replace
                  {:work [[:visit (:id root)]] :memo {} :results [] :root-rc (:rc n)})) ref]))
    (let [ref (first args) node (work-node ops w ref) state (:expr-replace node)]
      (case symbol
        "prototype_expr_replace_advance"
        (do (when (:request state) (fail "Replacement callback response pending" {}))
          (loop [w w]
            (let [node (work-node ops w ref) state (:expr-replace node)]
              (if-let [[action id shared? indices] (peek (:work state))]
                (let [state (update state :work pop) value (at node id)]
                  (if (= action :build)
                    (let [count-children (count indices) results (:results state)
                          split (- (count results) count-children)
                          new-children (mapv #(at node %) (subvec results split))
                          fields (reduce (fn [fields [i child]] (assoc fields i child))
                                         (vec (:fields (expr-node ops w value))) (map vector indices new-children))
                          state (assoc state :results (subvec results 0 split))
                          [w result] (transform/rebuild ops w value fields)]
                      (recur (save-result ops w ref state id shared? result)))
                    (if-let [result-id (get (:memo state) id)]
                      (recur (write-state ops w ref (update state :results conj result-id)))
                      (let [current (expr-node ops w value)
                            rc (if (= id (:id (second (:fields node)))) (:root-rc state) (:rc current))
                            state (assoc state :request {:id id :shared? (not= rc 1)})]
                        [(write-state ops w ref state) 1]))))
                [(write-state ops w ref state) 0]))))
        ("prototype_expr_replace_callback" "prototype_expr_replace_candidate")
        (let [request (:request state) _ (when-not request (fail "No pending replacement callback" {}))
              result (if (= symbol "prototype_expr_replace_callback") (first (:fields node)) (at node (:id request)))]
          [(retain ops w result) result])
        "prototype_expr_replace_got"
        (let [{:keys [id shared?] :as request} (:request state)
              _ (when-not request (fail "Unexpected replacement callback response" {}))
              response (second args) state (dissoc state :request)]
          (if (none?* response)
            (let [current (expr-node ops w (at node id)) indices (child-indices (:tag current))]
              (if (empty? indices)
                [(save-result ops (retain ops w (at node id)) ref state id shared? (at node id)) 0]
                [(write-state ops w ref
                   (update state :work into
                           (into [[:build id shared? indices]]
                                 (map #(vector :visit (:id (nth (:fields current) %))) (reverse indices))))) 0]))
            (let [_ (when-not ((:ref? ops) response) (fail "Invalid replacement Option result" {}))
                  option ((:node ops) w response)
                  _ (when-not (and (= :ctor (:kind option)) (= 1 (:tag option)) (= 1 (count (:fields option))))
                      (fail "Malformed replacement Option.some" {}))
                  result (first (:fields option)) _ (expr-node ops w result)
                  w (release ops (retain ops w result) response)]
              [(save-result ops w ref state id shared? result) 0])))
        "prototype_expr_replace_finish"
        (do (when (or (:request state) (seq (:work state)) (not= 1 (count (:results state))))
              (fail "Expression replacement is not complete" {}))
            (let [result (at node (first (:results state))) w (retain ops w result)]
              [(release ops w ref) result]))))))
