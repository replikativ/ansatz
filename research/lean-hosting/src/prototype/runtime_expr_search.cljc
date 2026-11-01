(ns prototype.runtime-expr-search
  "Lean4.33.1 kernel/for_each_fn.cpp lean_find_expr. Predicate calls remain
   ordinary guest calls. Preorder, early exit and native shared-node exceptions
   are preserved; no Java checking projection or host predicate evaluation.
   Pending IDs/seen set live in a guest work node whose fields own closure/root.
   Both extern arguments are borrowed; Option result and its Expr field owned."
  (:require [prototype.native-scalar :as native] [prototype.scalar :as scalar]))
(def supported-symbols {"lean_find_expr" {:arity 2} "lean_find_ext_expr" {:arity 2}})
(def internal-symbols
  {"prototype_expr_find_begin" {:arity 2} "prototype_expr_find_ext_begin" {:arity 2} "prototype_expr_find_advance" {:arity 1}
   "prototype_expr_find_predicate" {:arity 1} "prototype_expr_find_candidate" {:arity 1}
   "prototype_expr_find_got" {:arity 2} "prototype_expr_find_finish" {:arity 1}})
(defn body
  ([params dest] (body params dest {}))
  ([params dest {:keys [extended?]}]
  (let [state dest status (inc dest) predicate (+ dest 2) candidate (+ dest 3)
        response (+ dest 4) ignored (+ dest 5) result (+ dest 6) loop-id (+ dest 20)
        v (fn [i] [:var i])
        resume [:let ignored [:runtime "prototype_expr_find_got" [(v state) (v response)]]
                [:jump loop-id []]]
        request [:let predicate [:runtime "prototype_expr_find_predicate" [(v state)]]
                 [:let candidate [:runtime "prototype_expr_find_candidate" [(v state)]]
                  [:call response [:closure (v predicate)] [(v candidate)] resume]]]
        finish [:let result [:runtime "prototype_expr_find_finish" [(v state)]] [:return (v result)]]
        step [:let status [:runtime "prototype_expr_find_advance" [(v state)]]
              [:case (v status) [[0 finish] [1 request]]]]]
    [:let state [:runtime (if extended? "prototype_expr_find_ext_begin" "prototype_expr_find_begin") (mapv v params)]
     [:join loop-id [] step [:jump loop-id []]]])))
(defn ext-body [params dest] (body params dest {:extended? true}))
(defn- fail [message data] (throw (ex-info message data)))
(defn- expr-node [ops world value]
  (when-not ((:ref? ops) value) (fail "Expected find Expr reference" {}))
  (let [node ((:node ops) world value) expected ({0 1 1 1 2 1 3 1 4 2 5 2 6 3 7 3 8 4 9 1 10 2 11 3} (:tag node))]
    (when-not (and (= :ctor (:kind node)) (some? expected) (= expected (count (:fields node))))
      (fail "Malformed find Expr" {:tag (:tag node)})) node))
(defn- work [ops world ref]
  (when-not ((:ref? ops) ref) (fail "Expected expression search work reference" {}))
  (let [node ((:node ops) world ref)]
    (when-not (and (= :ctor (:kind node)) (= 2 (count (:fields node))) (map? (:expr-search node)))
      (fail "Invalid expression search work state" {})) node))
(defn- ref-at [node id] (assoc (second (:fields node)) :id id))
(defn- save [ops world ref node] ((:replace-node ops) world ref node))
(defn- predicate-result [value extended?]
  (let [value (if (and (map? value) (contains? value :tag)) (:tag value) value)
        value (scalar/integer! "uint8" value)]
    (when-not (contains? (if extended? #{0 1 2} #{0 1}) value)
      (fail "Invalid expression predicate result" {})) value))
(defn- children [node]
  (let [fields (:fields node)]
    (case (:tag node) 5 [(nth fields 0) (nth fields 1)]
      (6 7) [(nth fields 1) (nth fields 2)]
      8 [(nth fields 1) (nth fields 2) (nth fields 3)]
      10 [(nth fields 1)] 11 [(nth fields 2)] [])))
(defn evaluate [ops world symbol args]
  (when-not (= (get-in internal-symbols [symbol :arity]) (count args))
    (fail "Expression search requires generated guest-call lowering" {:symbol symbol}))
  (if (contains? #{"prototype_expr_find_begin" "prototype_expr_find_ext_begin"} symbol)
    (let [[predicate root] args root-node (expr-node ops world root)
          world (reduce #((:retain ops) %1 %2 1) world args)
          [world state] ((:allocate ops) world :ctor 0 args)
          node ((:node ops) world state)]
      [(save ops world state
         (assoc node :expr-search {:work [[:visit (:id root)]] :seen #{} :root-rc (:rc root-node)
                                  :extended? (= symbol "prototype_expr_find_ext_begin")})) state])
    (let [ref (first args) node (work ops world ref) state (:expr-search node)]
      (case symbol
        "prototype_expr_find_advance"
        (do
          (when (:request state) (fail "Expression predicate result is pending" {}))
          (loop [state state]
            (if-let [[kind id] (when-not (:found state) (peek (:work state)))]
              (let [value (ref-at node id) expr (expr-node ops world value)
                    state (update state :work pop)]
                (if (and (= kind :app-function) (= 5 (:tag expr)))
                  ;; for_each_fn<false>::apply_fn bypasses BOTH predicate and
                  ;; visited cache on partial applications along the fn spine.
                  (recur (update state :work into
                                 [[:visit (:id (second (:fields expr)))]
                                  [:app-function (:id (first (:fields expr)))]]))
                  (let [rc (if (= id (:id (second (:fields node)))) (:root-rc state) (:rc expr))
                        cached? (and (not (contains? #{0 3 4} (:tag expr))) (not= 1 rc) (not= -1 rc))]
                    (if (and cached? (contains? (:seen state) id)) (recur state)
                      [(save ops world ref
                         (assoc node :expr-search
                                (cond-> (assoc state :request id) cached? (update :seen conj id)))) 1]))))
              [(save ops world ref (assoc node :expr-search state)) 0])))
        ("prototype_expr_find_predicate" "prototype_expr_find_candidate")
        (let [_ (when-not (:request state) (fail "No pending expression predicate" {}))
              value (if (= symbol "prototype_expr_find_predicate") (first (:fields node)) (ref-at node (:request state)))]
          [((:retain ops) world value 1) value])
        "prototype_expr_find_got"
        (let [id (:request state) _ (when-not id (fail "Unexpected expression predicate response" {}))
              extended? (:extended? state)
              response (predicate-result (second args) extended?)
              found? (= (if extended? 0 1) response)
              visit? (= (if extended? 1 0) response)
              current (expr-node ops world (ref-at node id))
              pending (when visit?
                        (if (and extended? (= 5 (:tag current)))
                          [[:app-function (:id (first (:fields current)))]
                           [:visit (:id (second (:fields current)))]]
                          (mapv #(vector :visit (:id %)) (children current))))
              state (dissoc state :request)
              state (if found? (assoc state :found id :work [])
                      (update state :work into (rseq (vec pending))))]
          [(save ops world ref (assoc node :expr-search state)) 0])
        "prototype_expr_find_finish"
        (do
          (when (or (:request state) (seq (:work state))) (fail "Expression search is not complete" {}))
          (let [[world result] (if-let [id (:found state)]
                                 (let [value (ref-at node id) world ((:retain ops) world value 1)]
                                   ((:allocate ops) world :ctor 1 [value])) [world 0])]
            [((:release ops) world ref 1) result]))))))
