(ns prototype.runtime-mvars
  "Pinned instantiate_mvars.cpp level pass. Persistent-map operations run as
   ordinary guest calls. The explicit traversal/cache is snapshot-local heap
   state: every stored reference has an owner in :fields, never in host globals."
  (:require [prototype.runtime-expr :as expr]
            [prototype.runtime-string :as string]
            [prototype.scalar :as scalar]
            [prototype.native-scalar :as native]))

(def supported-symbols {"lean_instantiate_level_mvars" {:arity 2}})
(def internal-symbols
  {"prototype_lmvars_begin" {:arity 2} "prototype_lmvars_advance" {:arity 1}
   "prototype_lmvars_context" {:arity 1} "prototype_lmvars_name" {:arity 1}
   "prototype_lmvars_value" {:arity 1} "prototype_lmvars_got" {:arity 2}
   "prototype_lmvars_assigned" {:arity 2} "prototype_lmvars_finish" {:arity 1}})
(def getter ["str" ["str" ["anonymous"] "Lean"] "getLevelMVarAssignmentExp"])
(def setter ["str" ["str" ["anonymous"] "Lean"] "assignLevelMVarExp"])
(defn body [params dest]
  (let [[m l] params s dest op (inc dest) ctx (+ dest 2) mid (+ dest 3)
        val (+ dest 4) response (+ dest 5) ignored (+ dest 6) result (+ dest 7)
        j (+ dest 8) v (fn [i] [:var i])
        resume (fn [symbol]
                 [:let ignored [:runtime symbol [(v s) (v response)]] [:jump j []]])
        request (fn [target args finish]
                  [:let ctx [:runtime "prototype_lmvars_context" [(v s)]]
                   [:let mid [:runtime "prototype_lmvars_name" [(v s)]]
                    (if (= target setter)
                      [:let val [:runtime "prototype_lmvars_value" [(v s)]]
                       [:call response [:direct target] args finish]]
                      [:call response [:direct target] args finish])]])]
    [:let s [:runtime "prototype_lmvars_begin" [(v m) (v l)]]
     [:join j []
      [:let op [:runtime "prototype_lmvars_advance" [(v s)]]
       [:case (v op)
        [[0 [:let result [:runtime "prototype_lmvars_finish" [(v s)]] [:return (v result)]]]
         [1 (request getter [(v ctx) (v mid)] (resume "prototype_lmvars_got"))]
         [2 (request setter [(v ctx) (v mid) (v val)]
                     (resume "prototype_lmvars_assigned"))]]]]
      ;; Assignment values are selected only inside the setter branch.
      [:jump j []]]]))

(defn- fail [message data] (throw (ex-info message data)))
(defn- zero?* [ops x]
  (and (not ((:ref? ops) x))
       (or (= 0 x) (and (native/native-scalar? x) (zero? (native/payload x)))
           (and (map? x) (= 0 (:tag x))))))
(defn- level [ops world x]
  (if (zero?* ops x) {:tag 0 :fields [] :data 2221}
    (let [n ((:node ops) world x) fields (vec (:fields n))
          count! ({1 1, 2 2, 3 2, 4 1, 5 1} (:tag n))]
      (when-not (and (= :ctor (:kind n)) (= count! (count fields)) (some? count!))
        (fail "Malformed universe level" {:value x :tag (:tag n)}))
      (assoc n :fields fields :data
             (scalar/read-bytes (:layout n) (:scalar-bytes n)
                                {:index (count fields) :offset 0 :type "uint64" :region :scalar})))))
(defn- power2 [n] #?(:clj (bigint (.shiftLeft java.math.BigInteger/ONE n)) :cljs (js/Math.pow 2 n)))
(defn- bits [x offset width] (mod (quot x (power2 offset)) (power2 width)))
(defn- has-mvar? [n] (= 1 (bits (:data n) 32 1)))
(defn- same-level? [ops world x y]
  (= 1 (second (expr/evaluate ops world "lean_level_eq" [x y]))))
(defn- offset [ops world x]
  (loop [x x n 0]
    (let [node (level ops world x)]
      (if (= 1 (:tag node)) (recur (first (:fields node)) (inc n)) [x n]))))
(defn- explicit? [ops world x] (zero?* ops (first (offset ops world x))))
(defn- never-zero? [ops world x]
  (loop [todo [x]]
    (if (empty? todo) false
      (let [n (level ops world (peek todo)) todo (pop todo)]
        (case (:tag n)
          1 true
          2 (recur (into todo (:fields n)))
          3 (recur (conj todo (second (:fields n))))
          (recur todo))))))
(defn- smart-select [ops world tag x y]
  (let [nx (level ops world x) ny (level ops world y)
        eq (fn [a b] (same-level? ops world a b))
        max-select (fn []
                     (cond
                       (and (explicit? ops world x) (explicit? ops world y))
                       (if (>= (bits (:data nx) 40 24) (bits (:data ny) 40 24)) x y)
                       (eq x y) x
                       (= 0 (:tag nx)) y
                       (= 0 (:tag ny)) x
                       (and (= 2 (:tag ny)) (some #(eq x %) (:fields ny))) y
                       (and (= 2 (:tag nx)) (some #(eq y %) (:fields nx))) x
                       :else (let [[bx ox] (offset ops world x) [by oy] (offset ops world y)]
                               (when (eq bx by) (if (> ox oy) x y)))))]
    (if (= tag 2) [2 (max-select)]
      (cond
        (never-zero? ops world y) [2 (max-select)]
        (= 0 (:tag ny)) [3 y]
        (or (= 0 (:tag nx))
            (and (= 1 (:tag nx)) (zero?* ops (first (:fields nx))))) [3 y]
        (eq x y) [3 x]
        :else [3 nil]))))
(defn- build-level [ops world tag children]
  (let [nodes (mapv #(level ops world %) children)
        mix (fn [a b] (second (string/evaluate ops world "lean_uint64_mix_hash" [a b])))
        hash (if (= tag 1) (mix 2243 (mod (:data (first nodes)) 4294967296))
               (mix (if (= tag 2) 2251 2267)
                    (mix (mod (:data (first nodes)) 4294967296)
                         (mod (:data (second nodes)) 4294967296))))
        data (second (expr/evaluate ops world "lean_level_mk_data"
                                   [hash (inc (reduce max 0 (map #(bits (:data %) 40 24) nodes)))
                                    (if (some has-mvar? nodes) 1 0)
                                    (if (some #(= 1 (bits (:data %) 33 1)) nodes) 1 0)]))
        world (reduce #((:retain ops) %1 %2 1) world children)
        [world value] ((:allocate ops) world :ctor tag children)
        node ((:node ops) world value) layout {:objects (count children) :usize 0 :ssize 8}
        bytes (scalar/write-bytes layout {} {:index (count children) :offset 0 :type "uint64" :region :scalar} data)]
    [((:replace-node ops) world value (assoc node :layout layout :scalar-bytes bytes)) value]))
(defn- work [ops world x]
  (let [n ((:node ops) world x)]
    (when-not (and (= :ctor (:kind n)) (= 1 (:rc n)) (map? (:level-mvars-work n)))
      (fail "Expected uniquely owned universe instantiation work" {:value x}))
    (update n :fields vec)))
(defn- save [ops world ref n]
  ((:replace-node ops) world ref n))
(defn- append-owned [n value] [(update n :fields conj value) (count (:fields n))])
(defn- append-borrowed [ops world n value]
  (let [[n i] (append-owned n value)] [((:retain ops) world value 1) n i]))
(defn- done [n original result]
  (-> n (assoc-in [:level-mvars-work :last] result)
      (assoc-in [:level-mvars-work :cache (get-in n [:fields original])] result)))

(defn restart
  "Reuse one level-pass cache for another level within an Expr instantiation.
   WORK is borrowed and uniquely owned; CONTEXT and LEVEL are transferred.
   A prior finish-keep must have transferred the old context out."
  [ops world ref context value]
  (let [n (work ops world ref)]
    (when-not (= :prototype.machine/erased (first (:fields n)))
      (fail "Reusable universe work still owns its context" {}))
    (let [[n i] (append-owned n value)
          n (-> n (assoc-in [:fields 0] context)
                (assoc-in [:level-mvars-work :jobs] [[:visit i]])
                (assoc-in [:level-mvars-work :last] i)
                (update :level-mvars-work dissoc :request))]
      [(save ops world ref n) ref])))

(defn finish-keep
  "Return owned (context, result), preserving WORK's owned cache for restart.
   Transfers context out and retains result; the caller still owns WORK."
  [ops world ref]
  (let [n (work ops world ref) state (:level-mvars-work n)]
    (when (or (seq (:jobs state)) (:request state) (seq (:active state)))
      (fail "Universe instantiation work has not completed" {}))
    (let [context (first (:fields n)) result (get-in n [:fields (:last state)])
          world ((:retain ops) world result 1)
          world (save ops world ref (assoc-in n [:fields 0] :prototype.machine/erased))]
      ((:allocate ops) world :ctor 0 [context result]))))

(defn- advance [ops world ref]
  (loop [world world n (work ops world ref)]
    (let [{:keys [jobs last cache request active]} (:level-mvars-work n)]
      (cond
        request [(save ops world ref n) (if (= :get (:kind request)) 1 2)]
        (empty? jobs) [(save ops world ref n) 0]
        :else
        (let [[op i a] (peek jobs) n (assoc-in n [:level-mvars-work :jobs] (pop jobs))
              value (get-in n [:fields i]) node (level ops world value)
              push (fn [n & jobs] (update-in n [:level-mvars-work :jobs] into jobs))]
          (case op
            :visit
            (cond
              (not (has-mvar? node)) (recur world (assoc-in n [:level-mvars-work :last] i))
              (contains? cache value) (recur world (assoc-in n [:level-mvars-work :last] (get cache value)))
              (contains? active value) (fail "Cyclic universe metavariable assignment" {:value value})
              :else
              (let [n (update-in n [:level-mvars-work :active] conj value)]
                (case (:tag node)
                  1 (let [[world n child] (append-borrowed ops world n (first (:fields node)))]
                      (recur world (push n [:succ i] [:visit child])))
                  (2 3) (let [[world n child] (append-borrowed ops world n (first (:fields node)))]
                          (recur world (push n [:left i] [:visit child])))
                  5 (let [[world n mid] (append-borrowed ops world n (first (:fields node)))]
                      (recur world (assoc-in n [:level-mvars-work :request] {:kind :get :original i :mid mid})))
                  (fail "Inconsistent universe hasMVar cache" {:tag (:tag node)}))))
            :succ
            (let [child (get-in n [:fields last]) old (first (:fields node))
                  [world result] (if (= child old) [world value] (build-level ops world 1 [child]))
                  [n result] (if (= result value) [n i] (append-owned n result))]
              (recur world (-> (done n i result) (update-in [:level-mvars-work :active] disj value))))
            :left
            (let [[world n child] (append-borrowed ops world n (second (:fields node)))]
              (recur world (push n [:right i last] [:visit child])))
            :right
            (let [x (get-in n [:fields a]) y (get-in n [:fields last])
                  unchanged (= [x y] (:fields node))
                  [tag selected] (if unchanged [(:tag node) value] (smart-select ops world (:tag node) x y))
                  [world result] (if (some? selected) [world selected] (build-level ops world tag [x y]))
                  [n result] (cond (= result value) [n i]
                                   (= result x) [n a]
                                   (= result y) [n last]
                                   :else (append-owned n result))]
              (recur world (-> (done n i result) (update-in [:level-mvars-work :active] disj value))))
            :assignment
            (let [n (update-in n [:level-mvars-work :active] disj value)]
              (if (= (get-in n [:fields a]) (get-in n [:fields last])) (recur world n)
                (let [[world n mid] (append-borrowed ops world n (first (:fields node)))]
                  (recur world (assoc-in n [:level-mvars-work :request]
                                        {:kind :assign :original i :mid mid :value last})))))
            (fail "Unknown universe instantiation continuation" {:operation op})))))))

(defn evaluate [ops world symbol args]
  (let [spec (or (get supported-symbols symbol) (get internal-symbols symbol))]
    (when-not (and spec (= (:arity spec) (count args)))
      (fail "Invalid universe instantiation runtime call" {:symbol symbol})))
  (when (contains? supported-symbols symbol)
    (fail "Universe instantiation requires explicit guest-call lowering" {:symbol symbol}))
  (if (= symbol "prototype_lmvars_begin")
    (let [[world ref] ((:allocate ops) world :ctor 0 args)
          n ((:node ops) world ref)]
      [(save ops world ref (assoc n :level-mvars-work {:jobs [[:visit 1]] :last 1 :cache {} :active #{}})) ref])
    (let [ref (first args) n (work ops world ref) state (:level-mvars-work n)
          request (:request state)]
      (case symbol
        "prototype_lmvars_advance" (advance ops world ref)
        ("prototype_lmvars_context" "prototype_lmvars_name" "prototype_lmvars_value")
        (let [index (case symbol "prototype_lmvars_context" 0 "prototype_lmvars_name" (:mid request)
                          "prototype_lmvars_value" (:value request))
              value (get-in n [:fields index])]
          (if (and (= symbol "prototype_lmvars_context") (= :assign (:kind request)))
            ;; C++ assign_lmvar steals the context owner. Keeping another work
            ;; owner here would force unnecessary PersistentHashMap copies.
            (do (when (:context-transferred? request)
                  (fail "Universe assignment context owner was already transferred" {}))
                [(save ops world ref (-> n (assoc-in [:fields 0] :prototype.machine/erased)
                                         (assoc-in [:level-mvars-work :request :context-transferred?] true))) value])
            [((:retain ops) world value 1) value]))
        "prototype_lmvars_got"
        (let [option (second args) opt (when ((:ref? ops) option) ((:node ops) world option))
              n (update n :level-mvars-work dissoc :request)]
          (if (zero?* ops option)
            [(save ops world ref (-> n (assoc-in [:level-mvars-work :last] (:original request))
                                    (update-in [:level-mvars-work :active] disj (get-in n [:fields (:original request)])))) 0]
            (do (when-not (and (= 1 (:tag opt)) (= 1 (count (:fields opt))))
                  (fail "Malformed level assignment Option" {}))
                (let [value (first (:fields opt)) [world n index] (append-borrowed ops world n value)
                      world ((:release ops) world option 1)
                      n (if (has-mvar? (level ops world value))
                          (update-in n [:level-mvars-work :jobs] into [[:assignment (:original request) index] [:visit index]])
                          (-> n (assoc-in [:level-mvars-work :last] index)
                              (update-in [:level-mvars-work :active] disj (get-in n [:fields (:original request)]))))]
                  [(save ops world ref n) 0]))))
        "prototype_lmvars_assigned"
        (let [world ((:release ops) world (first (:fields n)) 1)
              n (-> n (assoc-in [:fields 0] (second args)) (update :level-mvars-work dissoc :request))]
          [(save ops world ref n) 0])
        "prototype_lmvars_finish"
        (let [context (first (:fields n)) result (get-in n [:fields (:last state)])
              world (-> world ((:retain ops) context 1) ((:retain ops) result 1))
              [world pair] ((:allocate ops) world :ctor 0 [context result])]
          [((:release ops) world ref 1) pair])
        (fail "Universe instantiation requires explicit guest-call lowering" {:symbol symbol})))))
