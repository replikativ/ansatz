(ns prototype.runtime-expr-mvars
  "Pinned instantiate_mvars.cpp two-pass expression traversal. Guest MCtx
   operations and beta reduction are explicit calls; every suspended/cache
   value is owned in a snapshot heap node, not in a hidden host continuation."
  (:require [prototype.runtime-mvars :as levels]
            [prototype.runtime-expr-transform :as transform]
            [prototype.runtime-string :as string]
            [prototype.native-scalar :as native]
            [prototype.scalar :as scalar]))

(defn- name* [parts] (reduce (fn [p s] ["str" p s]) ["anonymous"] parts))
(def getter (name* ["Lean" "MetavarContext" "getExprAssignmentExp"]))
(def setter (name* ["Lean" "assignExp"]))
(def delayed-getter (name* ["Lean" "MetavarContext" "getDelayedMVarAssignmentExp"]))
(def beta (name* ["Lean" "Expr" "betaRev"]))
(def lift (name* ["Lean" "Expr" "liftLooseBVars"]))
(def requests
  {1 {:target getter :borrow [false false]}
   2 {:target setter :borrow [false false false] :transfer-context true}
   3 {:target delayed-getter :borrow [false false]}
   4 {:target levels/getter :borrow [false false]}
   5 {:target levels/setter :borrow [false false false]}
   6 {:target beta :borrow [false true false false]}
   7 {:target lift :borrow [true true true]}})
(def dependencies (mapv :target (vals (into (sorted-map) requests))))
(def supported-symbols {"lean_instantiate_expr_mvars" {:arity 2}})
(def internal-symbols
  {"prototype_emvars_begin" {:arity 2} "prototype_emvars_advance" {:arity 1}
   "prototype_emvars_arg" {:arity 2} "prototype_emvars_accept" {:arity 2}
   "prototype_emvars_finish" {:arity 1}})
(defn body [params dest]
  (let [[m e] params work dest opcode (inc dest) result (+ dest 2)
        args (mapv #(+ dest 3 %) (range 4)) ignored (+ dest 7) j (+ dest 8)
        v (fn [i] [:var i])
        branch (fn [[id {:keys [target borrow]}]]
                 [id (reduce (fn [next [position local]]
                               [:let local [:runtime "prototype_emvars_arg" [(v work) [:imm position]]] next])
                             [:call result [:direct target] (mapv v (take (count borrow) args))
                              [:let ignored [:runtime "prototype_emvars_accept" [(v work) (v result)]] [:jump j []]]]
                             (reverse (map-indexed vector (take (count borrow) args))))])]
    [:let work [:runtime "prototype_emvars_begin" [[:var m] [:var e]]]
     [:join j []
      [:let opcode [:runtime "prototype_emvars_advance" [(v work)]]
       [:case (v opcode)
        (into [[0 [:let result [:runtime "prototype_emvars_finish" [(v work)]] [:return (v result)]]]]
              (map branch (into (sorted-map) requests)))]]
      [:jump j []]]]))

(defn- fail [message data] (throw (ex-info message data)))
(def erased :prototype.machine/erased)
(defn- zero?* [ops x]
  (and (not ((:ref? ops) x))
       (or (= x 0) (and (native/native-scalar? x) (zero? (native/payload x)))
           (and (map? x) (= 0 (:tag x))))))
(defn- expr-node [ops world value]
  (let [n ((:node ops) world value) fields (vec (:fields n))
        expected ({0 1, 1 1, 2 1, 3 1, 4 2, 5 2, 6 3, 7 3, 8 4, 9 1, 10 2, 11 3} (:tag n))]
    (when-not (and (= :ctor (:kind n)) (some? expected) (= expected (count fields)))
      (fail "Malformed Expr in metavariable instantiation" {:value value :tag (:tag n)}))
    (assoc n :fields fields :data (scalar/read-bytes (:layout n) (:scalar-bytes n)
                                                   {:index expected :offset 0 :type "uint64" :region :scalar}))))
(defn- bit? [x n] (odd? (quot x #?(:clj (bigint (.shiftLeft java.math.BigInteger/ONE n)) :cljs (js/Math.pow 2 n)))))
(defn- has-mvar? [n] (or (bit? (:data n) 41) (bit? (:data n) 42)))
(defn- expr-mvar? [n] (bit? (:data n) 41))
(defn- has-fvar? [n] (bit? (:data n) 40))
(defn- name-key [ops world value]
  (loop [x value parts [] seen #{}]
    (if (zero?* ops x) (vec (rseq parts))
      (let [n ((:node ops) world x) [prefix component] (:fields n)]
        (when-not (and (= :ctor (:kind n)) (contains? #{1 2} (:tag n))
                       (= 2 (count (:fields n))) (not (contains? seen x)))
          (fail "Malformed/cyclic metavariable Name" {:value value}))
        (recur prefix (conj parts [(:tag n) (if (= 1 (:tag n))
                                            (string/string-value ops world component)
                                            (native/nat-value ops world component))]) (conj seen x))))))
(defn- work-node [ops world ref]
  (let [n ((:node ops) world ref)]
    (when-not (and (= :ctor (:kind n)) (= 1 (:rc n)) (map? (:expr-mvars-work n)))
      (fail "Expected uniquely owned Expr instantiation work" {}))
    (update n :fields vec)))
(defn- put-state [n state] (assoc n :expr-mvars-work state))
(defn- field [n i] (get-in n [:fields i]))
(defn- owned [n value] [(update n :fields conj value) (count (:fields n))])
(defn- borrowed [ops world n value]
  (let [[n i] (owned n value)] [((:retain ops) world value 1) n i]))
(defn- push [n & jobs] (update-in n [:expr-mvars-work :jobs] into jobs))
(defn- result [n i] (assoc-in n [:expr-mvars-work :last] i))
(defn- request [n helper args after]
  (assoc-in n [:expr-mvars-work :request] {:helper helper :args args :after after}))
(defn- child [ops world n i position]
  (borrowed ops world n (nth (:fields (expr-node ops world (field n i))) position)))
(defn- app-spine [ops world n i]
  (loop [n n world world current i args []]
    (let [node (expr-node ops world (field n current))]
      (if (= 5 (:tag node))
        (let [[world n arg] (borrowed ops world n (second (:fields node)))
              [world n fn] (borrowed ops world n (first (:fields node)))]
          (recur n world fn (conj args arg))) [world n current args]))))
(defn- array-values [ops world value]
  (let [n ((:node ops) world value)]
    (when-not (= :array (:kind n)) (fail "Delayed assignment expected Expr array" {}))
    (vec (:fields n))))
(defn- delayed [ops world value]
  (let [n ((:node ops) world value)]
    (when-not (and (= :ctor (:kind n)) (= 0 (:tag n)) (= 2 (count (:fields n))))
      (fail "Malformed delayed metavariable assignment" {}))
    (vec (:fields n))))
(defn- rebuild [ops world n original fields]
  (let [[world value] (transform/rebuild ops world (field n original) fields)
        [n i] (owned n value)] [world (result n i)]))
(defn- array-slot [ops world n indices]
  (let [values (mapv #(field n %) indices)
        world (reduce #((:retain ops) %1 %2 1) world values)
        [world value] ((:allocate ops) world :array 246 values)
        [n i] (owned n value)] [world n i]))
(defn- cache-result [n original saved-scope]
  (let [state (:expr-mvars-work n) last (:last state) phase (:phase state)
        value (field n original)]
    (if (= 1 phase)
      (assoc-in n [:expr-mvars-work :cache value] last)
      (let [key [value (:depth state)] rs (:result-scope state) scopes (:scopes state)
            prior (some #(get % key) (rseq scopes))
            last (if (= rs (:scope prior)) (:value prior) last)
            entry {:value last :scope rs}
            scopes (reduce #(assoc-in %1 [%2 key] entry) scopes (range rs (count scopes)))]
        (-> n (assoc-in [:expr-mvars-work :last] last)
            (assoc-in [:expr-mvars-work :scopes] scopes)
            (assoc-in [:expr-mvars-work :result-scope] (max saved-scope rs)))))))

(declare advance)

(defn- step [ops world n [op i a b c]]
  (let [state (:expr-mvars-work n) last (:last state) phase (:phase state)
        node (when (contains? #{:visit :app-struct :sort-done :const-done :one-done
                               :binding-domain :binding-done :let-type :let-value :let-done} op)
               (expr-node ops world (field n i)))]
    (case op
      :visit
      (let [outer? (empty? (:subst state)) value (field n i)
            entry (if (= phase 1) (when-let [x (get (:cache state) value)] {:value x :scope 0})
                    (get (peek (:scopes state)) [value (:depth state)]))]
        (cond
          a [world (push n [:app-struct i])]
          (if (= phase 1) (not (has-mvar? node))
            (and (or (not (has-fvar? node)) outer?) (not (expr-mvar? node)))) [world (result n i)]
          entry [world (cond-> (result n (:value entry)) (= phase 2)
                         (update-in [:expr-mvars-work :result-scope] max (:scope entry)))]
          :else
          (let [tag (:tag node) saved (:result-scope state)
                structured? (not (contains? #{1 2} tag))
                n (if structured? (push n [:finish i saved])
                    (if (= phase 2) (push n [:restore-scope saved]) n))
                n (if (= phase 2) (assoc-in n [:expr-mvars-work :result-scope] 0) n)]
            (case tag
              1 (if (= phase 1) (fail "Inconsistent fvar Expr cache" {})
                  (if-let [{:keys [depth scope value]} (get (:subst state) (name-key ops world (first (:fields node))))]
                    (let [delta (- (:depth state) depth)
                          n (update-in n [:expr-mvars-work :result-scope] max scope)]
                      (when (neg? delta) (fail "Invalid delayed substitution binder depth" {}))
                      (if (zero? delta) [world (result n value)]
                        (let [[n cutoff] (owned n 0) [n delta] (owned n delta)]
                          [world (request n 7 [value cutoff delta] nil)]))) [world (result n i)]))
              2 (if (= phase 2)
                  (do (when-not outer? (fail "Bare unresolved MVar inside resolvable delayed assignment" {}))
                      [world (result n i)])
                  (let [[world n mid] (child ops world n i 0)]
                    [world (push n [:get-assignment mid [:mvar-direct i mid]])]))
              3 (let [[world n l] (child ops world n i 0)]
                  [world (push n [:sort-done i] [:start-level l])])
              4 (let [[world n ls] (child ops world n i 1)]
                  [world (push n [:const-done i] [:levels-list ls])])
              5 (let [[world n head args] (app-spine ops world n i)
                      head-node (expr-node ops world (field n head))]
                  (if (not= 2 (:tag head-node)) [world (push n [:app-struct i])]
                    (let [[world n mid] (borrowed ops world n (first (:fields head-node)))
                          job [:app-direct i {:mid mid :args args}]]
                      [world (if (= phase 1) (push n [:get-assignment mid job])
                               (request n 3 [0 mid] [:app-delayed i {:mid mid :args args}]))])))
              (6 7) (let [[world n domain] (child ops world n i 1)]
                      [world (push n [:binding-domain i (:depth state)] [:visit domain false])])
              8 (let [[world n ty] (child ops world n i 1)]
                  [world (push n [:let-type i (:depth state)] [:visit ty false])])
              (10 11) (let [position (if (= tag 10) 1 2) [world n child] (child ops world n i position)]
                        [world (push n [:one-done i position] [:visit child false])])
              (fail "Inconsistent hasMVar Expr cache" {:tag tag})))))
      :finish [world (cache-result n i a)]
      :restore-scope [world (update-in n [:expr-mvars-work :result-scope] max i)]
      :one-done (rebuild ops world n i (assoc (:fields node) a (field n last)))
      :sort-done (rebuild ops world n i [(field n last)])
      :const-done (rebuild ops world n i (assoc (:fields node) 1 (field n last)))
      :binding-domain
      (let [[world n body] (child ops world n i 2)]
        [world (-> n (assoc-in [:expr-mvars-work :depth] (inc a))
                   (push [:binding-done i a last] [:visit body false]))])
      :binding-done
      (rebuild ops world (assoc-in n [:expr-mvars-work :depth] a) i
               (-> (:fields node) (assoc 1 (field n b)) (assoc 2 (field n last))))
      :let-type
      (let [[world n value] (child ops world n i 2)]
        [world (push n [:let-value i a last] [:visit value false])])
      :let-value
      (let [[world n body] (child ops world n i 3)]
        [world (-> n (assoc-in [:expr-mvars-work :depth] (inc a))
                   (push [:let-done i a b last] [:visit body false]))])
      :let-done
      (rebuild ops world (assoc-in n [:expr-mvars-work :depth] a) i
               (-> (:fields node) (assoc 1 (field n b)) (assoc 2 (field n c)) (assoc 3 (field n last))))
      :app-struct
      (let [[world n arg] (child ops world n i 1)]
        [world (push n [:app-arg i] [:visit arg false])])
      :app-arg
      (let [[world n fn] (child ops world n i 0)
            force? (= 5 (:tag (expr-node ops world (field n fn))))]
        [world (push n [:app-fn i last] [:visit fn force?])])
      :app-fn
      (let [old (:fields (expr-node ops world (field n i)))]
        (rebuild ops world n i [(field n last) (field n a)]))
      :levels-list
      (let [value (field n i)]
        (if (zero?* ops value) [world (result n i)]
          (let [list-node ((:node ops) world value)]
            (when-not (and (= :ctor (:kind list-node)) (= 1 (:tag list-node)) (= 2 (count (:fields list-node))))
              (fail "Malformed constant universe-level list" {}))
            (let [[world n head] (borrowed ops world n (first (:fields list-node)))
                  [world n tail] (borrowed ops world n (second (:fields list-node)))]
              [world (push n [:levels-head i tail] [:start-level head])]))))
      :levels-head [world (push n [:levels-tail i last] [:levels-list a])]
      :levels-tail
      (let [old ((:node ops) world (field n i)) values [(field n a) (field n last)]]
        (if (= values (vec (:fields old))) [world (result n i)]
          (let [world (reduce #((:retain ops) %1 %2 1) world values)
                [world value] ((:allocate ops) world :ctor 1 values) [n index] (owned n value)]
            [world (result n index)])))
      :start-level
      ;; Context transfers into a reusable nested level worker. Its cache is
      ;; shared across all sorts/constants in this expression pass.
      (let [ctx (field n 0) value (field n i)
            world ((:retain ops) world value 1)
            n (assoc-in n [:fields 0] erased)
            world ((:replace-node ops) world (:work-ref state) n)
            existing (field n 2)
            [world worker] (if (= existing erased)
                             (levels/evaluate ops world "prototype_lmvars_begin" [ctx value])
                             (levels/restart ops world existing ctx value))]
        [world (-> n (assoc-in [:fields 2] worker) (assoc-in [:expr-mvars-work :level-running?] true))])
      :get-assignment [world (request n 1 [0 i] [:assignment-found i a])]
      :assignment-found
      (if-not (:found state) [world (push n a)]
        (let [value (field n last) key (name-key ops world (field n i))
              outer? (empty? (:subst state))
              ready? (contains? (:normalized state) key)
              skip? (if (= phase 1) (or ready? (not (has-mvar? (expr-node ops world value)))) (and outer? ready?))]
          (if skip? [world (push n a)]
            [world (-> n (cond-> (or (= phase 1) outer?)
                           (update-in [:expr-mvars-work :normalized] conj key))
                       (push [:assignment-visited i last (or (= phase 1) outer?) a] [:visit last false]))])))
      :assignment-visited
      (let [n (assoc-in n [:expr-mvars-work :found] true)]
        (if (and b (not= (field n a) (field n last)))
          [world (request n 2 [0 i last] c)] [world (push n c)]))
      :mvar-direct
      (if (:found state) [world n]
        [world (request n 3 [0 a] [:bare-delayed i])])
      :bare-delayed
      (if-not (:found state) [world (result n i)]
        (let [[_ pending] (delayed ops world (field n last))
              [world n pending] (borrowed ops world n pending)]
          [world (push n [:get-assignment pending [:pending-normalized i :bare]])]))
      :pending-normalized
      [world (-> n (cond-> (:found state) (assoc-in [:expr-mvars-work :has-delayed?] true))
                 (result i) (cond-> (= a :app) (push [:app-struct i])))]
      :app-direct
      (if (:found state)
        [world (push n [:visit-args (:args a) [] {:kind :beta :fn last}])]
        [world (request n 3 [0 (:mid a)] [:app-delayed i a])])
      :app-delayed
      (if-not (:found state) [world (push n [:app-struct i])]
        (let [record last [fvars pending] (delayed ops world (field n record))
              [world n pending] (borrowed ops world n pending)]
          (if (= phase 1) [world (push n [:get-assignment pending [:pending-normalized i :app]])]
            (if (> (count (array-values ops world fvars)) (count (:args a))) [world (push n [:app-struct i])]
              [world (push n [:delayed-resolvable i {:record record :pending pending :args (:args a)}]
                            [:resolvable-pending pending])]))))
      :delayed-resolvable
      (if (:predicate state)
        [world (push n [:visit-args (:args a) [] {:kind :delayed :record (:record a) :pending (:pending a)}])]
        (do (when (seq (:subst state)) (fail "Nonresolvable delayed MVar in inner mode" {}))
            [world (push n [:get-assignment (:pending a) [:app-unresolved i]])]))
      :app-unresolved [world (push n [:app-struct i])]
      :visit-args
      (if (seq i) [world (push n [:arg-visited (subvec i 1) a b] [:visit (first i) false])]
        (case (:kind b)
          :beta (let [[world n args] (array-slot ops world n a)
                      [n zeta] (owned n 1) [n mdata] (owned n 0)]
                  [world (request n 6 [(:fn b) args zeta mdata] nil)])
          :delayed
          (let [[fvars _] (delayed ops world (field n (:record b))) fvars (array-values ops world fvars)
                count! (count fvars) scope (count (:scopes state)) saved (:subst state)
                substitution
                (reduce (fn [subst [index fvar]]
                          (let [node (expr-node ops world fvar)]
                            (when-not (= 1 (:tag node)) (fail "Delayed local context contains a non-fvar" {}))
                            (assoc subst (name-key ops world (first (:fields node)))
                                   {:depth (:depth state) :scope scope :value (nth a (- (count a) 1 index))})))
                        saved (map-indexed vector fvars))]
            [world (-> n (assoc-in [:expr-mvars-work :subst] substitution)
                       (update-in [:expr-mvars-work :scopes] conj {})
                       (request 1 [0 (:pending b)] [:delayed-pending a count! saved]))])))
      :arg-visited [world (push n [:visit-args i (conj a last) b])]
      :delayed-pending
      (do (when-not (:found state) (fail "Resolvable pending MVar unexpectedly unassigned" {}))
          [world (push n [:delayed-finish i a b] [:visit last false])])
      :delayed-finish
      (let [scopes (pop (:scopes state)) scope (dec (count scopes))
            n (-> n (assoc-in [:expr-mvars-work :subst] b)
                  (assoc-in [:expr-mvars-work :scopes] scopes)
                  (update-in [:expr-mvars-work :result-scope] min scope))
            [world n args] (array-slot ops world n (subvec i 0 (- (count i) a)))
            [n zeta] (owned n 1) [n mdata] (owned n 0)]
        [world (request n 6 [last args zeta mdata] nil)])
      :resolvable-pending
      (let [key (name-key ops world (field n i)) prior (get (:pending-cache state) key)]
        (if prior [world (assoc-in n [:expr-mvars-work :predicate] (= :yes prior))]
          [world (-> n (assoc-in [:expr-mvars-work :pending-cache key] :busy)
                     (request 1 [0 i] [:resolvable-pending-found key]))]))
      :resolvable-pending-found
      (if-not (:found state)
        [world (-> n (assoc-in [:expr-mvars-work :predicate] false)
                   (assoc-in [:expr-mvars-work :pending-cache i] :no))]
        [world (push n [:resolvable-pending-cache i] [:resolvable-expr last])])
      :resolvable-pending-cache
      [world (assoc-in n [:expr-mvars-work :pending-cache i] (if (:predicate state) :yes :no))]
      :resolvable-expr
      (let [value (field n i) node (expr-node ops world value)]
        (cond
          (not (expr-mvar? node)) [world (assoc-in n [:expr-mvars-work :predicate] true)]
          (contains? (:predicate-cache state) value)
          [world (assoc-in n [:expr-mvars-work :predicate] (get (:predicate-cache state) value))]
          :else
          (let [n (push n [:resolvable-cache i])]
            (case (:tag node)
              2 [world (assoc-in n [:expr-mvars-work :predicate] false)]
              5 (let [[world n head args] (app-spine ops world n i)
                      head-node (expr-node ops world (field n head))]
                  (if (= 2 (:tag head-node))
                    (let [[world n mid] (borrowed ops world n (first (:fields head-node)))]
                      [world (request n 3 [0 mid] [:resolvable-app-found args])])
                    (let [[world n fn] (child ops world n i 0) [world n arg] (child ops world n i 1)]
                      [world (push n [:check-all [fn arg]])])))
              (6 7 8 10 11)
              (let [positions (case (:tag node) (6 7) [1 2] 8 [1 2 3] 10 [1] 11 [2])
                    [world n children] (reduce (fn [[world n children] position]
                                                 (let [[world n child] (child ops world n i position)]
                                                   [world n (conj children child)])) [world n []] positions)]
                [world (push n [:check-all children])])
              [world (assoc-in n [:expr-mvars-work :predicate] true)]))))
      :resolvable-cache
      [world (assoc-in n [:expr-mvars-work :predicate-cache (field n i)] (:predicate state))]
      :resolvable-app-found
      (if-not (:found state) [world (assoc-in n [:expr-mvars-work :predicate] false)]
        (let [[fvars pending] (delayed ops world (field n last))]
          (if (> (count (array-values ops world fvars)) (count i))
            [world (assoc-in n [:expr-mvars-work :predicate] false)]
            (let [[world n pending] (borrowed ops world n pending)]
              [world (push n [:resolvable-app-pending i] [:resolvable-pending pending])]))))
      :resolvable-app-pending
      [world (if (:predicate state) (push n [:check-all i]) n)]
      :check-all
      (if (empty? i) [world (assoc-in n [:expr-mvars-work :predicate] true)]
        [world (push n [:check-next (subvec i 1)] [:resolvable-expr (first i)])])
      :check-next [world (if (:predicate state) (push n [:check-all i]) n)]
      (fail "Unknown expression metavariable continuation" {:operation op}))))

(defn- advance [ops world ref]
  (loop [world world n (work-node ops world ref)]
    (let [state (:expr-mvars-work n)]
      (cond
        (:request state) [((:replace-node ops) world ref n) (:helper (:request state))]
        (:level-running? state)
        (let [worker (field n 2)
              [world opcode] (levels/evaluate ops world "prototype_lmvars_advance" [worker])]
          (if (zero? opcode)
            (let [[world pair] (levels/finish-keep ops world worker)
                  [ctx value] (:fields ((:node ops) world pair))
                  world (-> world ((:retain ops) ctx 1) ((:retain ops) value 1) ((:release ops) pair 1))
                  [n i] (owned n value)
                  n (-> n (assoc-in [:fields 0] ctx) (result i)
                        (update :expr-mvars-work dissoc :level-running?))]
              (recur world n))
            [((:replace-node ops) world ref
               (assoc-in n [:expr-mvars-work :request] {:helper (if (= opcode 1) 4 5) :source :level}))
             (if (= opcode 1) 4 5)]))
        (seq (:jobs state))
        (let [job (peek (:jobs state)) n (assoc-in n [:expr-mvars-work :jobs] (pop (:jobs state)))
              [world n] (step ops world n job)]
          (recur world n))
        (and (= 1 (:phase state)) (:has-delayed? state))
        (recur world (-> n (assoc-in [:expr-mvars-work :phase] 2)
                         (assoc-in [:expr-mvars-work :normalized] #{})
                         (assoc-in [:expr-mvars-work :scopes] [{}])
                         (assoc-in [:expr-mvars-work :jobs] [[:visit (:last state) false]])))
        :else [((:replace-node ops) world ref n) 0]))))

(defn- accept [ops world ref response]
  (let [n (work-node ops world ref) req (get-in n [:expr-mvars-work :request]) helper (:helper req)
        n (update n :expr-mvars-work dissoc :request)]
    (when-not req (fail "Expr instantiation has no requested guest response" {}))
    (if (= :level (:source req))
      (let [[world _] (levels/evaluate ops world (if (= helper 4) "prototype_lmvars_got" "prototype_lmvars_assigned")
                                      [(field n 2) response])]
        [((:replace-node ops) world ref n) 0])
      (let [[world n]
            (case helper
              (1 3)
              (if (zero?* ops response)
                [world (assoc-in n [:expr-mvars-work :found] false)]
                (let [option ((:node ops) world response)]
                  (when-not (and (= :ctor (:kind option)) (= 1 (:tag option)) (= 1 (count (:fields option))))
                    (fail "Malformed assignment lookup Option" {}))
                  (let [[world n i] (borrowed ops world n (first (:fields option)))
                        world ((:release ops) world response 1)]
                    [world (-> n (result i) (assoc-in [:expr-mvars-work :found] true))])))
              2 (do (when-not (:context-transferred? req) (fail "MCtx setter did not receive its context owner" {}))
                    [world (assoc-in n [:fields 0] response)])
              (6 7) (let [[n i] (owned n response)] [world (result n i)]))
            n (if-let [after (:after req)] (push n after) n)]
        [((:replace-node ops) world ref n) 0]))))

(defn evaluate [ops world symbol args]
  (let [spec (or (get supported-symbols symbol) (get internal-symbols symbol))]
    (when-not (and spec (= (:arity spec) (count args)))
      (fail "Invalid expression instantiation runtime call" {:symbol symbol})))
  (when (contains? supported-symbols symbol)
    (fail "Expression metavariable instantiation requires explicit guest-call lowering" {:symbol symbol}))
  (if (= symbol "prototype_emvars_begin")
    (let [[world ref] ((:allocate ops) world :ctor 0 (conj args erased))
          n ((:node ops) world ref)
          state {:phase 1 :depth 0 :work-ref ref :jobs [[:visit 1 false]] :last 1
                 :cache {} :normalized #{} :has-delayed? false :scopes [{}]
                 :result-scope 0 :subst {} :pending-cache {} :predicate-cache {}}]
      [((:replace-node ops) world ref (put-state n state)) ref])
    (let [ref (first args)]
      (case symbol
        "prototype_emvars_advance" (advance ops world ref)
        "prototype_emvars_accept" (accept ops world ref (second args))
        "prototype_emvars_arg"
        (let [n (work-node ops world ref) req (get-in n [:expr-mvars-work :request])
              helper (:helper req) position (second args)]
          (when-not (and req (integer? position) (< -1 position (count (:borrow (get requests helper)))))
            (fail "Invalid expression instantiation guest request argument" {}))
          (if (= :level (:source req))
            (levels/evaluate ops world (nth ["prototype_lmvars_context" "prototype_lmvars_name" "prototype_lmvars_value"] position)
                             [(field n 2)])
            (let [index (nth (:args req) position) value (field n index)
                  borrowed? (nth (:borrow (get requests helper)) position)]
              (if (and (= 0 position) (:transfer-context (get requests helper)))
                (do (when (:context-transferred? req) (fail "MCtx owner already transferred" {}))
                    [((:replace-node ops) world ref
                       (-> n (assoc-in [:fields 0] erased)
                           (assoc-in [:expr-mvars-work :request :context-transferred?] true))) value])
                [(if borrowed? world ((:retain ops) world value 1)) value]))))
        "prototype_emvars_finish"
        (let [n (work-node ops world ref) state (:expr-mvars-work n)]
          (when (or (:request state) (:level-running? state) (seq (:jobs state)) (seq (:subst state)))
            (fail "Expr instantiation has not completed" {}))
          (let [ctx (field n 0) value (field n (:last state))
                world (-> world ((:retain ops) ctx 1) ((:retain ops) value 1))
                [world pair] ((:allocate ops) world :ctor 0 [ctx value])]
            [((:release ops) world ref 1) pair]))))))
