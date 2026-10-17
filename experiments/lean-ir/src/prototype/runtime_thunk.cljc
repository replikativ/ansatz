(ns prototype.runtime-thunk
  "World-local memoized Lean thunks, using explicit guest IR to force closures.
   Owned closures/results live in :fields for normal RC traversal; begin transfers
   the closure to a visible Unit application and publication installs its result.
   The guest is single-threaded: recursive force fails instead of native spinning.
   Failed/in-flight executions are not falsely cached; resume/rollback must use
   the caller's explicit execution checkpoint. No host-global memoization."
)

(def supported-symbols
  {"lean_mk_thunk" {:arity 2}
   "lean_thunk_pure" {:arity 2}
   "lean_thunk_get_own" {:arity 2}})

;; These helpers occur only in trusted lowered IR, never as public extern ABIs.
(def internal-symbols
  {"prototype_thunk_ready" {:arity 1}
   "prototype_thunk_begin" {:arity 1}
   "prototype_thunk_read_own" {:arity 1}
   "prototype_thunk_publish_own" {:arity 2}})

(defn- fail [message data] (throw (ex-info message data)))
(defn- thunk! [ops world value]
  (when-not ((:ref? ops) value) (fail "Expected guest thunk reference" {:value value}))
  (let [node ((:node ops) world value)]
    (when-not (and (= :thunk (:kind node)) (= 251 (:tag node))
                   (contains? #{:pending :running :ready} (:thunk-state node))
                   (= (if (= :running (:thunk-state node)) 0 1) (count (:fields node))))
      (fail "Invalid guest thunk layout" {:value value :node node})) node))

(defn get-own-body
  "Lower borrowed Thunk.get into ordinary visible guest steps/calls. The thunk
   owns the cached result, and each get returns a distinct retained owner."
  [thunk-variable dest]
  (let [t [:var thunk-variable] ready dest closure (inc dest) value (+ dest 2) owned (+ dest 3)]
    [:let ready [:runtime "prototype_thunk_ready" [t]]
     [:case [:var ready]
      [[0 [:let closure [:runtime "prototype_thunk_begin" [t]]
           [:call value [:closure [:var closure]] [[:imm 0]]
            [:let owned [:runtime "prototype_thunk_publish_own" [t [:var value]]]
             [:return [:var owned]]]]]]
       [1 [:let owned [:runtime "prototype_thunk_read_own" [t]] [:return [:var owned]]]]]]]))

(defn evaluate [ops world symbol args]
  (let [spec (or (get supported-symbols symbol) (get internal-symbols symbol))]
    (when-not spec (fail "Unsupported thunk runtime extern" {:symbol symbol}))
    (when-not (= (:arity spec) (count args)) (fail "Thunk runtime arity mismatch" {:symbol symbol})))
  (case symbol
    ("lean_mk_thunk" "lean_thunk_pure")
    (let [value (second args)
          [world thunk] ((:allocate ops) world :thunk 251 [value])
          node ((:node ops) world thunk)]
      [((:replace-node ops) world thunk
         (assoc node :thunk-state (if (= symbol "lean_mk_thunk") :pending :ready))) thunk])
    "lean_thunk_get_own"
    (fail "Thunk.get requires explicit guest-call lowering" {:symbol symbol})
    (let [thunk (first args) node (thunk! ops world thunk) state (:thunk-state node)]
      (case symbol
        "prototype_thunk_ready"
        (case state :pending [world 0] :ready [world 1]
                    :running (fail "Recursive or concurrent guest thunk force is unsupported" {:thunk thunk}))
        "prototype_thunk_begin"
        (do (when-not (= :pending state) (fail "Guest thunk is not pending" {:thunk thunk :state state}))
            [((:replace-node ops) world thunk (assoc node :thunk-state :running :fields []))
             (first (:fields node))])
        "prototype_thunk_read_own"
        (do (when-not (= :ready state) (fail "Guest thunk is not ready" {:thunk thunk :state state}))
            (let [value (first (:fields node))] [((:retain ops) world value 1) value]))
        "prototype_thunk_publish_own"
        (do (when-not (= :running state) (fail "Guest thunk has no in-flight force" {:thunk thunk :state state}))
            (let [value (second args)
                  world ((:replace-node ops) world thunk (assoc node :thunk-state :ready :fields [value]))]
              [((:retain ops) world value 1) value]))))))
