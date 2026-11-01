(ns prototype.runtime-task
  "Snapshot-local cooperative tasks, promises and logical native ownership.
   Spawn/map/bind register jobs; guest get/wait steps execute queued producers and
   dependencies through ordinary guest calls. No host threads or implicit callback
   completion drain: hosts may explicitly drain queued jobs. Task queues own jobs,
   including BaseIO jobs whose user owner was dropped. Unresolved waits/cycles
   fail explicitly; suspended independent fibers/native timing are not emulated.
   Promise destruction resolves its outstanding result task to None."
  (:require [prototype.scalar :as scalar]
            [prototype.native-scalar :as native]
            [prototype.runtime-io :as io]
            [prototype.runtime-heartbeat :as heartbeat]))

(def supported-symbols
  {"lean_io_promise_new" {:arity 3}
   "lean_io_promise_resolve" {:arity 4}
   "lean_io_promise_result_opt" {:arity 2}
   "lean_option_get_or_block" {:arity 3}
   "lean_io_get_task_state" {:arity 3}
   "lean_io_cancel" {:arity 3}
   "lean_task_get_own" {:arity 2}
   "lean_task_spawn" {:arity 3} "lean_task_map" {:arity 6} "lean_task_bind" {:arity 6}
   "lean_io_as_task" {:arity 4} "lean_io_map_task" {:arity 7} "lean_io_bind_task" {:arity 7}
   "lean_io_wait" {:arity 3} "lean_io_wait_any" {:arity 4}
   "lean_io_check_canceled" {:arity 1}})

(def internal-symbols
  {"prototype_task_mode" {:arity 1} "prototype_task_begin" {:arity 1}
   "prototype_task_dependency" {:arity 1} "prototype_task_take_closure" {:arity 1}
   "prototype_task_publish" {:arity 2} "prototype_task_read_own" {:arity 1}
   "prototype_task_next" {:arity 0} "prototype_task_next_sync" {:arity 0}
   "prototype_task_sync_ready" {:arity 1} "prototype_task_wait_any_ready" {:arity 1}})

(def get-target ["str" ["str" ["anonymous"] "Task"] "get"])
(def job-modes {:spawn 1 :spawn-io 2 :map 3 :map-io 4 :bind 5 :bind-io 6})
(def erased :prototype.machine/erased)

(defn- letv [id expression continuation] [:let id expression continuation])
(defn- callv [id target arguments continuation] [:call id target arguments continuation])
(defn- varv [id] [:var id])
(defn- get-call [dest task continuation]
  (callv dest [:direct get-target] [[:imm erased] task] continuation))

(defn get-body [task-variable dest]
  (let [t (varv task-variable) mode dest begun (inc dest) dep (+ dest 2)
        arg (+ dest 3) closure (+ dest 4) out (+ dest 5) bound (+ dest 6)
        published (+ dest 7) result (+ dest 8) queued (+ dest 9)
        ready (letv result [:runtime "prototype_task_read_own" [t]] [:return (varv result)])
        publish (fn [value] (letv published [:runtime "prototype_task_publish" [t value]] ready))
        invoke (fn [kind arguments]
                 (letv closure [:runtime "prototype_task_take_closure" [t]]
                   (callv out [:closure (varv closure)] arguments
                     (if (contains? #{5 6} kind)
                       (get-call bound (varv out) (publish (varv bound)))
                       (publish (varv out))))))
        execute (fn [kind]
                  (letv begun [:runtime "prototype_task_begin" [t]]
                    (if (contains? #{1 2} kind)
                      (invoke kind [[:imm (if (= kind 1) 0 erased)]])
                      (letv dep [:runtime "prototype_task_dependency" [t]]
                        (get-call arg (varv dep)
                          (invoke kind (cond-> [(varv arg)] (contains? #{4 6} kind) (conj [:imm erased]))))))))
        blocked (letv queued [:runtime "prototype_task_next" []]
                  [:case (varv queued)
                   [[0 [:trap {:symbol "Task.get" :runtime-limit :unresolved-task
                               :message "No runnable producer, unresolved wait or dependency cycle"} [t]]]
                    [252 (get-call out (varv queued)
                           [:dec (varv out) 1 [:tail [:direct get-target] [[:imm erased] t]]])]]])]
    (letv mode [:runtime "prototype_task_mode" [t]]
      [:case (varv mode) (into [[0 ready]] (concat (map (fn [kind] [kind (execute kind)]) (range 1 7)) [[7 blocked]]))])))

(defn drain-body
  "Explicit host/resolve continuation: :sync-only true runs only synchronous
   dependents with ready inputs; false runs all queued work to quiescence."
  [dest sync-only]
  (let [job dest value (inc dest) loop-id (+ dest 20)]
    [:join loop-id []
     (letv job [:runtime (if sync-only "prototype_task_next_sync" "prototype_task_next") []]
       [:case (varv job)
        [[0 [:return [:imm 0]]]
         [252 (get-call value (varv job) [:dec (varv value) 1 [:jump loop-id []]])]]])
     [:jump loop-id []]]))

(defn wait-any-body [list-variable dest]
  (let [ready dest job (inc dest) ignored (+ dest 2) loop-id (+ dest 20)]
    [:join loop-id []
     (letv ready [:runtime "prototype_task_wait_any_ready" [(varv list-variable)]]
       [:case (varv ready)
        [[252 [:tail [:direct get-target] [[:imm erased] (varv ready)]]]
         [0 (letv job [:runtime "prototype_task_next" []]
              [:case (varv job)
               [[252 (get-call ignored (varv job) [:dec (varv ignored) 1 [:jump loop-id []]])]
                [0 [:trap {:symbol "IO.waitAny" :runtime-limit :unresolved-task
                            :message "No finished task or runnable producer"} [(varv list-variable)]]]]])]]])
     [:jump loop-id []]]))

(defn registration-body [symbol params dest]
  (let [task dest ready (inc dest) ignored (+ dest 2)
        return-task [:return (varv task)]]
    (letv task [:runtime symbol (mapv varv params)]
      (if (contains? #{"lean_task_map" "lean_task_bind" "lean_io_map_task" "lean_io_bind_task"} symbol)
        (letv ready [:runtime "prototype_task_sync_ready" [(varv task)]]
          [:case (varv ready)
           [[0 return-task]
            [1 [:inc (varv task) 1
                (get-call ignored (varv task) [:dec (varv ignored) 1 return-task])]]]])
        return-task))))

(defn- fail [message data] (throw (ex-info message data)))
(defn- node! [ops world value kind]
  (when-not ((:ref? ops) value) (fail "Expected guest task/promise reference" {:value value :kind kind}))
  (let [node ((:node ops) world value)]
    (when-not (= kind (:kind node)) (fail "Wrong guest task/promise object kind" {:value value :expected kind})) node))
(defn task-state [node]
  ;; Historical Task.pure snapshots use a single result field and no state key.
  (or (:task-state node) (when (= 1 (count (:fields node))) :ready)
      (fail "Malformed guest task state" {:node node})))
(defn- promise-task [ops world promise]
  (let [node (node! ops world promise :promise)]
    (when-not (and (= 244 (:tag node)) (= 1 (count (:fields node))))
      (fail "Malformed guest promise" {:promise promise}))
    (first (:fields node))))

(defn deactivate-promise
  "Called by RC only when the last promise owner is dropped. The task remains
   shared with result? holders. Generic release subsequently drops its owner."
  [ops world promise-node]
  (let [task (first (:fields promise-node)) node (node! ops world task :task)]
    (if (= :promise-pending (task-state node))
      ((:replace-node ops) world task (assoc node :task-state :ready :fields [0])) world)))

(defn- context [ops world]
  (or ((:get-task-runtime ops) world) {:queue [] :active []}))
(defn- set-context [ops world value] ((:set-task-runtime ops) world value))
(defn- update-context [ops world f & arguments]
  (set-context ops world (apply f (context ops world) arguments)))
(defn- unqueue [ops world task]
  (let [node (node! ops world task :task)]
    (->> (update-context ops world update :queue (fn [queue] (filterv #(not= task %) queue)))
         (#((:replace-node ops) % task (assoc node :queued? false))))))

(defn prepare-release
  "Removing the final user owner cancels an unstarted pure task (dropping the
   queue owner too), or requests cooperative cancellation of keep-alive BaseIO.
   Returns updated world and the number of owners RC must actually drop."
  [ops world task n]
  (let [node (node! ops world task :task)]
    (if (and (:queued? node) (pos? (:rc node)) (= 1 (- (:rc node) n)))
      (if (:keep-alive? node)
        [((:replace-node ops) world task (assoc node :cancelled? true)) n]
        [(unqueue ops world task) (inc n)])
      [world n])))

(defn- job-ready? [ops world node]
  (and (= :waiting (task-state node))
       (or (contains? #{:spawn :spawn-io} (:task-kind node))
           (= :ready (task-state (node! ops world (second (:fields node)) :task))))))
(defn- take-next [ops world sync-only]
  (let [queue (:queue (context ops world))
        next-task (some (fn [task]
                          (let [node (node! ops world task :task)]
                            (when (and (= :waiting (task-state node))
                                       (or (not sync-only) (and (:sync? node) (job-ready? ops world node)))) task))) queue)]
    (if next-task
      [(unqueue ops world next-task) next-task]
      (if sync-only [world 0]
        ;; get-body calls this only on a blocked task; drain-body checks zero.
        [world 0]))))

(defn- nullary-zero? [value]
  (or (= 0 value) (= 0 (:tag value))
      (and (native/native-scalar? value) (zero? (native/payload value)))))

(defn- priority! [ops world priority]
  ;; Pinned native task registration unboxes a small Nat, never an MPZ pointer.
  (when ((:ref? ops) priority)
    (fail "Task priority must be a native small Nat" {:priority priority}))
  (let [priority (native/nat-value priority)]
    (when (> priority #?(:clj 9223372036854775807 :cljs js/Number.MAX_SAFE_INTEGER))
      (fail "Task priority must be a native small Nat" {:priority priority})) priority))
(defn- register-job [ops world symbol args]
  (let [spawn? (contains? #{"lean_task_spawn" "lean_io_as_task"} symbol)
        io? (contains? #{"lean_io_as_task" "lean_io_map_task" "lean_io_bind_task"} symbol)
        bind? (contains? #{"lean_task_bind" "lean_io_bind_task"} symbol)
        function (if spawn? (second args) (nth args (if bind? 3 2)))
        dependency (when-not spawn? (nth args (if bind? 2 3)))
        priority (priority! ops world (nth args (if spawn? 2 4)))
        sync (scalar/integer! "uint8" (if spawn? 0 (nth args 5)))
        _ (when dependency (node! ops world dependency :task))
        kind (cond spawn? (if io? :spawn-io :spawn)
                   bind? (if io? :bind-io :bind)
                   :else (if io? :map-io :map))
        [world task] ((:allocate ops) world :task 252 (cond-> [function] dependency (conj dependency)))
        world ((:replace-node ops) world task (assoc ((:node ops) world task)
                                                :task-state :waiting :task-kind kind :sync? (not (zero? sync))
                                                :priority priority :keep-alive? io? :queued? true :cancelled? false))
        world ((:retain ops) world task 1)]
    [(update-context ops world update :queue conj task) task]))

(defn- ready-owned [ops world task]
  (let [node (node! ops world task :task) state (task-state node)]
    (when-not (= :ready state)
      (fail "Unresolved guest task: no runnable producer in this execution slice"
            {:task task :state state :runtime-limit :unresolved-task}))
    (when-not (= 1 (count (:fields node))) (fail "Malformed ready guest task" {:task task}))
    (let [value (first (:fields node))]
      [((:release ops) ((:retain ops) world value 1) task 1) value])))

(defn evaluate [ops world symbol args]
  (let [spec (or (get supported-symbols symbol) (get internal-symbols symbol))]
    (when-not spec (fail "Unsupported task runtime extern" {:symbol symbol}))
    (when-not (= (:arity spec) (count args)) (fail "Task runtime arity mismatch" {:symbol symbol})))
  (cond
    (contains? #{"lean_task_spawn" "lean_task_map" "lean_task_bind" "lean_io_as_task" "lean_io_map_task" "lean_io_bind_task"} symbol)
    (register-job ops world symbol args)
    :else
    (case symbol
      "lean_io_promise_new"
      (let [[world task] ((:allocate ops) world :task 252 [])
            world ((:replace-node ops) world task (assoc ((:node ops) world task) :task-state :promise-pending))]
        ((:allocate ops) world :promise 244 [task]))
      "lean_io_promise_result_opt"
      (let [task (promise-task ops world (second args))] [((:retain ops) world task 1) task])
      "lean_io_promise_resolve"
      (let [[_ value promise _] args task (promise-task ops world promise) node (node! ops world task :task)]
        (if (= :promise-pending (task-state node))
          (let [[world option] ((:allocate ops) world :ctor 1 [value])]
            [((:replace-node ops) world task (assoc node :task-state :ready :fields [option])) 0])
          [((:release ops) world value 1) 0]))
      "lean_task_get_own" (ready-owned ops world (second args))
      "prototype_task_read_own" (ready-owned ops world (first args))
      "lean_io_get_task_state"
      (let [task (second args) node (node! ops world task :task)]
        [world (case (task-state node) :ready 2 :promise-pending 1 :running 1 :waiting 0
                     (fail "Unsupported task lifecycle state" {:task task :node node}))])
      "lean_io_cancel"
      (let [task (second args) node (node! ops world task :task)]
        [((:replace-node ops) world task (assoc node :cancelled? true)) 0])
      "lean_io_check_canceled"
      (let [task (peek (:active (context ops world)))]
        [world (if (and task (:cancelled? (node! ops world task :task))) 1 0)])
      "lean_option_get_or_block"
      (let [option (nth args 2)]
        (if ((:ref? ops) option)
          (let [node ((:node ops) world option)]
            (when-not (and (= :ctor (:kind node)) (= 1 (:tag node)) (= 1 (count (:fields node))))
              (fail "Malformed promise result Option" {:value option}))
            (let [value (first (:fields node))]
              [((:release ops) ((:retain ops) world value 1) option 1) value]))
          (do (when-not (nullary-zero? option) (fail "Malformed promise result Option" {:value option}))
              (fail "Dropped promise result cannot be forced" {:runtime-limit :unresolved-promise}))))
      "prototype_task_mode"
      (let [task (first args) node (node! ops world task :task)]
        [world (case (task-state node) :ready 0 :waiting (or (get job-modes (:task-kind node))
                                                           (fail "Unknown guest task job" {:task task}))
                     (:promise-pending :running) 7)])
      "prototype_task_begin"
      (let [task (first args) node (node! ops world task :task)]
        (when-not (= :waiting (task-state node)) (fail "Task job is not waiting" {:task task}))
        (let [world (if (:queued? node)
                      ((:release ops) (unqueue ops world task) task 1) world)
              node (node! ops world task :task)
              parent (peek (:active (context ops world)))
              thread (if (:sync? node) (if parent (or (:thread-key (node! ops world parent :task)) parent) :main) task)
              world (heartbeat/switch-thread ops world thread)
              world ((:replace-node ops) world task (assoc node :task-state :running :thread-key thread))]
          [(update-context ops world update :active conj task) 0]))
      "prototype_task_dependency"
      (let [node (node! ops world (first args) :task) dependency (second (:fields node))]
        (when-not (and (= :running (task-state node)) dependency) (fail "Task has no active dependency" {}))
        [((:retain ops) world dependency 1) dependency])
      "prototype_task_take_closure"
      (let [task (first args) node (node! ops world task :task)
            [function dependency] (:fields node)]
        (when-not (and (= :running (task-state node)) (seq (:fields node))) (fail "Task has no active closure" {}))
        (let [world ((:replace-node ops) world task (assoc node :fields []))
              world (if dependency ((:release ops) world dependency 1) world)]
          [world function]))
      "prototype_task_publish"
      (let [[task value] args node (node! ops world task :task) active (:active (context ops world))]
        (when-not (and (= :running (task-state node)) (empty? (:fields node)) (= task (peek active)))
          (fail "Task publication has no matching active job" {:task task :active active}))
        (let [world (io/finish-task-streams ops world task (:thread-key node))
              parent (peek (pop active))
              thread (if parent (or (:thread-key (node! ops world parent :task)) parent) :main)
              world (heartbeat/switch-thread ops world thread)
              world ((:replace-node ops) world task (assoc node :task-state :ready :fields [value]))]
          [(update-context ops world assoc :active (pop active)) 0]))
      "prototype_task_next" (take-next ops world false)
      "prototype_task_next_sync" (take-next ops world true)
      "prototype_task_sync_ready"
      (let [node (node! ops world (first args) :task)] [world (if (and (:sync? node) (job-ready? ops world node)) 1 0)])
      "prototype_task_wait_any_ready"
      (loop [tail (first args) seen #{}]
        (if (nullary-zero? tail) [world 0]
          (let [node (node! ops world tail :ctor) [task rest] (:fields node)]
            (when (or (contains? seen tail) (not= 1 (:tag node)) (not= 2 (count (:fields node))))
              (fail "Malformed waitAny task list" {}))
            (if (= :ready (task-state (node! ops world task :task)))
              [((:retain ops) world task 1) task]
              (recur rest (conj seen tail))))))
      (fail "Task operation requires explicit guest-call lowering" {:symbol symbol}))))
