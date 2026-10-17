(ns prototype.runtime-heartbeat
  "Allocation heartbeats for cooperative guest threads. This hosted profile
   charges logical guest heap allocations, not JVM allocations/native allocator
   block sizes or Java kernel work. UInt64 counters, resets and thread switches
   are snapshot-local; counters never read a host clock."
  (:require [prototype.native-scalar :as native]))

(def supported-symbols
  {"lean_io_get_num_heartbeats" {:arity 1} "lean_io_set_heartbeats" {:arity 2}})
(defn- fail [message data] (throw (ex-info message data)))
(defn- add-counter [a b]
  #?(:clj (mod (+' a b) 18446744073709551616N)
     :cljs (let [n (+ a b)]
             (when-not (js/Number.isSafeInteger n)
               (fail "Heartbeat count exceeds exact JS profile" {})) n)))
(defn- allocation-count [ops world]
  (when-not (ifn? (:allocation-count ops)) (fail "Missing guest allocation counter" {}))
  (let [n ((:allocation-count ops) world)]
    (when-not (and (integer? n) (<= 0 n)
                   #?(:clj true :cljs (js/Number.isSafeInteger n)))
      (fail "Invalid guest allocation counter" {})) n))
(defn thread-key [ops world]
  (if-let [task (peek (:active ((:get-task-runtime ops) world)))]
    (or (:thread-key ((:node ops) world task)) task) :main))

(defn switch-thread
  "Flush costs to the previous logical thread before changing scheduler context.
   The allocation mark is derived state. Allocators exclude lazy imported ID
   reservations, which create no local guest heap objects."
  [ops world target]
  (let [context (or ((:get-task-runtime ops) world) {:queue [] :active []})
        allocation (allocation-count ops world)
        heartbeat (or (:heartbeats context) {:thread :main :mark 0 :counts {}})
        {:keys [thread mark counts]} heartbeat]
    (when-not (and (integer? mark) (<= 0 mark allocation) (map? counts)
                   #?(:clj true :cljs (js/Number.isSafeInteger mark)))
      (fail "Invalid or rewound guest heartbeat state" {}))
    (let [counts (update counts thread #(add-counter (or % 0) (- allocation mark)))]
      ((:set-task-runtime ops) world
       (assoc context :heartbeats {:thread target :mark allocation :counts counts})))))

(defn evaluate [ops world symbol args]
  (when-not (= (get-in supported-symbols [symbol :arity]) (count args))
    (fail "Invalid heartbeat runtime call" {:symbol symbol}))
  (let [thread (thread-key ops world)
        world (switch-thread ops world thread)
        context ((:get-task-runtime ops) world)]
    (case symbol
      "lean_io_get_num_heartbeats" [world (get-in context [:heartbeats :counts thread] 0)]
      "lean_io_set_heartbeats"
      (let [value (first args)
            n (native/nat-value ops world value)
            n #?(:clj (mod n 18446744073709551616N)
                 :cljs (do (when-not (js/Number.isSafeInteger n)
                             (fail "Heartbeat count exceeds exact JS profile" {})) n))
            world ((:release ops) world value 1)]
        [((:set-task-runtime ops) world (assoc-in context [:heartbeats :counts thread] n)) 0]))))
