(ns prototype.runtime-sync
  "Snapshot-local allocation of pinned Std.BaseMutex handles.
   runtime/mutex.cpp:25 returns an unlocked external object (lean.h tag254),
   directly as BaseIO, with no owned Lean fields. This is a logical handle:
   there is no host mutex, pointer, OS finalizer or shared mutable fork state.
   Blocking lock/tryLock/unlock are deliberately unadmitted until their task
   ownership and visible guest blocking behavior are implemented and tested.")

(def supported-symbols {"lean_io_basemutex_new" {:arity 1}})

(defn evaluate [ops world symbol args]
  (when-not (contains? supported-symbols symbol)
    (throw (ex-info "Unsupported synchronization runtime extern" {:symbol symbol})))
  (when-not (= 1 (count args))
    (throw (ex-info "Synchronization runtime arity mismatch" {:symbol symbol :arity (count args)})))
  (let [[world mutex] ((:allocate ops) world :mutex 254 [])
        node ((:node ops) world mutex)]
    [((:replace-node ops) world mutex (assoc node :mutex-state :unlocked)) mutex]))
