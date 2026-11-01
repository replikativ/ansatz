(ns prototype.stdio
  "Explicit in-memory standard streams using the real pinned guest ofBuffer.
   No OS handles or process/JVM stdout changes. World default slots own streams;
   returned :buffers are additional caller-owned guest IO.Ref Buffer roots."
  (:require [prototype.machine :as m]
            [prototype.scalar :as scalar]))

(def of-buffer-target
  (reduce (fn [parent part] ["str" parent part]) ["anonymous"] ["IO" "FS" "Stream" "ofBuffer"]))

(defn seed-memory
  "[world invoke options] -> {:world world :buffers channel->ownedBufferRef}.
   invoke has raw scoped-helper shape [world target args] -> [world result].
   The supplied program must link of-buffer-target with its real guest callbacks.
   :stdin/:stdout/:stderr options are initial UInt8 vectors (default empty).
   Empty stdin is an explicit caller-selected memory buffer, not host stdin."
  ([world invoke] (seed-memory world invoke {}))
  ([world invoke initial-bytes]
   (when (:stdio-runtime world)
     (throw (ex-info "Standard streams are already configured" {})))
   (when (seq (get-in world [:task-runtime :active]))
     (throw (ex-info "Seed stream defaults before entering a cooperative task" {})))
   (reduce
    (fn [{:keys [world buffers]} channel]
      (let [bytes (get initial-bytes channel [])]
        (when-not (vector? bytes) (throw (ex-info "Memory stream input must be UInt8 vector" {:channel channel})))
        (doseq [byte bytes] (scalar/integer! "uint8" byte))
        (let [[world array] (m/allocate world :byte-array 248 [])
              world (assoc-in world [:heap (:id array) :bytes] bytes)
              [world buffer] (m/allocate world :ctor 0 [array 0])
              [world reference] (m/allocate world :ref 253 [buffer])
              [world stream] (invoke (m/retain world reference 1) of-buffer-target [reference])]
          {:world (-> world (assoc-in [:stdio-runtime :defaults channel] stream) (assoc :result 0))
           :buffers (assoc buffers channel reference)})))
    {:world world :buffers {}} [:stdin :stdout :stderr])))
