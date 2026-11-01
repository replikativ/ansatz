(ns prototype.host-cells-lab
  "Pure branch-local scalar cells for the Klara/Lean experiment.
   Cell identity is data, not resource authority. Raw host atoms are excluded.
   Stores are persistent values; callers publish them through branch handles.
   No serialization, merge, concurrency or production interop contract."
  (:refer-clojure :exclude [read]))

(defrecord Cell [store-id id allocation-id])

(defn store [] {:store-id (Object.) :next-id 0 :values {} :identities {}})

(defn- value! [value]
  (when-not (or (nil? value) (boolean? value) (integer? value)
                (string? value) (keyword? value))
    (throw (ex-info "Host-cell lab accepts immutable scalar values only" {})))
  value)

(defn allocate [store value]
  (value! value)
  (let [id (:next-id store) allocation-id (Object.)]
    [(-> store (update :next-id inc) (assoc-in [:values id] value)
         (assoc-in [:identities id] allocation-id))
     (->Cell (:store-id store) id allocation-id)]))

(defn- cell! [store cell]
  (when-not (and (instance? Cell cell)
                 (identical? (:store-id store) (:store-id cell))
                 (identical? (get-in store [:identities (:id cell)]) (:allocation-id cell))
                 (contains? (:values store) (:id cell)))
    (throw (ex-info "Cell is not allocated in this branch store" {})))
  cell)

(defn read [store cell]
  (cell! store cell)
  (get-in store [:values (:id cell)]))

(defn write [store cell value]
  (cell! store cell)
  (value! value)
  (assoc-in store [:values (:id cell)] value))

(defn request
  "Closed effect descriptor table. Returns persistent store, guest reply and
   optional deferred intent. Never calls arbitrary host functions."
  [store {:keys [symbol arguments]} n]
  (when-not (< n 64)
    (throw (ex-info "Lab effect budget exhausted" {})))
  (case symbol
    :lab/emit
    (do (when-not (and (= 1 (count arguments)) (integer? (first arguments)))
          (throw (ex-info "Unsupported lab output" {})))
        {:store store :reply 0 :intent (first arguments)})
    :lab/cell-read
    (do (when-not (= 1 (count arguments)) (throw (ex-info "Cell read arity" {})))
        {:store store :reply (read store (first arguments))})
    :lab/cell-write
    (do (when-not (= 2 (count arguments)) (throw (ex-info "Cell write arity" {})))
        {:store (write store (first arguments) (second arguments)) :reply 0})
    (throw (ex-info "Unsupported lab effect" {:symbol symbol}))))
