(ns kernel-support.carrier
  "Immutable constructor fixtures for independent kernel projection contracts.
   This is test data, with no instruction evaluator, execution state, scheduling,
   native source discovery or guest effects. Copying its map isolates fixtures."
  (:require [kernel-support.scalar :as scalar]))

(defrecord Ref [id])
(defrecord Tag [tag])
(defn ref? [value] (instance? Ref value))
(defn fail [message data] (throw (ex-info message data)))

(defn world
  "Compatibility spelling for a fresh fixture carrier; accepts no executable code."
  [functions]
  (when (seq functions) (fail "Fixture carrier cannot execute functions" {}))
  {:heap {} :next-id 0 :stats {:allocations 0}})

(defn node [carrier reference]
  (when-not (ref? reference) (fail "Expected fixture reference" {:ref reference}))
  (or (get-in carrier [:heap (:id reference)])
      (fail "Dangling guest reference" {:ref reference})))

(defn allocate [carrier kind tag fields]
  (when-not (contains? #{:ctor :array :string :mpz} kind)
    (fail "Unsupported fixture object kind" {:kind kind}))
  (let [id (:next-id carrier)]
    (when (contains? (:heap carrier) id) (fail "Fixture ID collision" {:id id}))
    [(-> carrier
         (update :next-id inc)
         (assoc-in [:heap id] {:kind kind :tag tag :fields (vec fields) :rc 1})
         (update-in [:stats :allocations] inc))
     (->Ref id)]))

(defn retain [carrier value count]
  (if-not (ref? value) carrier
    (let [rc (:rc (node carrier value))]
      (if (zero? rc) carrier
        (update-in carrier [:heap (:id value) :rc] + count)))))

(defn release [carrier value count]
  (loop [carrier carrier pending [[value count]]]
    (if (empty? pending) carrier
      (let [[value count] (peek pending) pending (pop pending)]
        (if-not (ref? value) (recur carrier pending)
          (let [{:keys [rc fields]} (node carrier value) remaining (- rc count)]
            (cond
              (zero? rc) (recur carrier pending)
              (neg? remaining) (fail "Reference count underflow" {:ref value :rc rc :drop count})
              (pos? remaining) (recur (assoc-in carrier [:heap (:id value) :rc] remaining) pending)
              :else (recur (update carrier :heap dissoc (:id value))
                           (into pending (map #(vector % 1) fields))))))))))

(defn scalar-constructor [carrier tag fields layout]
  (scalar/layout! layout)
  (when-not (= (:objects layout) (count fields))
    (fail "Scalar constructor object count mismatch" {}))
  (let [[carrier reference] (allocate carrier :ctor tag fields)]
    [(update-in carrier [:heap (:id reference)] assoc :layout layout :scalar-bytes {}) reference]))

(defn read-scalar-node [node slot]
  (when-not (and (= :ctor (:kind node)) (:layout node))
    (fail "Expected scalar constructor storage" {:node node}))
  (scalar/read-bytes (:layout node) (:scalar-bytes node) slot))
