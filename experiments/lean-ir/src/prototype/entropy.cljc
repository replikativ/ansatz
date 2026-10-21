(ns prototype.entropy
  "Replayable guest entropy input. Hosts supply bytes before execution; snapshots
   preserve the cursor and forks replay the same remaining input. This is not an
   OS randomness generator or a policy for independent fork streams."
  (:require [prototype.scalar :as scalar]))

(defn take-bytes [world n]
  (when-not (and (integer? n) (<= 0 n 2147483647))
    (throw (ex-info "Invalid entropy byte count" {:count n})))
  (let [{:keys [bytes position] :or {position 0} :as tape} (:entropy world)]
    (when-not (and (map? tape) (vector? bytes) (integer? position) (<= 0 position (count bytes)))
      (throw (ex-info "Missing or invalid guest entropy input" {})))
    (when (> n (- (count bytes) position))
      (throw (ex-info "Guest entropy input exhausted" {:requested n :available (- (count bytes) position)})))
    (let [result (subvec bytes position (+ position n))]
      (doseq [byte result] (scalar/integer! "uint8" byte))
      [(assoc world :entropy (assoc tape :position (+ position n))) result])))
