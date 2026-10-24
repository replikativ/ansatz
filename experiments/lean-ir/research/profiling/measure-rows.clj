(ns profile-restored-ir
  "REPL helpers for authenticated checkpoint samples, not an admission API."
  (:require [clojure.java.io :as io] [clojure.data.json :as json]
            [prototype.checkpoint-wire :as wire] [prototype.restore-consumer :as restore])
  (:import [prototype.profile ObjectMeter] [java.io DataInputStream]))

(defn read-functions [path n shared?]
  (let [names (when-not shared? (java.util.HashMap.))
        {:keys [normalize! release!]} (when shared? (#'restore/make-row-normalizer))]
    (try
      (with-open [input (DataInputStream. (io/input-stream path))]
        (let [rows (mapv (fn [_]
                           (let [row (wire/read-frame! input)]
                             (if shared? (normalize! row) (wire/share-name-prefixes names row)))) (range n))]
          (assert (= -1 (.read input))) rows))
      (finally (when names (.clear names)) (when release! (release!))))))

(defn- registries [rows]
  (reduce (fn [out [_ name flags f]]
            (cond-> (assoc-in out [:functions name] f)
              (contains? flags :prepared) (assoc-in [:prepared name] f)
              (contains? flags :imported) (assoc-in [:imported name] f)))
          {:functions {} :prepared {} :imported {}} rows))

(defn compare! [path n]
  (let [before (read-functions path n false) after (read-functions path n true)
        exact (every? true? (map (fn [a b] (java.util.Arrays/equals ^bytes (wire/encode a) ^bytes (wire/encode b))) before after))]
    (assert exact)
    {:sample-functions n :wire-exact exact
     :sizes (into {} (for [[label rows] [[:before before] [:after after]]]
                      [label (into {} (ObjectMeter/graph (registries rows) 2000000))]))
     :scope "Inclusive reachable object sizes, excluding statics; not dominator retained heap or full frontend"}))

(defn save! [path result]
  (spit path (str (json/write-str result) "\n")))
