(ns prototype.binding-dependencies
  "Finite immutable declarations of fixed guest dependencies of trusted host
   bindings. Data is not authority: consumers must first authenticate the exact
   binding object against independently retained trusted configuration. Absent
   metadata for a legacy/custom callback implies no introspection guarantee.")

(def ^:private max-roots 1024)
(def ^:private max-name-nodes 256)
(def ^:private max-total-nodes 16384)
(def ^:private max-name-chars 16384)
(def ^:private max-total-chars 262144)
(defn- fail [] (throw (ex-info "Invalid or unbounded binding guest helper roots" {})))

(defn validate-roots
  "Validate an immutable vector of structured Lean Names before executable map
   lookup/hashing. Limits include duplicate occurrences; never walk a caller's
   unbounded lazy sequence or mutable list. Return the original immutable vector."
  [roots]
  (when-not (and (vector? roots) (<= (count roots) max-roots)) (fail))
  (loop [pending roots total-nodes 0 total-chars 0]
    (if (empty? pending) roots
      (let [[nodes chars]
            (loop [name (peek pending) nodes 0 chars 0]
              (when-not (and (vector? name) (< nodes max-name-nodes)) (fail))
              (let [tag (first name) nodes (inc nodes)]
                (when-not (string? tag) (fail))
                (cond
                  (= tag "anonymous")
                  (do (when-not (= 1 (count name)) (fail)) [nodes chars])
                  (or (= tag "str") (= tag "num"))
                  (let [[_ prefix value] name]
                    (when-not (and (= 3 (count name)) (string? value)
                                   (<= (count value) (- max-name-chars chars))) (fail))
                    (when (and (= tag "num") (not (re-matches #"0|[1-9][0-9]*" value))) (fail))
                    (recur prefix nodes (+ chars (count value))))
                  :else (fail))))
            next-nodes (+ total-nodes nodes) next-chars (+ total-chars chars)]
        (when (or (> next-nodes max-total-nodes) (> next-chars max-total-chars)) (fail))
        (recur (pop pending) next-nodes next-chars)))))

(defn declared-roots
  "Collect fixed roots FROM authenticated independent binding objects. The caller
   owns identity authentication; arbitrary candidate metadata never grants code
   authority. A present field must be finite/well formed, including an empty
   vector; an absent field preserves legacy trusted-callback behavior."
  [bindings]
  (reduce (fn [out binding]
            (if (contains? binding :guest-helper-roots)
              (let [roots (:guest-helper-roots binding)]
                (validate-roots roots)
                (when (> (+ (count out) (count roots)) max-roots) (fail))
                ;; Revalidate combined node/character budgets, including repeated
                ;; roots across different independently trusted callbacks.
                (validate-roots (into out roots))) out))
          [] (vals bindings)))
