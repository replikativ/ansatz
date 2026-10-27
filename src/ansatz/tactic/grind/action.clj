(ns ansatz.tactic.grind.action
  "Stage 2 action results and limits (Lean Grind/Action.lean, Grind/Simp.lean,
   Simp/Main.lean and Init/MetaTypes.lean, v4.33.1).")

(def defaults {:splits 9 :ematch 5 :gen 8 :instances 1000 :iterations 10000 :max-steps 100000 :max-rec-depth 512
               :split-imp false :split-ind-pred false})

(defn fail! [message data]
  (throw (ex-info (str "Tactic error: grind_v2: " message)
                  (assoc data :kind :tactic-error))))

(defn budget! [config counter used]
  (let [limit (get config counter)]
    (when (>= used limit)
      (fail! (str (name counter) " budget exhausted (" limit ")")
             {:limit counter :value limit :used used}))))

(defn attempt
  "Action.orElse: only a declared tactic failure means not applicable."
  [f]
  (try (f)
       (catch clojure.lang.ExceptionInfo ex
         (if (= :tactic-error (:kind (ex-data ex))) nil (throw ex)))))

(defn configure [options]
  (doseq [[k v] options]
    (when-not (and (contains? defaults k)
                   (if (contains? #{:split-imp :split-ind-pred} k)
                     (boolean? v) (and (integer? v) (not (neg? v)))))
      (fail! "unsupported configuration" {:option k :value v})))
  (merge defaults options))

(def ^:dynamic *config* defaults)

(defn check-rec-depth!
  "Lean withIncRecDepth: bound actual internalizer/transform recursion."
  [depth]
  (let [limit (:max-rec-depth *config*)]
    (when (> depth limit)
      (fail! (str "maximum recursion depth exceeded (maxRecDepth = " limit ")")
             {:limit :maxRecDepth :value limit :used depth}))))
