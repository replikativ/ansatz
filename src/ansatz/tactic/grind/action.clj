(ns ansatz.tactic.grind.action
  "Stage 2 action results and limits (Lean Grind/Action.lean, Grind/Simp.lean,
   Simp/Main.lean and Init/MetaTypes.lean, v4.33.1)."
  (:require [ansatz.kernel.expr :as e]))

(def defaults {:splits 9 :ematch 5 :gen 8 :instances 1000 :iterations 10000 :max-steps 100000
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

(defn check-expr!
  "Grind.Simp.simpCore / Simp.Main.simpLoop's maxSteps and withIncRecDepth.
   Count shared nodes once, as simp's memoization does. Revisit a node only
   at a greater binder/term depth to retain the maximum recursion-depth check."
  [expr]
  (let [config *config*
        seen (java.util.IdentityHashMap.)]
    (loop [todo [[expr 0]] steps 0]
      (when-let [[expr depth] (peek todo)]
        (when (>= depth 1000)
          (fail! "maximum recursion depth exceeded (1000)" {:limit :maxRecDepth :value 1000}))
        (let [previous (.get seen expr)]
          (if (and previous (>= (long previous) depth))
            (recur (pop todo) steps)
            (let [_ (when-not previous (budget! config :max-steps steps))
                  _ (.put seen expr depth)
                  children (case (e/tag expr)
                             :app [(e/app-fn expr) (e/app-arg expr)]
                             :lam [(e/lam-type expr) (e/lam-body expr)]
                             :forall [(e/forall-type expr) (e/forall-body expr)]
                             :let [(e/let-type expr) (e/let-value expr) (e/let-body expr)]
                             :proj [(e/proj-struct expr)]
                             :mdata [(e/mdata-expr expr)] [])]
              (recur (into (pop todo) (map #(vector % (inc depth)) children))
                     (if previous steps (inc steps))))))))))
