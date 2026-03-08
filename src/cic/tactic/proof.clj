;; Copyright (c) 2026 Simmis GmbH. All rights reserved.
;; Tactic layer — proof state and metavariable infrastructure.

(ns cic.tactic.proof
  "Proof state management for interactive tactic proofs.
   Proof states are persistent Clojure maps; forking is free.

   Trace support: each tactic application is recorded in :trace,
   enabling search strategies to learn from proof histories."
  (:require [cic.kernel.reduce :as red]))

(defn alloc-id
  "Allocate a fresh unique id, returning [ps' new-id]."
  [ps]
  (let [id (:next-id ps)]
    [(update ps :next-id inc) id]))

(defn fresh-mvar
  "Create a fresh metavariable with the given type and local context.
   Returns [ps' mvar-id]."
  [ps type lctx]
  (let [[ps' id] (alloc-id ps)]
    [(-> ps'
         (assoc-in [:mctx id] {:type type :lctx lctx :assignment nil})
         (update :goals conj id))
     id]))

(defn assign-mvar
  "Assign a metavariable, removing it from open goals."
  [ps mvar-id assignment]
  (-> ps
      (assoc-in [:mctx mvar-id :assignment] assignment)
      (update :goals (fn [gs] (into [] (remove #{mvar-id}) gs)))))

(defn start-proof
  "Create a proof state with one open goal of the given type.
   Returns [ps mvar-id]."
  [env goal-type]
  (let [ps {:env env
            :goals []
            :mctx {}
            :next-id 1
            :root-mvar nil
            :trace []
            :weight 1.0}
        [ps' root-id] (fresh-mvar ps goal-type (red/empty-lctx))]
    [(assoc ps' :root-mvar root-id) root-id]))

(defn current-goal
  "Get the first open goal as {:id :type :lctx}, or nil."
  [ps]
  (when-let [id (first (:goals ps))]
    (let [m (get-in ps [:mctx id])]
      {:id id :type (:type m) :lctx (:lctx m)})))

(defn goals
  "Get all open goals as seq of {:id :type :lctx}."
  [ps]
  (map (fn [id]
         (let [m (get-in ps [:mctx id])]
           {:id id :type (:type m) :lctx (:lctx m)}))
       (:goals ps)))

(defn solved?
  "True if all goals are solved."
  [ps]
  (empty? (:goals ps)))

;; ============================================================
;; Trace and search infrastructure
;; ============================================================

(defn record-tactic
  "Record a tactic application in the trace."
  [ps tactic-name args goal-id]
  (update ps :trace conj
          {:tactic tactic-name
           :args args
           :goal-id goal-id
           :timestamp (System/nanoTime)}))

(defn set-weight
  "Set the weight (log-likelihood) of this proof branch."
  [ps w]
  (assoc ps :weight w))

(defn adjust-weight
  "Multiply the weight by a factor."
  [ps factor]
  (update ps :weight * factor))

(defn mvar-assigned?
  "Check if a metavariable has been assigned."
  [ps mvar-id]
  (some? (get-in ps [:mctx mvar-id :assignment])))
