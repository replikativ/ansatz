;; Copyright (c) 2026 Simmis GmbH. All rights reserved.
;; Tactic layer — NDJSON trace export for proof search.

(ns cic.tactic.trace
  "Export proof search traces as NDJSON for training data collection.
   Each line is a JSON object recording a tactic application step."
  (:require [clojure.data.json :as json]
            [cic.kernel.expr :as e]
            [cic.kernel.name :as name]
            [cic.tactic.proof :as proof])
  (:import [java.io BufferedWriter FileWriter]))

;; ============================================================
;; Goal serialization
;; ============================================================

(defn serialize-goal
  "Serialize a goal to a map suitable for JSON export."
  [goal]
  (when goal
    {:id (:id goal)
     :type (e/->string (:type goal))
     :hypotheses
     (->> (:lctx goal)
          (filter (fn [[_ d]] (= :local (:tag d))))
          (sort-by first)
          (mapv (fn [[id d]]
                  {:id id
                   :name (:name d)
                   :type (e/->string (:type d))})))}))

(defn serialize-goals
  "Serialize all open goals in a proof state."
  [ps]
  (mapv serialize-goal (proof/goals ps)))

;; ============================================================
;; Trace step serialization
;; ============================================================

(defn serialize-trace-step
  "Serialize one tactic trace entry to a JSON-writable map."
  [{:keys [tactic args goal-id] :as step}]
  {:tactic (clojure.core/name tactic)
   :args (mapv (fn [a]
                 (cond
                   (string? a) a
                   (number? a) a
                   (keyword? a) (clojure.core/name a)
                   (instance? cic.kernel.Expr a) (e/->string a)
                   :else (str a)))
               (or args []))
   :goal-id goal-id})

(defn serialize-proof-trace
  "Export the full proof trace from a solved proof state as a seq of maps."
  [ps]
  (let [root-type (get-in ps [:mctx (:root-mvar ps) :type])]
    {:goal (e/->string root-type)
     :solved (proof/solved? ps)
     :num-steps (count (:trace ps))
     :weight (:weight ps)
     :steps (mapv serialize-trace-step (:trace ps))}))

;; ============================================================
;; NDJSON file I/O
;; ============================================================

(defn write-trace-ndjson
  "Append a proof trace as one NDJSON line to a file."
  [path ps]
  (let [trace-map (serialize-proof-trace ps)
        line (json/write-str trace-map)]
    (with-open [w (BufferedWriter. (FileWriter. (str path) true))]
      (.write w line)
      (.newLine w))))

(defn write-traces-ndjson
  "Write multiple proof traces to an NDJSON file."
  [path traces]
  (with-open [w (BufferedWriter. (FileWriter. (str path)))]
    (doseq [ps traces]
      (.write w (json/write-str (serialize-proof-trace ps)))
      (.newLine w))))

;; ============================================================
;; Goal prompt formatting (for LLM consumption)
;; ============================================================

(defn goal->prompt
  "Format a goal as a text prompt for LLM tactic suggestion.
   Returns a string describing the goal and hypotheses."
  [goal]
  (when goal
    (let [hyps (->> (:lctx goal)
                    (filter (fn [[_ d]] (= :local (:tag d))))
                    (sort-by first)
                    (map (fn [[_ d]]
                           (str "  " (:name d) " : " (e/->string (:type d))))))
          target (e/->string (:type goal))]
      (str (when (seq hyps)
             (str "Hypotheses:\n" (clojure.string/join "\n" hyps) "\n"))
           "Goal: " target))))

(defn proof-state->prompt
  "Format the current proof state as a prompt for LLM tactic suggestion."
  [ps]
  (let [gs (proof/goals ps)
        n (count gs)]
    (if (zero? n)
      "No goals remaining."
      (str n " goal" (when (> n 1) "s") " remaining.\n\n"
           (clojure.string/join
            "\n\n"
            (map-indexed
             (fn [i g]
               (str "Goal " (inc i) ":\n" (goal->prompt g)))
             gs))))))
