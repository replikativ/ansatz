;; Copyright (c) 2026 Simmis GmbH. All rights reserved.
;; Tactic layer — LLM-based tactic suggestion.

(ns cic.tactic.suggest
  "LLM-based tactic suggestion for proof search.
   Queries an LLM with the current proof state and parses suggested tactics.
   Implements the heuristic plugin interface: (fn [ps] → [{:ps :weight}])."
  (:require [clojure.string :as str]
            [cic.kernel.expr :as e]
            [cic.kernel.name :as name]
            [cic.tactic.proof :as proof]
            [cic.tactic.basic :as basic]
            [cic.tactic.search :as search]
            [cic.tactic.trace :as trace]
            [cic.tactic.llm :as llm]))

;; ============================================================
;; System prompt
;; ============================================================

(def system-prompt
  "You are a proof assistant for the Calculus of Inductive Constructions (CIC),
the type theory underlying Lean 4. Given a proof goal with hypotheses, suggest
tactics to make progress.

Available tactics (in order of typical usefulness):
- intro [name] : introduce a forall/arrow binder
- intros : introduce all leading binders
- assumption : close the goal if a hypothesis matches exactly
- rfl : close an @Eq goal where both sides are definitionally equal
- exact <term> : provide the exact proof term
- apply <term> : apply a term (lemma/hypothesis), generating subgoals for its arguments
- constructor : apply the constructor of the goal's inductive type
- rewrite <hyp> : rewrite the goal using an equality hypothesis
- cases <hyp> : case analysis on an inductive hypothesis

Respond with a JSON array of suggested tactics, ordered by likelihood of success.
Each element should be: {\"tactic\": \"name\", \"args\": [\"arg1\", ...], \"confidence\": 0.0-1.0}

Only suggest tactics that are likely applicable given the goal structure.
Keep suggestions concise — at most 5 tactics. Do not explain, just return the JSON array.")

;; ============================================================
;; Response parsing
;; ============================================================

(defn- extract-json-array
  "Extract a JSON array from LLM response text, handling markdown fences."
  [text]
  (let [text (str/trim text)
        ;; Strip markdown code fences if present
        text (if (str/starts-with? text "```")
               (-> text
                   (str/replace #"^```\w*\n?" "")
                   (str/replace #"\n?```$" ""))
               text)
        ;; Find the JSON array
        start (str/index-of text "[")
        end (when start (str/last-index-of text "]"))]
    (when (and start end (< start end))
      (try
        (let [json-str (subs text start (inc end))
              parsed (clojure.data.json/read-str json-str :key-fn keyword)]
          (when (vector? parsed) parsed))
        (catch Exception _ nil)))))

(defn- parse-suggestion
  "Parse a single tactic suggestion from the LLM response."
  [{:keys [tactic args confidence] :as m}]
  (when tactic
    {:name (keyword tactic)
     :args (or args [])
     :weight (or confidence 0.5)}))

(defn parse-suggestions
  "Parse LLM response into a seq of tactic suggestions."
  [response-text]
  (when-let [arr (extract-json-array response-text)]
    (->> arr
         (keep parse-suggestion)
         (sort-by :weight >)
         vec)))

;; ============================================================
;; Tactic application from suggestions
;; ============================================================

(defn- resolve-arg
  "Resolve a string argument to an expression, looking up in the local context."
  [ps arg]
  (cond
    ;; Name lookup in lctx
    (string? arg)
    (let [goal (proof/current-goal ps)]
      (or (some (fn [[id decl]]
                  (when (and (= :local (:tag decl))
                             (= arg (:name decl)))
                    (e/fvar id)))
                (:lctx goal))
          ;; Try as a constant name
          (e/const' (name/from-string arg) [])))

    :else arg))

(defn- apply-suggestion
  "Try to apply a parsed tactic suggestion to a proof state.
   Returns the new proof state or nil on failure."
  [ps {:keys [name args]}]
  (try
    (case name
      :intro (if (seq args)
               (basic/intro ps (first args))
               (basic/intro ps))
      :intros (if (seq args)
                (basic/intros ps args)
                (basic/intros ps))
      :assumption (basic/assumption ps)
      :rfl (basic/rfl ps)
      :exact (when (seq args)
               (let [term (resolve-arg ps (first args))]
                 (basic/exact ps term)))
      :apply (when (seq args)
               (let [term (resolve-arg ps (first args))]
                 (basic/apply-tac ps term)))
      :constructor (basic/constructor ps)
      :rewrite (when (seq args)
                 (let [term (resolve-arg ps (first args))
                       reverse? (= "reverse" (second args))]
                   (basic/rewrite ps term reverse?)))
      :cases (when (seq args)
               (let [goal (proof/current-goal ps)
                     hyp-name (first args)
                     hyp-id (some (fn [[id decl]]
                                    (when (and (= :local (:tag decl))
                                               (= hyp-name (:name decl)))
                                      id))
                                  (:lctx goal))]
                 (when hyp-id
                   (basic/cases ps hyp-id))))
      ;; Unknown tactic
      nil)
    (catch Exception _ nil)))

;; ============================================================
;; LLM suggestion — the main entry point
;; ============================================================

(defn suggest-tactics
  "Query the LLM for tactic suggestions given the current proof state.

   Args:
     config - LLM config (from llm/make-config)
     ps     - Current proof state

   Returns:
     Vector of {:name keyword :args vector :weight double}"
  [config ps]
  (let [prompt (trace/proof-state->prompt ps)
        response (llm/chat-with-system config system-prompt prompt)]
    (or (parse-suggestions response) [])))

(defn suggest-and-apply
  "Query the LLM for tactic suggestions and try applying each one.
   Returns a seq of {:ps proof-state :weight double :tactic keyword}
   for each successful application."
  [config ps]
  (let [suggestions (suggest-tactics config ps)]
    (->> suggestions
         (keep (fn [{:keys [name weight] :as suggestion}]
                 (when-let [ps' (apply-suggestion ps suggestion)]
                   {:ps (proof/adjust-weight ps' weight)
                    :weight (* (:weight ps') weight)
                    :tactic name
                    :args (:args suggestion)})))
         vec)))

;; ============================================================
;; LLM-guided beam search
;; ============================================================

(defn llm-beam-search
  "Beam search using LLM suggestions as the proposal distribution.
   Falls back to enumerate-tactics if LLM returns nothing useful.

   Args:
     config     - LLM config
     ps         - Initial proof state
     beam-width - Number of branches to keep
     max-steps  - Maximum search steps
     trace-path - Optional NDJSON path to log successful traces

   Returns:
     Solved proof state, or nil."
  [config ps beam-width max-steps & {:keys [trace-path verbose]}]
  (loop [beam [{:ps ps :weight 1.0}]
         step 0]
    (when (< step max-steps)
      ;; Check for solved state
      (if-let [solved (first (filter #(proof/solved? (:ps %)) beam))]
        (do
          (when trace-path
            (trace/write-trace-ndjson trace-path (:ps solved)))
          (when verbose
            (println (str "Solved in " step " steps")))
          (:ps solved))
        ;; Expand each beam element using LLM suggestions
        (let [expanded
              (mapcat
               (fn [{:keys [ps weight]}]
                 (let [llm-branches (try (suggest-and-apply config ps)
                                         (catch Exception e
                                           (when verbose
                                             (println (str "LLM error: " (.getMessage e))))
                                           []))
                       ;; Scale weights by parent weight
                       llm-branches (mapv #(update % :weight * weight) llm-branches)]
                   (if (seq llm-branches)
                     llm-branches
                     ;; Fallback: try basic enumeration
                     (let [candidates (search/enumerate-tactics ps)]
                       (keep (fn [{:keys [tactic weight tac-weight] :as c}]
                               (when-let [ps' (try (tactic ps) (catch Exception _ nil))]
                                 {:ps ps'
                                  :weight (* weight (or (:weight c) 0.5))
                                  :tactic (:name c)}))
                             candidates)))))
               beam)
              ;; Keep top beam-width by weight
              top (take beam-width (sort-by :weight > expanded))]
          (when verbose
            (println (str "Step " step ": " (count top) " branches"
                          (when (seq top)
                            (str ", best weight: "
                                 (format "%.4f" (:weight (first top))))))))
          (if (empty? top)
            nil
            (recur (vec top) (inc step))))))))
