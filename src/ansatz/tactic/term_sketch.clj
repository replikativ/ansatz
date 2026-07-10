;; Tactic layer - surface proof-term sketches with holes.

(ns ansatz.tactic.term-sketch
  "Experimental proof-term sketches.

   This is intentionally smaller than the main surface elaborator. It accepts a
   tiny proof-term fragment and drives the existing proof-state machinery:

     (lam [a Prop] (lam [h a] _))

   Lambda binders become checked intro steps, ordinary leaves become exact
   terms elaborated in the current local context, and holes delegate to the
   tactic sketch/search layer."
  (:require [ansatz.kernel.tc :as tc]
            [ansatz.surface.elaborate :as elab]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.search :as search]
            [ansatz.tactic.sketch :as sketch]))

(defn term-hole?
  "True when `x` is a term-sketch hole."
  [x]
  (sketch/hole? x))

(defn- parse-binders [binder-vec]
  (let [tokens (vec (remove (fn [t]
                              (contains? #{";" "," ":" ":-"} (str t)))
                            binder-vec))]
    (when (odd? (count tokens))
      (throw (ex-info "Lambda sketch binder is missing a type"
                      {:binder binder-vec})))
    (mapv (fn [[nam typ]]
            {:name (str nam)
             :type-sexpr typ})
          (partition 2 tokens))))

(defn- lambda-form? [sexpr]
  (and (seq? sexpr)
       (#{'lam 'fn} (first sexpr))
       (= 3 (count sexpr))
       (vector? (second sexpr))))

(defn- current-goal! [ps]
  (or (proof/current-goal ps)
      (throw (ex-info "Term sketch has no current goal"
                      {:kind :term-sketch-error}))))

(defn- tc-state [ps goal]
  (tc/attach-lctx (tc/mk-tc-state (:env ps)) (:lctx goal)))

(defn- validate-binder! [ps {:keys [name type-sexpr]}]
  (let [goal (current-goal! ps)
        st (tc-state ps goal)
        [_ expected-domain _ _] (tc/ensure-pi st (:type goal))
        annotated (elab/elaborate-in-context (:env ps) (:lctx goal) type-sexpr)]
    (tc/ensure-sort st (tc/infer-type st annotated))
    (when-not (tc/is-def-eq st annotated expected-domain)
      (throw (ex-info "Binder annotation does not match expected goal domain"
                      {:binder name
                       :annotated annotated
                       :expected expected-domain})))
    true))

(defn- action-summary [name args]
  {:kind :tactic
   :name name
   :args (vec args)
   :prior 1.0
   :source :term-sketch})

(defn- verify-result [ps verify?]
  (when verify?
    (try
      {:ok? true
       :proof (extract/verify ps)}
      (catch Throwable ex
        {:ok? false
         :error {:class (.getName (class ex))
                 :message (.getMessage ex)
                 :data (when (instance? clojure.lang.ExceptionInfo ex)
                         (ex-data ex))}}))))

(defn- terminal-result [ps path verify?]
  (let [verification (verify-result ps verify?)]
    (if (and verify? (not (:ok? verification)))
      {:status :invalid
       :ps ps
       :path path
       :summary (search/state-summary ps)
       :verification verification}
      (cond-> {:status :solved
               :ps ps
               :path path
               :summary (search/state-summary ps)}
        verification (assoc :verification verification)
        (:proof verification) (assoc :proof (:proof verification))))))

(declare refine-term-sketch)

(defn- refine-lambda [ps sexpr opts]
  (let [[_ binder-vec body] sexpr
        binders (parse-binders binder-vec)]
    (loop [ps ps
           binders binders
           prefix []]
      (if-let [binder (first binders)]
        (do
          (validate-binder! ps binder)
          (recur (basic/intro ps (:name binder))
                 (rest binders)
                 (conj prefix (action-summary :intro [(:name binder)]))))
        (let [result (refine-term-sketch ps body opts)]
          (update result :path #(vec (concat prefix (or % [])))))))))

(defn- refine-exact [ps sexpr opts]
  (let [goal (current-goal! ps)
        term (if (instance? ansatz.kernel.Expr sexpr)
               sexpr
               (elab/elaborate-in-context (:env ps) (:lctx goal) sexpr (:type goal)))
        ps' (basic/exact ps term)]
    (terminal-result ps' [(action-summary :exact-term [(pr-str sexpr)])]
                     (get opts :verify? true))))

(defn- refine-hole [ps opts]
  (sketch/solve-sketch ps ['_]
                       (merge {:verify? (get opts :verify? true)}
                              opts
                              (:hole-search-opts opts))))

(defn refine-term-sketch
  "Refine `sexpr` against the current goal of `ps`.

   Supported fragment:
   - holes: `_`, `?`, `:_`, `:?`
   - lambdas: `(lam [x A ...] body)` or `(fn [x :- A ...] body)`
   - any other leaf term accepted by `elaborate-in-context`, closed with exact"
  ([ps sexpr]
   (refine-term-sketch ps sexpr nil))
  ([ps sexpr opts]
   (cond
     (term-hole? sexpr) (refine-hole ps opts)
     (lambda-form? sexpr) (refine-lambda ps sexpr opts)
     :else (refine-exact ps sexpr opts))))

(defn solve-term-sketch
  "Start a proof for `expected-type` in `env` and refine `sexpr` against it."
  ([env expected-type sexpr]
   (solve-term-sketch env expected-type sexpr nil))
  ([env expected-type sexpr opts]
   (let [[ps _] (proof/start-proof env expected-type)]
     (refine-term-sketch ps sexpr opts))))
