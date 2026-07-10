;; Tactic layer - hole-aware proof sketches for policy search.

(ns ansatz.tactic.sketch
  "A proof sketch is an ordered sequence of tactic steps with holes.

   Bare keywords/symbols are no-argument steps:
     [:intro :intro :assumption]

   Steps with arguments are nested vectors:
     [[:intro \"a\"] [:intro \"h\"] [:exact 'h]]

   Holes (`_`, `?`, `:_`, `:?`) delegate to ordinary search proposers. This
   makes sketches a light-weight way to constrain and guide tactic search while
   keeping every branch inside the normal proof-state/kernel boundary."
  (:require [ansatz.surface.elaborate :as elab]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.search :as search]))

(def ^:private hole-forms
  #{'_ '? :_ :?})

(defn hole?
  "True when `x` denotes a proof-sketch hole."
  [x]
  (contains? hole-forms x))

(defn- op-keyword [op]
  (cond
    (keyword? op) op
    (symbol? op) (keyword (name op))
    :else (throw (ex-info "Sketch step operation must be a keyword or symbol"
                          {:op op}))))

(defn normalize-step
  "Normalize one sketch step into `{:op ... :args [...]}`.

   Public primarily for tests/tools that want to inspect sketches before search."
  [step]
  (cond
    (hole? step)
    {:op :hole :args []}

    (map? step)
    (update step :op op-keyword)

    (or (keyword? step) (symbol? step))
    {:op (op-keyword step) :args []}

    (or (vector? step) (seq? step))
    (let [xs (vec step)]
      (when (empty? xs)
        (throw (ex-info "Empty sketch step" {:step step})))
      {:op (op-keyword (first xs))
       :args (subvec xs 1)})

    :else
    (throw (ex-info "Unsupported sketch step" {:step step}))))

(defn- current-goal! [ps]
  (or (proof/current-goal ps)
      (throw (ex-info "Sketch step has no current goal" {:kind :sketch-error}))))

(defn- expr? [x]
  (instance? ansatz.kernel.Expr x))

(defn- elaborate-term
  ([ps sexpr]
   (elaborate-term ps sexpr nil))
  ([ps sexpr expected]
   (if (expr? sexpr)
     sexpr
     (let [goal (current-goal! ps)]
       (elab/elaborate-in-context (:env ps) (:lctx goal) sexpr expected)))))

(defn- one-arg! [op args]
  (when-not (= 1 (count args))
    (throw (ex-info (str "Sketch step " op " expects one argument")
                    {:op op :args args})))
  (first args))

(defn- names-args [args]
  (cond
    (empty? args) nil
    (and (= 1 (count args)) (sequential? (first args)))
    (mapv str (first args))
    :else
    (mapv str args)))

(defn- sketch-action [name apply-fn args prior]
  (search/make-action name apply-fn
                      {:args args
                       :prior prior
                       :source :sketch}))

(defn- step-actions [step]
  (let [{:keys [op args]} (normalize-step step)]
    (case op
      :hole
      ::hole

      :intro
      (let [binding-name (some-> (first args) str)]
        [(sketch-action :intro
                        #(basic/intro % binding-name)
                        (if binding-name [binding-name] [])
                        0.95)])

      :intros
      (let [names (names-args args)]
        [(sketch-action :intros
                        #(if names
                           (basic/intros % names)
                           (basic/intros %))
                        (or names [])
                        0.95)])

      :assumption
      (do
        (when (seq args)
          (throw (ex-info "Sketch step :assumption expects no arguments"
                          {:op op :args args})))
        [(sketch-action :assumption basic/assumption [] 0.95)])

      :rfl
      (do
        (when (seq args)
          (throw (ex-info "Sketch step :rfl expects no arguments"
                          {:op op :args args})))
        [(sketch-action :rfl basic/rfl [] 0.95)])

      :constructor
      (do
        (when (seq args)
          (throw (ex-info "Sketch step :constructor expects no arguments"
                          {:op op :args args})))
        [(sketch-action :constructor basic/constructor [] 0.75)])

      :exact
      (let [term-sexpr (one-arg! op args)]
        [(sketch-action :exact-term
                        (fn [ps]
                          (let [goal (current-goal! ps)
                                term (elaborate-term ps term-sexpr (:type goal))]
                            (basic/exact ps term)))
                        [(pr-str term-sexpr)]
                        0.9)])

      :apply
      (let [term-sexpr (one-arg! op args)]
        [(sketch-action :apply-term
                        (fn [ps]
                          (basic/apply-tac ps (elaborate-term ps term-sexpr)))
                        [(pr-str term-sexpr)]
                        0.7)])

      (throw (ex-info "Unknown sketch step" {:step step :op op :args args})))))

(defn- fallback-proposers [{:keys [sketch-hole-proposer sketch-hole-proposers]}]
  (cond
    sketch-hole-proposers sketch-hole-proposers
    sketch-hole-proposer [sketch-hole-proposer]
    :else [search/default-proposer search/theorem-proposer]))

(defn- fallback-actions [ps node opts]
  (->> (fallback-proposers opts)
       (mapcat #(% ps node opts))
       (mapv search/normalize-action)))

(defn sketch-actions
  "Return actions for the current node under `:sketch` in opts.

   Options:
   - `:sketch` sequence of sketch steps
   - `:sketch-after` `:fallback` (default) or `:stop` after the sketch is consumed
   - `:sketch-hole-proposers` proposers used for holes/exhausted fallback"
  [ps node {:keys [sketch sketch-after] :as opts}]
  (let [steps (vec sketch)
        pos (count (:path node))
        step (get steps pos ::done)]
    (cond
      (= step ::done)
      (if (= :stop sketch-after)
        []
        (fallback-actions ps node opts))

      (hole? step)
      (fallback-actions ps node opts)

      :else
      (let [actions (step-actions step)]
        (if (= actions ::hole)
          (fallback-actions ps node opts)
          actions)))))

(defn sketch-proposer
  "Search proposer that reads the sketch from opts."
  [ps node opts]
  (sketch-actions ps node opts))

(defn proposer
  "Return a proposer closed over `sketch` and optional defaults."
  ([sketch]
   (proposer sketch nil))
  ([sketch opts]
   (fn [ps node search-opts]
     (sketch-actions ps node (merge search-opts opts {:sketch sketch})))))

(defn solve-sketch
  "Run best-first search with a hole-aware sketch proposer."
  ([ps sketch]
   (solve-sketch ps sketch nil))
  ([ps sketch opts]
   (search/best-first-search ps (merge {:proposer sketch-proposer
                                        :sketch sketch}
                                       opts))))
