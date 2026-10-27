(ns ansatz.tactic.grind.theorem
  "Theorem compilation and joint matching, following Grind/EMatchTheorem.lean and EMatch.lean."
  (:require [clojure.set :as set]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.eqns :as eqns]
            [ansatz.tactic.grind.action :as action]
            [ansatz.tactic.grind.egraph :as eg]
            [ansatz.tactic.grind.ematch :as ematch]))

(defn prop? [st type]
  (let [s (#'tc/cached-whnf st (tc/infer-type st type))]
    (and (e/sort? s) (lvl/level= lvl/zero (e/sort-level s)))))

(defn head-index [expr]
  (let [[h _] (e/get-app-fn-args expr)]
    (cond (e/const? h) (e/const-name h)
          (e/fvar? h) [:fvar (e/fvar-id h)])))

(defn- variables [expr]
  (cond (e/bvar? expr) #{(e/bvar-idx expr)}
        (e/app? expr) (set/union (variables (e/app-fn expr)) (variables (e/app-arg expr)))
        :else #{}))

(defn- pattern-parts [expr]
  ;; EMatchTheorem.splitWhileForbidden: logical wrappers are not pattern heads.
  (let [[h args] (e/get-app-fn-args expr)
        n (when (e/const? h) (name/->string (e/const-name h)))]
    (case n
      "Eq" (mapcat pattern-parts (rest args))
      ("And" "Or" "Iff" "Not") (mapcat pattern-parts args)
      (when (and (e/app? expr) (head-index expr) (seq (variables expr))) [expr]))))

(defn compile-theorem
  "Compile both local fvar proofs and named proofs. Proof binders are constraints.
   Explicit patterns are one multipattern, sharing a single assignment.
   Returns nil when inferred patterns cannot cover the data binders (Lean
   EMatchTheorem.mkEMatchTheoremWithKind?). Invalid explicit metadata still errors."
  ([st origin proof type levels] (compile-theorem st origin proof type levels nil))
  ([st origin proof type levels explicit-patterns]
   (let [n (loop [t type n 0]
             (if (e/forall? t) (recur (e/forall-body t) (inc n)) n))
         {:keys [params body]}
         (loop [t type st st i 0 params []]
           (if (e/forall? t)
             (let [domain (e/forall-type t)
                   id (+ 800000000 i)
                   param {:index (- n i 1) :proof? (prop? st domain)
                          ;; Lift the raw domain to the full telescope's bvar coordinates.
                          :pattern-domain (e/lift (loop [raw type j i]
                                                   (if (zero? j) (e/forall-type raw)
                                                       (recur (e/forall-body raw) (dec j))))
                                                 (- n i) 0)}]
               (recur (e/instantiate1 (e/forall-body t) (e/fvar id))
                      (update st :lctx red/lctx-add-local id "x" domain)
                      (inc i) (conj params param)))
             {:params params :body t}))
         raw-body (loop [t type] (if (e/forall? t) (recur (e/forall-body t)) t))
         data-vars (set (map :index (remove :proof? params)))
         candidates (concat (mapcat (comp pattern-parts :pattern-domain) (filter :proof? params))
                            (pattern-parts raw-body))
         patterns (or explicit-patterns
                      (:patterns (reduce (fn [{:keys [covered] :as s} pat]
                                           (let [vs (set/intersection data-vars (variables pat))]
                                             (if (set/subset? vs covered) s
                                                 (-> s (update :covered set/union vs)
                                                     (update :patterns conj pat)))))
                                         {:covered #{} :patterns []} candidates)))
         _ (when (and (some? explicit-patterns)
                      (not (and (sequential? explicit-patterns)
                                (every? #(instance? ansatz.kernel.Expr %) explicit-patterns))))
             (throw (ex-info "grind: malformed theorem patterns"
                             {:kind :grind-metadata-error :origin origin :patterns explicit-patterns})))
         covered (reduce set/union #{} (map variables patterns))]
     (when-not (prop? (loop [st st i 0 t type]
                       (if (e/forall? t)
                         (let [id (+ 800000000 i) d (e/forall-type t)]
                           (recur (update st :lctx red/lctx-add-local id "x" d)
                                  (inc i) (e/instantiate1 (e/forall-body t) (e/fvar id)))) st)) body)
       (action/fail! "hint is not a proposition" {:origin origin}))
     (when (and (some? explicit-patterns)
                (or (not (set/subset? data-vars covered))
                    (not (set/subset? covered data-vars))
                    (not-every? head-index patterns)))
       (throw (ex-info "grind: malformed theorem patterns"
                       {:kind :grind-metadata-error :origin origin :patterns patterns})))
     (when (set/subset? data-vars covered)
       {:origin origin :proof proof :type type :level-params levels :num-params n
        :params params :patterns (vec patterns) :symbols (mapv head-index patterns)
        :kind :default :constraints (vec (filter :proof? params))}))))

(defn mk-ematch-intro-theorem?
  "Attr.addEMatchAttr for constructors. Prefer a conclusion pattern when it
   covers the data parameters; otherwise retain optional inferred patterns."
  [st nm]
  (let [ci (env/lookup (:env st) nm)
        body (loop [t (.type ci)] (if (e/forall? t) (recur (e/forall-body t)) t))]
    (when-let [thm (compile-theorem st nm (e/const' nm (mapv lvl/param (.levelParams ci)))
                                  (.type ci) (vec (.levelParams ci)))]
      (if (and (e/app? body)
               (set/subset? (set (map :index (remove :proof? (:params thm)))) (variables body)))
        (assoc thm :patterns [body] :symbols [(head-index body)] :kind :bwd) thm))))

(defn named [st hint]
  (let [nm (if (instance? ansatz.kernel.Name hint) hint (name/from-string (str hint)))
        ci (env/lookup (:env st) nm)]
    (when-not ci (action/fail! "unknown hint" {:hint hint}))
    ;; EMatchTheorem.mkEMatchEqTheoremsForDef? requires getEqnsFor? metadata.
    ;; Surface definitions currently have no complete equation inventory. Fail explicitly
    ;; rather than guessing eq_N names or silently dropping missing equations.
    (when (= :def (env/ci-tag ci))
      (action/fail! "definition equation inventory unavailable" {:hint hint :unsupported :equation-inventory}))
    (or (compile-theorem st nm (e/const' nm (mapv lvl/param (.levelParams ci)))
                         (.type ci) (vec (.levelParams ci)))
        (action/fail! "cannot infer covering patterns for hint" {:hint hint}))))

(defn mk-ematch-eq-theorems-for-def?
  "EMatchTheorem.lean mkEMatchEqTheoremsForDef?: expand getEqnsFor? in order."
  [st nm]
  (when-let [equations (eqns/eqns-for (:env st) nm)]
    (when-let [errors (seq (eqns/errors-for (:env st) nm))]
      (action/fail! "definition has equation generation errors" {:hint nm :errors errors}))
    (mapv #(assoc (named st %) :kind :eq-lhs) equations)))

(defn for-hint [st hint]
  (let [nm (if (instance? ansatz.kernel.Name hint) hint (name/from-string (str hint)))
        ci (env/lookup (:env st) nm)]
    (when-not ci (action/fail! "unknown hint" {:hint hint}))
    (if (= :def (env/ci-tag ci))
      (or (not-empty (mk-ematch-eq-theorems-for-def? st nm))
          (action/fail! "definition equation inventory unavailable" {:hint hint}))
      [(named st nm)])))

(defn- match-constraints [gs unknowns pat term choice max-gen]
  ;; EMatch.lean matchArg?/processMatch/processChoices: each nested argument is
  ;; its own matching constraint. Backtrack over its class, retaining the shared
  ;; assignment and the maximum generation of every selected application.
  (letfn [(search [choices]
            (lazy-seq
             (loop [choices choices]
               (when-let [{:keys [constraints assignment gen] :as choice} (first choices)]
                 (let [tail (rest choices)]
                   (if-let [[p t] (first constraints)]
                     (let [choice (assoc choice :constraints (rest constraints))
                           [head args] (e/get-app-fn-args p)
                           next-choices
                           (if (e/bvar? p)
                             (when-let [m (#'ematch/match-pattern gs unknowns p t assignment)]
                               [(assoc choice :assignment m)])
                             (for [member (or (eg/collect-eqc gs t) [t])
                                   :let [node (eg/get-enode gs member)]
                                   :when (or (nil? node) (< (:gen node) max-gen))
                                   :let [[mh ma] (e/get-app-fn-args member)
                                         app-pattern? (and (e/app? p) (or (e/const? head) (e/fvar? head)))
                                         m (if app-pattern?
                                             (when (and (e/app? member) (= (count args) (count ma)))
                                               (#'ematch/match-pattern gs unknowns head mh assignment))
                                             (#'ematch/match-pattern gs unknowns p member assignment))]
                                   :when m]
                               (cond-> (assoc choice :assignment m :gen (max gen (or (:gen node) 0)))
                                 app-pattern? (update :constraints #(concat (map vector args ma) %)))))]
                       (recur (concat next-choices tail)))
                     (cons (dissoc choice :constraints) (search tail))))))))]
    (search [(assoc choice :constraints [[pat term]])])))

(defn matches
  "EMatch.Cnstr.continue: a multipattern is a join, never alternative matches.
   Generations follow matched terms, independently of the round number."
  [gs thm config]
  (reduce
   (fn [assignments pat]
     (for [choice assignments
           candidate (get (:app-map gs) (head-index pat))
           match (match-constraints gs (set (:level-params thm)) pat candidate choice (:gen config))]
       match))
   (when (< (get thm :gen 0) (:gen config))
     [{:assignment {:vars {} :levels {} :ftypes {}} :gen (get thm :gen 0)}])
   (:patterns thm)))

(defn instantiate
  "Solve proof arguments from established facts, then assert any proposition.
   Retain trailing unsolved proof binders as an implication (EMatch.lean
   instantiateTheorem abstracts unassigned proof parameters). Malformed metadata errors."
  [st thm {:keys [assignment gen]} prove]
  (let [levels (into {} (map (fn [p] [p (get-in assignment [:levels p] lvl/zero)]) (:level-params thm)))
        proof (e/instantiate-level-params (:proof thm) levels)
        type (e/instantiate-level-params (:type thm) levels)
        fact (fn [type proof args]
               {:kind :fact :prop type :proof proof :gen (inc gen)
                :key [(:origin thm) args (mapv levels (:level-params thm))]})]
    (loop [type type proof proof params (:params thm) args []]
      (if-let [param (first params)]
        (let [domain (e/forall-type type)
              arg (if (:proof? param) (prove domain) (get-in assignment [:vars (:index param)]))]
          (if arg
            (do (when-not (tc/is-def-eq st domain (tc/infer-type st arg))
                  (action/fail! "theorem assignment type mismatch" {:origin (:origin thm) :domain domain :argument arg}))
                (recur (e/instantiate1 (e/forall-body type) arg) (e/app proof arg) (rest params) (conj args arg)))
            (when (every? :proof? params) (fact type proof args))))
        (fact type proof args)))))
