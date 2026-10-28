;; Surface syntax — match expression compilation.
;;
;; Elaborates patterns and delegates decision tree compilation to Meta.Match.

(ns ansatz.surface.match
  "Match expression compilation through Lean's Meta.Match design.

   Surface syntax:
     (match discr
       [pat1 rhs1]
       [pat2 rhs2]
       ...)

   Patterns:
     _                    — wildcard (ignored)
     symbol               — variable binding (lowercase) or constructor (if resolves)
     (Ctor p1 p2 ...)     — constructor with sub-patterns
     0, 1, 2, ...         — Nat literal (desugars to Nat.zero/Nat.succ chains)

   Elaborates discriminants and patterns, generalizes dependent locals, and
   installs a kernel-checked matcher declaration with its metadata. Structural
   and well-founded recursion are compiled separately from match expressions."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta.fvar-subst :as subst]
            [ansatz.meta.generalize-vars :as generalize]
            [ansatz.meta.constructions.util :as u]
            [ansatz.meta.tactic.cases :as cases]
            [ansatz.meta.match.basic :as basic]
            [ansatz.meta.match.match :as matcher]
            [ansatz.meta.match.matcher-info :as mi])
  (:import [ansatz.kernel ConstantInfo]))

;; ============================================================
;; Pattern representation
;; ============================================================

(declare parse-pattern)

(defn- resolve-as-ctor
  "Check if a symbol resolves to a constructor in the environment.
   Returns the ConstantInfo if so, nil otherwise."
  [env sym-str]
  (let [n (name/from-string sym-str)
        ci (env/lookup env n)]
    (when (and ci (.isCtor ^ConstantInfo ci))
      ci)))

(defn parse-pattern
  "Parse a surface s-expression into a Pattern structure.
   env is used to distinguish constructors from variables."
  [env sexpr]
  (cond
    (= '_ sexpr)
    {:tag :wildcard}

    (integer? sexpr)
    {:tag :lit-nat :val (long sexpr)}

    ;; Handle Clojure booleans as constructor names
    (boolean? sexpr)
    (let [s (if sexpr "Bool.true" "Bool.false")]
      {:tag :ctor :ctor-name (name/from-string s) :args []})

    (symbol? sexpr)
    (let [s (str sexpr)]
      (if-let [ci (resolve-as-ctor env s)]
        {:tag :ctor :ctor-name (.name ^ConstantInfo ci) :args []}
        {:tag :var :name sexpr}))

    (and (sequential? sexpr) (seq sexpr))
    (let [head (first sexpr)
          head-str (str head)
          args (rest sexpr)]
      (if-let [ci (resolve-as-ctor env head-str)]
        {:tag :ctor
         :ctor-name (.name ^ConstantInfo ci)
         :args (mapv #(parse-pattern env %) args)}
        (throw (ex-info (str "Match: unknown constructor: " head-str)
                        {:kind :match-error :name head-str}))))

    :else
    (throw (ex-info (str "Match: unsupported pattern: " (pr-str sexpr))
                    {:kind :match-error :pattern sexpr}))))

(defn- est-infer
  "Infer the type of expr, using the est's mvar-aware infer-fn when present (the
   fvar elaborator supplies one so terms still mentioning unsolved/solved mvars are
   typed correctly); falls back to the plain kernel inferType (bvar path has no mvars)."
  [est expr]
  (if-let [f (:infer-fn est)]
    (f est expr)
    (tc/infer-type (:tc est) expr)))

(defn- est-whnf
  "Weak-head normalize expr, using the est's mvar-aware whnf-fn when present."
  [est expr]
  (if-let [f (:whnf-fn est)]
    (f est expr)
    (#'tc/cached-whnf (:tc est) expr)))

(defn- lean-env [est] (if-let [r (:env-ref est)] @r (:env est)))

(defn- refine-index [ctx s lhs rhs]
  (let [lhs (subst/apply s lhs) rhs (subst/apply s rhs)]
    (cond
      (tc/is-def-eq @ctx lhs rhs) s
      ;; Pattern metavariables specialize to existing locals during Lean's
      ;; elabPatterns unification. Keep the older local when both are variables.
      (and (e/fvar? lhs) (e/fvar? rhs))
      (if (< (e/fvar-id lhs) (e/fvar-id rhs))
        (subst/insert s (e/fvar-id rhs) lhs)
        (subst/insert s (e/fvar-id lhs) rhs))
      (and (e/fvar? lhs) (not (cases/depends-on? rhs (e/fvar-id lhs))))
      (subst/insert s (e/fvar-id lhs) rhs)
      (and (e/fvar? rhs) (not (cases/depends-on? lhs (e/fvar-id rhs))))
      (subst/insert s (e/fvar-id rhs) lhs)
      :else
      (let [a (#'cases/constructor-app? ctx lhs) b (#'cases/constructor-app? ctx rhs)]
        (if (and a b (= (.name (:info a)) (.name (:info b))))
          (reduce (fn [s [x y]] (refine-index ctx s x y)) s (map vector (:args a) (:args b)))
          (cases/tactic-error! "match: incompatible constructor indices" {:lhs lhs :rhs rhs}))))))

(defn- lean-pattern [ctx type form]
  (let [type (u/whnf ctx type)
        [type-head type-args] (e/get-app-fn-args type)
        raw-name (cond (nil? form) (symbol "nil")
                       (true? form) 'Bool.true
                       (false? form) 'Bool.false
                       (seq? form) (first form)
                       :else form)
        ctor (when (symbol? raw-name)
               (or (resolve-as-ctor (:env @ctx) (str raw-name))
                   (when (and (e/const? type-head) (not (.contains (str raw-name) ".")))
                     (resolve-as-ctor (:env @ctx) (str (e/const-name type-head) "." raw-name)))))]
    (cond
      (integer? form)
      (do (when (neg? form) (cases/tactic-error! "match: natural literal must be nonnegative" {:value form}))
          {:pattern (basic/val-pattern (e/lit-nat form)) :locals [] :bindings {} :subst {}})
      (string? form) {:pattern (basic/val-pattern (e/lit-str form)) :locals [] :bindings {} :subst {}}
      ctor
      (let [us (e/const-levels type-head) np (.numParams ctor)
            params (subvec type-args 0 np)
            head (u/app (e/const' (.name ctor) us) params)]
        (loop [type (u/infer-type ctx head) i 0 forms (vec (when (seq? form) (rest form)))
               fields [] locals [] bindings {} s {}]
          (if (= i (.numFields ctor))
            (do
              (when (seq forms) (cases/tactic-error! "match: too many constructor fields" {:pattern form}))
              (let [ind (env/lookup! (:env @ctx) (.inductName ctor))
                    ret-args (e/get-app-args (u/whnf ctx type))
                    s (reduce (fn [s [a b]] (refine-index ctx s a b)) s
                              (map vector (subvec type-args (.numParams ind)) (subvec ret-args (.numParams ind))))]
                {:pattern (basic/ctor (.name ctor) us params fields)
                 :locals locals :bindings bindings :subst s}))
            (let [type (u/whnf ctx type)
                  implicit? (and (not= :default (e/forall-info type))
                                 (< (count forms) (- (.numFields ctor) i)))
                  _ (when (and (empty? forms) (not implicit?))
                      (cases/tactic-error! "match: not enough constructor fields" {:pattern form}))
                  child (lean-pattern ctx (subst/apply s (e/forall-type type))
                                      (if implicit? '_ (first forms)))
                  s (subst/append s (:subst child))]
              (when (seq (filter #(contains? bindings %) (keys (:bindings child))))
                (cases/tactic-error! "match: repeated pattern variable" {:pattern form}))
              (recur (e/instantiate1 (e/forall-body type) (basic/pattern-to-expr (:pattern child)))
                     (inc i) (if implicit? forms (subvec forms 1))
                     (conj fields (:pattern child)) (into locals (:locals child))
                     (merge bindings (:bindings child)) s)))))
      (symbol? form)
      (let [x (u/local-decl ctx (str form) type) d (u/decl ctx x)]
        {:pattern (basic/var-pattern (e/fvar-id x)) :locals [d]
         :bindings (if (= '_ form) {} {form {:fvar-id (:id d) :type type}}) :subst {}})
      :else (cases/tactic-error! "match: unsupported pattern" {:pattern form}))))

(defn- lean-row [ctx discrs types forms]
  (when-not (= (count discrs) (count forms))
    (cases/tactic-error! "Incorrect number of patterns in match alternative"
                         {:expected (count discrs) :actual (count forms)}))
  (loop [i 0 pats [] locals [] bindings {} s {}]
    (if (= i (count discrs))
      {:patterns (mapv #(basic/pattern-apply-fvar-subst s %) pats)
       :locals (mapv #(subst/apply-local-decl s %) (remove #(contains? s (:id %)) locals))
       :bindings bindings :subst s}
      (let [result (lean-pattern ctx (subst/apply s (nth types i)) (nth forms i))
            s (subst/append s (:subst result))
            discr (nth discrs i)
            s (if (e/fvar? discr)
                (subst/insert s (e/fvar-id discr) (basic/pattern-to-expr (:pattern result))) s)]
        (when (seq (filter #(contains? bindings %) (keys (:bindings result))))
          (cases/tactic-error! "match: repeated pattern variable" {:patterns forms}))
        (recur (inc i) (conj pats (:pattern result)) (into locals (:locals result))
               (merge bindings (:bindings result)) s)))))

(defn- refine-elab-state [est row]
  (let [s (:subst row)
        refine-entry (fn [entry]
                       (cond-> (update entry :type #(subst/apply s %))
                         (contains? s (:fvar-id entry)) (assoc :as-term (subst/get s (:fvar-id entry)))))
        scope (merge (:scope est) (:bindings row))
        lctx (reduce (fn [lctx d] (assoc lctx (:id d) d))
                     (into {} (map (fn [[id d]] [id (subst/apply-local-decl s d)])) (:lctx (:tc est)))
                     (:locals row))]
    (assoc est :scope (into {} (map (fn [[k v]] [k (refine-entry v)])) scope)
           :tc (tc/attach-lctx (tc/mk-tc-state (lean-env est)) lctx))))

(defn- compile-lean-match [est elab-fn discr-form alt-forms]
  (let [discr-forms (if (vector? discr-form) discr-form [discr-form])
        discrs (mapv #(elab-fn est %) discr-forms)
        types (mapv #(est-whnf est (est-infer est %)) discrs)
        environment (lean-env est)
        ctx (cases/context environment (:lctx (:tc est)))
        _ (swap! ctx assoc :next-id (:next-id est) :meta-mctx (:meta-mctx est))
        explicit-ids (set (keep #(when (e/fvar? %) (e/fvar-id %)) discrs))
        indices (vec (distinct
                      (mapcat (fn [type]
                                (let [[f args] (e/get-app-fn-args type)
                                      ci (when (e/const? f) (env/lookup environment (e/const-name f)))]
                                  (when (and ci (.isInduct ci))
                                    (filter #(and (e/fvar? %) (not (contains? explicit-ids (e/fvar-id %))))
                                            (drop (.numParams ci) args))))) types)))
        ;; Elab/Match.lean generalize: dependent locals become additional
        ;; discriminants, shadowed by fresh pattern variables in each branch.
        generalized (mapv e/fvar (generalize/get-fvars-to-generalize
                                  ctx (vec (concat indices discrs))
                                  :target-types (vec (concat (map #(u/infer-type ctx %) indices) types))
                                  :ignore-let-decls true))
        generalized-types (mapv #(u/infer-type ctx %) generalized)
        all-discrs (vec (concat indices discrs generalized))
        all-types (vec (concat (map #(u/infer-type ctx %) indices) types generalized-types))
        matcher-name (loop []
                       (let [n (str (:matcher-prefix est) ".match_" (swap! (:matcher-counter est) inc))]
                         (if (env/lookup (lean-env est) (name/from-string n)) (recur) n)))
        ;; Allocate the outer match name before elaborating its branch bodies.
        rows (mapv (fn [[forms rhs]]
                     (let [forms (if (= 1 (count discrs)) [forms] forms)
                           row (lean-row ctx (into discrs generalized) (into types generalized-types)
                                         (into (vec forms) (mapv (fn [_] (gensym "_generalized")) generalized)))
                           row (update row :patterns #(into (mapv (fn [x] (basic/inaccessible (subst/apply (:subst row) x))) indices) %))]
                       (assoc row :rhs-form rhs))) alt-forms)
        ret (atom (:declared-ret-type est))
        rows (mapv (fn [row]
                     (let [branch (refine-elab-state est row)
                           rhs (elab-fn branch (:rhs-form row))
                           type (est-infer branch rhs)]
                       (if-let [ret @ret]
                         (when-not ((:unify-fn est) branch type (subst/apply (:subst row) ret))
                           (cases/tactic-error! "match: alternative result type mismatch" {:actual type :expected ret}))
                         (reset! ret type))
                       (assoc row :rhs rhs))) rows)
        zonk #((:zonk-fn est) est %)
        _ (swap! ctx assoc :env (lean-env est))
        _ (cases/set-lctx! ctx (into {} (map (fn [[id d]] [id (update d :type zonk)])) (:lctx @ctx)))
        ;; The match type abstracts fresh discriminants; actual argument expressions
        ;; need not themselves be variables. Earlier indices occur in later types.
        [formal s] (reduce (fn [[xs s] [x type]]
                             (let [v (u/local-decl ctx "_x" (subst/apply s (zonk type)))]
                               [(conj xs v) (if (e/fvar? x) (subst/insert s (e/fvar-id x) v) s)]))
                           [[] {}] (map vector all-discrs all-types))
        ret-type (zonk @ret)
        motive (u/mk-lambda-fvars ctx formal (subst/apply s ret-type))
        match-type (u/mk-forall-fvars ctx formal (subst/apply s ret-type))
        lhss (mapv (fn [row]
                     (basic/alt-lhs (:rhs-form row) (mapv #(update % :type zonk) (:locals row))
                                    (:patterns row))) rows)
        result (matcher/mk-matcher ctx {:matcher-name matcher-name :match-type match-type
                                        :discr-infos (mapv (fn [_] (mi/discr-info)) all-discrs) :lhss lhss})]
    (when (seq (:counter-examples result))
      (cases/tactic-error! "match: non-exhaustive patterns" {:counter-examples (:counter-examples result)}))
    (when (seq (:unused-alt-idxs result))
      (cases/tactic-error! "match: redundant alternatives" {:unused-alt-idxs (:unused-alt-idxs result)}))
    (let [alternatives
          (mapv (fn [row]
                  (cases/set-lctx! ctx (reduce (fn [lctx d] (assoc lctx (:id d) (update d :type zonk)))
                                               (:lctx (:tc est)) (:locals row)))
                  (let [xs (mapv (comp e/fvar :id) (:locals row))
                        rhs (zonk (:rhs row))]
                    (if (seq xs) (u/mk-lambda-fvars ctx xs rhs)
                        (e/lam "_" (u/const' "Unit" []) (e/lift rhs 1 0) :default)))) rows)
          term (u/app (:matcher result) (concat [motive] (map zonk all-discrs) alternatives))]
      (reset! (:env-ref est) (:env result))
      term)))

;; ============================================================
;; Public API
;; ============================================================

(defn compile-match
  "Compile surface alternatives with Lean's Meta.Match compiler."
  [est elab-fn discr-sexpr alt-sexprs]
  (compile-lean-match est elab-fn discr-sexpr alt-sexprs))
