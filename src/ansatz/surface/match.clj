;; Surface syntax — match expression compilation.
;;
;; Compiles pattern-matching expressions to recursor (Ind.rec) applications,
;; following Lean 4's kernel semantics. Handles nested patterns via recursive
;; case splitting (decision tree compilation).

(ns ansatz.surface.match
  "Match expression compilation: surface patterns → Ansatz recursor application.

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

   Compilation strategy:
     1. Elaborate the discriminant, infer its inductive type
     2. Look up Ind.rec (the recursor)
     3. For each constructor: find matching alternative, build minor premise lambda
     4. For nested constructor patterns: recursively compile inner match
     5. Motive: λ (x : IndType) => RetType (non-dependent)
     6. Result: @Ind.rec motive minor1 ... minorN discr"
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.tc :as tc])
  (:import [ansatz.kernel ConstantInfo ConstantInfo$RecursorRule]))

;; ============================================================
;; Recursion context — Lean 4 separation of match vs recursion
;; ============================================================

;; When true, matches use casesOn (no IH) instead of rec (with IH).
;; Set to true after the outermost match in a defn body fires.
;; This prevents inner matches from generating IH bindings that
;; shadow the outer recursion's IH — matching Lean 4's design where
;; only the top-level structural recursion provides IHs.
(def ^:dynamic *use-cases-on?* false)

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

(defn- desugar-nat-lit
  "Desugar a natural number literal pattern into Nat.zero/Nat.succ constructor patterns."
  [n]
  (if (zero? n)
    {:tag :ctor :ctor-name (name/from-string "Nat.zero") :args []}
    {:tag :ctor
     :ctor-name (name/from-string "Nat.succ")
     :args [(desugar-nat-lit (dec n))]}))

(defn- normalize-pattern
  "Normalize pattern: desugar nat literals to constructor patterns."
  [pat]
  (case (:tag pat)
    :lit-nat (desugar-nat-lit (:val pat))
    :ctor (update pat :args #(mapv normalize-pattern %))
    pat))

;; ============================================================
;; Constructor field extraction
;; ============================================================

(defn- get-ctor-fields
  "Get the field types of a constructor, after instantiating params.
   Returns [{:name str :type Expr} ...] for each field."
  [env ctor-name ind-levels params]
  (let [^ConstantInfo ctor-ci (env/lookup! env ctor-name)
        ctor-type (.type ctor-ci)
        num-params (.numParams ctor-ci)
        ;; Instantiate level params
        subst (into {} (map vector (vec (.levelParams ctor-ci)) ind-levels))
        ctor-type (e/instantiate-level-params ctor-type subst)
        ;; Skip params (instantiate with actual values)
        ctor-type (loop [t ctor-type i 0 ps (seq params)]
                    (if (and (< i num-params) (e/forall? t) ps)
                      (recur (e/instantiate1 (e/forall-body t) (first ps))
                             (inc i) (next ps))
                      t))]
    ;; Peel remaining foralls = fields
    (loop [t ctor-type fvars [] result []]
      (if (e/forall? t)
        (let [fid (+ 700000 (count fvars))
              fv (e/fvar fid)
              field-name (let [n (e/forall-name t)]
                           (if n (if (string? n) n (name/->string n))
                               (str "x" (count fvars))))
              field-type (e/forall-type t)]
          (recur (e/instantiate1 (e/forall-body t) fv)
                 (conj fvars fid)
                 (conj result {:name field-name :type field-type})))
        result))))

(defn- count-ih-args
  "Count how many IH (induction hypothesis) arguments the recursor adds
   for a given constructor. This is the number of recursive fields
   (fields whose type is the inductive type being matched)."
  [env ctor-name ind-name ind-levels params]
  (let [fields (get-ctor-fields env ctor-name ind-levels params)]
    (count (filter (fn [{:keys [type]}]
                     ;; A field is recursive if its type's head is the inductive
                     (let [[head _] (e/get-app-fn-args type)]
                       (and (e/const? head)
                            (= (e/const-name head) ind-name))))
                   fields))))

;; ============================================================
;; Minor premise construction
;; ============================================================

(declare compile-match-inner)
(declare compile-match-term)

(defn- find-matching-alts
  "Find ALL alternatives that match a constructor (including wildcards/vars).
   Returns a vector of matching alternatives, preserving order."
  [ctor-name alts]
  (filterv (fn [alt]
             (let [pat (:pattern alt)]
               (or (= :wildcard (:tag pat))
                   (= :var (:tag pat))
                   (and (= :ctor (:tag pat))
                        (= ctor-name (:ctor-name pat))))))
           alts))

(defn- build-minor-premise
  "Build a minor premise lambda for one constructor.

   The minor premise is:
     λ (field1 : T1) ... (fieldN : TN) (ih1 : IH1) ... => rhs-body

   Fields come from the constructor type.
   IH args come from the recursor (one per recursive field).

   matching-alts: vector of ALL alternatives that match this constructor
   (including wildcard/var alts). When multiple ctor alts match the same
   constructor with different sub-patterns, we build nested matches from
   all of them."
  [env est elab-fn ind-name ind-levels params ctor-name nfields
   num-ih-args matching-alts ret-type & [discr-fvar-id]]
  (when (empty? matching-alts)
    (throw (ex-info (str "Match: non-exhaustive patterns, missing case for "
                         (name/->string ctor-name))
                    {:kind :match-error :ctor ctor-name})))
  (let [;; Get field info from constructor type
        field-info (get-ctor-fields env ctor-name ind-levels params)
        _ (assert (= nfields (count field-info))
                  (str "Field count mismatch for " (name/->string ctor-name)
                       ": expected " nfields " got " (count field-info)))
        ;; Create fvars for fields
        field-fvar-ids (mapv (fn [_] (swap! (:next-id est) inc))
                             (range nfields))
        field-fvars (mapv e/fvar field-fvar-ids)
        ;; Create fvars for IH args
        ih-fvar-ids (mapv (fn [_] (swap! (:next-id est) inc))
                          (range num-ih-args))
        ;; Re-derive field types by peeling the ctor type with our actual fvars
        ^ConstantInfo ctor-ci (env/lookup! env ctor-name)
        ctor-type-raw (.type ctor-ci)
        subst (into {} (map vector (vec (.levelParams ctor-ci)) ind-levels))
        ctor-type-inst (e/instantiate-level-params ctor-type-raw subst)
        ;; Skip params
        ctor-type-inst (loop [t ctor-type-inst i 0 ps (seq params)]
                         (if (and (< i (.numParams ctor-ci)) (e/forall? t) ps)
                           (recur (e/instantiate1 (e/forall-body t) (first ps))
                                  (inc i) (next ps))
                           t))
        ;; Peel fields with our fvars — this gives us correct types
        real-field-types
        (loop [t ctor-type-inst i 0 types []]
          (if (and (< i nfields) (e/forall? t))
            (let [ft (e/forall-type t)]
              (recur (e/instantiate1 (e/forall-body t) (nth field-fvars i))
                     (inc i)
                     (conj types ft)))
            types))
        ;; Compute IH types: motive applied to the recursive field.
        ;; Lean 4: IH has type `motive(recursive-field)`, not just `ret-type`.
        ;; ret-type has bvar 0 referencing the motive's variable — instantiate
        ;; with the actual recursive field fvar.
        early-rec-indices (vec (keep-indexed
                                 (fn [i fi]
                                   (let [ft (:type fi)
                                         [fh _] (e/get-app-fn-args ft)]
                                     (when (and (e/const? fh) (= (e/const-name fh) ind-name))
                                       i)))
                                 field-info))
        ih-types (mapv (fn [i]
                         (let [field-idx (get early-rec-indices i)
                               rec-fvar (when field-idx (nth field-fvars field-idx))]
                           (if rec-fvar
                             (e/instantiate1 ret-type rec-fvar)
                             ret-type)))
                       (range num-ih-args))
        ;; Determine which alt to use for variable bindings in scope:
        ;; Use the first ctor alt (for var bindings from sub-patterns),
        ;; falling back to wildcard/var alt
        first-ctor-alt (first (filter #(= :ctor (:tag (:pattern %))) matching-alts))
        first-alt (or first-ctor-alt (first matching-alts))
        pat (:pattern first-alt)
        sub-patterns (when (= :ctor (:tag pat)) (:args pat))
        ;; Build elaboration scope with field bindings
        est' (reduce
              (fn [est i]
                (let [fid (nth field-fvar-ids i)
                      ft (nth real-field-types i)
                      sub-pat (when sub-patterns (get sub-patterns i))
                      field-name (or (when sub-pat
                                       (case (:tag sub-pat)
                                         :var (str (:name sub-pat))
                                         nil))
                                     (:name (nth field-info i)))]
                  ;; Always add field to scope (by user-given name or default name)
                  ;; so nested match bodies can reference it.
                  (let [scope-sym (cond
                                    (and sub-pat (= :var (:tag sub-pat)))
                                    (:name sub-pat)
                                    field-name (symbol (str field-name))
                                    :else nil)]
                    (cond-> est
                      scope-sym
                      (assoc-in [:scope scope-sym] {:fvar-id fid :type ft})
                      true
                      (update :tc update :lctx
                              red/lctx-add-local fid (or field-name (str "x" i)) ft)))))
              est
              (range nfields))
        ;; Identify recursive fields for IH naming
        rec-field-indices (vec (keep-indexed
                                (fn [i fi]
                                  (let [ft (:type fi)
                                        [fh _] (e/get-app-fn-args ft)]
                                    (when (and (e/const? fh) (= (e/const-name fh) ind-name))
                                      i)))
                                field-info))
        ;; Add IH fvars to lctx (always needed for recursor lambda) and
        ;; to scope ONLY when not suppressed. Lean 4: only the outermost
        ;; structural recursion binds IH names; inner matches don't.
        est' (reduce
              (fn [est i]
                (let [fid (nth ih-fvar-ids i)
                      iht (nth ih-types i)
                      ;; Name IH after the recursive field: ih_left, ih_right, etc.
                      rec-field-idx (get rec-field-indices i)
                      field-name (when rec-field-idx (:name (nth field-info rec-field-idx)))
                      ih-name (if field-name (str "ih_" field-name) (str "ih" i))
                      ih-sym (symbol ih-name)]
                  (cond-> est
                    ;; Always add to lctx (recursor lambda needs the binding)
                    true
                    (update :tc update :lctx red/lctx-add-local fid ih-name iht)
                    ;; Only add to scope when NOT suppressed (top-level recursion)
                    (not *use-cases-on?*)
                    (assoc-in [:scope ih-sym] {:fvar-id fid :type iht}))))
              est'
              (range num-ih-args))
        ;; Check if we have nested ctor sub-patterns from ANY matching alt
        has-nested-ctors?
        (some (fn [alt]
                (and (= :ctor (:tag (:pattern alt)))
                     (some #(= :ctor (:tag %)) (:args (:pattern alt)))))
              matching-alts)
        ;; Elaborate the RHS, handling nested patterns
        rhs-body
        (if has-nested-ctors?
          ;; Build nested alts from ALL matching alternatives
          (compile-match-inner est' env elab-fn
                               field-fvar-ids field-fvars
                               matching-alts nfields)
          ;; Simple case: just elaborate the first alt's RHS
          (elab-fn est' (:rhs-sexpr first-alt)))
        ;; Replace discriminant variable with constructor application.
        ;; When the match body references the original parameter (e.g., `l` in
        ;; `(cons x l)`), the elaborated RHS has fvar_l. But the recursor's iota
        ;; reduction decomposes `l` into `(cons hd tl)`. We must substitute so
        ;; the recursor body and equation theorems agree on the structure.
        rhs-body (if discr-fvar-id
                   (let [ctor-app (reduce e/app
                                          (e/const' ctor-name ind-levels)
                                          (concat params field-fvars))]
                     (e/instantiate1 (e/abstract1 rhs-body discr-fvar-id) ctor-app))
                   rhs-body)
        ;; Build lambda: abstract IH fvars, then field fvars (inside out)
        body-with-ih
        (reduce (fn [body i]
                  (let [fid (nth ih-fvar-ids i)
                        iht (nth ih-types i)]
                    (e/lam (str "ih" i) iht
                           (e/abstract1 body fid) :default)))
                rhs-body
                (reverse (range num-ih-args)))
        ;; Field fvars
        result
        (reduce (fn [body i]
                  (let [fid (nth field-fvar-ids i)
                        ft (nth real-field-types i)
                        fname (:name (nth field-info i))]
                    (e/lam fname ft
                           (e/abstract1 body fid) :default)))
                body-with-ih
                (reverse (range nfields)))]
    result))

(defn- compile-match-inner
  "Handle nested patterns by recursively matching on fields that have
   constructor sub-patterns.

   matching-alts: all alternatives that matched this constructor at the outer level.
   Each may have different sub-patterns on the fields. We find the first field
   with nested ctor patterns and compile a match on it, collecting alternatives
   from all outer alts that have ctor sub-patterns on that field."
  [est env elab-fn field-fvar-ids field-fvars matching-alts nfields]
  ;; Find the first field index that has any ctor sub-pattern across all alts
  (let [nested-field-idx
        (first (keep (fn [i]
                       (when (some (fn [alt]
                                     (and (= :ctor (:tag (:pattern alt)))
                                          (let [args (:args (:pattern alt))]
                                            (and (< i (count args))
                                                 (= :ctor (:tag (nth args i)))))))
                                   matching-alts)
                         i))
                     (range nfields)))]
    (if (nil? nested-field-idx)
      ;; No nested ctor patterns — elaborate the first alt's RHS
      (elab-fn est (:rhs-sexpr (first matching-alts)))
      ;; Build a nested match on the field at nested-field-idx
      (let [fvar-id (nth field-fvar-ids nested-field-idx)
            fvar (nth field-fvars nested-field-idx)
            field-decl (red/lctx-lookup (:lctx (:tc est)) fvar-id)
            field-type (or (:type field-decl)
                           (tc/infer-type (:tc est) fvar))
            field-type-whnf (#'tc/cached-whnf (:tc est) field-type)
            ;; Collect inner alts from all matching outer alts
            inner-alts
            (reduce
             (fn [acc alt]
               (let [pat (:pattern alt)]
                 (cond
                   ;; Wildcard/var alt at outer level → wildcard at inner level
                   (or (= :wildcard (:tag pat))
                       (= :var (:tag pat)))
                   (conj acc {:pattern {:tag :wildcard}
                              :rhs-sexpr (:rhs-sexpr alt)})
                   ;; Ctor alt with ctor sub-pattern on this field
                   (and (= :ctor (:tag pat))
                        (< nested-field-idx (count (:args pat)))
                        (= :ctor (:tag (nth (:args pat) nested-field-idx))))
                   (conj acc {:pattern (nth (:args pat) nested-field-idx)
                              :rhs-sexpr (:rhs-sexpr alt)})
                   ;; Ctor alt with wildcard/var sub-pattern on this field
                   (and (= :ctor (:tag pat))
                        (< nested-field-idx (count (:args pat)))
                        (or (= :wildcard (:tag (nth (:args pat) nested-field-idx)))
                            (= :var (:tag (nth (:args pat) nested-field-idx)))))
                   (conj acc {:pattern (nth (:args pat) nested-field-idx)
                              :rhs-sexpr (:rhs-sexpr alt)})
                   :else acc)))
             []
             matching-alts)]
        (compile-match-term est env elab-fn fvar field-type-whnf inner-alts)))))

(defn- compile-match-term
  "Compile a match on a single discriminant to a recursor application."
  [est env elab-fn discr-expr discr-type alts]
  (let [[type-head type-args] (e/get-app-fn-args discr-type)
        _ (when-not (e/const? type-head)
            (throw (ex-info "Match: discriminant type head is not a constant"
                            {:kind :match-error :type discr-type})))
        ind-name (e/const-name type-head)
        ^ConstantInfo ind-ci (env/lookup! env ind-name)
        _ (when-not (.isInduct ind-ci)
            (throw (ex-info (str "Match: discriminant type is not an inductive: "
                                 (name/->string ind-name))
                            {:kind :match-error :type discr-type})))
        ind-levels (e/const-levels type-head)
        num-params (.numParams ind-ci)
        params (subvec (vec type-args) 0 (min num-params (count type-args)))
        indices (subvec (vec type-args) (min num-params (count type-args)))
        ;; Suppress IH for inner matches: still use rec (same arg order),
        ;; but don't bind IH params to scope. Lean 4: only the top-level
        ;; structural recursion generates IHs. Inner matches are pure
        ;; destructuring — IH lambdas exist but are unnamed/unused.
        suppress-ih *use-cases-on?*
        rec-name (name/mk-str ind-name "rec")
        ^ConstantInfo rec-ci (env/lookup! env rec-name)
        _ (when-not (.isRecursor rec-ci)
            (throw (ex-info (str "Match: recursor not found: " (name/->string rec-name))
                            {:kind :match-error :name rec-name})))
        ^"[Lansatz.kernel.ConstantInfo$RecursorRule;" rules (.rules rec-ci)
        num-minors (.numMinors rec-ci)
        ;; Normalize patterns
        alts (mapv #(update % :pattern normalize-pattern) alts)
        ;; Find the first concrete alternative to determine return type
        ;; Elaborate its RHS in a temporary scope to get the type
        first-concrete-alt (first (filter #(or (= :wildcard (:tag (:pattern %)))
                                               (= :var (:tag (:pattern %)))
                                               (= :ctor (:tag (:pattern %))))
                                          alts))
        ;; For return type: elaborate first wildcard/var alt's RHS if available
        ;; Otherwise we'll determine it from the first ctor alt
        ;; First, build all minor premises and infer ret-type from the first
        ;; We need ret-type to build the motive, but we need the motive to
        ;; know the recursor level... chicken-and-egg.
        ;; Solution: use Type (level 1) as default motive level, then verify.
        motive-level (lvl/succ lvl/zero)
        rec-levels (into [motive-level] ind-levels)
        ;; Determine return type by finding a simple alt and elaborating its RHS
        ret-type-info
        (let [simple-alt (or (first (filter #(= :var (:tag (:pattern %))) alts))
                             (first (filter #(= :wildcard (:tag (:pattern %))) alts)))]
          (if simple-alt
            ;; Elaborate the simple alt's RHS to determine return type
            (let [rhs-expr (elab-fn est (:rhs-sexpr simple-alt))
                  tc (:tc est)
                  rhs-type (tc/infer-type tc rhs-expr)]
              {:ret-type rhs-type :sample-rhs rhs-expr})
            ;; No simple alt — use first ctor alt, elaborate its RHS
            ;; with fields in scope
            (let [alt (first alts)
                  pat (:pattern alt)
                  ctor-name (:ctor-name pat)
                  field-info (get-ctor-fields env ctor-name ind-levels params)
                  ;; Create temp fvars for fields
                  temp-est est
                  temp-est (reduce
                            (fn [est fi]
                              (let [fid (swap! (:next-id est) inc)
                                    ft (:type fi)
                                    sub-pat (get (:args pat) (.indexOf field-info fi))]
                                (cond-> est
                                  (and sub-pat (= :var (:tag sub-pat)))
                                  (assoc-in [:scope (:name sub-pat)]
                                            {:fvar-id fid :type ft})
                                  true
                                  (update :tc update :lctx
                                          red/lctx-add-local fid (:name fi) ft))))
                            temp-est
                            field-info)
                  rhs-expr (elab-fn temp-est (:rhs-sexpr alt))
                  tc (:tc temp-est)
                  rhs-type (tc/infer-type tc rhs-expr)]
              {:ret-type rhs-type})))
        ret-type (:ret-type ret-type-info)
        ;; Build the motive: λ (x : IndType params) => ret-type
        ind-applied (reduce e/app (e/const' ind-name ind-levels) params)
        motive (e/lam "x" ind-applied ret-type :default)
        ;; Build minor premises for each constructor.
        ;; When suppress-ih: still create IH lambda params (rec requires them),
        ;; but don't bind them to scope — preventing name shadowing.
        ;; When NOT suppress-ih (top-level): wrap elab-fn so nested matches
        ;; suppress IH (Lean 4: only outermost recursion provides IHs).
        elab-fn-for-rhs (if suppress-ih
                           elab-fn  ;; already suppressing
                           ;; Top-level rec: set *use-cases-on?* for RHS elaboration
                           (fn [est sexpr]
                             (binding [*use-cases-on?* true]
                               (elab-fn est sexpr))))
        minor-terms
        (mapv
         (fn [i]
           (let [^ConstantInfo$RecursorRule rule (aget rules i)
                 ctor-name (.ctor rule)
                 nfields (.nfields rule)
                 num-ih (count-ih-args env ctor-name ind-name ind-levels params)
                 matching-alts (find-matching-alts ctor-name alts)]
             (build-minor-premise env est elab-fn-for-rhs ind-name ind-levels params
                                  ctor-name nfields num-ih
                                  matching-alts ret-type
                                  ;; Pass discriminant fvar-id for substitution
                                  (when (e/fvar? discr-expr) (e/fvar-id discr-expr)))))
         (range num-minors))]
    ;; Build recursor application: params, motive, minors, indices, major
    (reduce e/app
            (e/const' rec-name rec-levels)
            (concat params [motive] minor-terms indices [discr-expr]))))

;; ============================================================
;; Public API
;; ============================================================

(defn compile-match
  "Compile a match expression from surface syntax.

   est: elaboration state (from elaborate.clj)
   elab-fn: function (elab-fn est sexpr) → Expr to elaborate sub-expressions
   discr-sexpr: the discriminant s-expression
   alt-sexprs: list of [pattern rhs] pairs

   Returns the compiled Expr (a recursor application)."
  [est elab-fn discr-sexpr alt-sexprs]
  (let [env (:env est)
        discr-expr (elab-fn est discr-sexpr)
        tc (:tc est)
        discr-type (tc/infer-type tc discr-expr)
        discr-type-whnf (#'tc/cached-whnf tc discr-type)
        alts (mapv (fn [[pat-sexpr rhs-sexpr]]
                     {:pattern (parse-pattern env pat-sexpr)
                      :rhs-sexpr rhs-sexpr})
                   alt-sexprs)]
    (compile-match-term est env elab-fn discr-expr discr-type-whnf alts)))
