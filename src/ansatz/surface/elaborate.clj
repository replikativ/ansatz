;; Surface syntax — runtime elaboration with implicit argument insertion.

(ns ansatz.surface.elaborate
  "Runtime elaboration: transforms surface s-expressions into fully explicit
   Ansatz terms by resolving names, inserting implicit arguments, inferring
   universe levels, and type-checking.

   This is THE elaborator: type-directed, fvar-first, with metavariables + instance synthesis.
   It backs `a/defn` bodies+signatures, `a/theorem` goals, proof terms, and tactic-arg
   elaboration. (The legacy bvar-only `term` builder it superseded has been retired.)

   Usage:
     (elaborate env '(forall [a Nat] (Eq a a)))
     ;; => fully explicit: (forall [a Nat] (@Eq.{1} Nat a a))

     (elaborate env '(lam [a Nat] (Eq.refl a))  expected-type)
     ;; => checks against expected-type, infers implicits"
  (:require [clojure.string]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.tc :as tc]
            [ansatz.surface.match :as match]
            [ansatz.surface.ingest :as ingest])
  (:import [ansatz.kernel Env]))

;; ============================================================
;; Elaboration state
;; ============================================================

(defn- mk-elab-state
  "Create elaboration state with metavar tracking."
  [^Env env]
  {:env env
   :tc (tc/mk-tc-state env)
   :next-id (atom 1000000)  ;; high start to avoid collision with tc ids
   :mctx (atom {})          ;; {id → {:type Expr :solution Expr-or-nil}}
   :level-mctx (atom {})    ;; {id → {:solution Level-or-nil}}
   :scope {}                ;; symbol → {:fvar-id long :type Expr}
   :depth 0})

(defn- fresh-id! [est]
  (let [id (swap! (:next-id est) inc)]
    id))

(defn- fresh-mvar!
  "Create a fresh metavariable (as an fvar) with the given type.
   Returns the fvar Expr. Records in mctx for later solving."
  [est type]
  (let [id (fresh-id! est)]
    (swap! (:mctx est) assoc id {:type type :solution nil})
    (e/fvar id)))

(defn- fresh-level-mvar!
  "Create a fresh universe level metavariable.
   Returns a Level/param with a synthetic name."
  [est]
  (let [id (fresh-id! est)
        n (name/from-string (str "?u" id))]
    (swap! (:level-mctx est) assoc id {:name n :solution nil})
    (lvl/param n)))

(declare unify-levels!)

(defn- solve-mvar!
  "Assign a solution to a metavariable. Returns true if successful.
   Also attempts to solve level metavars by inferring the type of the solution
   and unifying with the expected type."
  [est id solution]
  (let [m (get @(:mctx est) id)]
    (when m
      (if (:solution m)
        ;; Already solved — check consistency
        (= (:solution m) solution)
        (do (swap! (:mctx est) assoc-in [id :solution] solution)
            ;; Try to solve level metavars: if the mvar's expected type is Sort ?u
            ;; and solution's type is Sort N, unify ?u = N
            (try
              (let [expected-type (:type m)
                    tc (:tc est)
                    actual-type (tc/infer-type tc solution)
                    expected-whnf (#'tc/cached-whnf tc expected-type)
                    actual-whnf (#'tc/cached-whnf tc actual-type)]
                (when (and (e/sort? expected-whnf) (e/sort? actual-whnf))
                  (unify-levels! est (e/sort-level expected-whnf) (e/sort-level actual-whnf))))
              (catch Exception _ nil))
            true)))))

(defn- mvar-solution [est id]
  (get-in @(:mctx est) [id :solution]))

(defn- solve-level-mvar!
  "Assign a solution to a level metavariable."
  [est id solution]
  (let [m (get @(:level-mctx est) id)]
    (when m
      (if (:solution m)
        true
        (do (swap! (:level-mctx est) assoc-in [id :solution] solution)
            true)))))

;; ============================================================
;; Metavariable zonking (substitute solutions)
;; ============================================================

(defn- zonk-level
  "Substitute solved level metavariables in a level."
  [est l]
  (if (nil? l) l
      (let [tag (.tag ^ansatz.kernel.Level l)]
        (case tag
          0 l ;; zero
          1 (let [pred (lvl/succ-pred l)
                  pred' (zonk-level est pred)]
              (if (identical? pred pred') l (lvl/succ pred')))
          2 (let [lhs (zonk-level est (lvl/max-lhs l))
                  rhs (zonk-level est (lvl/max-rhs l))]
              (lvl/level-max lhs rhs))
          3 (let [lhs (zonk-level est (lvl/imax-lhs l))
                  rhs (zonk-level est (lvl/imax-rhs l))]
              (lvl/imax lhs rhs))
          4 (let [n (lvl/param-name l)
                ;; Check if this is one of our level mvars
                  entry (some (fn [[id m]]
                                (when (= (:name m) n) m))
                              @(:level-mctx est))]
              (if (and entry (:solution entry))
                (zonk-level est (:solution entry))
                l))))))

(defn- zonk
  "Substitute all solved metavariables in an expression."
  [est expr]
  (case (e/tag expr)
    :fvar (let [id (e/fvar-id expr)]
            (if-let [sol (mvar-solution est id)]
              (zonk est sol)
              expr))
    :app (let [f (zonk est (e/app-fn expr))
               a (zonk est (e/app-arg expr))]
           (if (and (identical? f (e/app-fn expr))
                    (identical? a (e/app-arg expr)))
             expr
             (e/app f a)))
    :lam (let [ty (zonk est (e/lam-type expr))
               body (zonk est (e/lam-body expr))]
           (if (and (identical? ty (e/lam-type expr))
                    (identical? body (e/lam-body expr)))
             expr
             (e/lam (e/lam-name expr) ty body (e/lam-info expr))))
    :forall (let [ty (zonk est (e/forall-type expr))
                  body (zonk est (e/forall-body expr))]
              (if (and (identical? ty (e/forall-type expr))
                       (identical? body (e/forall-body expr)))
                expr
                (e/forall' (e/forall-name expr) ty body (e/forall-info expr))))
    :let (let [ty (zonk est (e/let-type expr))
               val (zonk est (e/let-value expr))
               body (zonk est (e/let-body expr))]
           (e/let' (e/let-name expr) ty val body))
    :const (let [levels (e/const-levels expr)
                 levels' (mapv #(zonk-level est %) levels)]
             (if (= levels levels')
               expr
               (e/const' (e/const-name expr) levels')))
    :sort (let [l (e/sort-level expr)
                l' (zonk-level est l)]
            (if (identical? l l') expr (e/sort' l')))
    :proj (let [s (zonk est (e/proj-struct expr))]
            (if (identical? s (e/proj-struct expr))
              expr
              (e/proj (e/proj-type-name expr) (e/proj-idx expr) s)))
    ;; Atoms
    expr))

;; ============================================================
;; Level parsing (same as surface.term)
;; ============================================================

(defn- parse-level-token [s]
  (if-let [n (try (Long/parseLong (str s)) (catch NumberFormatException _ nil))]
    (lvl/from-nat n)
    (lvl/param (name/from-string (str s)))))

(defn- parse-levels
  "Parse universe levels from 'Foo.{1,2}'. Returns [base-name levels-or-nil]."
  [sym-str]
  (if-let [idx (clojure.string/index-of sym-str ".{")]
    (let [base (subs sym-str 0 idx)
          lvl-str (subs sym-str (+ idx 2) (dec (count sym-str)))
          parts (clojure.string/split lvl-str #"\s*,\s*")
          levels (mapv parse-level-token parts)]
      [base levels])
    [sym-str nil]))

;; ============================================================
;; Binder parsing (same as surface.term)
;; ============================================================

(defn- parse-binders [binder-vec]
  (let [tokens (remove (fn [t] (or (= (str t) ",") (= (str t) ":") (= (str t) ":-"))) binder-vec)]
    (loop [ts (seq tokens) result []]
      (if (or (nil? ts) (empty? ts))
        result
        (let [nam (first ts)
              typ (second ts)]
          (when (nil? typ)
            (throw (ex-info (str "Binder missing type for: " nam) {:name nam})))
          (recur (nnext ts) (conj result [nam typ])))))))

;; ============================================================
;; First-order unification
;; ============================================================

(defn- unify-levels!
  "Try to unify two levels, solving level metavars."
  [est l1 l2]
  (let [l1 (zonk-level est l1)
        l2 (zonk-level est l2)]
    (or (lvl/level= l1 l2)
        ;; If one side is a level mvar, solve it
        (when (lvl/param? l1)
          (let [n (lvl/param-name l1)
                entry (some (fn [[id m]] (when (= (:name m) n) id))
                            @(:level-mctx est))]
            (when entry
              (solve-level-mvar! est entry l2))))
        (when (lvl/param? l2)
          (let [n (lvl/param-name l2)
                entry (some (fn [[id m]] (when (= (:name m) n) id))
                            @(:level-mctx est))]
            (when entry
              (solve-level-mvar! est entry l1))))
        ;; succ a =?= succ b → a =?= b. Needed for Type-u constants (α : Type ?u =
        ;; Sort (succ ?u)): unifying succ ?u with succ 0 must peel to solve ?u, since
        ;; the param-mvar cases above only fire on a *bare* param level.
        (when (and (lvl/succ? l1) (lvl/succ? l2))
          (unify-levels! est (lvl/succ-pred l1) (lvl/succ-pred l2))))))

(defn- unify!
  "First-order unification of two expressions, solving metavars in est.
   Returns true on success."
  [est a b]
  (let [a (zonk est a)
        b (zonk est b)]
    (or (= a b)
        ;; If one side is an unsolved mvar, solve it
        (and (e/fvar? a) (get @(:mctx est) (e/fvar-id a))
             (not (mvar-solution est (e/fvar-id a)))
             (solve-mvar! est (e/fvar-id a) b))
        (and (e/fvar? b) (get @(:mctx est) (e/fvar-id b))
             (not (mvar-solution est (e/fvar-id b)))
             (solve-mvar! est (e/fvar-id b) a))
        ;; Structural unification
        (and (= (e/tag a) (e/tag b))
             (case (e/tag a)
               :sort (unify-levels! est (e/sort-level a) (e/sort-level b))
               :const (and (= (e/const-name a) (e/const-name b))
                           (let [la (e/const-levels a)
                                 lb (e/const-levels b)]
                             (and (= (count la) (count lb))
                                  (every? true? (map #(unify-levels! est %1 %2) la lb)))))
               :app (and (unify! est (e/app-fn a) (e/app-fn b))
                         (unify! est (e/app-arg a) (e/app-arg b)))
               :forall (and (unify! est (e/forall-type a) (e/forall-type b))
                            (unify! est (e/forall-body a) (e/forall-body b)))
               :lam (and (unify! est (e/lam-type a) (e/lam-type b))
                         (unify! est (e/lam-body a) (e/lam-body b)))
               :fvar (= (e/fvar-id a) (e/fvar-id b))
               :bvar (= (e/bvar-idx a) (e/bvar-idx b))
               (:lit-nat :lit-str) (= a b)
               false)))))

(defn- infer-with-mvars
  "infer-type using a tc context augmented with the current elaboration mvars (as
   locals keyed by their fvar id), so terms still mentioning mvars can be typed.
   The kernel tc otherwise has no knowledge of elaboration mvars; Lean keeps them
   in the metacontext that inferType consults. Falls back to plain infer-type."
  [est expr]
  ;; Zonk first so SOLVED mvars are substituted (otherwise the kernel sees an
  ;; opaque local where a concrete type belongs, e.g. List.cons ?α n with ?α
  ;; solved=Nat → spurious mismatch). Only the remaining UNSOLVED mvars are added
  ;; to the lctx as typed locals.
  (let [expr (zonk est expr)
        tc (reduce (fn [tc [id m]]
                     (if (:solution m)
                       tc
                       (try (update tc :lctx red/lctx-add-local id (str "?m" id) (zonk est (:type m)))
                            (catch Throwable _ tc))))
                   (:tc est) @(:mctx est))]
    (tc/infer-type tc expr)))

;; ============================================================
;; Core elaboration
;; ============================================================

(declare elab-term)

(defn- elab-error! [msg data]
  (throw (ex-info (str "Elaboration error: " msg) (merge {:kind :elab-error} data))))

(defn- resolve-const
  "Resolve a constant name, creating level metavars if levels not provided."
  [est base-name explicit-levels]
  (let [cname (name/from-string base-name)
        ci (env/lookup (:env est) cname)]
    (when-not ci
      (elab-error! (str "Unknown constant: " base-name) {:name base-name}))
    (let [level-params (env/ci-level-params ci)
          levels (if explicit-levels
                   explicit-levels
                   ;; Create fresh level metavars for each param
                   (mapv (fn [_] (fresh-level-mvar! est)) level-params))]
      (when (not= (count levels) (count level-params))
        (elab-error! (str "Wrong number of universe levels for " base-name)
                     {:expected (count level-params) :actual (count levels)}))
      (e/const' cname levels))))

(defn- strip-at-prefix
  "If sym-str starts with @, return [true stripped] else [false sym-str]."
  [sym-str]
  (if (clojure.string/starts-with? sym-str "@")
    [true (subs sym-str 1)]
    [false sym-str]))

(defn- resolve-symbol
  "Resolve a symbol: check scope (bound vars) first, then env constants.
   Returns {:expr Expr :explicit? bool} — explicit? means no implicit insertion."
  [est sym]
  (let [sym-str (str sym)
        [explicit? sym-str] (strip-at-prefix sym-str)]
    ;; Bound variable? (:as-term carries a coercion — e.g. a Subtype-typed parameter
    ;; whose references elaborate as its .val, so refined params are usable directly)
    (if-let [{:keys [fvar-id as-term]} (get (:scope est) sym)]
      {:expr (or as-term (e/fvar fvar-id)) :explicit? false}
      ;; Special shortcuts
      (case sym-str
        "Prop" {:expr (e/sort' lvl/zero) :explicit? false}
        "Type" {:expr (e/sort' (lvl/succ lvl/zero)) :explicit? false}
        ;; Parse levels and resolve
        (let [[base-name explicit-levels] (parse-levels sym-str)]
          (if (and (= base-name "Type") explicit-levels)
            {:expr (e/sort' (lvl/succ (first explicit-levels))) :explicit? false}
            {:expr (resolve-const est base-name explicit-levels)
             :explicit? explicit?}))))))

(defn- insert-implicits
  "Given a function expr and its type, insert metavariables for leading
   implicit/instance-implicit arguments. Returns [expr' type'] where
   type' is the remaining (non-implicit) type."
  [est fn-expr fn-type]
  (let [tc (:tc est)]
    (loop [expr fn-expr
           ty (#'tc/cached-whnf tc fn-type)]
      (if (and (e/forall? ty)
               (let [info (e/forall-info ty)]
                 (or (= info :implicit)
                     (= info :strict-implicit)
                     (= info :inst-implicit))))
        (let [arg-mvar (fresh-mvar! est (e/forall-type ty))
              ;; Mark instance-implicit mvars so they can be solved by instance
              ;; synthesis (not just unification) before the final unsolved-check.
              _ (when (= (e/forall-info ty) :inst-implicit)
                  (swap! (:mctx est) assoc-in [(e/fvar-id arg-mvar) :inst-implicit] true))
              expr' (e/app expr arg-mvar)
              ty' (#'tc/cached-whnf tc (e/instantiate1 (e/forall-body ty) arg-mvar))]
          (recur expr' ty'))
        [expr ty]))))

(defn- type-head-name
  "Whnf the (zonked) type and return its head constant's name as a string (e.g. \"Nat\",
   \"Int\"), or nil if the head isn't a constant. Used for type-directed op selection."
  [est ty]
  (let [tw (#'tc/cached-whnf (:tc est) (zonk est ty))
        [h _] (e/get-app-fn-args tw)]
    (when (e/const? h) (name/->string (e/const-name h)))))

(defn- elab-app
  "Elaborate a function application, inserting implicit arguments."
  [est head-sexpr arg-sexprs]
  (let [;; Resolve head, checking for @-prefix
        {:keys [expr explicit?]}
        (if (symbol? head-sexpr)
          (resolve-symbol est head-sexpr)
          {:expr (elab-term est head-sexpr) :explicit? false})
        head-expr expr
        tc (:tc est)
        head-type (infer-with-mvars est head-expr)
        ;; Positional convention (matches sexp->ansatz / the prior a/defn bodies): when
        ;; the user supplies exactly the full binder count (implicits INCLUDED, e.g.
        ;; (List.cons Nat x xs) or (TRBTree.node Nat color l v r)), apply positionally —
        ;; i.e. treat like @-explicit (no implicit insertion). Fewer args ⇒ implicits are
        ;; inferred as usual (e.g. (List.cons x xs), (Eq n n)).
        total-binders (loop [t head-type c 0]
                        (if (e/forall? t) (recur (e/forall-body t) (inc c)) c))
        explicit? (or explicit?
                      (and (e/const? head-expr) (pos? (count arg-sexprs))
                           (= (count arg-sexprs) total-binders)))
        ;; Insert leading implicits (unless @-explicit or positional)
        [head-expr head-type] (if explicit?
                                [head-expr head-type]
                                (insert-implicits est head-expr head-type))]
    ;; Apply explicit arguments one at a time
    (loop [expr head-expr
           ty head-type
           args (seq arg-sexprs)]
      (if-not args
        ;; After all args applied, insert trailing implicits
        (if explicit?
          expr
          (first (insert-implicits est expr ty)))
        (let [;; Insert implicit arguments before each explicit arg (unless @-explicit)
              [expr ty] (if explicit?
                          [expr ty]
                          (insert-implicits est expr ty))]
          (if (e/forall? ty)
            (let [arg-expr (elab-term est (first args))
                  ;; Unify arg type with expected domain
                  arg-type (infer-with-mvars est arg-expr)
                  dom-type (e/forall-type ty)]
              (unify! est arg-type dom-type)
              (let [expr' (e/app expr arg-expr)
                    body-inst (e/instantiate1 (e/forall-body ty) arg-expr)
                    ty' (#'tc/cached-whnf tc body-inst)]
                (recur expr' ty' (next args))))
            (elab-error! "Too many arguments"
                         {:fn head-sexpr :remaining-args (vec args)
                          :type ty})))))))

(defn- elab-forall
  "Elaborate a forall expression with binders."
  [est binder-vec body-sexpr]
  (let [binders (parse-binders binder-vec)]
    (letfn [(build [binders est]
              (if (empty? binders)
                (elab-term est body-sexpr)
                (let [[nam typ-sexpr] (first binders)
                      ;; Zonk the binder type so its solved level-mvars (`?u`) are substituted before
                      ;; it is stored into :scope / the tc :lctx. Lean instantiates mvars in binder
                      ;; types; without this the stored type keeps raw `?u`, and a later EAGER kernel
                      ;; infer of a sub-term in ARGUMENT position (elab-app) trips on the opaque `?u`
                      ;; ("Type mismatch in application") — the body position survives only because it
                      ;; reaches the final whole-term zonk. See [[elab-binder-zonk-bug]].
                      typ-expr (zonk est (elab-term est typ-sexpr))
                      fvar-id (fresh-id! est)
                      fv (e/fvar fvar-id)
                      est' (-> est
                               (assoc-in [:scope nam] {:fvar-id fvar-id :type typ-expr})
                               (update :tc update :lctx red/lctx-add-local fvar-id (str nam) typ-expr))
                      body-expr (build (rest binders) est')
                      abs-body (e/abstract1 body-expr fvar-id)]
                  (e/forall' (str nam) typ-expr abs-body :default))))]
      (build binders est))))

(defn- subtype-as-term
  "If `typ-expr` is a `Subtype B P`, the coercion term `Subtype.val B P fv` (the binder read through its
   carrier) — else nil. Used to auto-coerce a refined binder's references to the underlying value, the
   way a refined a/defn param already is (ansatz.core), so a predicate like `(<= 5 x)` / `(count s)` over
   a `Subtype`-refined element reads naturally. Lean-faithful: this is the `Subtype` → base coercion."
  [typ-expr fv]
  (let [[h args] (e/get-app-fn-args typ-expr)]
    (when (and (e/const? h) (= "Subtype" (name/->string (e/const-name h))) (= 2 (count args)))
      (e/app* (e/const' (name/from-string "Subtype.val") (vec (e/const-levels h)))
              (first args) (second args) fv))))

(defn- elab-lam
  "Elaborate a lambda expression with binders. When `(:coerce-refined-binders est)` is set (the data-
   pipeline SOAC context — wandler.surface.collections/compile-fn turns it on), a `Subtype`-typed binder
   gets an `:as-term` so its references auto-coerce to the carrier value; default off, so proofs and
   ordinary lambdas are unaffected."
  [est binder-vec body-sexpr]
  (let [binders (parse-binders binder-vec)
        coerce? (:coerce-refined-binders est)]
    (letfn [(build [binders est]
              (if (empty? binders)
                (elab-term est body-sexpr)
                (let [[nam typ-sexpr] (first binders)
                      ;; Zonk the binder type so its solved level-mvars (`?u`) are substituted before
                      ;; it is stored into :scope / the tc :lctx. Lean instantiates mvars in binder
                      ;; types; without this the stored type keeps raw `?u`, and a later EAGER kernel
                      ;; infer of a sub-term in ARGUMENT position (elab-app) trips on the opaque `?u`
                      ;; ("Type mismatch in application") — the body position survives only because it
                      ;; reaches the final whole-term zonk. See [[elab-binder-zonk-bug]].
                      typ-expr (zonk est (elab-term est typ-sexpr))
                      fvar-id (fresh-id! est)
                      fv (e/fvar fvar-id)
                      as-term (when coerce? (subtype-as-term typ-expr fv))
                      est' (-> est
                               (assoc-in [:scope nam] (cond-> {:fvar-id fvar-id :type typ-expr}
                                                        as-term (assoc :as-term as-term)))
                               (update :tc update :lctx red/lctx-add-local fvar-id (str nam) typ-expr))
                      body-expr (build (rest binders) est')
                      abs-body (e/abstract1 body-expr fvar-id)]
                  (e/lam (str nam) typ-expr abs-body :default))))]
      (build binders est))))

(defn- elab-let
  "Elaborate a let expression."
  [est binder-vec body-sexpr]
  (let [tokens (remove (fn [t] (or (= (str t) ":") (= (str t) "="))) binder-vec)
        tokens-vec (vec tokens)]
    (when (not= 3 (count tokens-vec))
      (elab-error! "let binder expects [name type value]" {:binder binder-vec}))
    (let [nam (nth tokens-vec 0)
          typ-sexpr (nth tokens-vec 1)
          val-sexpr (nth tokens-vec 2)
          typ-expr (elab-term est typ-sexpr)
          val-expr (elab-term est val-sexpr)
          fvar-id (fresh-id! est)
          est' (-> est
                   (assoc-in [:scope nam] {:fvar-id fvar-id :type typ-expr})
                   (update :tc update :lctx red/lctx-add-let fvar-id (str nam) typ-expr val-expr))
          body-expr (elab-term est' body-sexpr)
          abs-body (e/abstract1 body-expr fvar-id)]
      (e/let' (str nam) typ-expr val-expr abs-body))))

(defn sizeof-inst
  "Synthesize a SizeOf instance term for supported types: Nat, List of sized, and custom
   inductives with a derived `<T>._sizeOf_inst` (wf-derive-sizeof! in ansatz.core)."
  [env ty]
  (let [[h as] (e/get-app-fn-args ty)]
    (cond
      (and (e/const? h) (= "Nat" (name/->string (e/const-name h))) (empty? as))
      (e/const' (name/from-string "instSizeOfNat") [])
      (and (e/const? h) (= "List" (name/->string (e/const-name h))) (= 1 (count as)))
      (when-let [elt (sizeof-inst env (first as))]
        (e/app* (e/const' (name/from-string "List._sizeOf_inst") (vec (e/const-levels h)))
                (first as) elt))
      (and (e/const? h) (empty? as)
           (env/lookup env (name/mk-str (e/const-name h) "_sizeOf_inst")))
      (e/const' (name/mk-str (e/const-name h) "_sizeOf_inst") [])
      :else nil)))

(defn- recur-form? [x]
  (and (seq? x) (symbol? (first x)) (= "recur" (name (first x)))))

(defn- elab-loop
  "Compile the common counting-loop shape
     (loop [i init, a0 i0, …] (if (== i 0) BASE (recur (dec i) s0 …)))
   to Nat.rec on the decreasing counter i, into the accumulator function space:
     ((Nat.rec (λ_:Nat. T0→…→R) (λ a0…. BASE) (λ k ih a0…. ih s0[i:=k+1] …) init) i0 …)
   The counter must be the first binding, recur's first arg (dec counter), and the test
   (== counter 0). Other loop shapes throw (→ use ^:partial for general loops)."
  [est binder-vec body]
  (let [pairs (vec (partition 2 binder-vec))
        bad (fn [msg] (elab-error!
                       (str "loop: " msg " — only the counting shape "
                            "(loop [i n …] (if (== i 0) base (recur (dec i) …))) is auto-compiled; "
                            "use ^:partial for general loops") {:body body}))
        _ (when (empty? pairs) (bad "needs a counter binding"))
        [ivar iinit] (first pairs)
        accs (vec (rest pairs))
        _ (when-not (and (seq? body) (symbol? (first body)) (= "if" (name (first body)))
                         (= 4 (count body))) (bad "body must be an if"))
        [_ test br-a br-b] body
        recur-br (cond (recur-form? br-b) br-b (recur-form? br-a) br-a :else (bad "no (recur …) branch"))
        base-br (if (identical? recur-br br-b) br-a br-b)
        rargs (vec (rest recur-br))
        dec-arg (first rargs)
        _ (when-not (and (seq? dec-arg) (symbol? (first dec-arg)) (= "dec" (name (first dec-arg)))
                         (= ivar (second dec-arg))) (bad "first recur arg must be (dec counter)"))
        _ (when-not (= (count rargs) (inc (count accs))) (bad "recur arity must match the bindings"))
        _ (when-not (and (seq? test) (symbol? (first test)) (= "==" (name (first test)))
                         (let [a (second test) b (nth test 2)]
                           (or (and (= a ivar) (= b 0)) (and (= a 0) (= b ivar)))))
            (bad "test must be (== counter 0)"))
        steps (vec (rest rargs))
        nat (e/const' (name/from-string "Nat") [])
        succ-of (fn [k] (e/app (e/const' (name/from-string "Nat.succ") []) k))
        iinit* (elab-term est iinit)
        acc-inits* (mapv (fn [[_ ini]] (elab-term est ini)) accs)
        acc-types (mapv (fn [a*] (zonk est (infer-with-mvars est a*))) acc-inits*)
        bind-accs (fn [est0]                          ; → [est' acc-fids]
                    (reduce (fn [[e ids] [[av _] at]]
                              (let [fid (fresh-id! e)]
                                [(-> e (assoc-in [:scope av] {:fvar-id fid :type at})
                                     (update :tc update :lctx red/lctx-add-local fid (str av) at))
                                 (conj ids fid)]))
                            [est0 []] (map vector accs acc-types)))
        wrap-acc-lams (fn [body0]                      ; λ a0 … . body0 (accs already abstracted)
                        (reduce (fn [b i] (e/lam (str (first (nth accs i))) (nth acc-types i) b :default))
                                body0 (reverse (range (count accs)))))
        ;; base : T0→…→R
        [est-b acc-fids-b] (bind-accs est)
        base* (elab-term est-b base-br)
        ret-type (zonk est-b (infer-with-mvars est-b base*))
        base-fn (wrap-acc-lams (e/abstract-many base* acc-fids-b))
        ;; arrow type + motive + universe
        arrow-type (reduce (fn [acc t] (e/forall' "_" t acc :default)) ret-type (reverse acc-types))
        u (let [s (zonk est (infer-with-mvars est arrow-type))]
            (if (e/sort? s) (e/sort-level s) (lvl/succ lvl/zero)))
        motive (e/lam "_" nat arrow-type :default)
        ;; step : λ k ih a0 … . ih s0[i:=succ k] …
        k-fid (fresh-id! est)
        ih-fid (fresh-id! est)
        i-fid (fresh-id! est)
        est-s0 (-> est (assoc-in [:scope ivar] {:fvar-id i-fid :type nat})
                   (update :tc update :lctx red/lctx-add-local i-fid (str ivar) nat))
        [est-s acc-fids-s] (bind-accs est-s0)
        succ-k (succ-of (e/fvar k-fid))
        steps* (mapv (fn [s] (let [s* (elab-term est-s s)]
                               (e/instantiate1 (e/abstract1 s* i-fid) succ-k)))
                     steps)
        step-body (reduce e/app (e/fvar ih-fid) steps*)
        step-abs (e/abstract-many step-body (into [k-fid ih-fid] acc-fids-s))
        step-fn (e/lam (str ivar) nat
                       (e/lam "ih" arrow-type (wrap-acc-lams step-abs) :default) :default)
        nat-rec (e/const' (name/from-string "Nat.rec") [u])]
    (reduce e/app (e/app* nat-rec motive base-fn step-fn iinit*) acc-inits*)))

(def ^:dynamic *bypass-registries-once*
  "When true, the NEXT elab-term seq dispatch skips the user registries (term + macro)
   and falls through to the built-in forms — then resets. The delegation primitive for
   extension authors (api/elab-base): a registered elaborator wrapping a built-in verb
   hands the non-special case back without re-entering itself."
  false)

(defn- elab-term
  "Recursively elaborate an s-expression into a Ansatz Expr."
  [est sexpr]
  (cond
    ;; an already-elaborated kernel Expr passes through — term elaborators (elab_rules)
    ;; splice Exprs into surface forms they hand back to elab (quotation with term holes)
    (instance? ansatz.kernel.Expr sexpr) sexpr
    (integer? sexpr) (e/lit-nat sexpr)
    ;; FLOAT literal: a Clojure double → OfScientific.ofScientific Float inst m s e
    ;; (m × 10^±e; BigDecimal's shortest round-trip repr). Float is the computable
    ;; carrier (native double); Real is for proofs, so a bare double means Float.
    (double? sexpr)
    (let [neg? (neg? sexpr)
          bd (java.math.BigDecimal. (Double/toString (Math/abs (double sexpr))))
          scale (.scale bd)
          mant (.unscaledValue bd)
          [sign expn] (if (>= scale 0) [true scale] [false (- scale)])
          FloatT (e/const' (name/from-string "Float") [])
          lit (e/app* (e/const' (name/from-string "OfScientific.ofScientific") [lvl/zero])
                      FloatT (e/const' (name/from-string "instOfScientificFloat") [])
                      (e/lit-nat mant)
                      (e/const' (name/from-string (if sign "Bool.true" "Bool.false")) [])
                      (e/lit-nat expn))]
      (if neg?
        (elab-error! "negative Float literals not yet supported (wrap as (sub Float 0.0 x))"
                     {:form sexpr})
        lit))
    (string? sexpr)  (e/lit-str sexpr)
    (boolean? sexpr) (e/const' (name/from-string (if sexpr "Bool.true" "Bool.false")) [])
    (nil? sexpr)     (elab-term est (symbol "List.nil"))  ;; bare nil = empty List

    (symbol? sexpr)
    ;; A bare symbol in term position: insert its implicit/instance arguments
    ;; (as Lean does for any term, not only application heads) so e.g. List.nil
    ;; becomes List.nil.{?u} ?α rather than the under-applied bare constant.
    (let [{:keys [expr explicit?]} (resolve-symbol est sexpr)]
      (if explicit?
        expr
        (first (insert-implicits est expr (infer-with-mvars est expr)))))

    (seq? sexpr)
    (let [head (first sexpr)
          bypass? *bypass-registries-once*
          _ (when bypass? (set! *bypass-registries-once* false))]
      ;; user-registered surface forms. Term elaborators first (lean4 elab_rules-shaped:
      ;; syntax → kernel Expr with elaborator access, for type-directed forms), then
      ;; macro elaborators (lean4 macro_rules-shaped: syntax → syntax, which re-elaborates) —
      ;; both compose with every surface feature. LEXICAL SCOPING: a LOCAL BINDER shadows the global
      ;; vocabulary — `(get (:scope est) head)` is checked first, so e.g. a binder named `dec`
      ;; (a DecidableEq instance) applied as `(dec a b)` resolves to the binder, NOT the registered
      ;; `dec` (clojure decrement) from the wandler collections vocabulary. (Before this, loading any
      ;; namespace that registered `dec`/`map`/`min`/… globally silently shadowed same-named binders.)
      (if-let [telab (and (symbol? head) (not bypass?)
                          (not (contains? (:scope est) head))
                          (get @ingest/term-elaborator-registry head))]
        (telab est (vec (rest sexpr)))
        (if-let [expander (and (symbol? head) (not bypass?)
                               (not (contains? (:scope est) head))
                               (get @ingest/elaborator-registry head))]
          (elab-term est (expander (rest sexpr)))
          (case (when (symbol? head) (str head))
            "forall" (let [[_ binder-vec & body-forms] sexpr]
                       (when (not= 1 (count body-forms))
                         (elab-error! "forall expects one body" {:forms body-forms}))
                       (elab-forall est binder-vec (first body-forms)))

            "lam"    (let [[_ binder-vec & body-forms] sexpr]
                       (when (not= 1 (count body-forms))
                         (elab-error! "lam expects one body" {:forms body-forms}))
                       (elab-lam est binder-vec (first body-forms)))

            ;; Non-dependent function type. `arrow` plus the idiomatic `=>` (THE function-type arrow
            ;; per clj-ingest; `->` is ALWAYS Clojure threading, never the arrow) and `→`, with N-ary
            ;; currying: (=> A B C) = A → B → C (right-associated). Each part elaborates in the same
            ;; scope (fvar-based — no de-Bruijn depth shift); `e/arrow` wraps `_ : A`. This brings the
            ;; a/theorem fvar elaborator in line with a/defn, which already accepts `=>` binders.
            ("arrow" "=>" "→")
            (let [parts (rest sexpr)]
              (when (< (count parts) 2)
                (elab-error! "arrow / => expects at least two types" {:form sexpr}))
              (let [exprs (mapv #(elab-term est %) parts)]
                (reduce (fn [b a] (e/arrow a b)) (last exprs) (reverse (butlast exprs)))))

            "Sort"   (let [[_ level-form] sexpr
                           level (cond
                                   (integer? level-form) (lvl/from-nat level-form)
                                   (= 'zero level-form) lvl/zero
                                   :else (elab-error! (str "Unsupported Sort level: " level-form)
                                                      {:level level-form}))]
                       (e/sort' level))

            "let"    (let [[_ binder-vec & body-forms] sexpr
                           toks (remove #(contains? #{":" ":-" "=" ","} (str %)) binder-vec)]
                   ;; ansatz typed surface let is a single [name type value] (3 tokens);
                   ;; Clojure's let (name/value pairs) is a macro → expand to let*.
                       (if (and (= 3 (count toks)) (= 1 (count body-forms)))
                         (elab-let est binder-vec (first body-forms))
                         (elab-term est (macroexpand-1 sexpr))))

            "app"    (let [[_ f a] sexpr]
                       (e/app (elab-term est f) (elab-term est a)))

        ;; Two surface forms funnel to the one inferring compiler (compile-match):
        ;;  - inferring (proofs):    (match discr [pat rhs] …)            — vector alts
        ;;  - explicit (a/defn):     (match scrut type ret (ctor [fields] body) …)
        ;; The explicit form is desugared (drop type+ret, which are a bvar-era workaround
        ;; and dead code respectively; ctor qualification is done inside compile-match).
            "match"  (let [args (vec (rest sexpr))
                           est* (assoc est :infer-fn infer-with-mvars :unify-fn unify! :zonk-fn zonk)]
                       (if (vector? (get args 1))
                         (match/compile-match est* elab-term (first args) (mapv vec (rest args)))
                     ;; explicit form: (match scrut type ret (ctor [fields] body) …). Keep the
                     ;; declared ret-type as the motive — it's the type-directed hint that lets
                     ;; under-determined branches (e.g. a bare `nil`) resolve their element type.
                         (let [scrut (first args)
                               declared-ret (try (elab-term est (nth args 2)) (catch Throwable _ nil))
                               alts (mapv (fn [c]
                                            (let [ctor (first c)
                                                  has-fields (and (> (count c) 2) (vector? (second c)))
                                                  fields (if has-fields (second c) [])
                                                  body (if has-fields (nth c 2) (second c))]
                                              [(if (seq fields) (cons ctor (seq fields)) ctor) body]))
                                          (drop 3 args))]
                           (match/compile-match (cond-> est* declared-ret
                                                        (assoc :declared-ret-type declared-ret))
                                                elab-term scrut alts))))

        ;; (=> A B) is handled by the unified arrow clause above (with currying + the → glyph).

        ;; Bool if-then-else → Bool.rec. The motive is the then-branch's type,
        ;; inferred directly (fvar context is present — no open/close needed).
        ;; if over a recognizable comparison lifts to its Prop + Decidable instance and emits
        ;; dite — the shape lean4's @[macro_inline] ite/dite reduce to (Decidable.casesOn),
        ;; whose branch binders CARRY the guard. Downstream this is what gives well-founded
        ;; decrease proofs their hypotheses with no special-casing. A non-comparison Bool
        ;; condition (variable, Bool-valued call) stays on Bool.rec.
            "if" (let [[_ c t e] sexpr
                       cmp (when (and (seq? c) (symbol? (first c)) (= 3 (count c)))
                             (case (str (first c))
                               "==" ["Eq" "Nat.decEq" false]
                               "<"  ["lt" "Nat.decLt" false]
                               ">"  ["lt" "Nat.decLt" true]
                               ("<=" "≤") ["le" "Nat.decLe" false]
                               (">=" "≥") ["le" "Nat.decLe" true]
                               nil))]
                   (if cmp
                     (let [[prop-head dec-name swap?] cmp
                           [a b] (if swap? [(nth c 2) (nth c 1)] [(nth c 1) (nth c 2)])
                           a* (elab-term est a)
                           b* (elab-term est b)
                           ;; Build the Prop with the CONCRETE canonical Nat instance
                           ;; (instLTNat/instLENat), not via (lt Nat a b) — that path
                           ;; leaves an instance MVAR which the paired Nat.decLt/decLe
                           ;; (whose type mentions the canonical instance) cannot match
                           ;; under a strict mid-elaboration infer (e.g. as an argument
                           ;; of List.map, before the synthesis pass runs).
                           prop (case prop-head
                                  "Eq" (elab-term est (list 'Eq 'Nat a b))
                                  "lt" (e/app* (e/const' (name/from-string "LT.lt") [lvl/zero])
                                               (e/const' (name/from-string "Nat") [])
                                               (e/const' (name/from-string "instLTNat") []) a* b*)
                                  "le" (e/app* (e/const' (name/from-string "LE.le") [lvl/zero])
                                               (e/const' (name/from-string "Nat") [])
                                               (e/const' (name/from-string "instLENat") []) a* b*))
                           inst (e/app* (e/const' (name/from-string dec-name) []) a* b*)
                           then-expr (elab-term est t)
                           else-expr (elab-term est e)
                           ret-type (tc/infer-type (:tc est) (zonk est then-expr))
                           ret-sort (tc/infer-type (:tc est) ret-type)
                           u (if (e/sort? ret-sort) (e/sort-level ret-sort) (lvl/succ lvl/zero))
                           not-prop (e/app (e/const' (name/from-string "Not") []) prop)]
                       (e/app* (e/const' (name/from-string "dite") [u])
                               ret-type prop inst
                               (e/lam "h" prop (e/lift then-expr 1 0) :default)
                               (e/lam "h" not-prop (e/lift else-expr 1 0) :default)))
                     (let [cond-expr (elab-term est c)
                           then-expr (elab-term est t)
                           else-expr (elab-term est e)
                           ret-type (tc/infer-type (:tc est) (zonk est then-expr))]
                       (e/app* (e/const' (name/from-string "Bool.rec") [(lvl/succ lvl/zero)])
                               (e/lam "_" (e/const' (name/from-string "Bool") []) ret-type :default)
                               else-expr then-expr cond-expr))))

        ;; Prop-valued comparisons over an explicit type: (le T a b) / (lt T a b)
        ;; → LE.le.{?u} T ?inst a b — the instance + level resolve via synthesis.
            ("le" "lt") (let [[_ T a b] sexpr
                              cn  (if (= (str head) "le") "LE.le" "LT.lt")
                              icn (if (= (str head) "le") "LE" "LT")
                              T'  (elab-term est T)
                              a'  (elab-term est a)
                              b'  (elab-term est b)
                          ;; EAGER level: a mid-elaboration infer (e.g. as the argument of Not)
                          ;; cannot apply a const carrying an unsolved level-mvar. T's sort is
                          ;; concrete in practice (Nat/Int/custom : Sort 1 → u = 0); fall back
                          ;; to a level mvar only when it isn't.
                              Ts  (try (zonk est (infer-with-mvars est T')) (catch Exception _ nil))
                              u   (if (and Ts (e/sort? Ts) (lvl/succ? (e/sort-level Ts)))
                                    (lvl/succ-pred (e/sort-level Ts))
                                    (fresh-level-mvar! est))
                              inst (fresh-mvar! est (e/app (e/const' (name/from-string icn) [u]) T'))
                              _ (swap! (:mctx est) assoc-in [(e/fvar-id inst) :inst-implicit] true)]
                          (e/app* (e/const' (name/from-string cn) [u]) T' inst a' b'))

        ;; (= T a b) → Eq T a b (the theorem-statement equality form)
            "="
            (if (= 4 (count sexpr))
              (elab-term est (list 'Eq (nth sexpr 1) (nth sexpr 2) (nth sexpr 3)))
              (elab-error! "= expects (= Type lhs rhs)" {:form sexpr}))

        ;; Surface comparison glyphs: 3-arg → Prop (le/lt), 2-arg → Bool (Nat.b*).
            ("<" "==" "<=" ">" ">=" "≤" "≥")
            (let [hs (str head)]
              (if (= 4 (count sexpr))
                (let [[_ T a b] sexpr]
                  (if (= hs "==")
                    (elab-term est (list 'Eq T a b))     ; (== T a b) → Eq T a b (Prop)
                    (let [[a* b*] (case hs (">" ">=" "≥") [b a] [a b])
                          rel (case hs ("<" ">") "lt" "le")]
                      (elab-term est (list (symbol rel) T a* b*)))))
                ;; 2-arg Bool comparison, TYPE-DIRECTED on the operands (a non-literal
                ;; operand's type head picks the ops; literals coerce to that type):
                ;; Nat → Nat.b* · Int/Float → Decidable.decide over the order Props ·
                ;; String → decide over String.decEq (== only).
                (let [[rel a-form b-form] (case hs
                                            "<"  [:lt (nth sexpr 1) (nth sexpr 2)]
                                            "==" [:eq (nth sexpr 1) (nth sexpr 2)]
                                            ("<=" "≤") [:le (nth sexpr 1) (nth sexpr 2)]
                                            (">") [:lt (nth sexpr 2) (nth sexpr 1)]
                                            (">=" "≥") [:le (nth sexpr 2) (nth sexpr 1)])
                      a0 (elab-term est a-form)
                      b0 (elab-term est b-form)
                      tn (or (some (fn [x]
                                     (when-not (e/lit-nat? x)
                                       (let [t (zonk est (infer-with-mvars est x))
                                             [th _] (when t (e/get-app-fn-args t))]
                                         (when (and th (e/const? th))
                                           (name/->string (e/const-name th))))))
                                   [a0 b0])
                             "Nat")
                      coerce (fn [x] (if (e/lit-nat? x)
                                       (case tn
                                         "Int"   (e/app (e/const' (name/from-string "Int.ofNat") []) x)
                                         "Float" (e/app (e/const' (name/from-string "Float.ofNat") []) x)
                                         x)
                                       x))
                      a (coerce a0) b (coerce b0)
                      Tc (e/const' (name/from-string tn) [])
                      bool-op (fn [op] (e/app* (e/const' (name/from-string op) []) a b))
                      decide (fn [propc decc]
                               (e/app* (e/const' (name/from-string "Decidable.decide") [])
                                       (e/app* (e/const' (name/from-string propc) []) a b)
                                       (e/app* (e/const' (name/from-string decc) []) a b)))
                      decide-eq (fn []
                                  (e/app* (e/const' (name/from-string "Decidable.decide") [])
                                          (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) Tc a b)
                                          (e/app* (e/const' (name/from-string (str tn ".decEq")) []) a b)))]
                  (if-let [cmp-handler (get @ingest/comparison-registry tn)]
                    ;; type-directed comparison for a registered custom type (e.g. dynamic-EDN
                    ;; Value); pass the PRE-coercion operands — the handler owns unwrapping.
                    (cmp-handler est rel a0 b0)
                    (case tn
                      "Int"   (case rel :lt (decide "Int.lt" "Int.decLt") :le (decide "Int.le" "Int.decLe") :eq (decide-eq))
                      "Float" (case rel :lt (decide "Float.lt" "Float.decLt") :le (decide "Float.le" "Float.decLe") :eq (bool-op "Float.beq"))
                      "String" (case rel :eq (decide-eq)
                                     (elab-error! "String comparison: only == is supported" {:rel rel}))
                      (bool-op (case rel :lt "Nat.blt" :le "Nat.ble" :eq "Nat.beq")))))))

        ;; Dependent if over a Prop condition → dite. The Decidable instance is an
        ;; inst-implicit mvar solved by synthesis (no comparison fallback needed); the
        ;; branch binders (proof of cond / ¬cond) are fvars abstracted back to lambdas.
            "dif" (let [[_ cond-form then-clause else-clause] sexpr
                        [tv tbody] then-clause
                        [ev ebody] else-clause
                        cond-expr (elab-term est cond-form)
                        dec-ty (e/app (e/const' (name/from-string "Decidable") []) cond-expr)
                        inst (fresh-mvar! est dec-ty)
                        _ (swap! (:mctx est) assoc-in [(e/fvar-id inst) :inst-implicit] true)
                        mk-branch (fn [bv bty body]
                                    (let [fid (fresh-id! est)
                                          est' (-> est
                                                   (assoc-in [:scope bv] {:fvar-id fid :type bty})
                                                   (update :tc update :lctx red/lctx-add-local fid (str bv) bty))
                                          be (elab-term est' body)]
                                      [(e/lam (str bv) bty (e/abstract1 be fid) :default)
                                       (tc/infer-type (:tc est') (zonk est be))]))
                        [then-fn ret-type] (mk-branch tv cond-expr tbody)
                        not-cond (e/app (e/const' (name/from-string "Not") []) cond-expr)
                        [else-fn _] (mk-branch ev not-cond ebody)
                        ret-sort (tc/infer-type (:tc est) (zonk est ret-type))
                        u (if (e/sort? ret-sort) (e/sort-level ret-sort) (lvl/succ lvl/zero))]
                    (e/app* (e/const' (name/from-string "dite") [u])
                            ret-type cond-expr inst then-fn else-fn))

        ;; Type-directed arithmetic: infer the first operand's type head and pick the matching
        ;; kernel op from the core-lift table (Nat.add / Int.add / …), defaulting to Nat when
        ;; the head isn't listed. Picking the concrete op avoids HAdd's output-param synthesis.
            ("+" "-" "*")
            (let [op (str head)]
              (if (>= (count sexpr) 3)
                (let [a*    (elab-term est (nth sexpr 1))
                      tn    (type-head-name est (infer-with-mvars est a*))
                      const (or (get-in ingest/arith-lift [op tn])
                                (get-in ingest/arith-lift [op "Nat"]))]
                  (elab-app est (symbol const) (rest sexpr)))
                (elab-app est (symbol (get-in ingest/arith-lift [op "Nat"])) (rest sexpr))))

        ;; do → value of the last form (pure setting: earlier forms have no effect).
            "do" (elab-term est (last sexpr))

        ;; (sizeOf x) → SizeOf.sizeOf T inst x — the WF measure for data-typed params.
        ;; The argument's type is INFERRED (fvar scope carries it); the instance is
        ;; synthesized structurally (Nat, List of sized, derived custom instances).
            "sizeOf"
            (let [x* (elab-term est (nth sexpr 1))
                  ty (zonk est (infer-with-mvars est x*))
                  inst (sizeof-inst (:env est) ty)]
              (when-not inst
                (elab-error! (str "sizeOf: no SizeOf instance for type " (e/->string ty)) {:form sexpr}))
              (e/app* (e/const' (name/from-string "SizeOf.sizeOf") [(lvl/succ lvl/zero)]) ty inst x*))

        ;; Clojure loop/recur — the common counting-loop shape compiles to Nat.rec (see elab-loop).
            "loop" (elab-loop est (second sexpr) (last sexpr))

        ;; Clojure fn* (single arity) → lambda. parse-params reads the binders' metadata
        ;; types (^Nat / ^{:- T}); flatten to a [name type …] vec and reuse elab-lam.
            ;; "fn" handled natively (NOT clojure-macroexpanded): typed binders
            ;; ([x :- T] / [x T] / metadata) violate clojure.core/fn's spec
            ("fn" "fn*") (let [cls (rest sexpr)
                               cls (if (symbol? (first cls)) (rest cls) cls)  ; skip optional self-name
                               arities (if (vector? (first cls))
                                         [cls]   ; unwrapped surface (fn [params] body)
                                         (filter #(and (sequential? %) (vector? (first %))) cls))]
                           (when (not= 1 (count arities))
                             (elab-error! "fn: only single-arity lambdas elaborate to kernel terms" {:form sexpr}))
                           (let [[params & body] (first arities)
                                 body-form (if (> (count body) 1) (cons 'do body) (first body))
                                 pairs (ingest/parse-params params)
                                 binder-vec (vec (mapcat (fn [p] [(first p) (second p)]) pairs))]
                             (elab-lam est binder-vec body-form)))

        ;; cond is NOT macroexpanded (Clojure's :else isn't Bool); desugar natively to
        ;; nested if, with :else/:default/true as the catch-all.
            "cond" (letfn [(build [cs]
                             (if (empty? cs)
                               (elab-error! "cond: no clause matched and no :else" {:form sexpr})
                               (let [[t e & more] cs]
                                 (if (contains? #{:else :default true} t)
                                   (elab-term est e)
                                   (e/app* (e/const' (name/from-string "Bool.rec") [(lvl/succ lvl/zero)])
                                           (e/lam "_" (e/const' (name/from-string "Bool") [])
                                                  (tc/infer-type (:tc est) (zonk est (elab-term est e))) :default)
                                           (build more) (elab-term est e) (elab-term est t))))))]
                     (build (rest sexpr)))

        ;; `bif` — Lean's boolean-`if` notation, the escape to the `cond` CONSTANT
        ;; (cond.{u} {α : Type u} (c : Bool) (a b : α) : α). The surface `cond` is overloaded as
        ;; Clojure-style clause-cond (above), so a lemma statement that needs the literal `cond`
        ;; head — e.g. to state `lookup_insert : … = cond (k==k') (some v) (lookup k l)` so that
        ;; `cond_true`/`cond_false` fire by name — spells it `(bif c a b)`. α + the level are
        ;; inferred from `a` (mirrors Lean's `bif` elaborating the implicit motive).
            "bif" (let [[_ c-form a-form b-form] sexpr
                        c (elab-term est c-form)
                        a (elab-term est a-form)
                        b (elab-term est b-form)
                        ;; cond.{u} : {α : Sort u} → Bool → α → α → α. α (implicit, but passed
                        ;; positionally here) = type of `a`; the level param u = the level of α's
                        ;; OWN type (type-of(Option Nat) = Sort 1 ⟹ u = 1), i.e. sort-level of α's type.
                        α (tc/infer-type (:tc est) (zonk est a))
                        αsort (#'tc/cached-whnf (:tc est) (tc/infer-type (:tc est) (zonk est α)))
                        u (if (e/sort? αsort) (e/sort-level αsort) lvl/zero)]
                    (e/app* (e/const' (name/from-string "cond") [u]) α c a b))

        ;; Clojure let* : [name val name val …] with inferred types → nested let.
            "let*" (let [[_ bindings & body] sexpr]
                     (letfn [(build [ps est]
                               (if (empty? ps)
                                 (elab-term est (if (= 1 (count body)) (first body) (cons 'do body)))
                                 (let [[nm vform] (first ps)
                                       vexpr (elab-term est vform)
                                       vtype (tc/infer-type (:tc est) (zonk est vexpr))
                                       fid (fresh-id! est)
                                       est' (-> est
                                                (assoc-in [:scope nm] {:fvar-id fid :type vtype})
                                                (update :tc update :lctx
                                                        red/lctx-add-let fid (str nm) vtype vexpr))
                                       body-expr (build (rest ps) est')]
                                   (e/let' (str nm) vtype vexpr (e/abstract1 body-expr fid)))))]
                       (build (partition 2 bindings) est)))

        ;; Default: keyword projection / get / cons sugar, then macroexpand any
        ;; clojure macro (cond/->/and/or/…), otherwise application.
            (cond
          ;; (:malli/schema <form>) — a schema marker from the gradual-typing surface
          ;; (ansatz.malli signature-for): translate to the kernel type. requiring-resolve
          ;; is the optionality seam; the marker only ever appears when malli produced it.
              (= :malli/schema head)
              ((requiring-resolve 'ansatz.malli/schema->type-expr) (second sexpr))
          ;; (:field struct) → structure projection
              (keyword? head)
              (let [field-name (name head)
                    struct-expr (elab-term est (second sexpr))
                    struct-type (#'tc/cached-whnf (:tc est) (infer-with-mvars est struct-expr))
                    [th _] (e/get-app-fn-args struct-type)
                    tn (when (e/const? th) (name/->string (e/const-name th)))
                    reg (deref ingest/structure-registry)
                    sinfo (get reg tn)
                    fidx (when sinfo (first (keep-indexed (fn [i f] (when (= f field-name) i))
                                                          (:fields sinfo))))]
                (cond
                  fidx (e/proj (name/from-string tn) fidx struct-expr)
                  ;; non-structure receiver: type-directed keyword access via the
                  ;; extension registry (e.g. dynamic-EDN Value → vget)
                  (get @ingest/keyword-access-registry tn)
                  ((get @ingest/keyword-access-registry tn) est head struct-expr)
                  :else (elab-error! (str "Unknown structure field: :" field-name
                                          (when tn (str " (receiver type " tn
                                                        " is not a registered structure and has"
                                                        " no keyword-access handler)")))
                                     {:field field-name :type tn})))
          ;; (get struct :field) → (:field struct)
              (= (str head) "get") (elab-term est (list (nth sexpr 2) (nth sexpr 1)))
          ;; (cons x xs) → List.cons sugar (element type inferred)
              (= (str head) "cons") (elab-app est (symbol "List.cons") (rest sexpr))
          ;; (case x k1 v1 … default) → a bound scrutinee + nested type-directed ==
          ;; chain. Intercepted BEFORE clojure's macroexpansion: case* is a jump-table
          ;; encoding we never want to elaborate. A default is REQUIRED (totality).
              (= (str head) "case")
              (let [[_ scrut & clauses] sexpr]
                (when (even? (count clauses))
                  (elab-error! "case in a verified body requires a default branch (odd clause count)"
                               {:form sexpr}))
                (let [g (gensym "case")
                      default (last clauses)
                      pairs (partition 2 (butlast clauses))]
                  (elab-term est
                             (list 'let [g scrut]
                                   (reduce (fn [acc [k v]] (list 'if (list '== g k) v acc))
                                           default (reverse pairs))))))
              (and (symbol? head) (ingest/expand-macro? head))
              (elab-term est (macroexpand-1 sexpr))
              :else (elab-app est (first sexpr) (rest sexpr)))))))

    ;; vector literal = List literal: [a b c] → (cons a (cons b (cons c nil))).
    ;; Generalizes the bare-nil = List.nil rule above; the element type is
    ;; inferred through List.cons as usual ([] elaborates as List.nil ?α).
    (vector? sexpr)
    (elab-term est (reduce (fn [acc x] (list 'cons x acc)) nil (rseq sexpr)))

    :else
    (elab-error! (str "Unsupported form: " (pr-str sexpr)) {:form sexpr})))

;; ============================================================
;; Instance synthesis for unsolved inst-implicit metavariables
;; ============================================================

(defn- has-unsolved-mvar?
  "True if (zonked) expr still contains an fvar that is an unsolved mvar."
  [est expr]
  (let [mctx @(:mctx est)]
    (letfn [(unsolved? [id] (let [m (get mctx id)] (and m (nil? (:solution m)))))
            (go [x]
                (when (instance? ansatz.kernel.Expr x)
                  (case (e/tag x)
                    :fvar (unsolved? (e/fvar-id x))
                    :app (or (go (e/app-fn x)) (go (e/app-arg x)))
                    :lam (or (go (e/lam-type x)) (go (e/lam-body x)))
                    :forall (or (go (e/forall-type x)) (go (e/forall-body x)))
                    :let (or (go (e/let-type x)) (go (e/let-value x)) (go (e/let-body x)))
                    :proj (go (e/proj-struct x))
                    false)))]
      (boolean (go expr)))))

(defn- solve-instance-mvars!
  "Solve unsolved instance-implicit metavariables via the instance-synthesis
   engine (using the elaboration's fvar context, so goals mentioning local
   binders resolve). Loops to a fixpoint: solving one inst may determine another."
  [est]
  (let [synth* (requiring-resolve 'ansatz.tactic.instance/synthesize*)
        build-idx (requiring-resolve 'ansatz.tactic.instance/build-instance-index)
        index (build-idx (:env est))]
    (loop []
      (let [pending (filterv (fn [[_ m]] (and (:inst-implicit m) (nil? (:solution m))))
                             @(:mctx est))
            solved-any (atom false)]
        (doseq [[id _] pending]
          (let [goal (zonk est (:type (get @(:mctx est) id)))]
            ;; Only synthesize once the goal is fully determined (no unsolved mvars),
            ;; else we'd resolve against an under-specified class.
            (when-not (has-unsolved-mvar? est goal)
              (when-let [sol (try (synth* (:tc est) (:env est) index goal 0)
                                  (catch Throwable _ nil))]
                (solve-mvar! est id sol)
                ;; Unify the instance's concrete type with the goal so universe
                ;; levels shared with the class head (e.g. LE.le.{?u}) get solved
                ;; (solve-mvar! only propagates levels when both sides are Sorts).
                (try (unify! est (tc/infer-type (:tc est) sol) goal)
                     (catch Throwable _ nil))
                (reset! solved-any true)))))
        (when @solved-any (recur))))))

;; ============================================================
;; Public API
;; ============================================================

;; ── Extension-author API (the stable surface behind ansatz.surface.api) ─────────────────
;; Term elaborators (ingest/term-elaborator-registry) receive the live elaboration state
;; `est` and use these — never elaborator internals.

(defn elab-subterm
  "Elaborate a surface form to a kernel Expr inside a term elaborator. The result may
   contain unsolved metavariable fvars; they resolve when the enclosing elaboration zonks."
  [est form]
  (elab-term est form))

(defn elab-base
  "Elaborate `form` with the user registries bypassed for ITS OWN head dispatch only
   (sub-forms dispatch normally) — the delegation primitive for elaborators that WRAP a
   built-in form (e.g. a narrowing `if`)."
  [est form]
  (binding [*bypass-registries-once* true]
    (elab-term est form)))

(defn with-local
  "Run `(f est' fvar-id)` with `sym` bound to a FRESH local of kernel type `ty` in the
   elaboration scope (and the typechecker lctx) — the primitive for NARROWING elaborators
   that rebind a variable at a refined type for one branch (e.g. Option unwrapping).
   Shadows any existing binding of `sym` for the dynamic extent of `f`."
  [est sym ty f]
  (let [fid (fresh-id! est)
        est' (-> est
                 (assoc-in [:scope (symbol sym)] {:fvar-id fid :type ty})
                 (update :tc update :lctx red/lctx-add-local fid (str sym) ty))]
    (f est' fid)))

(defn subterm-type
  "The (whnf'd, zonked) TYPE of an elaborated subterm — for type-directed dispatch
   (e.g. count → vsize / Map.size / List.length depending on the collection type)."
  [est expr]
  (zonk est (#'tc/cached-whnf (:tc est) (infer-with-mvars est expr))))

(defn subterm-whnf
  "whnf a kernel type/term in the elaboration's typechecker context."
  [est expr]
  (#'tc/cached-whnf (:tc est) (zonk est expr)))

(defn elaborate
  "Elaborate an s-expression into a fully explicit Ansatz Expr.

   Resolves names, inserts implicit arguments as metavariables,
   infers universe levels, and zonks (substitutes solutions).

   Args:
     env         - kernel Env
     sexpr       - Clojure s-expression (quoted)
     expected    - optional expected type (for bidirectional checking)

   Returns the elaborated Expr.

   Examples:
     (elaborate env '(forall [a Nat] (Eq a a)))
     ;; Inserts implicit type arg for Eq, infers universe level
     ;; => fully explicit Ansatz term with no unsolved metavars

     (elaborate env 'Nat)
     ;; => (const Nat [])"
  ([env sexpr]
   (elaborate env sexpr nil))
  ([env sexpr expected]
   (let [est (mk-elab-state env)
         expr (elab-term est sexpr)
         ;; If expected type given, unify
         _ (when expected
             (let [inferred (tc/infer-type (:tc est) expr)]
               (when-not (unify! est inferred expected)
                 (elab-error! "Type mismatch"
                              {:expected expected :inferred inferred}))))
         ;; Solve instance-implicit metavariables via synthesis (uses the fvar
         ;; context so goals mentioning local binders resolve), then zonk.
         _ (solve-instance-mvars! est)
         ;; Zonk all metavariables
         result (zonk est expr)
         ;; Check for remaining unsolved metavars
         unsolved (filterv (fn [[id m]] (nil? (:solution m))) @(:mctx est))
         unsolved-levels (filterv (fn [[id m]] (nil? (:solution m))) @(:level-mctx est))]
     (when (seq unsolved)
       (elab-error! "Unsolved metavariables"
                    {:count (count unsolved)
                     :mvars (mapv (fn [[id m]] {:id id :type (:type m)}) unsolved)}))
     (when (seq unsolved-levels)
       (elab-error! "Unsolved universe level metavariables"
                    {:count (count unsolved-levels)
                     :names (mapv (fn [[id m]] (:name m)) unsolved-levels)}))
     result)))

(defn elaborate-in-context
  "Elaborate an s-expression with a local context from a proof state.
   Local hypotheses are available as symbols.

   lctx is a map {fvar-id → {:name str :type Expr :tag :local/:let ...}}.
   The hypothesis names become available as symbols in the surface syntax.

   Example:
     ;; Inside a proof with hypothesis 'a : Nat' (fvar-id 42):
     (elaborate-in-context env lctx '(Eq a a))
     ;; => (Eq.{1} Nat (fvar 42) (fvar 42))"
  ([env lctx sexpr]
   (elaborate-in-context env lctx sexpr nil))
  ([env lctx sexpr expected]
   (let [est (mk-elab-state env)
         ;; Populate scope with lctx entries
         est (reduce (fn [est [id decl]]
                       (if-let [n (:name decl)]
                         (let [sym (symbol n)]
                           (-> est
                               (assoc-in [:scope sym]
                                         (cond-> {:fvar-id id :type (:type decl)}
                                           (:as-term decl) (assoc :as-term (:as-term decl))))
                               (update :tc update :lctx
                                       red/lctx-add-local id n (:type decl))))
                         est))
                     est
                     lctx)
         expr (elab-term est sexpr)
         _ (when expected
             (let [inferred (tc/infer-type (:tc est) expr)]
               (when-not (unify! est inferred expected)
                 (elab-error! "Type mismatch"
                              {:expected expected :inferred inferred}))))
         _ (solve-instance-mvars! est)
         result (zonk est expr)
         unsolved (filterv (fn [[_ m]] (nil? (:solution m))) @(:mctx est))
         unsolved-levels (filterv (fn [[_ m]] (nil? (:solution m))) @(:level-mctx est))]
     (when (seq unsolved)
       (elab-error! "Unsolved metavariables"
                    {:count (count unsolved)
                     :mvars (mapv (fn [[id m]] {:id id :type (:type m)}) unsolved)}))
     (when (seq unsolved-levels)
       (elab-error! "Unsolved universe level metavariables"
                    {:count (count unsolved-levels)
                     :names (mapv (fn [[_ m]] (:name m)) unsolved-levels)}))
     result)))

(defn elaborate-check
  "Elaborate and verify: elaborate the s-expression, then verify the result
   type-checks via the kernel type checker."
  ([env sexpr]
   (let [result (elaborate env sexpr)
         st (tc/mk-tc-state env)]
     (tc/infer-type st result)  ;; will throw on type error
     result))
  ([env sexpr expected]
   (let [result (elaborate env sexpr expected)
         st (tc/mk-tc-state env)
         inferred (tc/infer-type st result)]
     (when expected
       (when-not (tc/is-def-eq st inferred expected)
         (elab-error! "Elaborated term doesn't match expected type"
                      {:expected expected :inferred inferred})))
     result)))
