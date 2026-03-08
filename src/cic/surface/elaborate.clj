;; Copyright (c) 2026 Simmis GmbH. All rights reserved.
;; Surface syntax — runtime elaboration with implicit argument insertion.

(ns cic.surface.elaborate
  "Runtime elaboration: transforms surface s-expressions into fully explicit
   CIC terms by resolving names, inserting implicit arguments, inferring
   universe levels, and type-checking.

   Unlike `cic.surface.term` (which only does name→de Bruijn conversion),
   elaborate is type-directed: it uses the kernel type checker to infer
   omitted implicit arguments.

   Usage:
     (elaborate env '(forall [a Nat] (Eq a a)))
     ;; => fully explicit: (forall [a Nat] (@Eq.{1} Nat a a))

     (elaborate env '(lam [a Nat] (Eq.refl a))  expected-type)
     ;; => checks against expected-type, infers implicits"
  (:require [cic.kernel.expr :as e]
            [cic.kernel.env :as env]
            [cic.kernel.level :as lvl]
            [cic.kernel.name :as name]
            [cic.kernel.reduce :as red]
            [cic.kernel.tc :as tc]
            [cic.surface.match :as match])
  (:import [cic.kernel ConstantInfo Env]))

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
    (let [tag (.tag ^cic.kernel.Level l)]
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
  (let [tokens (remove (fn [t] (or (= (str t) ",") (= (str t) ":"))) binder-vec)]
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
              (solve-level-mvar! est entry l1)))))))

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
    ;; Bound variable?
    (if-let [{:keys [fvar-id]} (get (:scope est) sym)]
      {:expr (e/fvar fvar-id) :explicit? false}
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
              expr' (e/app expr arg-mvar)
              ty' (#'tc/cached-whnf tc (e/instantiate1 (e/forall-body ty) arg-mvar))]
          (recur expr' ty'))
        [expr ty]))))

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
        head-type (tc/infer-type tc head-expr)
        ;; Insert leading implicits (unless @-explicit)
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
                  arg-type (tc/infer-type tc arg-expr)
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
                      typ-expr (elab-term est typ-sexpr)
                      fvar-id (fresh-id! est)
                      fv (e/fvar fvar-id)
                      est' (-> est
                               (assoc-in [:scope nam] {:fvar-id fvar-id :type typ-expr})
                               (update :tc update :lctx red/lctx-add-local fvar-id (str nam) typ-expr))
                      body-expr (build (rest binders) est')
                      abs-body (e/abstract1 body-expr fvar-id)]
                  (e/forall' (str nam) typ-expr abs-body :default))))]
      (build binders est))))

(defn- elab-lam
  "Elaborate a lambda expression with binders."
  [est binder-vec body-sexpr]
  (let [binders (parse-binders binder-vec)]
    (letfn [(build [binders est]
              (if (empty? binders)
                (elab-term est body-sexpr)
                (let [[nam typ-sexpr] (first binders)
                      typ-expr (elab-term est typ-sexpr)
                      fvar-id (fresh-id! est)
                      fv (e/fvar fvar-id)
                      est' (-> est
                               (assoc-in [:scope nam] {:fvar-id fvar-id :type typ-expr})
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

(defn- elab-term
  "Recursively elaborate an s-expression into a CIC Expr."
  [est sexpr]
  (cond
    (integer? sexpr) (e/lit-nat sexpr)
    (string? sexpr)  (e/lit-str sexpr)

    (symbol? sexpr)
    (:expr (resolve-symbol est sexpr))

    (seq? sexpr)
    (let [head (first sexpr)]
      (case (when (symbol? head) (str head))
        "forall" (let [[_ binder-vec & body-forms] sexpr]
                   (when (not= 1 (count body-forms))
                     (elab-error! "forall expects one body" {:forms body-forms}))
                   (elab-forall est binder-vec (first body-forms)))

        "lam"    (let [[_ binder-vec & body-forms] sexpr]
                   (when (not= 1 (count body-forms))
                     (elab-error! "lam expects one body" {:forms body-forms}))
                   (elab-lam est binder-vec (first body-forms)))

        "arrow"  (let [[_ a b] sexpr
                       a-expr (elab-term est a)
                       b-expr (elab-term est b)]
                   (e/arrow a-expr b-expr))

        "Sort"   (let [[_ level-form] sexpr
                       level (cond
                               (integer? level-form) (lvl/from-nat level-form)
                               (= 'zero level-form) lvl/zero
                               :else (elab-error! (str "Unsupported Sort level: " level-form)
                                                  {:level level-form}))]
                   (e/sort' level))

        "let"    (let [[_ binder-vec & body-forms] sexpr]
                   (when (not= 1 (count body-forms))
                     (elab-error! "let expects one body" {:forms body-forms}))
                   (elab-let est binder-vec (first body-forms)))

        "app"    (let [[_ f a] sexpr]
                   (e/app (elab-term est f) (elab-term est a)))

        "match"  (let [[_ discr-sexpr & alt-forms] sexpr]
                   (match/compile-match est elab-term discr-sexpr
                                        (mapv vec alt-forms)))

        ;; Default: application with implicit insertion
        (elab-app est (first sexpr) (rest sexpr))))

    (vector? sexpr)
    (elab-error! "Unexpected vector in term position" {:form sexpr})

    :else
    (elab-error! (str "Unsupported form: " (pr-str sexpr)) {:form sexpr})))

;; ============================================================
;; Public API
;; ============================================================

(defn elaborate
  "Elaborate an s-expression into a fully explicit CIC Expr.

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
     ;; => fully explicit CIC term with no unsolved metavars

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
                               (assoc-in [:scope sym] {:fvar-id id :type (:type decl)})
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
