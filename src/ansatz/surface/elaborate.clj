;; Surface syntax — runtime elaboration with implicit argument insertion.

(ns ansatz.surface.elaborate
  "Runtime elaboration: transforms surface s-expressions into fully explicit
   Ansatz terms by resolving names, inserting implicit arguments, inferring
   universe levels, and type-checking.

   Unlike `ansatz.surface.term` (which only does name→de Bruijn conversion),
   elaborate is type-directed: it uses the kernel type checker to infer
   omitted implicit arguments.

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
            [ansatz.surface.match :as match])
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
  (let [tc (reduce (fn [tc [id m]]
                     (try (update tc :lctx red/lctx-add-local id (str "?m" id) (:type m))
                          (catch Throwable _ tc)))
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
              ;; Mark instance-implicit mvars so they can be solved by instance
              ;; synthesis (not just unification) before the final unsolved-check.
              _ (when (= (e/forall-info ty) :inst-implicit)
                  (swap! (:mctx est) assoc-in [(e/fvar-id arg-mvar) :inst-implicit] true))
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
        head-type (infer-with-mvars est head-expr)
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
  "Recursively elaborate an s-expression into a Ansatz Expr."
  [est sexpr]
  (cond
    (integer? sexpr) (e/lit-nat sexpr)
    (string? sexpr)  (e/lit-str sexpr)
    (boolean? sexpr) (e/const' (name/from-string (if sexpr "Bool.true" "Bool.false")) [])

    (symbol? sexpr)
    ;; A bare symbol in term position: insert its implicit/instance arguments
    ;; (as Lean does for any term, not only application heads) so e.g. List.nil
    ;; becomes List.nil.{?u} ?α rather than the under-applied bare constant.
    (let [{:keys [expr explicit?]} (resolve-symbol est sexpr)]
      (if explicit?
        expr
        (first (insert-implicits est expr (infer-with-mvars est expr)))))

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
        "match"  (let [args (vec (rest sexpr))]
                   (if (vector? (get args 1))
                     (match/compile-match est elab-term (first args) (mapv vec (rest args)))
                     (let [scrut (first args)
                           alts (mapv (fn [c]
                                        (let [ctor (first c)
                                              has-fields (and (> (count c) 2) (vector? (second c)))
                                              fields (if has-fields (second c) [])
                                              body (if has-fields (nth c 2) (second c))]
                                          [(if (seq fields) (cons ctor (seq fields)) ctor) body]))
                                      (drop 3 args))]
                       (match/compile-match est elab-term scrut alts))))

        "=>" (let [[_ a b] sexpr]
               (e/arrow (elab-term est a) (elab-term est b)))

        ;; Bool if-then-else → Bool.rec. The motive is the then-branch's type,
        ;; inferred directly (fvar context is present — no open/close needed).
        "if" (let [[_ c t e] sexpr
                   cond-expr (elab-term est c)
                   then-expr (elab-term est t)
                   else-expr (elab-term est e)
                   ret-type (tc/infer-type (:tc est) (zonk est then-expr))]
               (e/app* (e/const' (name/from-string "Bool.rec") [(lvl/succ lvl/zero)])
                       (e/lam "_" (e/const' (name/from-string "Bool") []) ret-type :default)
                       else-expr then-expr cond-expr))

        ;; Prop-valued comparisons over an explicit type: (le T a b) / (lt T a b)
        ;; → LE.le.{?u} T ?inst a b — the instance + level resolve via synthesis.
        ("le" "lt") (let [[_ T a b] sexpr
                          cn  (if (= (str head) "le") "LE.le" "LT.lt")
                          icn (if (= (str head) "le") "LE" "LT")
                          T'  (elab-term est T)
                          a'  (elab-term est a)
                          b'  (elab-term est b)
                          u   (fresh-level-mvar! est)
                          inst (fresh-mvar! est (e/app (e/const' (name/from-string icn) [u]) T'))
                          _ (swap! (:mctx est) assoc-in [(e/fvar-id inst) :inst-implicit] true)]
                      (e/app* (e/const' (name/from-string cn) [u]) T' inst a' b'))

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
            (let [[op a b] (case hs
                             "<"  ["Nat.blt" (nth sexpr 1) (nth sexpr 2)]
                             "==" ["Nat.beq" (nth sexpr 1) (nth sexpr 2)]
                             ("<=" "≤") ["Nat.ble" (nth sexpr 1) (nth sexpr 2)]
                             (">"  ) ["Nat.blt" (nth sexpr 2) (nth sexpr 1)]
                             (">=" "≥") ["Nat.ble" (nth sexpr 2) (nth sexpr 1)])]
              (e/app* (e/const' (name/from-string op) []) (elab-term est a) (elab-term est b)))))

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

        ;; Arithmetic: bare ops default to Nat (matching sexp->ansatz); explicit-type
        ;; forms (add/sub/mul T a b) handled separately. Nat.* avoids HAdd's output param.
        ("+" "-" "*") (elab-app est (symbol (case (str head) "+" "Nat.add"
                                                             "-" "Nat.sub"
                                                             "*" "Nat.mul"))
                                (rest sexpr))

        ;; do → value of the last form (pure setting: earlier forms have no effect).
        "do" (elab-term est (last sexpr))

        ;; Clojure fn* (single arity) → lambda. parse-params reads the binders' metadata
        ;; types (^Nat / ^{:- T}); flatten to a [name type …] vec and reuse elab-lam.
        "fn*" (let [cls (rest sexpr)
                    cls (if (symbol? (first cls)) (rest cls) cls)  ; skip optional self-name
                    arities (filter #(and (sequential? %) (vector? (first %))) cls)]
                (when (not= 1 (count arities))
                  (elab-error! "fn: only single-arity lambdas elaborate to kernel terms" {:form sexpr}))
                (let [[params & body] (first arities)
                      body-form (if (> (count body) 1) (cons 'do body) (first body))
                      pairs ((requiring-resolve 'ansatz.core/parse-params) params)
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

        ;; Default: macroexpand any clojure macro (cond/->/and/or/…) and re-elaborate;
        ;; otherwise application with implicit insertion.
        (if (and (symbol? head)
                 ((requiring-resolve 'ansatz.core/expand-macro?) head))
          (elab-term est (macroexpand-1 sexpr))
          (elab-app est (first sexpr) (rest sexpr)))))

    (vector? sexpr)
    (elab-error! "Unexpected vector in term position" {:form sexpr})

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
