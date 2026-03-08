;; Copyright (c) 2026 Simmis GmbH. All rights reserved.
;; Surface syntax — macro-based named term builder for CIC expressions.

(ns cic.surface.term
  "Eliminates manual de Bruijn index management, name interning, and
   universe level plumbing when constructing CIC terms.

   Usage:
     (term env (forall [a Nat] (Eq Nat a a)))

   Resolves symbols to bound variables (de Bruijn) or env constants,
   handles nested binders, applications, literals, and Sort shortcuts."
  (:require [cic.kernel.expr :as e]
            [cic.kernel.env :as env]
            [cic.kernel.level :as lvl]
            [cic.kernel.name :as name])
  (:import [cic.kernel Env Name]))

;; ============================================================
;; Level parsing
;; ============================================================

(defn- parse-level-token
  "Parse a single level token: a number, or a name (level param)."
  [s]
  (if-let [n (try (Long/parseLong (str s)) (catch NumberFormatException _ nil))]
    (lvl/from-nat n)
    (lvl/param (name/from-string (str s)))))

(defn- parse-levels
  "Parse universe levels from a symbol suffix like 'Foo.{1,2}' or 'Foo.{u}'.
   Returns [base-name levels-vec] or [original-name nil] if no levels."
  [sym-str]
  (if-let [idx (clojure.string/index-of sym-str ".{")]
    (let [base (subs sym-str 0 idx)
          lvl-str (subs sym-str (+ idx 2) (dec (count sym-str)))
          parts (clojure.string/split lvl-str #"\s*,\s*")
          levels (mapv parse-level-token parts)]
      [base levels])
    [sym-str nil]))

;; ============================================================
;; Symbol resolution
;; ============================================================

(defn- resolve-symbol
  "Resolve a symbol to an Expr.
   Checks scope (bound vars) first, then env constants.
   Special shortcuts: Prop, Type, Type.{n}."
  [^Env env scope depth sym]
  (let [sym-str (str sym)]
    ;; Check bound variables first
    (if-let [bind-depth (get scope sym)]
      (e/bvar (- depth bind-depth 1))
      ;; Check special shortcuts
      (case sym-str
        "Prop" (e/sort' lvl/zero)
        "Type" (e/sort' (lvl/succ lvl/zero))
        ;; Otherwise try to parse levels and look up in env
        (let [[base-name explicit-levels] (parse-levels sym-str)]
          ;; Check Type.{n} shortcut
          (if (and (= base-name "Type") explicit-levels)
            (e/sort' (lvl/succ (first explicit-levels)))
            ;; Look up constant in env
            (let [cname (name/from-string base-name)
                  ci (env/lookup env cname)]
              (if ci
                (let [level-params (env/ci-level-params ci)
                      levels (or explicit-levels
                                 (mapv lvl/param level-params))]
                  (e/const' cname levels))
                (throw (ex-info (str "Unresolved symbol: " sym-str)
                                {:symbol sym-str
                                 :scope (keys scope)}))))))))))

;; ============================================================
;; Binder parsing
;; ============================================================

(defn- parse-binders
  "Parse binder vector like [a Nat, b Nat] or [a : Nat, b : Nat].
   Returns a sequence of [name-sym type-sexpr] pairs.
   The colon is optional syntactic sugar and is ignored.
   Commas separate binders."
  [binder-vec]
  (let [;; Remove commas and colons
        tokens (remove (fn [t] (or (= (str t) ",") (= (str t) ":"))) binder-vec)]
    ;; Group into pairs: name type name type ...
    (loop [ts (seq tokens) result []]
      (if (or (nil? ts) (empty? ts))
        result
        (let [nam (first ts)
              typ (second ts)]
          (when (nil? typ)
            (throw (ex-info (str "Binder missing type for: " nam)
                            {:name nam})))
          (recur (nnext ts) (conj result [nam typ])))))))

;; ============================================================
;; Core compiler
;; ============================================================

(defn- compile-term
  "Recursively compile a Clojure s-expression into a CIC Expr.
   env   — kernel Env for constant lookup
   scope — map from symbol to binding depth
   depth — current binder depth"
  [env scope depth sexpr]
  (cond
    ;; Integers become nat literals
    (integer? sexpr)
    (e/lit-nat sexpr)

    ;; Strings become string literals
    (string? sexpr)
    (e/lit-str sexpr)

    ;; Symbols resolve to bound vars or constants
    (symbol? sexpr)
    (resolve-symbol env scope depth sexpr)

    ;; Keywords are passed through (shouldn't normally appear)
    (keyword? sexpr)
    (throw (ex-info (str "Unexpected keyword in term: " sexpr) {:keyword sexpr}))

    ;; Lists are special forms or applications
    (seq? sexpr)
    (let [head (first sexpr)]
      (case (when (symbol? head) (str head))
        ;; (forall [x Type, ...] body)
        "forall"
        (let [[_ binder-vec & body-forms] sexpr
              binders (parse-binders binder-vec)
              body-sexpr (if (= 1 (count body-forms))
                           (first body-forms)
                           (throw (ex-info "forall expects exactly one body form"
                                           {:forms body-forms})))]
          ;; Build nested foralls from right to left
          (letfn [(build [binders scope depth]
                    (if (empty? binders)
                      (compile-term env scope depth body-sexpr)
                      (let [[nam typ-sexpr] (first binders)
                            typ-expr (compile-term env scope depth typ-sexpr)
                            new-scope (assoc scope nam depth)
                            new-depth (inc depth)
                            body-expr (build (rest binders) new-scope new-depth)]
                        (e/forall' (str nam) typ-expr body-expr :default))))]
            (build binders scope depth)))

        ;; (lam [x Type, ...] body)
        "lam"
        (let [[_ binder-vec & body-forms] sexpr
              binders (parse-binders binder-vec)
              body-sexpr (if (= 1 (count body-forms))
                           (first body-forms)
                           (throw (ex-info "lam expects exactly one body form"
                                           {:forms body-forms})))]
          (letfn [(build [binders scope depth]
                    (if (empty? binders)
                      (compile-term env scope depth body-sexpr)
                      (let [[nam typ-sexpr] (first binders)
                            typ-expr (compile-term env scope depth typ-sexpr)
                            new-scope (assoc scope nam depth)
                            new-depth (inc depth)
                            body-expr (build (rest binders) new-scope new-depth)]
                        (e/lam (str nam) typ-expr body-expr :default))))]
            (build binders scope depth)))

        ;; (arrow Type1 Type2)
        "arrow"
        (let [[_ a b] sexpr
              a-expr (compile-term env scope depth a)
              b-expr (compile-term env scope depth b)]
          (e/arrow a-expr b-expr))

        ;; (Sort level)
        "Sort"
        (let [[_ level-form] sexpr
              level (cond
                      (integer? level-form) (lvl/from-nat level-form)
                      (= 'zero level-form) lvl/zero
                      :else (throw (ex-info (str "Unsupported Sort level: " level-form)
                                            {:level level-form})))]
          (e/sort' level))

        ;; (let [x Type val] body)
        "let"
        (let [[_ binder-vec & body-forms] sexpr
              body-sexpr (if (= 1 (count body-forms))
                           (first body-forms)
                           (throw (ex-info "let expects exactly one body form"
                                           {:forms body-forms})))
              ;; Parse let binder: [x Type val]
              tokens (remove (fn [t] (or (= (str t) ":") (= (str t) "=")))
                             binder-vec)
              tokens-vec (vec tokens)]
          (when (not= 3 (count tokens-vec))
            (throw (ex-info "let binder expects [name type value]"
                            {:binder binder-vec})))
          (let [nam (nth tokens-vec 0)
                typ-sexpr (nth tokens-vec 1)
                val-sexpr (nth tokens-vec 2)
                typ-expr (compile-term env scope depth typ-sexpr)
                val-expr (compile-term env scope depth val-sexpr)
                new-scope (assoc scope nam depth)
                new-depth (inc depth)
                body-expr (compile-term env new-scope new-depth body-sexpr)]
            (e/let' (str nam) typ-expr val-expr body-expr)))

        ;; (app f a) — explicit application
        "app"
        (let [[_ f a] sexpr]
          (e/app (compile-term env scope depth f)
                 (compile-term env scope depth a)))

        ;; Default: application (f a b c) => (app (app (app f a) b) c)
        (let [compiled (mapv #(compile-term env scope depth %) sexpr)]
          (reduce e/app compiled))))

    ;; Vectors — could be binder syntax used incorrectly at top level
    (vector? sexpr)
    (throw (ex-info "Unexpected vector in term position" {:form sexpr}))

    :else
    (throw (ex-info (str "Unsupported term form: " (pr-str sexpr))
                    {:form sexpr}))))

;; ============================================================
;; Public API
;; ============================================================

(defn term
  "Build a CIC Expr from a Clojure s-expression.

   Symbols resolve to bound variables (from forall/lam binders) or
   constants looked up in env. Special forms: forall, lam, arrow,
   Sort, let, app. Application is implicit: (f a b) = app(app(f,a),b).

   Examples:
     (term env 'Nat)
     (term env '(forall [a Nat] (Eq Nat a a)))
     (term env '(lam [x Prop] x))
     (term env '(arrow Prop Prop))"
  [env sexpr]
  (compile-term env {} 0 sexpr))
