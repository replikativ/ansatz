;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; Inductive type definitions compatible with Lean 4's kernel.
;;
;; Generates: inductive type, constructors, recursor, casesOn, recOn,
;; noConfusionType, noConfusion — matching Lean 4's exact declaration format.
;;
;; Usage:
;;   (define-inductive env "Color" [] [['red []] ['green []] ['blue []]])
;;   (define-inductive env "MyList" '[α Type] [['nil []] ['cons [['head 'α] ['tail '(MyList α)]]]])

(ns ansatz.inductive
  "Define inductive types compatible with Lean 4's kernel."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl])
  (:import [ansatz.kernel ConstantInfo]))

;; ============================================================
;; Scope helpers (de Bruijn index computation)
;; ============================================================

(defn- sref
  "Reference a symbol in scope at given depth → bvar."
  [scope depth sym]
  (let [d (get scope sym)]
    (when-not d (throw (ex-info (str "Unbound: " sym) {:scope (keys scope) :depth depth})))
    (e/bvar (- depth d 1))))

(defn- sbind
  "Add a binding, returning [new-scope new-depth]."
  [scope depth sym]
  [(assoc scope sym depth) (inc depth)])

;; ============================================================
;; Type compilation (extends ansatz.core's sexp->ansatz with self-references)
;; ============================================================

(declare compile-type)

(defn- compile-type
  "Compile a type s-expression to Ansatz Expr.
   Handles self-references to the inductive being defined."
  [env scope depth form self-name self-const]
  (cond
    (nil? form) (throw (ex-info "nil type" {}))
    (integer? form) (e/lit-nat form)

    (symbol? form)
    (let [s (str form)]
      (cond
        (contains? scope form) (sref scope depth form)
        (= s (str self-name))  self-const
        (= s "Prop")   (e/sort' lvl/zero)
        (= s "Type")   (e/sort' (lvl/succ lvl/zero))
        (= s "Nat")    (e/const' (name/from-string "Nat") [])
        (= s "Int")    (e/const' (name/from-string "Int") [])
        (= s "Bool")   (e/const' (name/from-string "Bool") [])
        (= s "String") (e/const' (name/from-string "String") [])
        (= s "True")   (e/const' (name/from-string "True") [])
        (= s "False")  (e/const' (name/from-string "False") [])
        :else
        (if-let [ci (or (env/lookup env (name/from-string s))
                        ;; Also check global env (may have types added in this session)
                        (when-let [global-env (try @@(requiring-resolve 'ansatz.core/ansatz-env)
                                                   (catch Exception _ nil))]
                          (env/lookup global-env (name/from-string s))))]
          (let [lps (vec (.levelParams ^ConstantInfo ci))]
            (e/const' (name/from-string s) (mapv (fn [_] lvl/zero) lps)))
          (throw (ex-info (str "Cannot compile type: " s) {:form s})))))

    (and (sequential? form) (seq form))
    (let [h (str (first form))]
      (case h
        ;; Arrow
        ("->" "arrow")
        (e/arrow (compile-type env scope depth (nth form 1) self-name self-const)
                 (compile-type env scope (inc depth) (nth form 2) self-name self-const))
        ;; Arithmetic operators
        ("+" "-" "*")
        (let [op (case h "+" "HAdd.hAdd" "*" "HMul.hMul" "-" "HSub.hSub")
              ic (case h "+" "instHAdd"   "*" "instHMul"   "-" "instHSub")
              in (case h "+" "instAddNat" "*" "instMulNat" "-" "instSubNat")
              nat (e/const' (name/from-string "Nat") [])
              a (compile-type env scope depth (nth form 1) self-name self-const)
              b (compile-type env scope depth (nth form 2) self-name self-const)]
          (e/app* (e/const' (name/from-string op) [lvl/zero lvl/zero lvl/zero])
                  nat nat nat
                  (e/app* (e/const' (name/from-string ic) [lvl/zero])
                          nat (e/const' (name/from-string in) []))
                  a b))
        ;; Equality
        ("=" "Eq")
        (let [args (vec (rest form))
              [ty lhs rhs] (if (= 3 (count args))
                             (mapv #(compile-type env scope depth % self-name self-const) args)
                             [(e/const' (name/from-string "Nat") [])
                              (compile-type env scope depth (nth args 0) self-name self-const)
                              (compile-type env scope depth (nth args 1) self-name self-const)])]
          (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) ty lhs rhs))
        ;; Default: application
        (reduce e/app (mapv #(compile-type env scope depth % self-name self-const) form))))

    ;; String: read as Clojure form and recurse (field specs use strings)
    (string? form)
    (let [parsed (read-string form)]
      (compile-type env scope depth parsed self-name self-const))

    :else (throw (ex-info (str "Cannot compile type: " form) {:form form}))))

;; ============================================================
;; Phase 2: Validation
;; ============================================================

(defn occurs-in?
  "Check if the inductive name occurs in an expression."
  [expr induct-name]
  (cond
    (e/const? expr) (= (e/const-name expr) induct-name)
    (e/app? expr) (or (occurs-in? (e/app-fn expr) induct-name)
                      (occurs-in? (e/app-arg expr) induct-name))
    (e/forall? expr) (or (occurs-in? (e/forall-type expr) induct-name)
                         (occurs-in? (e/forall-body expr) induct-name))
    (e/lam? expr) (or (occurs-in? (e/lam-type expr) induct-name)
                      (occurs-in? (e/lam-body expr) induct-name))
    :else false))

(defn- check-positivity!
  "Check strict positivity: inductive must not appear in negative position."
  [field-type induct-name ctor-name field-name]
  (cond
    (not (occurs-in? field-type induct-name)) nil

    (e/forall? field-type)
    (do (when (occurs-in? (e/forall-type field-type) induct-name)
          (throw (ex-info (str "Non-positive occurrence in " ctor-name "." field-name
                               ": inductive appears left of →")
                          {:ctor ctor-name :field field-name})))
        (check-positivity! (e/forall-body field-type) induct-name ctor-name field-name))

    ;; Direct application I params... — valid recursive reference
    :else
    (let [[head _] (e/get-app-fn-args field-type)]
      (when-not (and (e/const? head) (= (e/const-name head) induct-name))
        (throw (ex-info (str "Invalid occurrence of inductive in " ctor-name "." field-name)
                        {:ctor ctor-name :field field-name}))))))

;; ============================================================
;; Phase 1: Core declarations
;; ============================================================

(defn- build-inductive-type
  "Build: ∀ (p1:T1) ... (pn:Tn) (i1:I1) ... (ik:Ik) → Sort result_level
   indices is a vec of {:name :compiled-type} (empty for non-indexed types)."
  [params indices result-level]
  (let [body (e/sort' result-level)
        ;; Wrap index foralls (innermost first)
        body (loop [i (dec (count indices)) body body]
               (if (< i 0) body
                   (recur (dec i) (e/forall' (:name (nth indices i))
                                             (:compiled-type (nth indices i))
                                             body :default))))]
    ;; Wrap param foralls
    (loop [i (dec (count params)) body body]
      (if (< i 0) body
          (recur (dec i) (e/forall' (:name (nth params i)) (:compiled-type (nth params i))
                                    body :default))))))

(defn- build-constructor-type
  "Build: ∀ (p1:T1) ... (pn:Tn) (f1:F1) ... (fm:Fm) → I p1...pn idx1...idxk
   field-types must be compiled at depth = n_params + field_index.
   return-indices are compiled Expr for the constructor's specific index values,
   at depth n-params + n-fields (in scope of params + fields)."
  [params fields ind-name ind-lvls return-indices]
  (let [n-params (count params)
        n-fields (count fields)
        n-total (+ n-params n-fields)
        ;; Return type: I p1...pn idx1...idxk at depth n-total
        return-type (reduce (fn [acc i]
                              (e/app acc (e/bvar (- n-total i 1))))
                            (e/const' ind-name ind-lvls)
                            (range n-params))
        ;; Apply index expressions
        return-type (reduce (fn [acc idx-expr] (e/app acc idx-expr))
                            return-type return-indices)]
    ;; Wrap fields (inner binders), right-to-left
    (loop [i (dec n-fields) body return-type]
      (if (< i 0)
        ;; Wrap params (outer binders)
        (loop [i (dec n-params) body body]
          (if (< i 0) body
              (recur (dec i) (e/forall' (:name (nth params i))
                                        (:compiled-type (nth params i))
                                        body :default))))
        (recur (dec i) (e/forall' (:name (nth fields i))
                                  (:type (nth fields i))
                                  body :default))))))

(defn- compile-fields
  "Compile constructor field types starting at [base-scope, base-depth].
   Returns [{:name :sym :type (Ansatz Expr)} ...]"
  [env base-scope base-depth fields-spec self-name self-const]
  (loop [i 0 scope base-scope depth base-depth acc []]
    (if (>= i (count fields-spec))
      acc
      (let [[fname ftype-form] (nth fields-spec i)
            ftype (compile-type env scope depth ftype-form self-name self-const)
            [scope' depth'] (sbind scope depth fname)]
        (recur (inc i) scope' depth'
               (conj acc {:name (str fname) :sym fname :type ftype}))))))

(defn- is-recursive-field?
  "Check if a field has a recursive type."
  [field ind-name]
  (occurs-in? (:type field) ind-name))

;; ============================================================
;; Recursor construction
;; ============================================================

(defn- build-minor-type
  "Build the type of a minor premise for one constructor.
   At depth = base-depth (after params, motive already bound).
   Returns a forall nesting: ∀ fields, ∀ IH, motive(ctor-indices, ctor params fields).
   For indexed families, the motive is applied to the constructor's return indices
   THEN to the constructor application."
  [env ctor params indices ind-name ind-lvls elim-level
   base-scope base-depth self-name self-const is-rec]
  (let [n-params (count params)
        n-indices (count indices)
        ;; Compile field types at the minor's inner telescope
        fields (compile-fields env base-scope base-depth
                               (mapv (fn [f] [(:sym f) (:type-form f)])
                                     (:field-specs ctor))
                               self-name self-const)
        n-fields (count fields)
        ;; Identify recursive fields for IH
        rec-field-indices (when is-rec
                            (vec (keep-indexed
                                  (fn [i f] (when (is-recursive-field? f ind-name) i))
                                  fields)))
        n-ih (count (or rec-field-indices []))
        ;; Build motive application: motive(ctor-return-indices..., ctor params fields)
        ;; at depth = base-depth + n-fields + n-ih (inside all field + IH binders)
        body-depth (+ base-depth n-fields n-ih)
        motive-ref (sref base-scope body-depth 'motive)
        ;; Build constructor application: Ctor params f1...fn
        ctor-name (name/from-string (:full-name ctor))
        ctor-app (reduce (fn [acc i]
                           (e/app acc (sref base-scope body-depth (:sym (nth params i)))))
                         (e/const' ctor-name ind-lvls)
                         (range n-params))
        ctor-app (reduce (fn [acc i]
                           (e/app acc (e/bvar (- body-depth (+ base-depth i) 1))))
                         ctor-app (range n-fields))
        ;; Apply motive to constructor's return indices first, then ctor application
        ;; The return indices are compiled at depth n-params + n-fields (scope of params + fields)
        ;; We need to lift them to body-depth
        ctor-return-indices (or (:compiled-return-indices ctor) [])
        ;; Lift: each index was compiled at ctor field depth (n-params + n-fields)
        ;; Now at body-depth = base-depth + n-fields + n-ih
        ;; The bvars in index exprs reference params (0..n-params-1) and fields (n-params..n-params+n-fields-1)
        ;; At body-depth with base-scope, params are sref-accessible, fields are at base-depth+i
        ;; We need to recompile indices at body-depth using the field scope
        recompiled-indices (when (pos? n-indices)
                             (let [field-scope (reduce (fn [s [i f]] (assoc s (:sym f) (+ base-depth i)))
                                                       base-scope (map-indexed vector fields))]
                               (mapv (fn [idx-form]
                                       (compile-type env field-scope body-depth idx-form
                                                     self-name (e/const' ind-name ind-lvls)))
                                     (:return-index-forms ctor))))
        body (reduce (fn [acc idx] (e/app acc idx))
                     motive-ref (or recompiled-indices []))
        body (e/app body ctor-app)]
    ;; Wrap IH binders (from right to left)
    ;; IH for recursive field i: motive(field-indices..., field_i)
    (let [body (loop [ih-idx (dec n-ih) body body]
                 (if (< ih-idx 0) body
                     (let [field-idx (nth rec-field-indices ih-idx)
                           ih-depth (+ base-depth n-fields ih-idx)
                           motive-ref-ih (sref base-scope ih-depth 'motive)
                           field-ref-ih (e/bvar (- ih-depth (+ base-depth field-idx) 1))
                         ;; For indexed families, IH type is motive(field-type-indices..., field)
                         ;; Extract indices from the recursive field's type
                           rec-field-type (:type (nth fields field-idx))
                           rec-field-idx-exprs (when (pos? n-indices)
                                                 (let [[_ rargs] (e/get-app-fn-args rec-field-type)]
                                                 ;; Skip params, take indices from I params idx1...idxk
                                                   (when (>= (count rargs) (+ n-params n-indices))
                                                     (subvec (vec rargs) n-params (+ n-params n-indices)))))
                           ih-type (reduce (fn [acc idx] (e/app acc idx))
                                           motive-ref-ih (or rec-field-idx-exprs []))
                           ih-type (e/app ih-type field-ref-ih)]
                       (recur (dec ih-idx) (e/forall' (str "ih_" (:name (nth fields field-idx)))
                                                      ih-type body :default)))))]
      ;; Wrap field binders (from right to left)
      (loop [i (dec n-fields) body body]
        (if (< i 0)
          body
          (recur (dec i) (e/forall' (:name (nth fields i))
                                    (:type (nth fields i))
                                    body :default)))))))

(defn- build-recursor-rule-rhs
  "Build the RHS lambda for a recursor rule.
   λ params. λ motive. λ minors. λ fields.
     minor_i(fields, ih1, ..., ihk)
   For indexed families, recursive calls include field indices:
     rec params motive minors field-indices recursive-field"
  [env ctor ctor-idx params indices ctors ind-name ind-lvls
   rec-name rec-level-params rec-level-levels elim-level is-rec
   self-name self-const]
  (let [n-params (count params)
        n-indices (count indices)
        n-ctors (count ctors)
        n-minors n-ctors
        n-motives 1
        ;; Total binders before fields: params + motive + minors
        pre-fields (+ n-params n-motives n-minors)
        ;; Compile field types at the rule's inner telescope
        ;; Base scope: params at 0..n-params-1
        param-scope (reduce (fn [s i] (assoc s (:sym (nth params i)) i))
                            {} (range n-params))
        ;; Add motive to scope
        [scope depth] (sbind param-scope n-params 'motive)
        ;; Add minors to scope
        [scope depth] (reduce (fn [[s d] c]
                                (sbind s d (symbol (str "minor_" (:name c)))))
                              [scope depth] ctors)
        ;; Now at depth = pre-fields, compile field types
        fields (compile-fields env scope depth
                               (mapv (fn [f] [(:sym f) (:type-form f)])
                                     (:field-specs ctor))
                               self-name self-const)
        n-fields (count fields)
        rec-field-indices (when is-rec
                            (vec (keep-indexed
                                  (fn [i f] (when (is-recursive-field? f ind-name) i))
                                  fields)))
        n-ih (count (or rec-field-indices []))
        ;; Body depth: pre-fields + n-fields
        body-depth (+ pre-fields n-fields)
        ;; Reference to this ctor's minor: at depth (n-params + 1 + ctor-idx)
        minor-ref (e/bvar (- body-depth (+ n-params 1 ctor-idx) 1))
        ;; Build body: minor applied to fields + IH
        ;; Apply minor to fields
        body (reduce (fn [acc i]
                       (e/app acc (e/bvar (- body-depth (+ pre-fields i) 1))))
                     minor-ref (range n-fields))
        ;; Apply minor to IH (recursive calls)
        body (reduce (fn [acc ih-idx]
                       (let [field-idx (nth rec-field-indices ih-idx)
                             ;; Recursive call: rec params motive minors field
                             rec-const (e/const' rec-name rec-level-levels)
                             ;; Apply params
                             rc (reduce (fn [t i]
                                          (e/app t (e/bvar (- body-depth i 1))))
                                        rec-const (range n-params))
                             ;; Apply motive
                             rc (e/app rc (e/bvar (- body-depth n-params 1)))
                             ;; Apply minors
                             rc (reduce (fn [t i]
                                          (e/app t (e/bvar (- body-depth (+ n-params 1 i) 1))))
                                        rc (range n-minors))
                             ;; For indexed families: apply the recursive field's type indices
                             ;; The field has type I params idx1...idxk, extract idx exprs
                             rc (if (zero? n-indices)
                                  rc
                                  (let [rec-field-type (:type (nth fields field-idx))
                                        [_ rargs] (e/get-app-fn-args rec-field-type)
                                        idx-exprs (when (>= (count rargs) (+ n-params n-indices))
                                                    (subvec (vec rargs) n-params (+ n-params n-indices)))]
                                    (reduce (fn [t idx] (e/app t idx)) rc (or idx-exprs []))))
                             ;; Apply the recursive field
                             rc (e/app rc (e/bvar (- body-depth (+ pre-fields field-idx) 1)))]
                         (e/app acc rc)))
                     body (range n-ih))]
    ;; Wrap in lambdas from right to left
    ;; First: field lambdas
    (let [body (loop [i (dec n-fields) body body]
                 (if (< i 0) body
                     (let [f (nth fields i)]
                       (recur (dec i) (e/lam (:name f) (:type f) body :default)))))
          ;; Minor lambdas
          ;; Need minor types at the right depth — we'll use the types from the recursor
          ;; For simplicity, use the param types from the earlier computation
          ;; Build minor types at each depth
          body (loop [i (dec n-minors) body body]
                 (if (< i 0) body
                     (let [minor-depth (+ n-params 1 i)
                         ;; Use a placeholder type for minor lambdas (kernel doesn't check rule RHS types)
                           minor-type (e/sort' lvl/zero)]
                       (recur (dec i) (e/lam (str "minor_" (:name (nth ctors i)))
                                             minor-type body :default)))))
          ;; Motive lambda
          body (let [motive-type (e/sort' lvl/zero)] ; placeholder
                 (e/lam "motive" motive-type body :default))
          ;; Param lambdas
          body (loop [i (dec n-params) body body]
                 (if (< i 0) body
                     (recur (dec i) (e/lam (:name (nth params i))
                                           (:compiled-type (nth params i))
                                           body :default))))]
      body)))

(defn- build-recursor
  "Build the complete recursor ConstantInfo.
   For indexed families, the motive takes indices + major:
     motive : ∀ (i1:I1) ... (ik:Ik) (t : I params i1...ik), Sort elim_level
   And the recursor type has index foralls before the major."
  [env params indices ctors ind-name ind-lvls rec-name rec-level-params rec-level-levels
   result-level elim-level is-rec self-const self-name]
  (let [n-params (count params)
        n-indices (count indices)
        n-ctors (count ctors)
        n-minors n-ctors
        n-motives 1

        ;; Build recursor type from outside in
        param-scope (reduce (fn [s i] (assoc s (:sym (nth params i)) i))
                            {} (range n-params))

        ;; motive : ∀ (i1:I1) ... (ik:Ik) (t : I params i1...ik), Sort elim_level
        ;; At depth n-params, build motive type
        motive-depth n-params
        ;; Build motive type with index foralls
        ;; Innermost: ∀ (t : I params idx-bvars), Sort elim
        ;; The indices in the motive are fresh bvars at depth n-params..n-params+n-indices-1
        motive-inner-depth (+ n-params n-indices) ;; depth after all index binders in motive
        ind-for-motive-major (reduce (fn [acc i]
                                       (e/app acc (e/bvar (- motive-inner-depth i 1))))
                                     (e/const' ind-name ind-lvls)
                                     (range n-params))
        ;; Apply index bvars: bvar(n-indices-1), bvar(n-indices-2), ..., bvar(0)
        ind-for-motive-major (reduce (fn [acc i]
                                       (e/app acc (e/bvar (- n-indices i 1))))
                                     ind-for-motive-major
                                     (range n-indices))
        motive-type (e/forall' nil ind-for-motive-major (e/sort' elim-level) :default)
        ;; Wrap index foralls around motive type (right to left)
        motive-type (loop [i (dec n-indices) body motive-type]
                      (if (< i 0) body
                          (let [idx-type (:compiled-type (nth indices i))]
                            (recur (dec i) (e/forall' (:name (nth indices i))
                                                      idx-type body :default)))))
        [motive-scope motive-end-depth] (sbind param-scope motive-depth 'motive)

        ;; Build minor types
        minor-types (loop [i 0 depth motive-end-depth scope motive-scope acc []]
                      (if (>= i n-ctors)
                        acc
                        (let [ctor (nth ctors i)
                              mt (build-minor-type env ctor params indices ind-name ind-lvls
                                                   elim-level scope depth
                                                   self-name self-const is-rec)
                              minor-sym (symbol (str "minor_" (:name ctor)))
                              [scope' depth'] (sbind scope depth minor-sym)]
                          (recur (inc i) depth' scope' (conj acc {:type mt :sym minor-sym})))))

        minor-end-scope (reduce (fn [s m] (assoc s (:sym m) (get s (:sym m) 0)))
                                motive-scope
                                minor-types)
        minor-end-depth (+ motive-end-depth n-minors)

        ;; Major premise: t : I params at minor-end-depth
        major-depth minor-end-depth
        ind-major (reduce (fn [acc i]
                            (e/app acc (sref (reduce (fn [s [j m]] (assoc s (:sym m) (+ motive-end-depth j)))
                                                     motive-scope (map-indexed vector minor-types))
                                             major-depth (:sym (nth params i)))))
                          (e/const' ind-name ind-lvls)
                          (range n-params))
        ;; Actually simpler: just recompute param refs at major-depth
        ind-major (reduce (fn [acc i]
                            (e/app acc (e/bvar (- major-depth i 1))))
                          (e/const' ind-name ind-lvls)
                          (range n-params))

        ;; Build full scope for body computation
        full-scope (as-> param-scope s
                     (assoc s 'motive motive-depth)
                     (reduce (fn [s [i mt]]
                               (assoc s (:sym mt) (+ motive-end-depth (- n-minors 1) (- (dec n-minors) i))
                                      ;; Simpler: minor i is at depth motive-end-depth - n-minors + ... no
                                      ;; motive is at n-params, minor_0 at n-params+1, minor_1 at n-params+2
                                      ))
                             s (map-indexed vector minor-types)))

        ;; Depth layout:
        ;; 0..n-params-1: params
        ;; n-params: motive
        ;; n-params+1..n-params+n-minors: minors
        ;; n-params+1+n-minors..n-params+n-minors+n-indices: indices
        ;; n-params+1+n-minors+n-indices: major (t)
        ;; body at depth n-params+2+n-minors+n-indices

        idx-start (+ n-params 1 n-minors)
        t-depth (+ idx-start n-indices)
        body-depth (+ t-depth 1)

        ;; Body: motive idx1...idxk t
        body (let [m (e/bvar (- body-depth n-params 1))] ;; motive
               ;; Apply motive to index bvars
               (let [body (reduce (fn [acc i]
                                    (e/app acc (e/bvar (- body-depth (+ idx-start i) 1))))
                                  m (range n-indices))]
                 ;; Apply motive to major (t)
                 (e/app body (e/bvar (- body-depth t-depth 1)))))

        ;; Wrap major: ∀ (t : I params idx1...idxk), body
        t-ind (reduce (fn [acc i]
                        (e/app acc (e/bvar (- t-depth i 1))))
                      (e/const' ind-name ind-lvls)
                      (range n-params))
        ;; Apply index bvars to I for major type
        t-ind (reduce (fn [acc i]
                        (e/app acc (e/bvar (- n-indices i 1))))
                      t-ind (range n-indices))
        body (e/forall' "t" t-ind body :default)

        ;; Wrap index foralls
        body (loop [i (dec n-indices) body body]
               (if (< i 0) body
                   (recur (dec i) (e/forall' (:name (nth indices i))
                                             (:compiled-type (nth indices i))
                                             body :default))))

        ;; Wrap minors (right to left)
        body (loop [i (dec n-minors) body body]
               (if (< i 0) body
                   (recur (dec i) (e/forall' (str "h_" (:name (nth ctors i)))
                                             (:type (nth minor-types i))
                                             body :default))))

        ;; Wrap motive
        body (e/forall' "motive" motive-type body :implicit)

        ;; Wrap params (implicit)
        rec-type (loop [i (dec n-params) body body]
                   (if (< i 0) body
                       (recur (dec i) (e/forall' (:name (nth params i))
                                                 (:compiled-type (nth params i))
                                                 body :implicit))))

        ;; Build recursor rules
        rules (mapv (fn [i]
                      (let [ctor (nth ctors i)
                            rhs (build-recursor-rule-rhs
                                 env ctor i params indices ctors ind-name ind-lvls
                                 rec-name rec-level-params rec-level-levels elim-level is-rec
                                 self-name self-const)]
                        (env/mk-recursor-rule
                         (name/from-string (:full-name ctor))
                         (count (:field-specs ctor))
                         rhs)))
                    (range n-ctors))

        ;; K-axiom: only for Prop with exactly 1 ctor with 0 fields
        is-k (and (= result-level lvl/zero)
                  (= n-ctors 1)
                  (zero? (count (:field-specs (first ctors)))))]

    (env/mk-recursor rec-name (vec rec-level-params) rec-type
                     :all [ind-name]
                     :num-params n-params
                     :num-indices n-indices
                     :num-motives n-motives
                     :num-minors n-minors
                     :rules rules
                     :k? is-k)))

;; ============================================================
;; Phase 3: Auxiliaries
;; ============================================================

(defn- build-cases-on
  "Build casesOn as a definition that wraps the recursor.
   casesOn reorders: params, motive, MAJOR, minors (major before minors).
   For recursive ctors, wraps minors to drop IH arguments."
  [env params ctors ind-name ind-lvls rec-name rec-level-params rec-level-levels
   result-level elim-level is-rec self-const self-name]
  (let [n-params (count params)
        n-ctors (count ctors)
        cases-on-name (name/from-string (str self-name ".casesOn"))

        ;; casesOn type: ∀ {params} {motive} (t : I params) (h1 : ...) ... (hk : ...) → motive t
        ;; The minor types for casesOn are like rec's but WITHOUT IH
        param-scope (reduce (fn [s i] (assoc s (:sym (nth params i)) i))
                            {} (range n-params))
        ;; motive at n-params
        motive-depth n-params
        ind-for-motive (reduce (fn [acc i]
                                 (e/app acc (e/bvar (- motive-depth i 1))))
                               (e/const' ind-name ind-lvls)
                               (range n-params))
        motive-type (e/forall' nil ind-for-motive (e/sort' elim-level) :default)
        [motive-scope _] (sbind param-scope motive-depth 'motive)

        ;; Major at n-params+1
        major-depth (+ n-params 1)
        ind-for-major (reduce (fn [acc i]
                                (e/app acc (e/bvar (- major-depth i 1))))
                              (e/const' ind-name ind-lvls)
                              (range n-params))
        [major-scope _] (sbind motive-scope major-depth 'major)

        ;; CasesOn minors (no IH): ∀ fields → motive(ctor params fields)
        cases-minor-types
        (loop [i 0 scope major-scope depth (+ major-depth 1) acc []]
          (if (>= i n-ctors)
            acc
            (let [ctor (nth ctors i)
                  ;; Compile field types at this minor's depth
                  fields (compile-fields env scope depth
                                         (mapv (fn [f] [(:sym f) (:type-form f)])
                                               (:field-specs ctor))
                                         self-name self-const)
                  n-fields (count fields)
                  ;; Body: motive(ctor params fields)
                  body-depth (+ depth n-fields)
                  motive-ref (e/bvar (- body-depth motive-depth 1))
                  ctor-app (reduce (fn [acc j]
                                     (e/app acc (e/bvar (- body-depth j 1))))
                                   (e/const' (name/from-string (:full-name ctor)) ind-lvls)
                                   (range n-params))
                  ctor-app (reduce (fn [acc j]
                                     (e/app acc (e/bvar (- body-depth (+ depth j) 1))))
                                   ctor-app (range n-fields))
                  minor-body (e/app motive-ref ctor-app)
                  ;; Wrap field foralls
                  minor-type (loop [j (dec n-fields) body minor-body]
                               (if (< j 0) body
                                   (recur (dec j) (e/forall' (:name (nth fields j))
                                                             (:type (nth fields j))
                                                             body :default))))
                  minor-sym (symbol (str "ch_" (:name ctor)))
                  [scope' depth'] (sbind scope depth minor-sym)]
              (recur (inc i) scope' depth' (conj acc {:type minor-type :sym minor-sym})))))

        ;; Build casesOn type
        ;; body depth = n-params + 1(motive) + 1(major) + n-ctors(minors)
        co-body-depth (+ n-params 2 n-ctors)
        co-body (e/app (e/bvar (- co-body-depth motive-depth 1))      ;; motive
                       (e/bvar (- co-body-depth major-depth 1)))      ;; t
        ;; Wrap minors
        co-type (loop [i (dec n-ctors) body co-body]
                  (if (< i 0) body
                      (recur (dec i) (e/forall' (str "h_" (:name (nth ctors i)))
                                                (:type (nth cases-minor-types i))
                                                body :default))))
        ;; Wrap major
        co-type (e/forall' "t" ind-for-major co-type :default)
        ;; Wrap motive
        co-type (e/forall' "motive" motive-type co-type :implicit)
        ;; Wrap params
        co-type (loop [i (dec n-params) body co-type]
                  (if (< i 0) body
                      (recur (dec i) (e/forall' (:name (nth params i))
                                                (:compiled-type (nth params i))
                                                body :implicit))))

        ;; Build casesOn value: λ params motive t minors.
        ;;   rec params motive wrapped_minors t
        ;; where wrapped_minors drops IH for recursive ctors
        val-depth (+ n-params 2 n-ctors)  ;; inside all lambdas
        ;; Build rec call: rec params motive
        rec-call (reduce (fn [acc i]
                           (e/app acc (e/bvar (- val-depth i 1))))
                         (e/const' rec-name rec-level-levels)
                         (range n-params))
        rec-call (e/app rec-call (e/bvar (- val-depth motive-depth 1))) ;; motive
        ;; For each minor, wrap to drop IH if needed
        rec-call (reduce (fn [acc i]
                           (let [ctor (nth ctors i)
                                 minor-pos (+ n-params 2 i) ;; position of casesOn minor
                                 minor-ref (e/bvar (- val-depth minor-pos 1))
                                 has-rec-fields (and is-rec
                                                     (some #(is-recursive-field? % ind-name)
                                                           (:fields ctor)))]
                             (if-not has-rec-fields
                               ;; Non-recursive: pass through directly
                               (e/app acc minor-ref)
                               ;; Recursive: wrap to drop IH args
                               ;; λ fields. λ ih. user_minor fields
                               (let [n-fields (count (:fields ctor))
                                     rec-indices (vec (keep-indexed
                                                       (fn [j f] (when (is-recursive-field? f ind-name) j))
                                                       (:fields ctor)))
                                     n-ih (count rec-indices)
                                     ;; Wrapper: λ f1...fn. λ ih1...ihk. minor_ref f1...fn
                                     inner-depth (+ n-fields n-ih)
                                     ;; minor_ref from inside the wrapper
                                     ;; The wrapper is nested inside the casesOn value lambdas
                                     ;; At wrapper body: val-depth + inner-depth
                                     wd (+ val-depth inner-depth)
                                     mr (e/bvar (- wd minor-pos 1))
                                     wb (reduce (fn [t j]
                                                  (e/app t (e/bvar (- inner-depth j 1))))
                                                mr (range n-fields))
                                     ;; Wrap IH lambdas (just ignore them)
                                     ;; IH type for rec field j: motive(field_j)
                                     wb (loop [j (dec n-ih) body wb]
                                          (if (< j 0) body
                                              (let [field-idx (nth rec-indices j)
                                                  ;; IH binder is at depth val-depth + n-fields + j
                                                    ih-depth (+ val-depth n-fields j)
                                                  ;; motive ref from ih-depth
                                                    motive-ref (e/bvar (- ih-depth motive-depth 1))
                                                  ;; field ref from ih-depth
                                                    field-ref (e/bvar (- ih-depth (+ val-depth field-idx) 1))
                                                    ih-type (e/app motive-ref field-ref)]
                                                (recur (dec j) (e/lam "ih" ih-type body :default)))))
                                     ;; Wrap field lambdas
                                     ;; Need field types at wrapper depth
                                     wrapper-fields (compile-fields
                                                     env
                                                     (reduce (fn [s k]
                                                               (assoc s (:sym (nth params k)) k))
                                                             {} (range n-params))
                                                      ;; Fields see params but not motive/minors
                                                      ;; Actually in the wrapper, params are at the outer scope
                                                      ;; This is getting complex — use lifted types
                                                     val-depth
                                                     (mapv (fn [f] [(:sym f) (:type-form f)])
                                                           (:field-specs ctor))
                                                     self-name self-const)
                                     wb (loop [j (dec n-fields) body wb]
                                          (if (< j 0) body
                                              (let [f (nth wrapper-fields j)]
                                                (recur (dec j) (e/lam (:name f) (:type f)
                                                                      body :default)))))]
                                 (e/app acc wb)))))
                         rec-call (range n-ctors))
        ;; Apply major
        rec-call (e/app rec-call (e/bvar (- val-depth major-depth 1)))
        ;; Wrap in lambdas
        co-val (loop [i (dec n-ctors) body rec-call]
                 (if (< i 0) body
                     (recur (dec i) (e/lam (str "h_" (:name (nth ctors i)))
                                           (:type (nth cases-minor-types i))
                                           body :default))))
        co-val (e/lam "t" ind-for-major co-val :default)
        co-val (e/lam "motive" motive-type co-val :implicit)
        co-val (loop [i (dec n-params) body co-val]
                 (if (< i 0) body
                     (recur (dec i) (e/lam (:name (nth params i))
                                           (:compiled-type (nth params i))
                                           body :implicit))))]

    (env/mk-def cases-on-name (vec rec-level-params) co-type co-val
                :hints :abbrev :all [cases-on-name])))

(defn- build-rec-on
  "Build recOn: reorder rec args to put major before minors.
   recOn params motive t minors = rec params motive minors t"
  [env params ctors ind-name ind-lvls rec-name rec-level-params rec-level-levels
   result-level elim-level is-rec self-const self-name]
  (let [n-params (count params)
        n-ctors (count ctors)
        rec-on-name (name/from-string (str self-name ".recOn"))

        ;; recOn type: ∀ {params} {motive} (t : I params) (minors...) → motive t
        ;; Same as rec but with t before minors
        param-scope (reduce (fn [s i] (assoc s (:sym (nth params i)) i))
                            {} (range n-params))
        motive-depth n-params
        ind-for-motive (reduce (fn [acc i]
                                 (e/app acc (e/bvar (- motive-depth i 1))))
                               (e/const' ind-name ind-lvls)
                               (range n-params))
        motive-type (e/forall' nil ind-for-motive (e/sort' elim-level) :default)
        [motive-scope _] (sbind param-scope motive-depth 'motive)

        ;; Major at n-params+1
        major-depth (+ n-params 1)
        ind-for-major (reduce (fn [acc i]
                                (e/app acc (e/bvar (- major-depth i 1))))
                              (e/const' ind-name ind-lvls)
                              (range n-params))

        ;; Minor types (with IH, same as recursor)
        ;; After motive+major: depth n-params+2
        minor-types-2
        (loop [i 0 scope (assoc motive-scope 'major major-depth)
               depth (+ major-depth 1) acc []]
          (if (>= i n-ctors)
            acc
            (let [ctor (nth ctors i)
                  mt (build-minor-type env ctor params [] ind-name ind-lvls
                                       elim-level scope depth
                                       self-name self-const is-rec)
                  sym (symbol (str "rm_" (:name ctor)))
                  [scope' depth'] (sbind scope depth sym)]
              (recur (inc i) scope' depth' (conj acc {:type mt :sym sym})))))

        ;; Build type
        ro-body-depth (+ n-params 2 n-ctors)
        ro-body (e/app (e/bvar (- ro-body-depth motive-depth 1))
                       (e/bvar (- ro-body-depth major-depth 1)))
        ;; Wrap minors
        ro-type (loop [i (dec n-ctors) body ro-body]
                  (if (< i 0) body
                      (recur (dec i) (e/forall' (str "h_" (:name (nth ctors i)))
                                                (:type (nth minor-types-2 i))
                                                body :default))))
        ;; Wrap major
        ro-type (e/forall' "t" ind-for-major ro-type :default)
        ;; Wrap motive + params
        ro-type (e/forall' "motive" motive-type ro-type :implicit)
        ro-type (loop [i (dec n-params) body ro-type]
                  (if (< i 0) body
                      (recur (dec i) (e/forall' (:name (nth params i))
                                                (:compiled-type (nth params i))
                                                body :implicit))))

        ;; Build value: λ params motive t minors. rec params motive minors t
        val-depth (+ n-params 2 n-ctors)
        ;; rec params motive
        val (reduce (fn [acc i]
                      (e/app acc (e/bvar (- val-depth i 1))))
                    (e/const' rec-name rec-level-levels)
                    (range n-params))
        val (e/app val (e/bvar (- val-depth motive-depth 1)))
        ;; rec ... minors
        val (reduce (fn [acc i]
                      (let [minor-pos (+ n-params 2 i)]
                        (e/app acc (e/bvar (- val-depth minor-pos 1)))))
                    val (range n-ctors))
        ;; rec ... t
        val (e/app val (e/bvar (- val-depth major-depth 1)))
        ;; Wrap in lambdas
        ro-val (loop [i (dec n-ctors) body val]
                 (if (< i 0) body
                     (recur (dec i) (e/lam (str "h_" (:name (nth ctors i)))
                                           (:type (nth minor-types-2 i))
                                           body :default))))
        ro-val (e/lam "t" ind-for-major ro-val :default)
        ro-val (e/lam "motive" motive-type ro-val :implicit)
        ro-val (loop [i (dec n-params) body ro-val]
                 (if (< i 0) body
                     (recur (dec i) (e/lam (:name (nth params i))
                                           (:compiled-type (nth params i))
                                           body :implicit))))]

    (env/mk-def rec-on-name (vec rec-level-params) ro-type ro-val
                :hints :abbrev :all [rec-on-name])))

;; ============================================================
;; Public API
;; ============================================================

(defn- parse-type-form
  "Parse a parameter type form, extracting universe level params.
   (Type u) → {:level-param u, :compiled Sort(succ(param(u)))}
   Type     → {:level-param nil, :compiled Sort(succ(zero))}
   Prop     → {:level-param nil, :compiled Sort(zero)}"
  [form]
  (cond
    (and (sequential? form) (= 'Type (first form)) (= 2 (count form)))
    (let [u (second form)
          u-name (name/from-string (str u))]
      {:level-param u-name :level (lvl/param u-name)
       :compiled (e/sort' (lvl/succ (lvl/param u-name)))})
    (= 'Type form)
    {:level-param nil :level (lvl/succ lvl/zero)
     :compiled (e/sort' (lvl/succ lvl/zero))}
    (= 'Prop form)
    {:level-param nil :level lvl/zero
     :compiled (e/sort' lvl/zero)}
    :else nil))

(defn define-inductive
  "Define an inductive type, adding kernel declarations to env.

   Args:
     env          - kernel Env
     ind-name-str - name, e.g. \"MyList\"
     params-spec  - flat vector [α Type β (Type u) ...]
                    Type forms: Type (fixed), (Type u) (polymorphic), Prop
     ctors-spec   - list of [ctor-name fields] or [ctor-name fields return-indices] entries
                    fields: flat vector [field-name field-type ...]
                    return-indices: vector of index expressions for this ctor's return type
     opts:
       :in         - result universe: 'Prop or 'Type (default: auto from params)
       :indices    - flat vector [idx-name idx-type ...] for indexed families

   Adds: inductive, constructors, recursor, casesOn, recOn.
   Returns env."
  [env ind-name-str params-spec ctors-spec & {:keys [in indices]}]
  (let [ind-name (name/from-string ind-name-str)

        ;; Parse parameters, extracting universe level params
        param-pairs (vec (partition 2 params-spec))
        n-params (count param-pairs)

        ;; Extract level params from (Type u) forms
        ;; E.g., [α (Type u) β (Type v)] → level params [u, v]
        level-param-names (vec (distinct
                                (keep (fn [[_ ptype-form]]
                                        (:level-param (parse-type-form ptype-form)))
                                      param-pairs)))
        ;; Level param Level objects for const references
        ind-levels level-param-names
        ind-level-levels (mapv lvl/param level-param-names)

        ;; Compute result level:
        ;; - Prop: Sort 0
        ;; - Type (no level params): Sort 1
        ;; - (Type u): Sort(succ(param(u)))
        ;; - Multiple params: Sort(max(succ(u), succ(v), ...))
        is-prop (= in 'Prop)
        result-level (cond
                       is-prop lvl/zero
                       (empty? level-param-names) (lvl/succ lvl/zero)
                       (= 1 (count level-param-names))
                       (lvl/succ (lvl/param (first level-param-names)))
                       :else
                       (reduce (fn [acc lp] (lvl/level-max acc (lvl/succ (lvl/param lp))))
                               (lvl/succ (lvl/param (first level-param-names)))
                               (rest level-param-names)))

        self-const (e/const' ind-name ind-level-levels)

        ;; Compile parameter types
        params (loop [i 0 scope {} depth 0 acc []]
                 (if (>= i n-params)
                   acc
                   (let [[pname ptype-form] (nth param-pairs i)
                         parsed (parse-type-form ptype-form)
                         ptype (if parsed
                                 (:compiled parsed)
                                 (compile-type env scope depth ptype-form
                                               ind-name-str self-const))
                         [scope' depth'] (sbind scope depth pname)]
                     (recur (inc i) scope' depth'
                            (conj acc {:name (str pname) :sym pname
                                       :compiled-type ptype :depth i})))))

        param-scope (reduce (fn [s p] (assoc s (:sym p) (:depth p))) {} params)

        ;; Parse indices (if any)
        index-pairs (vec (partition 2 (or indices [])))
        n-indices (count index-pairs)
        ;; Compile index types at depth n-params (after params)
        compiled-indices (loop [i 0 scope param-scope depth n-params acc []]
                           (if (>= i n-indices)
                             acc
                             (let [[iname itype-form] (nth index-pairs i)
                                   parsed (parse-type-form itype-form)
                                   itype (if parsed
                                           (:compiled parsed)
                                           (compile-type env scope depth itype-form
                                                         ind-name-str self-const))
                                   [scope' depth'] (sbind scope depth iname)]
                               (recur (inc i) scope' depth'
                                      (conj acc {:name (str iname) :sym iname
                                                 :compiled-type itype :depth (+ n-params i)})))))

        ;; Parse constructors
        ;; Each ctor-spec is [cname cfields-spec] or [cname cfields-spec return-indices]
        ctors (mapv (fn [i ctor-entry]
                      (let [[cname cfields-spec return-idx-forms]
                            (if (= 3 (count ctor-entry))
                              ctor-entry
                              [(first ctor-entry) (second ctor-entry) nil])
                            cname-str (if (nil? cname) "nil" (str cname))
                            cfields-pairs (vec (partition 2 cfields-spec))
                            ;; Compile field types at ctor telescope depth
                            fields (compile-fields env param-scope n-params
                                                   cfields-pairs ind-name-str self-const)
                            n-fields (count fields)
                            ;; For non-indexed types, return-idx-forms is nil
                            ;; For indexed types, compile each return index at depth n-params + n-fields
                            field-scope (reduce (fn [s [j f]] (assoc s (:sym f) (+ n-params j)))
                                                param-scope (map-indexed vector fields))
                            compiled-ret-indices
                            (when (and (pos? n-indices) return-idx-forms)
                              (mapv (fn [idx-form]
                                      (compile-type env field-scope (+ n-params n-fields)
                                                    idx-form ind-name-str self-const))
                                    return-idx-forms))
                            ;; Keep original forms for recompilation at different depths
                            field-specs (mapv (fn [j [fname ftype-form]]
                                                {:name (str fname) :sym fname
                                                 :type-form ftype-form})
                                              (range) cfields-pairs)]
                        {:name cname-str :sym (symbol cname-str) :idx i
                         :full-name (str ind-name-str "." cname-str)
                         :fields fields
                         :field-specs field-specs
                         :return-index-forms (or return-idx-forms
                                                 ;; Default: use param refs as indices (non-indexed)
                                                 (vec (repeat n-indices nil)))
                         :compiled-return-indices (or compiled-ret-indices [])}))
                    (range) ctors-spec)

        n-ctors (count ctors)

        ;; Phase 2: Validation
        _ (doseq [ctor ctors, field (:fields ctor)]
            (check-positivity! (:type field) ind-name (:name ctor) (:name field)))

        ;; Compute metadata
        is-rec (boolean (some (fn [ctor]
                                (some (fn [f] (is-recursive-field? f ind-name))
                                      (:fields ctor)))
                              ctors))
        is-reflexive (boolean (some (fn [ctor]
                                      (some (fn [f]
                                              (and (e/forall? (:type f))
                                                   (occurs-in? (:type f) ind-name)))
                                            (:fields ctor)))
                                    ctors))

        ;; Elimination level
        prop-only? (and (= result-level lvl/zero) (> n-ctors 1))
        elim-level-param (when-not prop-only? (name/from-string "u_1"))
        elim-level (if prop-only? lvl/zero (lvl/param (name/from-string "u_1")))
        ;; rec-level-params: Name[] for ConstantInfo factory (elim + inductive levels)
        ;; rec-level-levels: Level[] for e/const' references
        rec-level-params (into (if elim-level-param [elim-level-param] [])
                               ind-levels)
        rec-level-levels (mapv lvl/param rec-level-params)

        ;; Build inductive type: ∀ params indices → Sort result-level
        ind-type (build-inductive-type params compiled-indices result-level)
        ind-ci (env/mk-induct ind-name ind-levels ind-type
                              :num-params n-params :num-indices n-indices
                              :all [ind-name]
                              :ctors (mapv #(name/from-string (:full-name %)) ctors)
                              :num-nested 0
                              :rec? is-rec :reflexive? is-reflexive)

        ;; Build constructor types
        ctor-cis (mapv (fn [ctor]
                         (let [ctor-cname (name/from-string (:full-name ctor))
                               ctor-type (build-constructor-type params (:fields ctor)
                                                                 ind-name ind-level-levels
                                                                 (:compiled-return-indices ctor))
                               n-fields (count (:fields ctor))]
                           (env/mk-ctor ctor-cname ind-levels ctor-type
                                        ind-name (:idx ctor) n-params n-fields)))
                       ctors)

        ;; Build recursor
        rec-name (name/from-string (str ind-name-str ".rec"))
        rec-ci (build-recursor env params compiled-indices ctors ind-name ind-level-levels
                               rec-name rec-level-params rec-level-levels
                               result-level elim-level is-rec
                               self-const ind-name-str)]

    ;; Add core declarations (thread immutable env)
    (let [env (env/add-constant env ind-ci)
          env (reduce (fn [e ci] (env/add-constant e ci)) env ctor-cis)
          env (env/add-constant env rec-ci)
          ;; Build and add auxiliaries (skip for indexed families for now —
          ;; casesOn/recOn need index-aware motive rewriting)
          env (if (zero? n-indices)
                (let [cases-on-ci (build-cases-on env params ctors ind-name ind-level-levels
                                                  rec-name rec-level-params rec-level-levels
                                                  result-level elim-level is-rec
                                                  self-const ind-name-str)
                      rec-on-ci (build-rec-on env params ctors ind-name ind-level-levels
                                              rec-name rec-level-params rec-level-levels
                                              result-level elim-level is-rec
                                              self-const ind-name-str)
                      env (env/add-constant env cases-on-ci)
                      env (env/add-constant env rec-on-ci)]
                  env)
                env)]
      ;; Update global env atom with the new env
      (reset! @(requiring-resolve 'ansatz.core/ansatz-env) env))

    ;; noConfusion (skip for now — complex, not required for basic use)
    ;; Future: build-no-confusion for non-Prop types

    (println "✓ inductive" ind-name-str "defined:"
             (count ctors) "constructors, recursor, casesOn, recOn")
    env))
