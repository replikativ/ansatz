;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; Ansatz kernel for Clojure — Reduction machinery (WHNF).

(ns ansatz.kernel.reduce
  "WHNF reduction: beta, delta, iota (recursor), zeta (let),
   projection reduction, nat/string literal reduction, and quotient reduction.
   Follows Lean 4's kernel type_checker.cpp reduction strategy."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.config :as config])
  (:import [ansatz.kernel Name ConstantInfo ConstantInfo$RecursorRule Env]))

;; ============================================================
;; Local context (for fvars during type checking)
;; ============================================================

(defn empty-lctx [] {})

(defn lctx-add-local
  "Add a local declaration (assumption) to the local context."
  [lctx id name type]
  (assoc lctx id {:tag :local :id id :name name :type type}))

(defn lctx-add-let
  "Add a let-binding to the local context."
  [lctx id name type value]
  (assoc lctx id {:tag :let-decl :id id :name name :type type :value value}))

(defn lctx-lookup [lctx id]
  (get lctx id))

;; ============================================================
;; Level parameter instantiation helper
;; ============================================================

(defn- make-level-subst
  "Create a level substitution map from level-param-names and concrete levels."
  [param-names levels]
  (into {} (map vector param-names levels)))

;; ============================================================
;; Nat literal reduction
;; ============================================================

(def ^:private nat-binop-names
  #{Name/NAT_ADD Name/NAT_SUB Name/NAT_MUL Name/NAT_DIV Name/NAT_MOD
    Name/NAT_POW Name/NAT_GCD Name/NAT_BEQ Name/NAT_BLE
    Name/NAT_LAND Name/NAT_LOR Name/NAT_XOR
    Name/NAT_SHIFT_LEFT Name/NAT_SHIFT_RIGHT})

(defn- nat-lit->constructor
  "Convert a Nat literal to constructor form for recursor matching.
   0 → Nat.zero, n → Nat.succ (n-1)"
  [n]
  (if (zero? n)
    (e/const' Name/NAT_ZERO [])
    (e/app (e/const' Name/NAT_SUCC []) (e/lit-nat (dec n)))))

(defn- reduce-nat-binop
  "Try to reduce a nat binary operation on two literals."
  [^Name op-name a b]
  (when (and (e/lit-nat? a) (e/lit-nat? b))
    (let [va (e/lit-nat-val a)
          vb (e/lit-nat-val b)]
      (condp identical? op-name
        Name/NAT_ADD (e/lit-nat (+ va vb))
        Name/NAT_SUB (e/lit-nat (max 0 (- va vb)))
        Name/NAT_MUL (e/lit-nat (* va vb))
        Name/NAT_DIV (if (zero? vb) (e/lit-nat 0) (e/lit-nat (quot va vb)))
        Name/NAT_MOD (if (zero? vb) (e/lit-nat va) (e/lit-nat (mod va vb)))
        Name/NAT_POW (e/lit-nat (.pow (biginteger va) (int vb)))
        Name/NAT_GCD (e/lit-nat (loop [a va b vb] (if (zero? b) a (recur b (mod a b)))))
        Name/NAT_BEQ (if (= va vb) (e/const' Name/BOOL_TRUE []) (e/const' Name/BOOL_FALSE []))
        Name/NAT_BLE (if (<= va vb) (e/const' Name/BOOL_TRUE []) (e/const' Name/BOOL_FALSE []))
        Name/NAT_LAND (e/lit-nat (.and (biginteger va) (biginteger vb)))
        Name/NAT_LOR  (e/lit-nat (.or (biginteger va) (biginteger vb)))
        Name/NAT_XOR  (e/lit-nat (.xor (biginteger va) (biginteger vb)))
        Name/NAT_SHIFT_LEFT  (e/lit-nat (.shiftLeft (biginteger va) (int vb)))
        Name/NAT_SHIFT_RIGHT (e/lit-nat (.shiftRight (biginteger va) (int vb)))
        nil))))

(defn- whnf-to-nat
  "Fully normalize an expression to a lit-nat, following Nat.succ chains."
  [whnf-fn e]
  (let [e' (whnf-fn e)]
    (cond
      (e/lit-nat? e') e'
      (and (e/app? e')
           (e/const? (e/app-fn e'))
           (identical? Name/NAT_SUCC (e/const-name (e/app-fn e'))))
      (when-let [inner (whnf-to-nat whnf-fn (e/app-arg e'))]
        (e/lit-nat (inc (e/lit-nat-val inner))))
      (and (e/const? e') (identical? Name/NAT_ZERO (e/const-name e')))
      (e/lit-nat 0)
      :else nil)))

(defn- try-reduce-nat
  "Try to reduce a nat operation."
  [head args whnf-fn]
  (when (and (e/const? head) (= 2 (count args)))
    (let [op-name (e/const-name head)]
      (when (nat-binop-names op-name)
        (let [a (whnf-to-nat whnf-fn (first args))
              b (whnf-to-nat whnf-fn (second args))]
          (when (and a b)
            (reduce-nat-binop op-name a b)))))))

;; ============================================================
;; Iota reduction (recursor application)
;; ============================================================

(defn- mk-nullary-cnstr
  "For K-recursors: create the nullary constructor from the major premise's type."
  [^Env env major-type num-params]
  (let [[type-head type-args] (e/get-app-fn-args major-type)]
    (when (and (e/const? type-head) (>= (count type-args) num-params))
      (let [ind-name (e/const-name type-head)
            ^ConstantInfo ind-ci (env/lookup env ind-name)]
        (when (and ind-ci (.isInduct ind-ci) (= 1 (alength (.ctors ind-ci))))
          (let [ctor-name (aget (.ctors ind-ci) 0)
                ^ConstantInfo ctor-ci (env/lookup env ctor-name)]
            (when (and ctor-ci (.isCtor ctor-ci) (zero? (.numFields ctor-ci)))
              (let [params (subvec (vec type-args) 0 num-params)]
                (reduce e/app (e/const' ctor-name (e/const-levels type-head)) params)))))))))

(defn- try-reduce-recursor
  "Try iota reduction: apply a recursor to a constructor."
  [^Env env head args whnf-fn infer-fn is-def-eq-fn]
  (when (e/const? head)
    (when-let [^ConstantInfo ci (env/lookup env (e/const-name head))]
      (when (.isRecursor ci)
        (let [num-params (.numParams ci)
              num-motives (.numMotives ci)
              num-minors (.numMinors ci)
              num-indices (.numIndices ci)
              ^"[Lansatz.kernel.ConstantInfo$RecursorRule;" rules (.rules ci)
              is-k (.isK ci)
              expected-args (+ num-params num-motives num-minors num-indices 1)]
          (when (>= (count args) expected-args)
            (let [major-idx (+ num-params num-motives num-minors num-indices)
                  major (if whnf-fn (whnf-fn env (nth args major-idx)) (nth args major-idx))
                  extra-args (subvec (vec args) (inc major-idx))
                  [ctor-head ctor-args] (e/get-app-fn-args major)
                  ctor-head (if (e/lit-nat? major)
                              (let [expanded (nat-lit->constructor (e/lit-nat-val major))]
                                (e/get-app-fn expanded))
                              ctor-head)
                  ;; Find matching rule
                  direct-rule (when (e/const? ctor-head)
                                (let [cn (e/const-name ctor-head)]
                                  (loop [i 0]
                                    (when (< i (alength rules))
                                      (let [^ConstantInfo$RecursorRule r (aget rules i)]
                                        (if (= cn (.ctor r))
                                          r
                                          (recur (inc i))))))))
                  [major ctor-head ctor-args]
                  (if (and is-k (not direct-rule) infer-fn is-def-eq-fn)
                    (try
                      (let [major-type (whnf-fn env (infer-fn major))
                            new-cnstr (mk-nullary-cnstr env major-type num-params)]
                        (if (and new-cnstr
                                 (let [new-type (infer-fn new-cnstr)]
                                   (is-def-eq-fn major-type new-type)))
                          (let [[ch ca] (e/get-app-fn-args new-cnstr)]
                            [new-cnstr ch ca])
                          [major ctor-head ctor-args]))
                      (catch Exception _ [major ctor-head ctor-args]))
                    [major ctor-head ctor-args])]
              (when (e/const? ctor-head)
                (let [ctor-name (e/const-name ctor-head)
                      ^ConstantInfo$RecursorRule rule
                      (or direct-rule
                          (loop [i 0]
                            (when (< i (alength rules))
                              (let [^ConstantInfo$RecursorRule r (aget rules i)]
                                (if (= ctor-name (.ctor r))
                                  r
                                  (recur (inc i)))))))]
                  (when rule
                    (let [subst (make-level-subst (vec (.levelParams ci)) (e/const-levels head))
                          rhs (e/instantiate-level-params (.rhs rule) subst)
                          params (subvec (vec args) 0 num-params)
                          motives (subvec (vec args) num-params (+ num-params num-motives))
                          minors (subvec (vec args) (+ num-params num-motives) (+ num-params num-motives num-minors))
                          actual-ctor-args (if (e/lit-nat? major)
                                             (let [expanded (nat-lit->constructor (e/lit-nat-val major))]
                                               (e/get-app-args expanded))
                                             (let [^ConstantInfo ci-ctor (env/lookup env ctor-name)
                                                   ctor-num-params (if ci-ctor (.numParams ci-ctor) num-params)]
                                               (subvec (vec ctor-args) ctor-num-params)))
                          result (reduce e/app rhs (concat params motives minors actual-ctor-args))]
                      (reduce e/app result extra-args))))))))))))

;; ============================================================
;; Quotient reduction
;; ============================================================

(defn- try-reduce-quot
  "Try quotient reduction."
  [^Env env head args]
  (when (and (e/const? head) (env/quot-enabled? env))
    (let [^Name name (e/const-name head)]
      (cond
        (identical? name Name/QUOT_LIFT)
        (when (>= (count args) 6)
          (let [q (nth args 5)
                [q-head q-args] (e/get-app-fn-args q)]
            (when (and (e/const? q-head)
                       (identical? Name/QUOT_MK (e/const-name q-head))
                       (>= (count q-args) 3))
              (let [f (nth args 3)
                    a (nth q-args 2)
                    result (e/app f a)]
                (reduce e/app result (subvec (vec args) 6))))))

        (identical? name Name/QUOT_IND)
        (when (>= (count args) 6)
          (let [q (nth args 5)
                [q-head q-args] (e/get-app-fn-args q)]
            (when (and (e/const? q-head)
                       (identical? Name/QUOT_MK (e/const-name q-head))
                       (>= (count q-args) 3))
              (let [p (nth args 3)
                    a (nth q-args 2)
                    result (e/app p a)]
                (reduce e/app result (subvec (vec args) 6))))))

        :else nil))))

;; ============================================================
;; Projection reduction
;; ============================================================

(defn- try-reduce-proj
  "Try to reduce a projection."
  [^Env env e whnf-fn]
  (when (e/proj? e)
    (let [struct (whnf-fn env (e/proj-struct e))
          [head args] (e/get-app-fn-args struct)]
      (when (e/const? head)
        (when-let [^ConstantInfo ci (env/lookup env (e/const-name head))]
          (when (.isCtor ci)
            (let [field-start (.numParams ci)
                  field-idx (+ field-start (e/proj-idx e))]
              (when (< field-idx (count args))
                (nth args field-idx)))))))))

;; ============================================================
;; Delta reduction (definition unfolding)
;; ============================================================

(defn- try-unfold-def
  "Try to unfold a definition. Returns the unfolded body or nil."
  [^Env env head]
  (when (e/const? head)
    (when-let [^ConstantInfo ci (env/lookup env (e/const-name head))]
      (when-let [value (.getValue ci)]
        (let [subst (make-level-subst (vec (.levelParams ci)) (e/const-levels head))]
          (e/instantiate-level-params value subst))))))

;; ============================================================
;; WHNF: Weak Head Normal Form
;; ============================================================

(declare whnf)

(def ^:dynamic *whnf-fuel* nil)

(def ^:private ^ThreadLocal whnf-depth-tl
  (ThreadLocal/withInitial (reify java.util.function.Supplier (get [_] (int-array 1)))))
;; Use config/*max-whnf-depth* (default 512) — read at call site via deref

(defn- check-fuel! []
  (when *whnf-fuel*
    (let [remaining (swap! *whnf-fuel* dec)]
      (when (neg? remaining)
        (throw (ex-info "WHNF reduction fuel exhausted" {:cause :fuel-exhausted}))))))

(defn- whnf-core
  "Reduce to WHNF without delta unfolding."
  [env e lctx opts]
  (case (e/tag e)
    (:bvar :sort :lam :forall :lit-nat :lit-str) e
    :fvar (if-let [decl (when lctx (lctx-lookup lctx (e/fvar-id e)))]
            (if-let [v (:value decl)]
              (do (check-fuel!) (recur env v lctx opts))
              e)
            e)
    :const (if (identical? Name/NAT_ZERO (e/const-name e))
             (e/lit-nat 0)
             e)
    :mdata (do (check-fuel!) (recur env (e/mdata-expr e) lctx opts))
    :let (do (check-fuel!) (recur env (e/instantiate1 (e/let-body e) (e/let-value e)) lctx opts))
    :proj (if-let [r (try-reduce-proj env e (fn [env e] (whnf env e lctx opts)))]
            (recur env r lctx opts)
            e)
    :app (let [[head args] (e/get-app-fn-args e)
               head' (whnf-core env head lctx opts)]
           (cond
             (e/lam? head')
             (do (check-fuel!)
                 (let [result (loop [f head' args args]
                                (if (and (e/lam? f) (seq args))
                                  (recur (e/instantiate1 (e/lam-body f) (first args))
                                         (rest args))
                                  (reduce e/app f args)))]
                   (recur env result lctx opts)))
             :else
             (if-let [reduced (or (try-reduce-recursor env head' args nil nil nil)
                                  (try-reduce-quot env head' args))]
               (do (check-fuel!) (recur env reduced lctx opts))
               (if (and (e/const? head')
                        (identical? Name/NAT_SUCC (e/const-name head'))
                        (= 1 (count args)))
                 (let [arg (first args)]
                   (cond
                     (e/lit-nat? arg) (e/lit-nat (inc (e/lit-nat-val arg)))
                     :else (let [arg' (whnf-core env arg lctx opts)]
                             (if (e/lit-nat? arg')
                               (e/lit-nat (inc (e/lit-nat-val arg')))
                               (if (= head head')
                                 e
                                 (reduce e/app head' args))))))
                 (if (= head head')
                   e
                   (reduce e/app head' args))))))))

(defn whnf-no-delta
  "Reduce to WHNF without delta unfolding (definition expansion).
   Does: beta, let expansion, fvar-let, projection, iota (recursor on ctor),
   Nat.succ folding, Nat.zero → lit 0.
   Does NOT: unfold named constants (delta).
   This matches Lean 4's 'reducible transparency' behavior used by simp."
  ([env e] (whnf-no-delta env e nil))
  ([env e lctx] (whnf-no-delta env e lctx nil))
  ([env e lctx opts] (whnf-core env e lctx opts)))

(defn whnf
  "Reduce expression to weak head normal form."
  ([env e] (whnf env e nil))
  ([env e lctx] (whnf env e lctx nil))
  ([env e lctx opts]
   (let [^ints depth-arr (.get whnf-depth-tl)
         d (aget depth-arr 0)]
     (when (>= d config/*max-whnf-depth*)
       (throw (ex-info "WHNF depth limit exceeded" {:cause :depth-exceeded})))
     (aset depth-arr 0 (inc d))
     (try
       (let [infer-fn (:infer-fn opts)
             is-def-eq-fn (:is-def-eq-fn opts)
             whnf-fn (fn [env e] (whnf env e lctx opts))]
         (loop [e (whnf-core env e lctx opts)]
           (let [[head args] (e/get-app-fn-args e)
                 nat-result (try-reduce-nat head args #(whnf env % lctx opts))]
             (if nat-result
               (recur (whnf-core env nat-result lctx opts))
               (let [unfolded (try-unfold-def env head)]
                 (if unfolded
                   (do (check-fuel!)
                       (recur (whnf-core env (reduce e/app unfolded args) lctx opts)))
                   (let [iota-result (try-reduce-recursor env head args
                                                          whnf-fn infer-fn is-def-eq-fn)]
                     (if iota-result
                       (do (check-fuel!) (recur (whnf-core env iota-result lctx opts)))
                       (if (and (e/const? head)
                                (identical? Name/NAT_SUCC (e/const-name head))
                                (= 1 (count args)))
                         (let [arg-whnf (whnf env (first args) lctx opts)]
                           (if (e/lit-nat? arg-whnf)
                             (e/lit-nat (inc (e/lit-nat-val arg-whnf)))
                             e))
                         e)))))))))
       (finally
         (aset depth-arr 0 d))))))
