;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; Ansatz kernel for Clojure — Type checker: infer, check, is-def-eq.

(ns ansatz.kernel.tc
  "Type checker implementing bidirectional type inference and
   definitional equality for the Calculus of Inductive Constructions.
   Follows Lean 4's kernel type_checker.cpp."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.reduce :as red])
  (:import [ansatz.kernel Name ConstantInfo Env]))

;; ============================================================
;; Type checker state
;; ============================================================

(defn mk-tc-state
  "Create a fresh type checker state."
  [env]
  {:env env
   :lctx (red/empty-lctx)
   :next-id (atom 0)
   :whnf-cache (atom {})
   :def-eq-cache (atom #{})
   :def-neq-cache (atom #{})
   :infer-cache (java.util.IdentityHashMap.)})

(defn- fresh-id! [st]
  (swap! (:next-id st) inc)
  @(:next-id st))

(declare infer-type is-def-eq)

(defn- cached-whnf [st e]
  (let [opts {:infer-fn (fn [e] (#'infer-type st e))
              :is-def-eq-fn (fn [a b] (#'is-def-eq st a b))}]
    (if (e/has-fvar-flag e)
      (red/whnf (:env st) e (:lctx st) opts)
      (if-let [cached (get @(:whnf-cache st) e)]
        cached
        (let [result (red/whnf (:env st) e (:lctx st) opts)]
          (swap! (:whnf-cache st) assoc e result)
          result)))))

;; ============================================================
;; Error helpers
;; ============================================================

(defn- tc-error! [msg data]
  (throw (ex-info (str "Type error: " msg) (merge {:kind :type-error} data))))

;; ============================================================
;; Type inference
;; ============================================================

(declare infer-type is-def-eq is-def-eq* ensure-sort ensure-pi try-eta)

(defn infer-type
  "Infer the type of expression e in type checker state st."
  [st e]
  (let [^java.util.IdentityHashMap cache (:infer-cache st)
        cached (.get cache e)]
    (if (some? cached)
      cached
      (let [result
            (case (e/tag e)
              :bvar (tc-error! "Loose bound variable in infer-type" {:expr e})

              :sort (e/sort' (lvl/succ (e/sort-level e)))

              :const (let [^ConstantInfo ci (env/lookup! (:env st) (e/const-name e))
                           levels (e/const-levels e)
                           expected-params (alength (.levelParams ci))
                           actual-params (count levels)]
                       (when (not= expected-params actual-params)
                         (tc-error! "Universe level mismatch"
                                    {:name (e/const-name e)
                                     :expected expected-params
                                     :actual actual-params}))
                       (let [subst (into {} (map vector (vec (.levelParams ci)) levels))]
                         (e/instantiate-level-params (.type ci) subst)))

              :app (let [fn-type (cached-whnf st (infer-type st (e/app-fn e)))
                         [dom-name dom-type body info] (ensure-pi st fn-type)
                         arg-type (infer-type st (e/app-arg e))]
                     (when-not (is-def-eq st arg-type dom-type)
                       (tc-error! "Type mismatch in application"
                                  {:expected dom-type :actual arg-type :fn (e/app-fn e) :arg (e/app-arg e)}))
                     (e/instantiate1 body (e/app-arg e)))

              :lam (let [dom-type (e/lam-type e)
                         _ (ensure-sort st (infer-type st dom-type))
                         fv-id (fresh-id! st)
                         fv (e/fvar fv-id)
                         st' (update st :lctx red/lctx-add-local fv-id (e/lam-name e) dom-type)
                         body (e/instantiate1 (e/lam-body e) fv)
                         body-type (infer-type st' body)
                         abs-body-type (e/abstract1 body-type fv-id)]
                     (e/forall' (e/lam-name e) dom-type abs-body-type (e/lam-info e)))

              :forall (let [dom-type (e/forall-type e)
                            dom-sort (ensure-sort st (infer-type st dom-type))
                            dom-level (e/sort-level dom-sort)
                            fv-id (fresh-id! st)
                            fv (e/fvar fv-id)
                            st' (update st :lctx red/lctx-add-local fv-id (e/forall-name e) dom-type)
                            body (e/instantiate1 (e/forall-body e) fv)
                            cod-sort (ensure-sort st' (infer-type st' body))
                            cod-level (e/sort-level cod-sort)]
                        (e/sort' (lvl/imax dom-level cod-level)))

              :let (let [val-type (infer-type st (e/let-value e))
                         _ (ensure-sort st (infer-type st (e/let-type e)))
                         _ (when-not (is-def-eq st val-type (e/let-type e))
                             (tc-error! "Let value type mismatch"
                                        {:expected (e/let-type e) :actual val-type}))
                         fv-id (fresh-id! st)
                         fv (e/fvar fv-id)
                         st' (update st :lctx red/lctx-add-let fv-id (e/let-name e) (e/let-type e) (e/let-value e))
                         body (e/instantiate1 (e/let-body e) fv)
                         body-type (infer-type st' body)]
                     (e/instantiate1 (e/abstract1 body-type fv-id) (e/let-value e)))

              :lit-nat (e/const' Name/NAT [])

              :lit-str (e/const' Name/STRING [])

              :mdata (infer-type st (e/mdata-expr e))

              :proj (let [struct-type (cached-whnf st (infer-type st (e/proj-struct e)))
                          [head args] (e/get-app-fn-args struct-type)]
                      (when-not (e/const? head)
                        (tc-error! "Projection target not an inductive" {:type struct-type :proj e}))
                      (let [^ConstantInfo ind-ci (env/lookup! (:env st) (e/const-name head))]
                        (when-not (.isInduct ind-ci)
                          (tc-error! "Projection target not an inductive" {:type struct-type}))
                        (when (not= 1 (alength (.ctors ind-ci)))
                          (tc-error! "Projection on non-structure inductive" {:name (e/const-name head)}))
                        (let [ctor-name (aget (.ctors ind-ci) 0)
                              ^ConstantInfo ctor-ci (env/lookup! (:env st) ctor-name)
                              ctor-type (.type ctor-ci)
                              subst (into {} (map vector (vec (.levelParams ctor-ci)) (e/const-levels head)))
                              ctor-type (e/instantiate-level-params ctor-type subst)
                              num-params (.numParams ctor-ci)
                              params (subvec (vec args) 0 (min num-params (count args)))
                              peeled (loop [t ctor-type ps params]
                                       (if (and (seq ps) (e/forall? t))
                                         (recur (e/instantiate1 (e/forall-body t) (first ps))
                                                (rest ps))
                                         t))
                              field-idx (e/proj-idx e)]
                          (loop [t peeled i 0]
                            (if (and (e/forall? t) (< i field-idx))
                              (recur (e/instantiate1 (e/forall-body t) (e/proj (e/proj-type-name e) i (e/proj-struct e)))
                                     (inc i))
                              (if (e/forall? t)
                                (e/forall-type t)
                                (tc-error! "Not enough fields in constructor" {:idx field-idx :type t})))))))

              :fvar (let [decl (red/lctx-lookup (:lctx st) (e/fvar-id e))]
                      (if decl
                        (:type decl)
                        (tc-error! "Unknown free variable" {:id (e/fvar-id e)}))))]
        (.put cache e result)
        result))))

(defn ensure-sort
  "Ensure e is (or reduces to) a Sort. Returns the sort."
  [st e]
  (let [e' (cached-whnf st e)]
    (if (e/sort? e')
      e'
      (tc-error! "Expected a sort (Type/Prop)" {:got e'}))))

(defn ensure-pi
  "Ensure e is (or reduces to) a Pi/forall type."
  [st e]
  (let [e' (cached-whnf st e)]
    (if (e/forall? e')
      [(e/forall-name e') (e/forall-type e') (e/forall-body e') (e/forall-info e')]
      (tc-error! "Expected a function type (Pi/forall)" {:got e'}))))

;; ============================================================
;; Definitional equality
;; ============================================================

(defn- is-sort-zero?
  "Check if expr reduces to Sort 0 (Prop)."
  [st expr]
  (let [t (cached-whnf st expr)]
    (and (e/sort? t) (lvl/level-zero? (e/sort-level t)))))

(defn- is-prop?
  "Check if expr is a proposition, i.e., its type is Prop.
   Matches Lean 4: is_prop(e) = (whnf(infer_type(e)) == mk_Prop()).
   A proposition is something like (Eq Nat 1 1) whose type is Prop."
  [st expr]
  (is-sort-zero? st (infer-type st expr)))

(defn- proof-irrelevant?
  "Check if both terms are proofs of the same Prop.
   Lean 4: two terms t,s are proof-irrelevant equal iff
   type(t) is a proposition (lives in Prop) and type(t) = type(s).
   This means t and s are PROOFS (values of propositions), not propositions themselves."
  [st t s]
  (try
    (let [tt (infer-type st t)]
      (when (is-prop? st tt)
        (let [ts (infer-type st s)]
          (is-def-eq st tt ts))))
    (catch Exception _ false)))

(defn is-def-eq
  "Check definitional equality of two expressions."
  [st t s]
  (or (identical? t s)
      (= t s)
      (contains? @(:def-eq-cache st) [t s])
      (contains? @(:def-eq-cache st) [s t])
      (when-not (or (contains? @(:def-neq-cache st) [t s])
                    (contains? @(:def-neq-cache st) [s t]))
        (let [result (is-def-eq* st t s)]
          (if result
            (swap! (:def-eq-cache st) conj [t s])
            (swap! (:def-neq-cache st) conj [t s]))
          result))))

(defn- is-def-eq*
  "Core definitional equality check."
  [st t s]
  (let [t' (cached-whnf st t)
        s' (cached-whnf st s)]
    (or
     (= t' s')

     (and (= (e/tag t') (e/tag s'))
          (case (e/tag t')
            :sort (lvl/level= (e/sort-level t') (e/sort-level s'))

            :const (and (= (e/const-name t') (e/const-name s'))
                        (= (count (e/const-levels t')) (count (e/const-levels s')))
                        (every? true? (map lvl/level= (e/const-levels t') (e/const-levels s'))))

            :app (and (is-def-eq st (e/app-fn t') (e/app-fn s'))
                      (is-def-eq st (e/app-arg t') (e/app-arg s')))

            :lam (let [fv-id (fresh-id! st)
                       fv (e/fvar fv-id)
                       st' (update st :lctx red/lctx-add-local fv-id nil (e/lam-type t'))]
                   (and (is-def-eq st (e/lam-type t') (e/lam-type s'))
                        (is-def-eq st'
                                   (e/instantiate1 (e/lam-body t') fv)
                                   (e/instantiate1 (e/lam-body s') fv))))

            :forall (let [fv-id (fresh-id! st)
                          fv (e/fvar fv-id)
                          st' (update st :lctx red/lctx-add-local fv-id nil (e/forall-type t'))]
                      (and (is-def-eq st (e/forall-type t') (e/forall-type s'))
                           (is-def-eq st'
                                      (e/instantiate1 (e/forall-body t') fv)
                                      (e/instantiate1 (e/forall-body s') fv))))

            :proj (and (= (e/proj-type-name t') (e/proj-type-name s'))
                       (= (e/proj-idx t') (e/proj-idx s'))
                       (is-def-eq st (e/proj-struct t') (e/proj-struct s')))

            :fvar (= (e/fvar-id t') (e/fvar-id s'))

            (:lit-nat :lit-str :bvar) (= t' s')

            false))

     (try-eta st t' s')
     (try-eta st s' t')

     (proof-irrelevant? st t' s'))))

(defn- try-eta
  "Try eta expansion."
  [st t s]
  (cond
    (and (e/lam? s) (not (e/lam? t)))
    (let [fv-id (fresh-id! st)
          fv (e/fvar fv-id)
          st' (update st :lctx red/lctx-add-local fv-id nil (e/lam-type s))]
      (is-def-eq st'
                 (e/app (e/lift t 1 0) fv)
                 (e/instantiate1 (e/lam-body s) fv)))
    :else false))

;; ============================================================
;; Declaration checking
;; ============================================================

(defn check-constant
  "Type-check a ConstantInfo and add it to the environment.
   Returns the updated environment."
  [^Env env ^ConstantInfo ci]
  (let [st (mk-tc-state env)]
    (ensure-sort st (infer-type st (.type ci)))
    (when-let [value (.value ci)]
      (when (or (.isDef ci) (.isThm ci) (.isOpaq ci))
        (let [inferred (infer-type st value)]
          (when-not (is-def-eq st inferred (.type ci))
            (tc-error! "Declaration value type does not match declared type"
                       {:name (.name ci)
                        :declared (.type ci)
                        :inferred inferred})))))
    (env/add-constant env ci)))
