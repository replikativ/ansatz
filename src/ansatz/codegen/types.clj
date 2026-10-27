(ns ansatz.codegen.types
  "Runtime erasure following Lean v4.33.1 (55f80e10a3) Compiler/LCNF/ToLCNF.lean
   visit, visitAppArg and isTypeFormerType; Types.lean erased;
   Meta/Basic.lean mkLetFVars and Meta/WHNF.lean whnfEasyCases (LocalDecl.ldecl)."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel TypeChecker Level]))

(defn bind-type [names n type]
  (with-meta (conj names n)
    (assoc (meta names) (count names) type)))

(defn bind-let [names n type value]
  (let [ctx (bind-type names n type)]
    (with-meta ctx (assoc-in (meta ctx) [::values (count names)] value))))

(defn whnf [env expr names]
  ;; Zeta-unfold let-decls while retaining the indices of ordinary locals.
  (let [values (::values (meta names))
        args (when (seq values)
               (reduce (fn [args i]
                         (conj args (if-let [value (get values i)]
                                      (e/instantiate value args)
                                      (e/bvar (- (count names) i 1)))))
                       [] (range (count names))))]
    (.whnf (.getReducer (TypeChecker. env))
           (if args (e/instantiate expr args) expr))))

(declare infer-type)

(defn infer-type
  "Infer in the code generator's de Bruijn context. Synthetic recursor locals
   without a recorded domain have no type here; constant applications still
   obtain their result type from the instantiated declaration telescope."
  [env expr names]
  (cond
    ;; Codegen lowerings can also be exercised with a minimal metadata env.
    ;; Missing declarations or omitted universe arguments do not establish a
    ;; type; leave those raw lowering probes to their registered handlers.
    (e/const? expr)
    (when-let [ci (env/lookup env (e/const-name expr))]
      (when (= (count (env/ci-level-params ci)) (count (e/const-levels expr)))
        (.inferType (TypeChecker. env) expr)))
    (e/lit-nat? expr) (when (env/lookup env (name/from-string "Nat"))
                        (.inferType (TypeChecker. env) expr))
    (e/lit-str? expr) (when (env/lookup env (name/from-string "String"))
                        (.inferType (TypeChecker. env) expr))
    (e/sort? expr) (.inferType (TypeChecker. env) expr)
    (e/bvar? expr)
    (let [i (e/bvar-idx expr) pos (- (count names) i 1)]
      (when-let [t (get (meta names) pos)] (e/lift t (inc i) 0)))
    (e/app? expr)
    (when-let [t (infer-type env (e/app-fn expr) names)]
      (let [t (whnf env t names)]
        (when (e/forall? t) (e/instantiate1 (e/forall-body t) (e/app-arg expr)))))
    (e/lam? expr)
    (when-let [t (infer-type env (e/lam-body expr)
                             (bind-type names "_" (e/lam-type expr)))]
      (e/forall' (e/lam-name expr) (e/lam-type expr) t (e/lam-info expr)))
    (e/let? expr) (infer-type env (e/instantiate1 (e/let-body expr) (e/let-value expr)) names)
    :else
    (when (and (every? #(contains? (meta names) %) (range (count names)))
               ;; Native dictionary lowering also uses untyped projection probes.
               ;; Only ask the kernel about a projection of its actual structure.
               (or (not (e/proj? expr))
                   (when-let [t (infer-type env (e/proj-struct expr) names)]
                     (let [t (whnf env t names)
                           [head _] (e/get-app-fn-args t)]
                       (and (e/const? head)
                            (= (e/const-name head) (e/proj-type-name expr)))))))
      (let [values (::values (meta names))
            closed (reduce (fn [body i]
                             (if-let [value (get values i)]
                               (e/let' "_" (get (meta names) i) value body)
                               (e/lam "_" (get (meta names) i) body :default)))
                           expr (reverse (range (count names))))
            type (.inferType (TypeChecker. env) closed)]
        ;; mkLetFVars preserves definitions. Inference may drop unused lets;
        ;; zeta-reduce them and reopen only the ordinary parameter binders.
        (whnf env
              (reduce (fn [type i]
                        (if (contains? values i) type
                            (e/instantiate1 (e/forall-body (whnf env type []))
                                            (e/bvar (- (count names) i 1)))))
                      type (range (count names))) [])))))

(defn irrelevant-type?
  "Lean's visit/visitAppArg: erase proofs and values of Sort or As → Sort.
   Native lowerings may additionally declare dictionary type heads erased.
   Clojure uses nil for LCNF's erased value, including type arguments."
  ([env type names] (irrelevant-type? env type names nil))
  ([env type names erased-type-heads]
   (or (when (seq erased-type-heads)
         (let [[head _] (e/get-app-fn-args (whnf env type names))]
           (and (e/const? head) (contains? erased-type-heads (name/->string (e/const-name head))))))
       (loop [t type ctx names]
         (let [t (whnf env t ctx)]
           (cond (e/sort? t) true
                 (e/forall? t) (recur (e/forall-body t)
                                      (bind-type ctx "_" (e/forall-type t)))
                 :else false)))
       (when-let [sort (infer-type env type names)]
         (let [sort (whnf env sort names)]
           (and (e/sort? sort) (Level/isZero (e/sort-level sort))))))))

(defn irrelevant?
  ([env expr names] (irrelevant? env expr names nil))
  ([env expr names erased-type-heads]
   (or (e/sort? expr) (e/forall? expr)
       (when-let [type (infer-type env expr names)]
         (irrelevant-type? env type names erased-type-heads)))))
