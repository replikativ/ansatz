(ns ansatz.codegen.types
  "Runtime erasure following Lean v4.33.1 (55f80e10a3) Compiler/LCNF/ToLCNF.lean
   visit, visitAppArg and isTypeFormerType; Types.lean erased."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel TypeChecker Level]))

(defn bind-type [names n type]
  (with-meta (conj names n)
    (assoc (meta names) (count names) type)))

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
      (let [t (.whnf (.getReducer (TypeChecker. env)) t)]
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
                     (let [t (.whnf (.getReducer (TypeChecker. env)) t)
                           [head _] (e/get-app-fn-args t)]
                       (and (e/const? head)
                            (= (e/const-name head) (e/proj-type-name expr)))))))
      (let [closed (reduce (fn [body i] (e/lam "_" (get (meta names) i) body :default))
                           expr (reverse (range (count names))))
            type (.inferType (TypeChecker. env) closed)]
        (nth (iterate e/forall-body type) (count names))))))

(defn irrelevant-type?
  "Lean's visit/visitAppArg: erase proofs and values of Sort or As → Sort.
   Clojure uses nil for LCNF's erased value, including type arguments."
  [env type names]
  (let [tc (TypeChecker. env)
        whnf #(.whnf (.getReducer tc) %)]
    (or (loop [t type]
          (let [t (whnf t)]
            (cond (e/sort? t) true
                  (e/forall? t) (recur (e/forall-body t))
                  :else false)))
        (when-let [sort (infer-type env type names)]
          (let [sort (whnf sort)]
            (and (e/sort? sort) (Level/isZero (e/sort-level sort))))))))

(defn irrelevant? [env expr names]
  (or (e/sort? expr) (e/forall? expr)
      (when-let [type (infer-type env expr names)]
        (irrelevant-type? env type names))))
