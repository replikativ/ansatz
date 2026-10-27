(ns ansatz.meta.fvar-subst
  "Lean/Meta/Tactic/FVarSubst.lean, FVarSubst (55f80e10a3).
   The persistent map represents FVarSubst's sole `map` field. Insert composes
   existing ranges; apply replaces simultaneously without revisiting ranges."
  (:refer-clojure :exclude [get apply find])
  (:require [ansatz.kernel.expr :as e]))

(def empty-subst {})

(defn map-expr-fvars [f expr]
  (if-not (e/has-fvar-flag expr)
    expr
    (let [go #(map-expr-fvars f %)]
      (case (e/tag expr)
        :fvar (f (e/fvar-id expr))
        :app (e/app (go (e/app-fn expr)) (go (e/app-arg expr)))
        :lam (e/lam (e/lam-name expr) (go (e/lam-type expr)) (go (e/lam-body expr)) (e/lam-info expr))
        :forall (e/forall' (e/forall-name expr) (go (e/forall-type expr))
                          (go (e/forall-body expr)) (e/forall-info expr))
        :let (e/let' (e/let-name expr) (go (e/let-type expr))
                    (go (e/let-value expr)) (go (e/let-body expr)))
        :mdata (e/mdata (e/mdata-data expr) (go (e/mdata-expr expr)))
        :proj (e/proj (e/proj-type-name expr) (e/proj-idx expr) (go (e/proj-struct expr)))
        expr))))

(defn find? [s id] (clojure.core/get s id))
(defn get [s id] (clojure.core/get s id (e/fvar id)))
(defn apply [s expr] (if (empty? s) expr (map-expr-fvars #(get s %) expr)))
(defn insert [s id value]
  (if (contains? s id) s
      (assoc (into {} (map (fn [[k v]] [k (apply {id value} v)])) s) id value)))
(defn erase [s id] (dissoc s id))
(defn domain [s] (vec (keys s)))
(defn any [pred s] (boolean (some (fn [[k v]] (pred k v)) s)))
(defn append [s t]
  (reduce-kv (fn [out k v] (insert out k (apply t v))) t s))
(defn apply-local-decl [s d]
  (cond-> d (:type d) (update :type #(apply s %)) (:value d) (update :value #(apply s %))))
