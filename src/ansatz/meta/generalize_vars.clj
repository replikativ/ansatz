(ns ansatz.meta.generalize-vars
  "Lean/Meta/GeneralizeVars.lean (55f80e10a3): forbidden dependencies and
   forward-dependent locals, in local-context order."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.meta :as meta]
            [ansatz.meta.fvar-subst :as subst]
            [ansatz.meta.constructions.util :as u]))

(defn- expr-fvars [ctx expr]
  (let [expr (if-let [mctx (:meta-mctx @ctx)] (meta/instantiate-expr-mvars @mctx expr) expr)
        ids (volatile! #{})]
    (subst/map-expr-fvars (fn [id] (vswap! ids conj id) (e/fvar id)) expr)
    @ids))

(defn- decl-dependencies [ctx d]
  (cond-> (expr-fvars ctx (:type d))
    (:value d) (into (expr-fvars ctx (:value d)))))

(defn mk-generalization-forbidden-set [ctx targets forbidden]
  (loop [todo (vec (mapcat #(if (e/fvar? %) [(e/fvar-id %)]
                               (expr-fvars ctx (u/infer-type ctx %))) targets))
         forbidden forbidden]
    (if-let [id (peek todo)]
      (if (contains? forbidden id)
        (recur (pop todo) forbidden)
        (recur (into (pop todo) (decl-dependencies ctx (get (:lctx @ctx) id)))
               (conj forbidden id)))
      forbidden)))

(defn get-fvars-to-generalize
  "GetFVarsToGeneralize: exclude targets and their dependencies; collect
   transitive forward dependencies, excluding instances and auxiliary locals."
  [ctx targets & {:keys [forbidden ignore-let-decls] :or {forbidden #{} ignore-let-decls false}}]
  (let [forbidden (mk-generalization-forbidden-set ctx targets forbidden)]
    (first
     (reduce (fn [[result deps] [id d]]
               (if (and (not (contains? forbidden id))
                        (not (:aux-decl? d)) (not= :inst-implicit (:info d))
                        (not (and ignore-let-decls (:value d)))
                        (some deps (decl-dependencies ctx d)))
                 [(conj result id) (conj deps id)]
                 [result deps]))
             [[] (set (keep #(when (e/fvar? %) (e/fvar-id %)) targets))]
             (sort-by key (:lctx @ctx))))))
