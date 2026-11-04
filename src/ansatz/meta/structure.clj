(ns ansatz.meta.structure
  "Projection declaration generation, following Lean v4.33.1
   Lean/Meta/Structure.lean:mkProjections."
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]))

(defn mk-projections
  "Instantiate each constructor field with its named projection before generating
   the next declaration. Values remain primitive kernel projections."
  [env0 struct-name projection-names num-params]
  (let [struct-name (name/from-string struct-name)
        ci (env/lookup env0 struct-name)
        ctor (env/lookup env0 (first (.ctors ci)))
        level-params (vec (.levelParams ci))
        levels (mapv lvl/param level-params)
        [params ctor-type] (loop [i 0 t (.type ctor) params []]
                             (if (= i num-params)
                               [params t]
                               (recur (inc i) (e/forall-body t)
                                      (conj params [(e/forall-name t) (e/forall-type t)]))))
        self-type (reduce e/app (e/const' struct-name levels)
                          (map #(e/bvar (- num-params % 1)) (range num-params)))
        proj-args (conj (mapv #(e/bvar (- num-params %)) (range num-params)) (e/bvar 0))
        ;; Ansatz's surface API takes class dictionaries explicitly as well as
        ;; structure values; retain that binder convention for generated classes.
        bind (fn [binder body]
               (reduce (fn [body [n t]] (binder n t body :implicit))
                       (binder "self" self-type body :default) (rseq params)))]
    (loop [env env0 i 0 ctor-type (e/lift ctor-type 1 0) names projection-names]
      (if-let [proj-name (first names)]
        (let [proj-name (name/from-string proj-name)
              proj-type (bind e/forall' (e/forall-type ctor-type))
              proj-val (bind e/lam (e/proj struct-name i (e/bvar 0)))
              env (if (env/lookup env proj-name)
                    env
                    (env/check-constant env (env/mk-def proj-name level-params proj-type proj-val
                                                        :hints :abbrev)))
              proj (reduce e/app (e/const' proj-name levels) proj-args)]
          (recur env (inc i) (e/instantiate1 (e/forall-body ctor-type) proj) (next names)))
        env))))
