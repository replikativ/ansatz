(ns ansatz.elab.structural
  "Lean/Elab/PreDefinition/Structural/BRecOn.lean: replace recursive applications
   using the `below` dictionary, transporting it through matcher alternatives."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta.constructions.util :as u]
            [ansatz.meta.match.matcher-app :as matcher-app]
            [ansatz.meta.match.matcher-info :as mi]))

(defn- contains-self? [self-id expr]
  (case (e/tag expr)
    :fvar (= self-id (e/fvar-id expr))
    :app (or (contains-self? self-id (e/app-fn expr))
             (contains-self? self-id (e/app-arg expr)))
    :lam (or (contains-self? self-id (e/lam-type expr))
             (contains-self? self-id (e/lam-body expr)))
    :forall (or (contains-self? self-id (e/forall-type expr))
                (contains-self? self-id (e/forall-body expr)))
    :let (or (contains-self? self-id (e/let-type expr))
             (contains-self? self-id (e/let-value expr))
             (contains-self? self-id (e/let-body expr)))
    :proj (contains-self? self-id (e/proj-struct expr))
    :mdata (contains-self? self-id (e/mdata-expr expr))
    false))

(defn- to-below [ctx motive below arg]
  (let [raw-type (u/infer-type ctx below)
        [raw-head raw-args] (e/get-app-fn-args raw-type)
        type (u/whnf ctx raw-type)
        [head args] (e/get-app-fn-args type)
        head-name (when (e/const? head) (str (e/const-name head)))]
    (cond
      (and (= raw-head motive) (= 1 (count raw-args))
           (tc/is-def-eq @ctx (first raw-args) arg))
      below

      (and (#{"PProd" "And"} head-name) (= 2 (count args)))
      (or (to-below ctx motive (e/proj (name/from-string head-name) 0 below) arg)
          (to-below ctx motive (e/proj (name/from-string head-name) 1 below) arg))

      :else nil)))

(defn replace-rec-apps
  "Lean replaceRecApps for one structurally recursive function. `self-id` is a
   temporary local, `below` has type `I.below motive major`, and `rec-pos` is
   the function argument chosen for structural recursion."
  [ctx environment self-id rec-pos arity fixed-args motive below expr]
  (letfn [(loop-expr [below expr]
            (if-not (contains-self? self-id expr)
              expr
              (case (e/tag expr)
                :app
                (let [[head args] (e/get-app-fn-args expr)]
                  (if (and (e/fvar? head) (= self-id (e/fvar-id head)))
                    (let [arg (nth args rec-pos nil)
                          _ (when-not (and arg (<= arity (count args)))
                              (throw (ex-info "Recursive call has too few arguments"
                                              {:rec-pos rec-pos :application expr})))
                          arg (loop-expr below arg)
                          value (to-below ctx motive below arg)]
                      (when-not value
                        (throw (ex-info "Cannot find recursive argument in below dictionary"
                                        {:kind :non-structural-recursion :argument arg
                                         :below-type (u/whnf ctx (u/infer-type ctx below))
                                         :motive motive})))
                      (doseq [[i fixed] fixed-args]
                        (when-not (tc/is-def-eq @ctx (nth args i) fixed)
                          (throw (ex-info "Recursive call changes an inductive parameter"
                                          {:kind :non-structural-recursion :position i}))))
                      (u/app value
                             (mapv #(loop-expr below %)
                                   (concat (keep-indexed (fn [i x]
                                                           (when (and (not= i rec-pos)
                                                                      (not (contains? fixed-args i))) x))
                                                         (subvec args 0 arity))
                                           (subvec args arity)))))
                    (if-let [app (matcher-app/match-matcher-app? environment expr)]
                      (if-let [app' (matcher-app/add-arg? ctx app below)]
                        (let [counts (mi/alt-num-params (:matcher-info app'))
                              alts (mapv
                                    (fn [alt count]
                                      (let [[xs body] (matcher-app/lambda-telescope ctx alt (inc count))
                                            below-alt (peek xs)]
                                        (u/mk-lambda-fvars ctx xs (loop-expr below-alt body))))
                                    (:alternatives app') counts)]
                          (matcher-app/to-expr (assoc app' :alternatives alts)))
                        (u/app (loop-expr below head) (mapv #(loop-expr below %) args)))
                      (u/app (loop-expr below head) (mapv #(loop-expr below %) args)))))

                :lam (let [type (loop-expr below (e/lam-type expr))
                           x (u/local-decl ctx (e/lam-name expr) type (e/lam-info expr))]
                       (u/mk-lambda-fvars ctx [x]
                                          (loop-expr below (e/instantiate1 (e/lam-body expr) x))))
                :forall (let [type (loop-expr below (e/forall-type expr))
                              x (u/local-decl ctx (e/forall-name expr) type (e/forall-info expr))]
                          (u/mk-forall-fvars ctx [x]
                                             (loop-expr below (e/instantiate1 (e/forall-body expr) x))))
                :proj (e/proj (e/proj-type-name expr) (e/proj-idx expr)
                              (loop-expr below (e/proj-struct expr)))
                :let (let [type (loop-expr below (e/let-type expr))
                           value (loop-expr below (e/let-value expr))
                           x (u/local-decl ctx (e/let-name expr) type)
                           body (loop-expr below (e/instantiate1 (e/let-body expr) x))]
                       (e/let' (e/let-name expr) type value
                               (e/abstract1 body (e/fvar-id x))))
                :mdata (e/mdata (e/mdata-data expr) (loop-expr below (e/mdata-expr expr)))
                (throw (ex-info "Unsupported recursive expression form"
                                {:tag (e/tag expr)})))))]
    (loop-expr below expr)))

(defn compile-recursive-match
  "Compile a recursive predefinition with `I.brecOn`. The source lambda has
   one local `self-id`, removed from the result. The matched argument occupies
   `rec-pos`; other varying arguments are carried by the brecOn motive."
  [environment source self-type self-id rec-pos arity]
  (let [ctx (u/context environment)
        [xs body] (matcher-app/lambda-telescope ctx source arity)
        _ (swap! (:next-id @ctx) max self-id)
        arg (nth xs rec-pos)
        arg-type (u/infer-type ctx arg)
        result-type (u/instantiate-forall ctx self-type xs)
        [head params] (e/get-app-fn-args arg-type)
        ind-name (e/const-name head)
        ind-info (env/lookup! environment ind-name)
        _ (when (pos? (.numIndices ind-info))
            (throw (ex-info "Indexed structural recursion is not yet supported by matcher compilation"
                            {:inductive ind-name})))
        ;; Inductive datatype parameters must remain fixed for `I.brecOn`.
        ;; All other function parameters are allowed to vary between calls.
        fixed-args (into {} (keep-indexed (fn [i x]
                                            (when (some #{x} params) [i x])) xs))
        varying (vec (keep-indexed (fn [i x]
                                     (when (and (not= i rec-pos)
                                                (not (contains? fixed-args i))) x)) xs))
        levels (vec (e/const-levels head))
        motive-body (u/mk-forall-fvars ctx varying result-type)
        motive-level (u/get-level ctx motive-body)
        motive (u/mk-lambda-fvars ctx [arg] motive-body)
        below-type (u/app (e/const' (name/mk-str ind-name "below")
                                    (into [motive-level] levels))
                          (concat params [motive arg]))
        below (u/local-decl ctx "below" below-type)
        transformed (replace-rec-apps ctx environment self-id rec-pos arity fixed-args
                                      motive below body)
        functional (u/mk-lambda-fvars ctx (into [arg below] varying) transformed)
        value (u/app (e/const' (name/mk-str ind-name "brecOn")
                               (into [motive-level] levels))
                     (concat params [motive arg functional]))
        value (u/app value varying)]
    (u/mk-lambda-fvars ctx xs value)))
