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

(defn- self-call-args [self-id expr]
  (let [seen (java.util.IdentityHashMap.)
        calls (transient [])]
    (letfn [(visit [expr]
              (when (and (e/has-fvar-flag expr)
                         (nil? (.put seen expr true)))
                (case (e/tag expr)
                  :app (let [[head args] (e/get-app-fn-args expr)]
                         (if (and (e/fvar? head) (= self-id (e/fvar-id head)))
                           (do (conj! calls args) (doseq [arg args] (visit arg)))
                           (do (visit (e/app-fn expr)) (visit (e/app-arg expr)))))
                  :lam (do (visit (e/lam-type expr)) (visit (e/lam-body expr)))
                  :forall (do (visit (e/forall-type expr)) (visit (e/forall-body expr)))
                  :let (do (visit (e/let-type expr)) (visit (e/let-value expr))
                           (visit (e/let-body expr)))
                  :proj (visit (e/proj-struct expr))
                  :mdata (visit (e/mdata-expr expr))
                  nil)))]
      (visit expr))
    (persistent! calls)))

(defn- expr-fvar-ids [expr]
  (if-not (e/has-fvar-flag expr)
    #{}
    (case (e/tag expr)
      :fvar #{(e/fvar-id expr)}
      :app (into (expr-fvar-ids (e/app-fn expr)) (expr-fvar-ids (e/app-arg expr)))
      :lam (into (expr-fvar-ids (e/lam-type expr)) (expr-fvar-ids (e/lam-body expr)))
      :forall (into (expr-fvar-ids (e/forall-type expr)) (expr-fvar-ids (e/forall-body expr)))
      :let (into (expr-fvar-ids (e/let-type expr))
                 (concat (expr-fvar-ids (e/let-value expr))
                         (expr-fvar-ids (e/let-body expr))))
      :proj (expr-fvar-ids (e/proj-struct expr))
      :mdata (expr-fvar-ids (e/mdata-expr expr))
      #{})))

(defn- fixed-parameter-positions [ctx self-id xs body arity rec-pos index-positions]
  (let [calls (self-call-args self-id body)
        excluded (set (conj index-positions rec-pos))
        unchanged? (fn [i]
                     (every? (fn [args]
                               (and (< i (count args))
                                    (try (tc/is-def-eq @ctx (nth args i) (nth xs i))
                                         (catch Exception _ false))))
                             calls))
        initial (set (filter #(and (not (excluded %)) (unchanged? %)) (range arity)))]
    ;; Lean FixedParamPerms.erase: changing the major or an index also erases
    ;; every fixed parameter whose type depends on it, transitively.
    (loop [fixed initial]
      (let [varying-ids (set (map #(e/fvar-id (nth xs %))
                                  (remove fixed (range arity))))
            fixed' (set (remove (fn [i]
                                  (some varying-ids
                                        (expr-fvar-ids (u/infer-type ctx (nth xs i)))))
                                fixed))]
        (if (= fixed fixed') fixed (recur fixed'))))))

(defn- to-below [ctx motive below target-args]
  (let [raw-type (u/infer-type ctx below)
        [raw-head raw-args] (e/get-app-fn-args raw-type)
        type (u/whnf ctx raw-type)
        [head args] (e/get-app-fn-args type)
        head-name (when (e/const? head) (str (e/const-name head)))]
    (cond
      (and (= raw-head motive) (= (count target-args) (count raw-args))
           (every? true? (map #(tc/is-def-eq @ctx %1 %2) raw-args target-args)))
      below

      (and (#{"PProd" "And"} head-name) (= 2 (count args)))
      (or (to-below ctx motive (e/proj (name/from-string head-name) 0 below) target-args)
          (to-below ctx motive (e/proj (name/from-string head-name) 1 below) target-args))

      :else nil)))

(defn replace-rec-apps
  "Lean replaceRecApps for one structurally recursive function. `self-id` is a
   temporary local, `below` has type `I.below motive major`, and `rec-pos` is
   the function argument chosen for structural recursion."
  [ctx environment self-id rec-pos index-positions arity fixed-args motive below expr]
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
                          index-args (mapv #(loop-expr below (nth args %)) index-positions)
                          value (to-below ctx motive below (conj index-args arg))]
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
                                                                      (not (some #{i} index-positions))
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
        [head ind-args] (e/get-app-fn-args arg-type)
        ind-name (e/const-name head)
        ind-info (env/lookup! environment ind-name)
        num-params (.numParams ind-info)
        params (subvec ind-args 0 num-params)
        indices (subvec ind-args num-params)
        _ (when-not (and (every? e/fvar? indices)
                         (= (count indices) (count (distinct indices)))
                         (every? (set xs) indices))
            (throw (ex-info "Indexed recursive argument requires distinct parameter indices"
                            {:kind :unsupported-structural-indices :argument arg-type})))
        index-positions (mapv #(.indexOf ^java.util.List xs %) indices)
        ;; Lean FixedParams: arguments unchanged at every recursive call stay
        ;; outside the motive, except indices/major and their dependents.
        fixed-positions (fixed-parameter-positions ctx self-id xs body arity
                                                   rec-pos index-positions)
        ind-param-positions (set (keep-indexed (fn [i x]
                                                 (when (some #{x} params) i)) xs))
        _ (when-not (every? fixed-positions ind-param-positions)
            (throw (ex-info "Recursive call changes an inductive parameter"
                            {:kind :non-structural-recursion})))
        fixed-args (into {} (map (fn [i] [i (nth xs i)]) fixed-positions))
        varying (vec (keep-indexed (fn [i x]
                                     (when (and (not= i rec-pos)
                                                (not (some #{i} index-positions))
                                                (not (contains? fixed-args i))) x)) xs))
        levels (vec (e/const-levels head))
        motive-body (u/mk-forall-fvars ctx varying result-type)
        motive-level (u/get-level ctx motive-body)
        motive (u/mk-lambda-fvars ctx (conj indices arg) motive-body)
        below-type (u/app (e/const' (name/mk-str ind-name "below")
                                    (into [motive-level] levels))
                          (concat params [motive] indices [arg]))
        below (u/local-decl ctx "below" below-type)
        transformed (replace-rec-apps ctx environment self-id rec-pos index-positions arity fixed-args
                                      motive below body)
        functional (u/mk-lambda-fvars ctx (into (conj indices arg below) varying) transformed)
        value (u/app (e/const' (name/mk-str ind-name "brecOn")
                               (into [motive-level] levels))
                     (concat params [motive] indices [arg functional]))
        value (u/app value varying)]
    (u/mk-lambda-fvars ctx xs value)))
