(ns ansatz.meta.match.matcher-app
  "Lean/Meta/Match/MatcherApp/{Basic,Transform}.lean. Matcher application
   decomposition and the addArg transport used by structural recursion."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta.constructions.util :as u]
            [ansatz.meta.match.matcher-info :as mi]))

(defn match-matcher-app? [environment expr]
  (let [[head args] (e/get-app-fn-args expr)]
    (when-let [info (mi/is-matcher-app-core? environment expr)]
      (let [np (:num-params info)
            nd (:num-discrs info)
            na (mi/num-alts info)]
        (assoc info
               :matcher-info info
               :matcher-name (e/const-name head)
               :matcher-levels (vec (e/const-levels head))
               :params (subvec args 0 np)
               :motive (nth args np)
               :discrs (subvec args (inc np) (+ 1 np nd))
               :alternatives (subvec args (+ 1 np nd) (+ 1 np nd na))
               :remaining (subvec args (+ 1 np nd na)))))))

(defn to-expr [{:keys [matcher-name matcher-levels params motive discrs alternatives remaining]}]
  (u/app (e/const' matcher-name matcher-levels)
         (concat params [motive] discrs alternatives remaining)))

(defn- lambda-telescope [ctx term n]
  (loop [term term xs []]
    (if (= n (count xs))
      [xs term]
      (do
        (when-not (e/lam? term)
          (throw (ex-info "Matcher alternative has too few binders"
                          {:expected n :actual (count xs)})))
        (let [x (u/local-decl ctx (e/lam-name term) (e/lam-type term) (e/lam-info term))]
          (recur (e/instantiate1 (e/lam-body term) x) (conj xs x)))))))

(defn- add-alt-args [ctx unrefined-type aux-type alt-counts alts]
  (loop [aux-type aux-type i 0 out [] refined? false]
    (if (= i (count alts))
      (if refined? (vec out)
          (throw (ex-info "Matcher argument type was not refined by case splitting" {})))
      (let [aux-type (u/whnf ctx aux-type)
            _ (when-not (e/forall? aux-type)
                (throw (ex-info "Unexpected matcher alternative type" {:index i})))
            [xs body] (lambda-telescope ctx (nth alts i) (nth alt-counts i))
            domain (u/instantiate-forall ctx (e/forall-type aux-type) xs)
            [ys _] (u/forall-telescope ctx domain 1)
            _ (when-not (= 1 (count ys))
                (throw (ex-info "Matcher alternative lacks transported argument" {:index i})))
            refined? (or refined? (not (tc/is-def-eq @ctx unrefined-type
                                                     (u/infer-type ctx (first ys)))))
            alt (u/mk-lambda-fvars ctx xs (u/mk-lambda-fvars ctx ys body))]
        (recur (e/instantiate1 (e/forall-body aux-type) (nth alts i))
               (inc i) (conj out alt) refined?)))))

(defn add-arg
  "Lean MatcherApp.addArg: push `arg` through a dependent matcher and refine its
   type in each alternative. Throws when the matcher does not refine it."
  [ctx matcher-app arg]
  (let [n (count (:discrs matcher-app))
        [motive-xs motive-body] (lambda-telescope ctx (:motive matcher-app) n)
        arg-type (u/infer-type ctx arg)
        arg-type-abst (reduce (fn [t i]
                                (let [d (nth (:discrs matcher-app) i)]
                                  (if (e/fvar? d)
                                    (u/replace-fvars t [[d (nth motive-xs i)]]) t)))
                              arg-type (reverse (range n)))
        motive-body (u/mk-arrow ctx arg-type-abst motive-body)
        motive (u/mk-lambda-fvars ctx motive-xs motive-body)
        levels (if-let [pos (:u-elim-pos matcher-app)]
                 (assoc (:matcher-levels matcher-app) pos (u/get-level ctx motive-body))
                 (:matcher-levels matcher-app))
        aux (u/app (e/const' (:matcher-name matcher-app) levels)
                   (concat (:params matcher-app) [motive] (:discrs matcher-app)))
        alts (add-alt-args ctx arg-type (u/infer-type ctx aux)
                           (mi/alt-num-params (:matcher-info matcher-app))
                           (:alternatives matcher-app))]
    (assoc matcher-app :matcher-levels levels :motive motive
           :alternatives alts :remaining (into [arg] (:remaining matcher-app)))))

(defn add-arg? [ctx matcher-app arg]
  (try (add-arg ctx matcher-app arg)
       (catch clojure.lang.ExceptionInfo _ nil)))
