(ns ansatz.tactic.grind.ctor
  "Homogeneous constructor consequences, following Grind/Ctor.lean propagateCtorHomo."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.grind.action :as action]
            [ansatz.tactic.grind.egraph :as eg]
            [ansatz.tactic.grind.proof :as gp]))

(defn- sort-level [st type]
  (let [s (#'tc/cached-whnf st (tc/infer-type st type))]
    (when-not (e/sort? s) (throw (ex-info "grind constructor: expected sort" {:type type})))
    (e/sort-level s)))

(defn- consequence [gs st a b]
  (let [[ha aa] (e/get-app-fn-args a) [hb ab] (e/get-app-fn-args b)
        ca (env/lookup (:env gs) (e/const-name ha))
        cb (env/lookup (:env gs) (e/const-name hb))
        ind (.inductName ca)
        params (.numParams ca)
        type (tc/infer-type st a)
        _ (when-not (and (= ind (.inductName cb)) (tc/is-def-eq st type (tc/infer-type st b)))
            (action/fail! "heterogeneous constructor equality unsupported" {:lhs a :rhs b}))
        hp (gp/mk-eq-proof gs st a b)
        levels (e/const-levels ha)
        proof
        (if (= (e/const-name ha) (e/const-name hb))
          (let [nm (name/mk-str (e/const-name ha) "inj")]
            (when (env/lookup (:env gs) nm)
              (reduce e/app (e/const' nm levels)
                      (concat (take params aa) (drop params aa) (drop params ab) [hp]))))
          (let [nm (name/mk-str ind "noConfusion")
                ci (env/lookup (:env gs) nm)]
            (when-not ci (action/fail! "missing constructor noConfusion lemma" {:lemma nm}))
            (let [arity (loop [t (.type ci) n 0]
                          (if (e/forall? t) (recur (e/forall-body t) (inc n)) n))
                  false-expr (e/const' (name/from-string "False") [])
                  args (if (= arity (+ params 4))
                         (concat [false-expr] (take params aa) [a b hp])
                         (if (and (= params 1) (= arity 7))
                           (let [alpha (first aa)
                                 hrefl (gp/mk-eq-refl st alpha)
                                 hheq (e/app* (e/const' (name/from-string "heq_of_eq") [(sort-level st type)])
                                               type a b hp)]
                             [false-expr alpha a (first ab) b hrefl hheq])
                           (action/fail! "indexed noConfusion telescope unsupported" {:lemma nm :arity arity}))) ]
              (reduce e/app (e/const' nm (into [lvl/zero] levels)) args))))]
    (when proof
      {:prop (#'tc/cached-whnf st (tc/infer-type st proof)) :proof proof
       :gen (max (:gen (eg/get-enode gs a)) (:gen (eg/get-enode gs b)))})))

(defn propagate [gs st seen]
  (reduce
   (fn [{:keys [seen] :as result} [a b]]
     (let [key #{a b}]
       (if (contains? seen key) result
         (let [fact (consequence gs st a b)]
           (cond-> (update result :seen conj key) fact (update :facts conj fact))))))
   {:seen seen :facts []}
   (for [[expr node] (:enodes gs)
         :when (and (= expr (:root node)) (> (:size node) 1))
         :let [ctors (filter #(:ctor (eg/get-enode gs %)) (eg/collect-eqc gs expr))]
         b (rest ctors)] [(first ctors) b])))
