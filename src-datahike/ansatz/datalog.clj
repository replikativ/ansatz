;; Direction-1 datahike integration (Stage 1): project the kernel env into an
;; in-memory datahike DB (a derived, queryable relational VIEW), and recall
;; type-directed candidate constants for the relational search. datahike narrows
;; in KEY space (conclusion head-symbol); ansatz.rel confirms in TERM space
;; (is-def-eq). Optional module — only on the classpath under the :datahike alias.
(ns ansatz.datalog
  (:require [datahike.api :as d]
            [datahike.db :as ddb]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.expr :as e])
  (:import [ansatz.kernel Expr ConstantInfo Env]
           [java.util IdentityHashMap ArrayList]))

;; ---- schema (datascript-style: only refs / cardinality-many / unique) ----
(def ^:private schema
  {:expr/fn {:db/valueType :db.type/ref}
   :expr/arg {:db/valueType :db.type/ref}
   :expr/dom {:db/valueType :db.type/ref}
   :expr/body {:db/valueType :db.type/ref}
   :expr/struct {:db/valueType :db.type/ref}
   :decl/type {:db/valueType :db.type/ref}
   :decl/sym {:db/cardinality :db.cardinality/many}
   :decl/name {:db/unique :db.unique/identity}})

(defn- head-sym ^String [^Expr e]
  (let [h (loop [x e] (if (e/app? x) (recur (e/app-fn x)) x))]
    (when (e/const? h) (nm/->string (e/const-name h)))))

(defn- peel-foralls [^Expr t]
  (loop [x t n 0] (if (e/forall? x) (recur (e/forall-body x) (inc n)) [x n])))

(defn- collect-syms [^Expr e]
  (let [out (java.util.HashSet.)]
    (letfn [(go [^Expr x]
              (case (e/tag x)
                :const (.add out (nm/->string (e/const-name x)))
                :app (do (go (e/app-fn x)) (go (e/app-arg x)))
                :lam (do (go (e/lam-type x)) (go (e/lam-body x)))
                :forall (do (go (e/forall-type x)) (go (e/forall-body x)))
                :let (do (go (e/let-type x)) (go (e/let-body x)))
                :mdata (go (e/mdata-expr x))
                :proj (go (e/proj-struct x))
                nil))]
      (go e))
    (vec out)))

(defn- encode-expr [^Expr ex ^IdentityHashMap seen tid ^ArrayList acc]
  (or (.get seen ex)
      (let [id (swap! tid dec)
            _ (.put seen ex id)
            base {:db/id id :expr/tag (e/tag ex)}
            m (case (e/tag ex)
                :const (assoc base :expr/const-name (nm/->string (e/const-name ex)))
                :app (assoc base
                            :expr/fn (encode-expr (e/app-fn ex) seen tid acc)
                            :expr/arg (encode-expr (e/app-arg ex) seen tid acc)
                            :expr/head-sym (or (head-sym ex) ""))
                :lam (assoc base :expr/dom (encode-expr (e/lam-type ex) seen tid acc)
                            :expr/body (encode-expr (e/lam-body ex) seen tid acc))
                :forall (assoc base :expr/dom (encode-expr (e/forall-type ex) seen tid acc)
                               :expr/body (encode-expr (e/forall-body ex) seen tid acc))
                :let (assoc base :expr/dom (encode-expr (e/let-type ex) seen tid acc)
                            :expr/body (encode-expr (e/let-body ex) seen tid acc))
                :mdata (assoc base :expr/body (encode-expr (e/mdata-expr ex) seen tid acc))
                :proj (assoc base :expr/struct (encode-expr (e/proj-struct ex) seen tid acc))
                base)]
        (.add acc m)
        id)))

(defn- kind-kw [^ConstantInfo ci]
  (cond (.isThm ci) :thm (.isDef ci) :def
        (= (.tag ci) ConstantInfo/AXIOM) :axiom
        (= (.tag ci) ConstantInfo/INDUCT) :induct
        (= (.tag ci) ConstantInfo/CTOR) :ctor
        (= (.tag ci) ConstantInfo/RECURSOR) :recursor
        :else :other))

(defn- encode-decl [^ConstantInfo ci ^IdentityHashMap seen tid ^ArrayList acc]
  (let [ty (.type ci)
        ty-id (encode-expr ty seen tid acc)
        [concl nb] (peel-foralls ty)
        hs (or (head-sym concl) (when (e/const? concl) (nm/->string (e/const-name concl))))]
    (.add acc (cond-> {:decl/name (nm/->string (.name ci))
                       :decl/kind (kind-kw ci)
                       :decl/type ty-id
                       :decl/num-univs (count (.levelParams ci))
                       :decl/num-binders nb
                       :decl/sym (collect-syms ty)}
                hs (assoc :decl/concl-head hs)))))

(defn project-env
  "Project every constant in `env` into an in-memory datahike DB — a derived,
   queryable VIEW (declaration kind, type-DAG with structural sharing, symbols,
   conclusion head-symbol, binder count). Returns the immutable db value."
  [^Env env]
  (let [seen (IdentityHashMap. 1000000)
        tid (atom 0)
        acc (ArrayList. 2000000)]
    (doseq [^ConstantInfo ci (env/all-constants env)]
      (encode-decl ci seen tid acc))
    (d/db-with (ddb/empty-db schema) (vec acc))))

;; ---- recall: goal type → weighted candidate constants ----

(defn- goal-head
  "The conclusion head-symbol of a goal TYPE (peel ∀, take the spine head).
   Matches project-env's :decl/concl-head normalization."
  [^Expr ty]
  (let [[concl _] (peel-foralls ty)]
    (or (head-sym concl) (when (e/const? concl) (nm/->string (e/const-name concl))))))

(defn candidates-for-head
  "Query the projected `db` for constants whose CONCLUSION head-symbol is
   `head` — the discrimination-tree first-level key — ranked simplest-first
   (fewer obligations). Returns [[weight name] …], capped at `limit`. This is
   the datalog KEY-space narrowing; term-space confirmation is rel's `===`."
  [db head limit]
  (when head
    (->> (d/q '[:find ?n ?nb
                :in $ ?h
                :where
                [?d :decl/concl-head ?h]
                [?d :decl/name ?n]
                [?d :decl/num-binders ?nb]]
              db head)
         (sort-by second)
         (take limit)
         (mapv (fn [[n nb]] [(/ 1.0 (+ 1.0 (double nb))) n])))))

(defn symbol-df
  "Document frequency per symbol across the projected declarations (for IDF)."
  [db]
  (into {} (d/q '[:find ?s (count ?d) :where [?d :decl/sym ?s]] db)))

(defn candidates-for-goal
  "Head-matched candidates ranked by MePo relevance: IDF-weighted overlap of
   each candidate's TYPE symbols with the goal-context symbols `ctx-syms`
   (the goal type's + hypotheses' symbols), plus a small simplicity term.
   This surfaces the relevant lemma (e.g. Nat.le_trans) that pure
   fewest-binders ranking buries. Returns [[weight name] …] capped at `limit`."
  [db head ctx-syms limit & {:keys [df ndecls]}]
  (when head
    (let [df (or df (symbol-df db))
          n-decls (double (or ndecls
                              (d/q '[:find (count ?d) . :where [?d :decl/name _]] db)
                              3000))
          ctx (set ctx-syms)
          idf (fn [s] (Math/log (/ n-decls (double (get df s 1)))))
          rows (d/q '[:find ?n ?nb ?s
                      :in $ ?h
                      :where
                      [?d :decl/concl-head ?h]
                      [?d :decl/name ?n]
                      [?d :decl/num-binders ?nb]
                      [?d :decl/sym ?s]]
                    db head)]
      (->> rows
           (reduce (fn [m [n nb s]]
                     (-> m
                         (assoc-in [n :nb] nb)
                         (update-in [n :syms] (fnil conj #{}) s)))
                   {})
           (map (fn [[n {:keys [nb syms]}]]
                  (let [overlap (reduce + 0.0 (map idf (filter ctx syms)))]
                    [n (+ overlap (/ 1.0 (+ 1.0 (double nb))))])))
           (sort-by (comp - second))
           (take limit)
           (mapv (fn [[n sc]] [(max 0.01 sc) n]))))))

(defn dq-provider
  "A candidate-provider for `ansatz.rel/expro`: `(state, goal-mvar) →
   [[weight name] …]`, computed by a datalog query over the projected `db`
   against the goal's zonked conclusion head. `resolve-type` extracts the
   goal's type from the state+mvar (pass ansatz.rel/mvar-type)."
  ([db resolve-type] (dq-provider db resolve-type 40))
  ([db resolve-type limit]
   (fn [s g]
     (candidates-for-head db (goal-head (resolve-type s g)) limit))))
