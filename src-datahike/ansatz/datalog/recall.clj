;; Wire disc-tree RECALL as an `inhabito` candidate PROVIDER: per goal, the
;; star-aware discrimination tree narrows the whole library to the lemmas whose
;; CONCLUSION structurally matches, and (optionally) the kernel `defeq`
;; confirmation filters to those that truly apply. The confirmed names feed the
;; relational search. This is where the search SCALES — candidates come from the
;; library-as-index, not a hand-list.
;;
;; NB: the same disc-tree is also exposed AS a datahike secondary index +
;; datalog foreign var (ansatz.index.discr/dt-match) — the "Direction-2" planned
;; query. Its `-search` is exact (validated: 143 hits for a `_ ≤ _` goal over
;; init-medium), but the datalog PLANNER integration of `dt-match` currently
;; returns empty at full-library scale (works on small DBs — see
;; datalog_confirm_test). Until that planner path is fixed we drive the provider
;; from the index `-search` directly (via a plain in-process trie), which is the
;; identical recall.
(ns ansatz.datalog.recall
  (:require [ansatz.tactic.discr-tree :as dt]
            [ansatz.index.discr :as dti]
            [ansatz.datalog.confirm :as cf]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.rel :as r]
            [datahike.api :as d]
            [clojure.edn :as edn])
  (:import [ansatz.kernel ConstantInfo]))

;; ---- Direction-2: the disc-tree AS a datahike secondary index + planned
;;      datalog recall query (needs the datahike Integer→Long eid coercion fix
;;      in execute-external-engine; recall via `-search` is identical). ----

(defn project-recall-db
  "Project `env` into a connection-backed datahike DB for recall: :decl/name
   (unique) + :decl/dt-key (conclusion disc-tree key), with the :ansatz.index/
   discr-tree secondary index over :decl/dt-key (fed by the transactor)."
  [env]
  (let [cfg {:store {:backend :memory :id (java.util.UUID/randomUUID)}
             :schema-flexibility :write :keep-history? false
             ;; disable datahike's 4096-char string cap: a few compiler-generated
             ;; decls (.noConfusion, .rec motives, match equations) have huge
             ;; conclusion types whose disc-tree key-path serializes past 4096.
             :max-string-length 0}
        _ (d/create-database cfg)
        conn (d/connect cfg)]
    (d/transact conn [{:db/ident :decl/name :db/valueType :db.type/string
                       :db/cardinality :db.cardinality/one :db/unique :db.unique/identity}
                      {:db/ident :decl/dt-key :db/valueType :db.type/string
                       :db/cardinality :db.cardinality/one}])
    (d/transact conn [{:db/ident :idx/dt :db.secondary/type :ansatz.index/discr-tree
                       :db.secondary/attrs [:decl/dt-key]}])
    (d/transact conn
                (vec (for [^ConstantInfo ci (env/all-constants env)
                           :let [k (try (dti/decl-key (.type ci)) (catch Throwable _ nil))]
                           :when k]
                       {:decl/name (nm/->string (.name ci)) :decl/dt-key k})))
    (Thread/sleep 400)
    conn))

(defn datalog-recall-provider
  "An inhabito/expro candidate provider backed by the PLANNED datalog recall
   query over `conn`: `dt-match` routes to the disc-tree secondary index in-plan
   (structural recall), then kernel `applies?` confirms in-plan. One SOTA-planned
   query per goal — the Direction-2 form."
  ([conn env] (datalog-recall-provider conn env 80))
  ([conn env limit]
   (fn [s g]
     (let [gty (r/mvar-type s g)
           gkey (dti/query-key gty)]
       (->> (d/q '[:find ?name :in $ ?env ?goal ?key :where
                   [(ansatz.index.discr/dt-match :idx/dt ?key) [[?d]]]
                   [?d :decl/name ?name]
                   [(ansatz.datalog.confirm/applies? ?env nil ?goal ?name)]]
                 @conn env gty gkey)
            (take limit)
            (mapv (fn [[nm]] [1.0 nm])))))))

(defn build-recall-trie
  "Build an in-process star-aware disc-tree over `env`: each declaration's
   CONCLUSION key (∀-telescope vars → wildcards) → its name. Same key format as
   the datahike secondary index (`dti/decl-key` stored, `dti/query-key`
   queried)."
  [env]
  (reduce (fn [trie ^ConstantInfo ci]
            (if-let [ks (try (edn/read-string (dti/decl-key (.type ci)))
                             (catch Throwable _ nil))]
              (dt/trie-insert trie ks (nm/->string (.name ci)))
              trie))
          dt/empty-trie
          (env/all-constants env)))

(defn- ranked-candidates
  "trie-match-scored output → `[[name score] …]` deduped (max specificity per
   name), most-specific FIRST. The score is Lean's DiscrTree specificity (# of
   concrete key matches); it becomes the `condw` prior so the search explores
   the structurally-specific lemma before the star-headed catch-alls."
  [scored]
  (->> scored
       (reduce (fn [m [nm sc]] (assoc m nm (max (long sc) (get m nm 0)))) {})
       (sort-by (comp - val))))

(defn recall-provider
  "An `inhabito`/`expro` candidate provider `(state, goal) → [[w name] …]` backed
   by disc-tree recall, RANKED by specificity: structural narrowing in key space,
   candidate weight = specificity score (+1) so more-specific lemmas get a higher
   `condw` prior. The search then confirms in term space via `applyo`/`===`.
   Capped at `limit`."
  ([trie] (recall-provider trie 80))
  ([trie limit]
   (fn [s g]
     (->> (dt/trie-match-scored trie (dti/query-key (r/mvar-type s g)))
          ranked-candidates
          (take limit)
          (mapv (fn [[nm sc]] [(double (inc (long sc))) nm]))))))

(defn recall+confirm-provider
  "Like `recall-provider` but ALSO runs kernel `defeq` confirmation
   (`applies?`) — in RANKED order — so only lemmas that TRULY apply to the goal
   are returned, most-specific first, weighted by specificity for the search."
  ([trie env] (recall+confirm-provider trie env 80))
  ([trie env limit]
   (fn [s g]
     (let [gty (r/mvar-type s g)]
       (->> (dt/trie-match-scored trie (dti/query-key gty))
            ranked-candidates
            (filter (fn [[nm _]] (cf/applies? env nil gty nm)))  ; confirm in ranked order
            (take limit)
            (mapv (fn [[nm sc]] [(double (inc (long sc))) nm])))))))
