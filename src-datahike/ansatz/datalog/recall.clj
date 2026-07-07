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
            [clojure.edn :as edn])
  (:import [ansatz.kernel ConstantInfo]))

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

(defn recall-provider
  "An `inhabito`/`expro` candidate provider `(state, goal) → [[w name] …]` backed
   by disc-tree recall: structural narrowing in key space; the search then
   confirms in term space via its own `applyo`/`===`. Capped at `limit`."
  ([trie] (recall-provider trie 80))
  ([trie limit]
   (fn [s g]
     (->> (dt/trie-match trie (dti/query-key (r/mvar-type s g)))
          distinct (take limit) (mapv (fn [nm] [1.0 nm]))))))

(defn recall+confirm-provider
  "Like `recall-provider` but ALSO runs kernel `defeq` confirmation
   (`applies?`), so only lemmas that TRULY apply to the goal are returned —
   recall THEN confirm, the search just applies the survivors."
  ([trie env] (recall+confirm-provider trie env 80))
  ([trie env limit]
   (fn [s g]
     (let [gty (r/mvar-type s g)]
       (->> (dt/trie-match trie (dti/query-key gty))
            distinct
            (filter #(cf/applies? env nil gty %))
            (take limit) (mapv (fn [nm] [1.0 nm])))))))
