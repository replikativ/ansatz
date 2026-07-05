;; Shared tactic term elaboration helpers.

(ns ansatz.tactic.elab-term
  "Lean-shaped tactic helpers for elaborating terms while collecting holes.

   This is the tactic-level analogue of Lean's `elabTermWithHoles`: elaborate a
   surface term in a goal context, collect fresh reachable holes, reject natural
   holes unless explicitly allowed, install the resulting metacontext in the
   proof state, and tag anonymous collected goals."
  (:require [clojure.string :as str]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.meta :as meta]
            [ansatz.surface.elaborate :as surface]
            [ansatz.tactic.proof :as proof]))

(defn- tactic-error! [msg data]
  (throw (ex-info (str "Tactic error: " msg) (merge {:kind :tactic-error} data))))

(defn- max-collected-mvar-id [mctx]
  (reduce max 0 (concat (keys (:decls mctx)) (keys (:level-depth mctx)))))

(defn- hole-display-name [hole]
  (if-let [user-name (:user-name hole)]
    (str "?" (name/->string user-name))
    (str "?m." (:id hole))))

(defn hole-diagnostic [hole]
  (assoc hole
         :display-name (hole-display-name hole)
         :type-str (e/->string (:type hole))))

(defn format-hole-diagnostics [holes]
  (str/join
   "\n"
   (map (fn [hole]
          (str "  " (:display-name hole) " : " (:type-str hole)))
        holes)))

(defn- collected-holes [mctx expr start-index]
  (mapv (fn [id]
          (let [decl (meta/expr-decl mctx id)]
            {:id id
             :expr (e/mvar id)
             :type (meta/zonk-expr mctx (:type decl))
             :kind (:kind decl)
             :user-name (:user-name decl)
             :inst-implicit? (boolean (:inst-implicit? decl))}))
        (meta/fresh-result-mvar-ids mctx expr start-index)))

(defn- collected-level-holes [mctx expr old-level-ids]
  (mapv (fn [id]
          {:id id
           :level (lvl/mvar id)
           :name (name/from-string (str "?u" id))})
        (meta/fresh-result-level-ids mctx expr old-level-ids)))

(defn elab-term-with-holes
  "Elaborate `form` in `goal` and collect newly-created holes.

   Options:
   - `:allow-natural-holes?` mirrors Lean's `allowNaturalHoles`.
   - `:tag-suffix` is used by `proof/tag-untagged-goals`.
   - `:tactic-name` prefixes diagnostics.
   - `:expected-type`, when omitted, defaults to the current goal type; when
     present as nil, elaborates without an expected type.
   - `:after-elab` may return an updated `{:expr ... :meta-mctx ...}` before
     final hole collection.

   Returns a map with the updated proof state under `:ps`, the raw elaborated
   `:expr`, the mvar-instantiated `:checked-expr`, all collected `:holes`, and
   the visible goal ids under `:visible-ids`."
  [ps goal form opts]
  (let [{:keys [allow-natural-holes? tag-suffix tactic-name expected-type parent-tag
                natural-hole-hint after-elab]
         :or {allow-natural-holes? false
              tactic-name "tactic"}} opts
        expected-provided? (contains? opts :expected-type)
        initial-meta-mctx (:meta-mctx ps)
        start-index (:mvar-counter initial-meta-mctx 0)
        old-level-ids (set (keys (:level-depth initial-meta-mctx)))
        parent-tag (or parent-tag (:user-name goal))
        tag-suffix (or tag-suffix (name/from-string tactic-name))
        expected-type (if expected-provided? expected-type (:type goal))
        next-id-start (max 1000000 (:next-id ps 1))
        {:keys [expr meta-mctx]}
        (surface/elaborate-in-context-collecting (:env ps) (:lctx goal) form expected-type
                                                 {:next-id-start next-id-start
                                                  :initial-meta-mctx initial-meta-mctx
                                                  :holes-as-synthetic-opaque? allow-natural-holes?})
        {:keys [expr meta-mctx]}
        (cond-> {:expr expr :meta-mctx meta-mctx}
          after-elab after-elab)
        checked-expr (meta/zonk-expr meta-mctx expr)
        holes (collected-holes meta-mctx checked-expr start-index)
        level-holes (collected-level-holes meta-mctx checked-expr old-level-ids)
        natural-holes (filterv #(= :natural (:kind %)) holes)]
    (when (seq level-holes)
      (tactic-error! (str tactic-name ": unresolved universe level holes")
                     {:level-holes level-holes}))
    (when (and (not allow-natural-holes?) (seq natural-holes))
      (let [diagnostics (mapv hole-diagnostic natural-holes)]
        (tactic-error! (str tactic-name ": unresolved natural holes\n"
                            (format-hole-diagnostics diagnostics)
                            (when natural-hole-hint
                              (str "\n" natural-hole-hint)))
                       {:holes natural-holes
                        :hole-diagnostics diagnostics
                        :hole-count (count diagnostics)})))
    (let [visible-holes (if allow-natural-holes?
                          holes
                          (remove #(= :natural (:kind %)) holes))
          visible-ids (mapv :id visible-holes)
          ps (-> ps
                 (assoc :meta-mctx meta-mctx)
                 (update :next-id #(max (or % 1) (inc (max-collected-mvar-id meta-mctx))))
                 (proof/prune-solved-goals)
                 (proof/tag-untagged-goals parent-tag tag-suffix visible-ids))]
      {:ps ps
       :expr expr
       :checked-expr checked-expr
       :holes holes
       :visible-holes visible-holes
       :visible-ids visible-ids
       :meta-mctx meta-mctx
       :parent-tag parent-tag
       :tag-suffix tag-suffix})))
