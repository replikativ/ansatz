(ns ansatz.export.non-safe
  "Plan unsafe/partial DEF admission from actual body references. DefinitionVal.all
   remains preserved compiler metadata; it never determines kernel groups."
  (:require [clojure.set :as set])
  (:import [ansatz.kernel ConstantInfo Expr Name]))

(defn non-safe-definition? [^ConstantInfo ci]
  (and (.isDef ci)
       (case (int (.safety ci))
         0 false
         (1 2) true
         (throw (ex-info "Invalid definition safety in replay input"
                         {:name (str (.name ci)) :safety (int (.safety ci))})))))

(defn expression-dependencies
  "Global Names referenced by an Expr DAG, including implicit literal types and
   PROJ structure names. Iterative identity traversal avoids expanding sharing."
  [root]
  (loop [pending (if root [root] []) seen (java.util.IdentityHashMap.) out #{}]
    (if (empty? pending) out
        (let [^Expr e (peek pending) pending (pop pending)]
          (if (.containsKey seen e) (recur pending seen out)
              (let [_ (.put seen e true)
                    children (case (.tag e)
                               3 [(.o0 e) (.o1 e)] (4 5) [(.o1 e) (.o2 e)]
                               6 [(.o1 e) (.o2 e) (.o3 e)] (9 10) [(.o1 e)] [])
                    out (case (.tag e) 2 (conj out (.o0 e))
                              7 (conj out (Name/mkStr Name/ANONYMOUS_NAME "Nat"))
                              8 (conj out (Name/mkStr Name/ANONYMOUS_NAME "String"))
                              10 (conj out (.o0 e)) out)]
                (recur (into pending children) seen out)))))))

(defn- finish-order [graph roots]
  (second
   (reduce
    (fn [[seen order] root]
      (loop [pending [[root false]] seen seen order order]
        (if-let [[node finish?] (peek pending)]
          (let [pending (pop pending)]
            (cond finish? (recur pending seen (conj order node))
                  (contains? seen node) (recur pending seen order)
                  :else (recur (into (conj pending [node true])
                                     (map #(vector % false)) (get graph node))
                               (conj seen node) order)))
          [seen order]))) [#{} []] roots)))

(defn- components [graph roots]
  (let [reverse-graph (reduce-kv (fn [g from tos]
                                   (reduce #(update %1 %2 conj from) g tos))
                                 (zipmap roots (repeat [])) graph)]
    (second
     (reduce
      (fn [[seen groups] root]
        (if (contains? seen root) [seen groups]
            (let [[seen members]
                  (loop [pending [root] seen seen members []]
                    (if-let [node (peek pending)]
                      (if (contains? seen node)
                        (recur (pop pending) seen members)
                        (recur (into (pop pending) (get reverse-graph node))
                               (conj seen node) (conj members node)))
                      [seen members]))]
              [seen (conj groups members)])))
      [#{} []] (rseq (finish-order graph roots))))))

(defn plan
  "Return Name->SCC plan for all non-safe DEFs. Each group carries original input
   indices/members, its last index, and external header/body dependencies. Only
   value CONST edges between non-safe DEFs form SCCs; recursive headers are NOT
   authorized. Group admission remains the kernel's responsibility."
  [declarations]
  (let [entries (filterv (fn [[_ ci]] (non-safe-definition? ci)) (map-indexed vector declarations))
        names (mapv (fn [[_ ^ConstantInfo ci]] (.name ci)) entries)]
    (when-not (= (count names) (count (set names)))
      (throw (ex-info "Duplicate non-safe definition names in replay input" {})))
    (let [index (into {} (map (fn [[i ^ConstantInfo ci]] [(.name ci) {:index i :constant ci}])) entries)
          body-deps (into {} (map (fn [[_ ^ConstantInfo ci]]
                                    [(.name ci) (expression-dependencies (.value ci))])) entries)
          graph (into {} (map (fn [name]
                                [name (vec (sort-by #(get-in index [% :index])
                                                    (filter index (get body-deps name))))])) names)]
      (reduce
       (fn [out group-names]
         (let [ordered (sort-by #(get-in index [% :index]) group-names)
               indices (mapv #(get-in index [% :index]) ordered)
               members (mapv #(get-in index [% :constant]) ordered)
               dependencies (reduce (fn [out ^ConstantInfo ci]
                                      (set/union out (get body-deps (.name ci))
                                                 (expression-dependencies (.type ci)))) #{} members)
               group {:indices indices :members members :last-index (peek indices)
                      :external-dependencies (set/difference dependencies (set group-names))}]
           (reduce #(assoc %1 %2 group) out group-names)))
       {} (components graph names)))))
