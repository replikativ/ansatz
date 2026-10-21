(ns prototype.source-graph-plan
  "Pure bounded planning for ordinary source-module graphs. Descriptors and version
   tokens are host inputs, NOT authenticated publications or checking capabilities.
   This namespace performs no guest work, registry changes, imports or checking.")

(def ^:private limit-keys
  #{:max-modules :max-roots :max-edges :max-depth :max-names
    :max-name-nodes :max-name-chars :max-total-name-chars})
(defn- fail! [reason] (throw (ex-info "Invalid bounded source graph plan" {:reason reason})))
(defn- shape! [value keys]
  (when-not (and (map? value) (= (count keys) (count value))
                 (every? #(contains? value %) keys))
    (fail! :shape)))
(defn- vector! [value limit]
  (when-not (and (vector? value) (<= (count value) limit)) (fail! :inventory-limit)))
(defn- limits! [limits]
  (shape! limits limit-keys)
  (when-not (every? #(and (integer? %) (<= 1 % Long/MAX_VALUE)) (vals limits))
    (fail! :limits))
  limits)
(defn- name! [encoded module? limits total-chars]
  (loop [current encoded nodes 0 chars 0]
    (when (> (inc nodes) (:max-name-nodes limits)) (fail! :name-limit))
    (if (= ["anonymous"] current)
      (when (and module? (zero? nodes)) (fail! :module-name))
      (do
        (when-not (and (vector? current) (= 3 (count current))) (fail! :name))
        (let [[tag parent part] current
              string-node? (= "str" tag)]
          (when-not (and (or string-node? (= "num" tag)) (string? part)) (fail! :name))
          ;; count(String) is constant-time. Gate both budgets BEFORE any dot
          ;; scan or numeric digit validation. Numeric wire segments stay strings:
          ;; no parse, BigInteger construction, or giant integer rendering.
          (let [chars' (+' chars (count part))
                total' (+' @total-chars (count part))]
            (when (or (> chars' (:max-name-chars limits))
                      (> total' (:max-total-name-chars limits))) (fail! :name-limit))
            (when (and module? (or (not string-node?) (empty? part) (.contains ^String part ".")))
              (fail! :module-name))
            (when (and (not string-node?) (not (re-matches #"(?:0|[1-9][0-9]*)" part)))
              (fail! :name))
            (vreset! total-chars total')
            (recur parent (inc nodes) chars'))))))
  encoded)

(defn- preflight! [native nodes roots limits]
  ;; Count containers before expanding names/edges. All later maps key only
  ;; validated bounded Names; opaque version tokens are compared by identity.
  (vector! native (:max-modules limits)) (vector! nodes (:max-modules limits))
  (vector! roots (:max-roots limits))
  (when (> (+' (count native) (count nodes)) (:max-modules limits)) (fail! :inventory-limit))
  (doseq [node native] (shape! node #{:module :const-names :extra-names}))
  (doseq [node nodes] (shape! node #{:module :version :dependencies :const-names :extra-names}))
  (doseq [node (concat native nodes)]
    (vector! (:const-names node) (:max-names limits))
    (vector! (:extra-names node) (:max-names limits)))
  (doseq [node nodes]
    (when (nil? (:version node)) (fail! :version))
    (vector! (:dependencies node) (:max-edges limits)))
  (let [edges (reduce +' 0 (map #(count (:dependencies %)) nodes))
        names (reduce +' (+' (count native) (count nodes) (count roots) edges)
                      (map #(+' (count (:const-names %)) (count (:extra-names %))) (concat native nodes)))]
    (when (> edges (:max-edges limits)) (fail! :edge-limit))
    (when (> names (:max-names limits)) (fail! :inventory-limit)))
  (doseq [reference (concat roots (mapcat :dependencies nodes))]
    (shape! reference #{:module :version})
    (when (nil? (:version reference)) (fail! :version)))
  (let [total (volatile! 0)]
    (doseq [node (concat native nodes)]
      (name! (:module node) true limits total)
      (doseq [name (concat (:const-names node) (:extra-names node))]
        (name! name false limits total)))
    (doseq [reference (concat roots (mapcat :dependencies nodes))]
      (name! (:module reference) true limits total))
    @total))

(defn- index! [native nodes]
  (let [native-modules (mapv :module native) native-set (set native-modules)]
    (when-not (= (count native-modules) (count (set native-modules))) (fail! :duplicate-module))
    (reduce (fn [out node]
              (let [module (:module node)]
                (when (or (contains? out module) (contains? native-set module))
                  (fail! :duplicate-module))
                (assoc out module node))) {} nodes)))
(defn- ordered-closure! [index roots max-depth]
  ;; Explicit frames reproduce dependency-first DFS in actual root/dependency
  ;; vector order. Heights also bound paths through already visited ancestors,
  ;; so root order cannot conceal an over-depth graph.
  (loop [pending (mapv #(vector :enter % 1) (rseq roots)) colors {} heights {} order []]
    (if (empty? pending) order
      (let [[action reference depth] (peek pending) pending (pop pending)
            module (:module reference) node (get index module)]
        (when-not node (fail! :missing-module))
        (when-not (identical? (:version reference) (:version node)) (fail! :version-conflict))
        (if (= :leave action)
          (let [height (inc (reduce max 0 (map #(get heights (:module %)) (:dependencies node))))]
            (when (> (+ depth height -1) max-depth) (fail! :depth-limit))
            (recur pending (assoc colors module :done) (assoc heights module height) (conj order module)))
          (do
            (when (> depth max-depth) (fail! :depth-limit))
            (case (get colors module)
              :visiting (fail! :cycle)
              :done (do (when (> (+ depth (get heights module) -1) max-depth) (fail! :depth-limit))
                        (recur pending colors heights order))
              (let [pending (conj pending [:leave reference depth])
                    pending (reduce #(conj %1 [:enter %2 (inc depth)]) pending (rseq (:dependencies node)))]
                (recur pending (assoc colors module :visiting) heights order)))))))))

(defn- native-attribution [native]
  ;; An already authenticated native prefix can have legitimate first-wins
  ;; aliases/subsumption. Preserve that order; never widen it for source names.
  (reduce (fn [out [index node]]
            (reduce (fn [out [kind name]]
                      (if (contains? out name) out
                        (assoc out name {:module (:module node) :module-index index :kind kind})))
                    out (concat (map #(vector :constant %) (:const-names node))
                                (map #(vector :extra %) (:extra-names node)))))
          {} (map-indexed vector native)))
(defn- source-attribution! [initial index order offset]
  (reduce (fn [out [position module]]
            (let [node (get index module)]
              (doseq [key [:const-names :extra-names]]
                (when-not (= (count (get node key)) (count (set (get node key))))
                  (fail! :duplicate-local-name)))
              (reduce (fn [out [kind name]]
                        (if-let [previous (get out name)]
                          (if (= module (:module previous)) out (fail! :attribution-conflict))
                          (assoc out name {:module module :module-index (+ offset position) :kind kind})))
                      out (concat (map #(vector :constant %) (:const-names node))
                                  (map #(vector :extra %) (:extra-names node))))))
          initial (map-indexed vector order)))

(defn plan
  "Return DESCRIPTIVE ordered closure/attempt-local attribution only; no authority.
   NATIVE is an ordered vector of {:module :const-names :extra-names} records.
   NODES adds :version (opaque identity token) and :dependencies (ordered vectors
   of {:module :version} source references). ROOTS has the same reference shape.
   Names use Lean JSON encoding; numeric segments are canonical decimal strings
   bounded before digit scans and never parsed. Kernel projectability is separate.
   Implicit Init/header/flag/CI/unit authenticity belongs to a future issued graph
   adapter, not this pure planner. Only reachable source nodes affect ordering or
   attribution; all input inventory/container/Name budgets are checked first.
   Native first-wins attribution stays intact. Source const/extra names cannot
   collide with another node/native attribution; a same-node constant repeated
   in its extra vector preserves the constant attribution. No alphabetic sort."
  [native nodes roots limits]
  (limits! limits)
  (let [chars (preflight! native nodes roots limits)
        index (index! native nodes)
        order (ordered-closure! index roots (:max-depth limits))
        modules (into (mapv :module native) order)
        attribution (source-attribution! (native-attribution native) index order (count native))]
    {:source-order order :module-order modules
     :module-indices (into {} (map-indexed (fn [i module] [module i]) modules))
     :name-attribution attribution
     :counts {:provided-modules (+ (count native) (count nodes))
              :selected-source-modules (count order) :ordered-modules (count modules)
              :attributed-names (count attribution) :validated-name-chars chars}}))
