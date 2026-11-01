(ns prototype.executable-closure-proof
  "Assert-only static closure evidence. No checked-kernel, readiness, ownership,
   binding-registry, Source-liveness or initialization authority is cached."
  (:require [prototype.eval-const :as eval]
            [prototype.import-ir :as ir])
  (:import [java.lang.ref WeakReference]
           [java.util WeakHashMap]))

(deftype ^:private ExecutableClosureProof [functions registry roots rules])
;; Scalar values and weak keys cannot keep proofs or their code images alive.
;; A namespace reload starts a new issuance epoch; existing proofs safely miss.
(def ^:private ^WeakHashMap issued (WeakHashMap.))

(defn- same-rules? [before after]
  (and (= (count before) (count after))
       (every? true? (map identical? before after))))
(defn- rule-references-match? [references rules]
  (and (= (count references) (count rules))
       (every? true? (map (fn [reference rule]
                           (and (some? rule) (instance? WeakReference reference)
                                (identical? rule (.get ^WeakReference reference))))
                         references rules))))

(defn- ordinary-map? [value]
  (contains? #{clojure.lang.PersistentHashMap clojure.lang.PersistentArrayMap} (class value)))
(defn- frozen-sequence? [value]
  (contains? #{clojure.lang.PersistentVector clojure.lang.PersistentHashSet
               clojure.lang.PersistentList clojure.lang.PersistentList$EmptyList} (class value)))

(defn- target-cost [value]
  (cond
    (string? value) (count value)
    (keyword? value) (+ (count (name value)) (count (namespace value)))
    :else (let [bits (.bitLength (biginteger value))]
            (when (<= bits 4096) (inc (quot bits 8))))))

(defn- freeze-target [target remaining]
  ;; Freeze eligibility includes EVERY vector in a Name spine. Reject metadata
  ;; rather than retaining an owner hidden on a root or parent Name. Only exact
  ;; immutable scalar classes accepted by the existing scanner are reusable.
  (when (#'ir/frozen-target? target)
    (loop [node target depth 0]
      (when (and (< depth 4096) (pos? (vswap! remaining dec)))
        (if (= clojure.lang.PersistentVector (class node))
          (when (nil? (meta node))
            (let [[tag parent value] node]
              (if (= tag "anonymous") target
                (when-let [cost (target-cost value)]
                  (when (pos? (vswap! remaining - cost))
                    (recur parent (inc depth)))))))
          (when-let [cost (target-cost node)]
            (when (pos? (vswap! remaining - cost)) target)))))))

(defn- freeze-roots [roots]
  (when (and (frozen-sequence? roots) (<= (count roots) 256))
    (let [remaining (volatile! 65536)]
      (loop [pending (seq roots) result []]
        (if-not pending result
          (when-let [target (freeze-target (first pending) remaining)]
            ;; Preserve order and duplicates. Equality never touches caller-owned
            ;; exotic containers, metadata or mutable lookup targets on a hit.
            (recur (next pending) (conj result target))))))))

(defn- stable-closure? [functions registry closure]
  (and (ordinary-map? functions) (ordinary-map? registry)
       (every? #'ir/frozen-target? (keys functions))
       (every? #'ir/frozen-target? (keys registry))
       (every? (fn [[name function]]
                 (and (identical? function (get functions name))
                      (identical? function (get registry name))
                      (ordinary-map? function)
                      (not= :prototype.import-ir/fallback
                            (#'ir/static-targets-canonical (:body function)))
                      (let [dependencies (:runtime-dependencies function [])]
                        (and (frozen-sequence? dependencies)
                             (every? #'ir/frozen-target? dependencies)))))
               closure)))

(defn- semantic-rules []
  ;; Include transitive dependency readers and local eligibility rules: a REPL
  ;; partial defn update must invalidate facts issued under the previous rules.
  [@#'eval/validate-executables! @#'eval/check-function-closure! @#'eval/executable-dependencies
   @#'ir/static-targets @#'ir/static-targets-canonical @#'ir/frozen-target?
   @#'ir/canonical-target @#'ir/frozen-target-scalar-classes
   @#'ir/static-targets-tree @#'ir/static-targets-shared @#'ir/terminal-static-ops
   @#'ordinary-map? @#'frozen-sequence? @#'target-cost @#'freeze-target @#'freeze-roots @#'stable-closure?])

(defn- matches? [table proof functions registry roots rules]
  (and roots (some? functions) (some? registry)
       (instance? ExecutableClosureProof proof)
       (locking table (true? (.get ^WeakHashMap table proof)))
       (identical? functions (.get ^WeakReference (.-functions ^ExecutableClosureProof proof)))
       (identical? registry (.get ^WeakReference (.-registry ^ExecutableClosureProof proof)))
       (= roots (.-roots ^ExecutableClosureProof proof))
       (rule-references-match? (.-rules ^ExecutableClosureProof proof) rules)))

(defn validate!
  "Assert the requested closure with the unchanged full validator on every miss.
   Return an issued opaque proof only for stable immutable dependency structure,
   or nil after successful uncached validation. A hit requires the exact weakly
   referenced functions/registry maps, unchanged validation functions/rule values, and
   freshly frozen equal roots. Rule references are weak too. Recompute
   current binding/configuration roots before EVERY call; no live readiness check
   is replaced. No closure map, World, Context, Source or code Fn is retained strongly."
  [world registry roots previous-proof]
  (let [table issued rules (semantic-rules)
        functions (:functions world) frozen (freeze-roots roots)]
    (if (and (matches? table previous-proof functions registry frozen rules)
             (same-rules? rules (semantic-rules)))
      previous-proof
      (let [closure (eval/validate-executables! world registry roots)]
        (when (and frozen (stable-closure? functions registry closure)
                   (same-rules? rules (semantic-rules)))
          (let [proof (ExecutableClosureProof. (WeakReference. functions) (WeakReference. registry)
                                               frozen (mapv #(WeakReference. %) rules))]
            (locking table
              (when (same-rules? rules (semantic-rules))
                (.put ^WeakHashMap table proof true)
                proof))))))))
