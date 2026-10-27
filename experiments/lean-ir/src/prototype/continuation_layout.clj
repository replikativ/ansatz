(ns prototype.continuation-layout
  "Bottom-up continuation register widths. Storage hints, never executable or
   ownership authority. Payloads in literal/imm positions remain opaque."
  (:import [java.lang.ref WeakReference ReferenceQueue]
           [java.util HashMap ArrayList IdentityHashMap ArrayDeque]))

(def ^:private id-classes
  #{Long Integer Short Byte java.math.BigInteger clojure.lang.BigInt})
(defn- frozen-id? [id] (or (nil? id) (contains? id-classes (class id))))
(defn- vector?* [x] (= clojure.lang.PersistentVector (class x)))
(defn- ids-width [xs]
  (when (and (vector?* xs) (every? frozen-id? xs))
    (inc (reduce max 0 (filter integer? xs)))))
(defn- operand-width [operand]
  (when (and (vector?* operand) (= 2 (count operand)) (keyword? (first operand)))
    (if (= :var (first operand)) (ids-width [(second operand)]) 1)))
(defn- operands-width [operands]
  (when (vector?* operands)
    (loop [i 0 width 1]
      (if (= i (count operands)) width
        (when-let [next-width (operand-width (nth operands i))]
          (recur (inc i) (max width next-width)))))))
(defn- target-width [target]
  (when (and (vector?* target) (= 2 (count target)) (keyword? (first target)))
    (if (= :closure (first target)) (operand-width (second target)) 1)))
(defn- expression-width [expression fallback]
  (when (and (vector?* expression) (keyword? (first expression)))
    (let [[op a b] expression]
      (case op
        :literal 1
        (:ctor :scalar-ctor :closure :runtime :prim) (operands-width b)
        (:project :shared? :scalar-get) (operand-width a)
        (:box :unbox) (operand-width b)
        (max 1 fallback)))))
(defn- branch-bodies [branches]
  (when (and (vector?* branches)
             (every? #(and (vector?* %) (= 2 (count %))) branches))
    (mapv second branches)))
(defn- description [body fallback]
  ;; Read exactly the register-bearing fields used by the reference scanner.
  ;; In particular do not walk callee/module names, layouts, labels or values.
  (when (and (vector?* body) (keyword? (first body)))
    (let [[op a b c d] body
          descriptor
          (case op
            :let (when-let [dest (ids-width [a])]
                   (when-let [expression (expression-width b fallback)]
                     [(max dest expression) [c]]))
            :call (when-let [dest (ids-width [a])]
                    (when-let [args (operands-width c)]
                      (when-let [target (target-width b)] [(max dest args target) [d]])))
            :tail (when-let [args (operands-width b)]
                    (when-let [target (target-width a)] [(max args target) []]))
            :return (when-let [width (operand-width a)] [width []])
            (:read-global :global :unreachable) [1 []]
            :begin-init (when-let [width (operands-width c)] [width []])
            :publish-global (when-let [width (operand-width b)] [width []])
            :publish-io-global (when-let [width (operand-width c)] [width []])
            :join (when-let [width (ids-width b)] [width [c d]])
            :jump (when-let [width (operands-width b)] [width []])
            :case (when-let [width (operand-width a)]
                    (when-let [children (branch-bodies b)] [width children]))
            :trap (when-let [width (operands-width b)] [width []])
            :del (when-let [width (operand-width a)] [width [b]])
            (:set-tag :inc :dec) (when-let [width (operand-width a)] [width [c]])
            (:set :scalar-set) (when-let [left (operand-width a)]
                                (when-let [right (operand-width c)] [(max left right) [d]]))
            :suspend (when-let [width (ids-width [a])] [width [b]])
            :host (when-let [args (operands-width b)]
                    (when-let [dest (ids-width [c])] [(max args dest) [d]]))
            ;; The old scanner reads no children of an unknown instruction.
            [(max 1 fallback) []])]
      ;; A missing child is NOT the same as a missing root in the old scanner.
      ;; Preserve that edge through uncached fallback instead of inventing a width.
      (when (and descriptor (every? vector?* (second descriptor))) descriptor))))

(def ^:private cache {:buckets (HashMap.) :queue (ReferenceQueue.) :owner (volatile! nil)})
(defn- ensure-owner! [generation]
  (let [^WeakReference previous @(:owner cache)]
    (when-not (and previous (identical? generation (.get previous)))
      (.clear ^HashMap (:buckets cache))
      (vreset! (:owner cache) (WeakReference. generation)))))
(defn- drain! []
  (let [^HashMap buckets (:buckets cache) ^ReferenceQueue queue (:queue cache)]
    (loop []
      (when-let [dead (.poll queue)]
        (let [key (.hashCode dead) ^ArrayList bucket (.get buckets key)]
          (when bucket
            (loop [i (dec (.size bucket))]
              (when (<= 0 i)
                (when (identical? dead (first (.get bucket i))) (.remove bucket (int i)))
                (recur (dec i))))
            (when (.isEmpty bucket) (.remove buckets key))))
        (recur)))))
(defn- cached-entry [body]
  ;; A cleared referent is never evidence for a missing root, even in an
  ;; identity-hash collision bucket before queue cleanup has run.
  (when (some? body)
    (let [^ArrayList bucket (.get ^HashMap (:buckets cache) (System/identityHashCode body))]
      (when bucket
        (some #(when (identical? body (.get ^WeakReference (first %))) %) bucket)))))
(defn- cached-width [body fallback]
  (let [entry (cached-entry body)] (when (= fallback (second entry)) (nth entry 2))))
(defn- remember! [body fallback width]
  (let [^HashMap buckets (:buckets cache) key (System/identityHashCode body)
        ^ArrayList bucket (or (.get buckets key) (ArrayList.))]
    ;; One replaceable fallback/width per live body, never a fallback history.
    (loop [i (dec (.size bucket))]
      (when (<= 0 i)
        (when (identical? body (.get ^WeakReference (first (.get bucket i))))
          (.remove bucket (int i)))
        (recur (dec i))))
    (let [reference (proxy [WeakReference] [body (:queue cache)] (hashCode [] key))]
      (.add bucket [reference fallback width])
      (.put buckets key bucket))))
(defn- analyze [body fallback]
  (let [pending (ArrayDeque.) widths (IdentityHashMap.) descriptions (IdentityHashMap.)
        visiting (IdentityHashMap.) entries (ArrayList.)]
    (.push pending [body false])
    (loop []
      (if (.isEmpty pending)
        {:width (.get widths body) :entries entries}
        (let [[node expanded?] (.pop pending)]
          (cond
            (.containsKey widths node) (recur)
            expanded?
            (let [[local children] (.get descriptions node)
                  width (reduce (fn [width child] (max width (.get widths child))) local children)]
              (.put widths node width)
              (.remove visiting node)
              (.add entries [node width])
              (recur))
            (.containsKey visiting node) nil
            :else
            (if-let [width (cached-width node fallback)]
              (do (.put widths node width) (recur))
              (when-let [[_ children :as descriptor] (description node fallback)]
                (.put descriptions node descriptor)
                (.put visiting node true)
                (.push pending [node true])
                (doseq [child (rseq children)] (.push pending [child false]))
                (recur)))))))))

(def ^:private rule-baseline
  ;; Old analysis functions are never held strongly across REPL redefinitions.
  (mapv #(WeakReference. %) [id-classes frozen-id? vector?* ids-width operand-width
                            operands-width target-width expression-width branch-bodies description analyze
                            ensure-owner! drain! cached-entry cached-width remember!]))
(defn- builtin-analysis? []
  (and (identical? (.get ^WeakReference (nth rule-baseline 0)) id-classes)
       (identical? (.get ^WeakReference (nth rule-baseline 1)) frozen-id?)
       (identical? (.get ^WeakReference (nth rule-baseline 2)) vector?*)
       (identical? (.get ^WeakReference (nth rule-baseline 3)) ids-width)
       (identical? (.get ^WeakReference (nth rule-baseline 4)) operand-width)
       (identical? (.get ^WeakReference (nth rule-baseline 5)) operands-width)
       (identical? (.get ^WeakReference (nth rule-baseline 6)) target-width)
       (identical? (.get ^WeakReference (nth rule-baseline 7)) expression-width)
       (identical? (.get ^WeakReference (nth rule-baseline 8)) branch-bodies)
       (identical? (.get ^WeakReference (nth rule-baseline 9)) description)
       (identical? (.get ^WeakReference (nth rule-baseline 10)) analyze)
       (identical? (.get ^WeakReference (nth rule-baseline 11)) ensure-owner!)
       (identical? (.get ^WeakReference (nth rule-baseline 12)) drain!)
       (identical? (.get ^WeakReference (nth rule-baseline 13)) cached-entry)
       (identical? (.get ^WeakReference (nth rule-baseline 14)) cached-width)
       (identical? (.get ^WeakReference (nth rule-baseline 15)) remember!)))

(defn width
  "Return a continuation width, computing all eligible child widths bottom-up.
   OWNER-BUILTIN? must assert that LEGACY and its sizing helpers retain their
   built-in semantics. Any unsupported structure or changed analysis rule takes
   the untouched LEGACY path. No partial traversal is published on a miss.
   Live locals, pending destinations and joins must still be sized by the caller."
  [body fallback legacy owner-builtin? generation]
  (let [guard? #(and (owner-builtin?) (builtin-analysis?))
        result
        (when (and (guard?) (frozen-id? fallback) (integer? fallback))
          (locking cache
            (ensure-owner! generation)
            (drain!)
            (if-let [width (cached-width body fallback)]
              (when (guard?) width)
              (let [analysis (try (analyze body fallback) (catch Exception _ nil))]
                (when (and analysis (guard?))
                  (doseq [[node width] (:entries analysis)] (remember! node fallback width))
                  (:width analysis))))))]
    (let [stable? (guard?)]
      (if (and result stable?) result
        (do
          ;; Discard facts if a rule changed, including during publication.
          ;; Use no changed analysis/cache helper on the fallback path.
          (when-not stable? (locking cache (.clear ^HashMap (:buckets cache))))
          (legacy body fallback))))))
