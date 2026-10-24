(ns ansatz.bundle-semantic-policy
  "Bounded diagnostic comparison of supplied role CIs and syntactic CSimp rows.
   No kernel checking, native oracle/provenance binding, receipt, or activation."
  (:require [ansatz.kernel.constant-info :as ci])
  (:import [ansatz.kernel ConstantInfo Expr Level Name]
           [clojure.lang PersistentVector PersistentArrayMap PersistentHashMap]
           [java.util IdentityHashMap]))

(def ^:private input-limit-keys
  #{:declarations :templates :registrations :name-components :name-bytes :name-depth :level-slots})
(def ^:private comparison-limit-keys #{:pairs :edges :items :scalar-bytes :depth})
(def ^:private row-keys #{:source :target :witness :global-ordinal})
(def ^:private eq-name [[:str "Eq"]])
(defn- fail [reason data]
  (throw (ex-info "Supplied role semantic comparison refused"
                  (assoc data :type ::comparison-refused :reason reason))))
(defn- vector! [value]
  (when-not (identical? PersistentVector (class value)) (fail :unsupported-vector {})) value)
(defn- standard-map? [value]
  (or (identical? PersistentArrayMap (class value)) (identical? PersistentHashMap (class value))))
(defn- exact-keys? [value expected]
  ;; Reject unknown key objects before any generic set/hash operation can invoke
  ;; their equality/hash implementations. Standard map iteration/count is finite.
  (and (standard-map? value) (= (count expected) (count value))
       (every? #(and (keyword? %) (contains? expected %)) (keys value))))
(defn- primitive-integer? [value]
  (or (instance? Long value) (instance? Integer value) (instance? Short value) (instance? Byte value)))

(defn compare-role-bounded
  "Compare finite standard vectors of supplied role CIs, ordered CSimp rows and
   explicit axiom templates. Rows have exact Name-valued :source/:target/:witness
   and increasing primitive nonnegative :global-ordinal. Keep duplicate sources.
   limits = {:inputs {...all seven input-limit-keys...} :comparison {...existing
   full-CI comparator limits...}}. All inputs/arrays must remain quiescent.

   Every observed axiom needs an exact complete template match; unused templates
   may describe other image roles. Templates must be independently trusted by
   their caller. This function does NOT establish that independence, native
   correspondence, or kernel typing. Compiler-marker axioms can be compared as
   image declarations; this does not admit them as safe-proof assumptions.

   Syntactic checks follow pinned Lean819816b2 Recognizers.eq?/CSimpAttr. No
   reduction, wrapper stripping or theorem-universe-list restriction is added.
   Safe body-bearing witness fields are a stricter diagnostic runtime policy;
   unsafe AND partial definitions are refused (Declaration.lean:453-465).

   Result contains detached counts/order diagnostics only. Native binding, proof
   assumptions and implemented_by's lossless native Expr.eqv bridge remain pending.
   No result authorizes a certificate, producer profile, promotion or activation."
  [role-cis ordered-csimp axiom-templates limits]
  (when-not (and (exact-keys? limits #{:inputs :comparison})
                 (exact-keys? (:inputs limits) input-limit-keys)
                 (exact-keys? (:comparison limits) comparison-limit-keys)
                 (every? #(and (integer? %) (pos? %) (<= % Long/MAX_VALUE)) (vals (:inputs limits)))
                 (<= (:name-depth (:inputs limits)) 256))
    (fail :explicit-finite-limits-required {}))
  (doseq [values [role-cis ordered-csimp axiom-templates]] (vector! values))
  (let [caps (:inputs limits) usage (volatile! {}) name-cache (IdentityHashMap.)
        charge! (fn [key amount]
                  (let [total (+' (get @usage key 0) amount)]
                    (when (> total (get caps key))
                      (fail :input-limit {:limit key :maximum (get caps key) :actual total}))
                    (vswap! usage assoc key total)))
        name-key
        (fn [root]
          (or (.get name-cache root)
              (let [key
                    (loop [value root segments [] depth 1]
                      (when (> depth (:name-depth caps))
                        (fail :input-limit {:limit :name-depth :maximum (:name-depth caps) :actual depth}))
                      (when-not (instance? Name value) (fail :invalid-name {}))
                      (charge! :name-components 1)
                      (let [^Name value value]
                        (case (int (.tag value))
                          0 (vec (rseq segments))
                          1 (let [text (.str value)]
                              (when-not (string? text) (fail :invalid-name {}))
                              (charge! :name-bytes (*' 2 (.length ^String text)))
                              (recur (.prefix value) (conj segments [:str text]) (inc depth)))
                          2 (do (when (neg? (.num value)) (fail :unsupported-native-name-number {}))
                                (charge! :name-bytes 8)
                                (recur (.prefix value) (conj segments [:num (.num value)]) (inc depth)))
                          (fail :invalid-name {}))))]
                (.put name-cache root key) key)))
        index-cis
        (fn [values template?]
          (reduce (fn [index value]
                    (when-not (instance? ConstantInfo value) (fail :invalid-ci {}))
                    (let [^ConstantInfo value value key (name-key (.name value))]
                      (when (and template? (not (.isAxiom value))) (fail :non-axiom-template {}))
                      (when (contains? index key) (fail :duplicate-declaration-name {}))
                      (assoc index key value))) {} values))]
    ;; Exact vector count gates precede name traversal, pair construction or
    ;; index hashing. Canonical keys contain only primitive tagged segments.
    (charge! :declarations (count role-cis))
    (charge! :templates (count axiom-templates))
    (charge! :registrations (count ordered-csimp))
    (let [role (index-cis role-cis false) templates (index-cis axiom-templates true)
          rows (loop [index 0 previous -1 result []]
                 (if (= index (count ordered-csimp)) result
                     (let [row (nth ordered-csimp index)]
                       (when-not (exact-keys? row row-keys)
                         (fail :invalid-registration {:row-index index}))
                       (let [ordinal (:global-ordinal row)]
                         (when-not (and (primitive-integer? ordinal) (< previous ordinal))
                           (fail :invalid-registration-order {:row-index index}))
                         (recur (inc index) ordinal
                                (conj result {:source (name-key (:source row)) :target (name-key (:target row))
                                              :witness (name-key (:witness row)) :global-ordinal ordinal}))))))
          axioms (filterv #(.isAxiom ^ConstantInfo %) role-cis)
          axiom-pairs (mapv (fn [^ConstantInfo value]
                             (if-let [template (get templates (name-key (.name value)))]
                               [value template]
                               (fail :missing-axiom-template {}))) axioms)
          pairs (into (mapv #(vector % %) role-cis)
                      (concat (map #(vector % %) axiom-templates) axiom-pairs))]
      ;; One shared completeness/identity-pair budget for all supplied CIs,
      ;; templates and observed-axiom comparisons. No full-shape/AST equals/hash.
      (when-not (ci/full-equal-batch-bounded? pairs (:comparison limits))
        (fail :axiom-template-mismatch {}))
      (let [parameter-keys
            (fn [levels]
              (let [array? (instance? (class (object-array 0)) levels)
                    size (if array? (alength ^objects levels) (count levels))]
                (charge! :level-slots size)
                (mapv (fn [i]
                        (let [^Level value (if array? (aget ^objects levels i) (nth levels i))]
                          (when-not (= 4 (int (.tag value))) (fail :non-parameter-universe {}))
                          (name-key (.o0 value)))) (range size))))
            diagnostics
            (mapv
             (fn [index {:keys [source target witness global-ordinal]}]
               (when-not (and (contains? role source) (contains? role target) (contains? role witness))
                 (fail :registration-outside-role {:row-index index :global-ordinal global-ordinal}))
               (let [^ConstantInfo declaration (get role witness)
                     tag (int (.tag declaration))]
                 (when-not (case tag 1 (= 0 (.getDefinitionSafety declaration)) 2 true
                                 3 (not (.isUnsafe declaration)) false)
                   (fail :witness-kind-or-safety {:row-index index :global-ordinal global-ordinal}))
                 ;; Full comparator completeness already required the body. Peel
                 ;; exactly three applications, matching app3?/eq? without defeq.
                 (let [type (.type declaration)]
                   (when-not (and (= 3 (int (.tag ^Expr type)))
                                  (= 3 (int (.tag ^Expr (.o0 ^Expr type))))
                                  (= 3 (int (.tag ^Expr (.o0 ^Expr (.o0 ^Expr type))))))
                     (fail :witness-not-direct-equality {:row-index index :global-ordinal global-ordinal}))
                   (let [^Expr rhs (.o1 ^Expr type)
                         ^Expr second (.o0 ^Expr type)
                         ^Expr lhs (.o1 second)
                         ^Expr first (.o0 second)
                         ^Expr head (.o0 first)]
                     (when-not (and (= 2 (int (.tag head))) (= eq-name (name-key (.o0 head)))
                                    (= 2 (int (.tag lhs))) (= source (name-key (.o0 lhs)))
                                    (= 2 (int (.tag rhs))) (= target (name-key (.o0 rhs))))
                       (fail :witness-endpoints {:row-index index :global-ordinal global-ordinal}))
                     (let [us (parameter-keys (.o1 lhs)) vs (parameter-keys (.o1 rhs))]
                       (when-not (and (= us vs) (= (count us) (count (set us))))
                         (fail :witness-universes {:row-index index :global-ordinal global-ordinal})))))
                 {:row-index index :global-ordinal global-ordinal
                  :witness-kind (case tag 1 :definition 2 :theorem 3 :opaque)}))
             (range) rows)]
        {:authority :none :native-binding :pending :proof-assumptions :pending
         :implemented-by :pending-lossless-native-eqv-bridge
         :declaration-count (count role-cis) :axiom-comparison-count (count axioms)
         :registrations diagnostics :input-usage @usage}))))
