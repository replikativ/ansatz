(ns ansatz.lean.jvm.value
  "Borrowed, type-directed result decoding. No guest allocation or RC operation.
   The caller keeps the actual owned result root until decoding completes."
  (:require [ansatz.lean.jvm.codec :as codec]
            [ansatz.lean.jvm.scalar-buffer :as scalar]
            [ansatz.lean.jvm.entry :as entry]
            [ansatz.lean.jvm.signature :as signature]
            [ansatz.lean.jvm.startup :as startup])
  (:import [ansatz.lean.jvm LeanChoice] [java.lang.reflect Field] [java.util ArrayList IdentityHashMap List Optional]))

(def ^:private maximum-occurrences 100000)
(def ^:private maximum-depth 128)
(def ^:private object-array-class (class (object-array 0)))
(def ^:private byte-array-class (class (byte-array 0)))
(defn- need [ok message]
  (when-not ok (throw (ex-info message {:code "RuntimeBoundary"}))))
(defn- limit! [ok message]
  (when-not ok (throw (ex-info message {:code "ResourceLimit"}))))
(defn- name-of [parts]
  (reduce (fn [prefix leaf] ["str" prefix leaf]) ["anonymous"] parts))
(def ^:private family-names
  {"product" (name-of ["Prod"]) "option" (name-of ["Option"])
   "list" (name-of ["List"]) "sum" (name-of ["Sum"]) "except" (name-of ["Except"]) "io" (name-of ["EST" "Out"])})
(defn- witness-index [witnesses]
  (if (nil? witnesses) {}
    (let [families (get witnesses "families")]
      (need (and (= "Lean.Compiler.LCNF.getCtorLayout" (get witnesses "algorithm"))
                 (= "actual-persisted-native-compiler-layout-not-host-allocation-authority" (get witnesses "scope"))
                 (vector? families) (<= (count families) 8)) "Malformed native codec witness collection")
      (reduce (fn [index family]
                (let [name (get family "typeName") constructors (get family "constructors")]
                  (need (and (contains? (set (vals family-names)) name) (not (contains? index name))
                             (nil? (get family "trivialStructure"))
                             (vector? constructors) (<= 1 (count constructors) 4)) "Malformed or duplicate native codec family")
                  (assoc index name family))) {} families))))
(defn- constructor [index kind leaf object-fields void-fields]
  (let [family (get index (get family-names kind))
        name ["str" (get family-names kind) leaf]
        candidates (filterv #(= name (get % "constructor")) (get family "constructors"))]
    (need (= 1 (count candidates)) "Required original constructor witness is absent or duplicate")
    (let [witness (first candidates) info (get witness "ctorInfo") fields (get witness "fields")
          _ (need (and (vector? fields) (<= (count fields) 8)) "Constructor field witness exceeds profile")
          objects (filterv #(= "object" (get % "kind")) fields)
          voids (filterv #(= "void" (get % "kind")) fields)
          positions (mapv #(get % "index") objects) size (get info "size") tag (get info "cidx")]
      (need (and (= name (get info "name")) (integer? tag) (<= 0 tag 243)
                 (= object-fields size (count objects)) (= 0 (get info "usize") (get info "ssize"))
                 (vector? fields) (= (+ object-fields void-fields) (count fields)) (= void-fields (count voids))
                 (every? integer? positions)
                 (= (set positions) (set (range object-fields))) (= (count positions) (count (set positions)))
                 (every? #(contains? #{"object" "tobject" "tagged"} (get % "irType")) objects))
            "Original constructor layout is outside the object-field codec profile")
      {:tag tag :size size :positions positions})))
(defn- pure-kind! [ctx node]
  ;; Sharing wrappers have no payload ownership. Pointer observations carry a
  ;; realm token which this borrowed ctx does not authenticate, so reject them.
  (let [sharing-name (str (.getName ^Class (:class ctx)) "$SharingMetadata")]
    (loop [metadata (#'startup/engine-field node "metadata") depth 0]
      (limit! (< depth 128) "Runtime metadata wrapper depth exceeds codec budget")
      (when metadata
        (need (= sharing-name (.getName (class metadata))) "Runtime value has unsupported kind or pointer metadata")
        (recur (#'startup/engine-field metadata "inner") (inc depth))))))
(defn- node-fields! [ctx raw layout]
  (need (= (:node-class ctx) (class raw)) "Expected constructor from the actual runtime cohort")
  (need (and (false? (#'startup/engine-field raw "dead"))
             (false? (#'startup/engine-field raw "array"))
             (false? (#'startup/engine-field raw "ref"))
             (false? (#'startup/engine-field raw "readyTask"))
             (nil? (#'startup/engine-field raw "closure"))) "Runtime value is not a live plain constructor")
  (pure-kind! ctx raw)
  (let [tag (.get ^Field (:tag ctx) raw) rc (.get ^Field (:rc ctx) raw)
        fields (.get ^Field (:fields ctx) raw) scalars (.get ^Field (:scalars ctx) raw)]
    (need (and (integer? rc) (not (neg? rc)) (= (:tag layout) tag)
               (= object-array-class (class fields)) (= (:size layout) (alength ^objects fields))
               (= byte-array-class (class scalars)) (zero? (alength ^bytes scalars))
               (every? some? fields)) "Runtime constructor tag/extent/scalars/reference count differs from witness")
    fields))
(defn- scalar? [raw layout]
  (and (= Long (class raw)) (= (:tag layout) raw)))
(defn- decoder [ctx witnesses]
  (let [index (witness-index witnesses) remaining (volatile! maximum-occurrences)
        active (IdentityHashMap.) integer-bits (volatile! 0) string-units (volatile! 0) buffer-bytes (volatile! 0)]
    (letfn [(charge! [depth]
              (when (.isInterrupted (Thread/currentThread))
                (throw (ex-info "Result decoding cancelled" {:code "Cancelled"})))
              (limit! (< depth maximum-depth) "Result nesting exceeds codec depth budget")
              (limit! (not (neg? (vswap! remaining dec))) "Result exceeds codec occurrence budget"))
            (account! [decoded]
              (cond
                (= java.math.BigInteger (class decoded)) (vswap! integer-bits + (.bitLength (.abs ^java.math.BigInteger decoded)))
                (= String (class decoded)) (vswap! string-units + (.length ^String decoded))
                (= byte-array-class (class decoded)) (vswap! buffer-bytes + (alength ^bytes decoded))
                (= Float (class decoded)) (vswap! buffer-bytes + 4)
                (= Double (class decoded)) (vswap! buffer-bytes + 8))
              (limit! (and (<= @integer-bits 4194304) (<= @string-units 1048576)
                           (<= @buffer-bytes scalar/maximum-buffer-bytes)) "Result aggregate codec budget exceeded"))
            (enter! [raw]
              (need (not (.containsKey active raw)) "Cyclic result cannot be decoded as an immutable host value")
              (.put active raw true))
            (leave! [raw] (.remove active raw))
            (visit-list [type raw depth]
              (let [nil-layout (constructor index "list" "nil" 0 0)
                    cons-layout (constructor index "list" "cons" 2 0)
                    head-index (first (:positions cons-layout)) tail-index (second (:positions cons-layout))
                    output (ArrayList.) chain (ArrayList.)]
                (try
                  (loop [raw raw first? true]
                    (when-not first? (charge! depth))
                    (if (scalar? raw nil-layout)
                      (List/copyOf output)
                      (let [fields (node-fields! ctx raw cons-layout)]
                        (enter! raw) (.add chain raw)
                        (.add output (visit (get type "element") (aget ^objects fields head-index) (inc depth)))
                        (recur (aget ^objects fields tail-index) false))))
                  (finally (doseq [node chain] (leave! node))))))
            (visit [type raw depth]
              (charge! depth)
              (let [decoded (case (get type "kind")
                ("nat" "int" "bool" "string" "unit") (codec/decode-leaf type raw)
                ("machine-int" "word" "float" "char") (scalar/decode-scalar ctx type raw)
                "bytes" (scalar/decode-bytes ctx raw)
                "array" (do (enter! raw)
                            (try (List/copyOf ^java.util.Collection
                                             (mapv #(visit (get type "element") % (inc depth))
                                                   (scalar/decode-array-fields ctx raw)))
                                 (finally (leave! raw))))
                "product"
                (let [layout (constructor index "product" "mk" 2 0) fields (node-fields! ctx raw layout)
                      [first-index second-index] (:positions layout)]
                  (enter! raw)
                  (try (List/of (visit (get type "first") (aget ^objects fields first-index) (inc depth))
                                (visit (get type "second") (aget ^objects fields second-index) (inc depth)))
                       (finally (leave! raw))))
                "option"
                (let [none-layout (constructor index "option" "none" 0 0)]
                  (if (scalar? raw none-layout) (Optional/empty)
                    (let [layout (constructor index "option" "some" 1 0) fields (node-fields! ctx raw layout)]
                      (enter! raw)
                      (try (Optional/of (visit (get type "element") (aget ^objects fields (first (:positions layout))) (inc depth)))
                           (finally (leave! raw))))))
                "list" (visit-list type raw depth)
                ("sum" "except")
                (let [kind (get type "kind") sum? (= kind "sum")
                      left (constructor index kind (if sum? "inl" "error") 1 0)
                      right (constructor index kind (if sum? "inr" "ok") 1 0)
                      _ (need (= (:node-class ctx) (class raw)) "Branch result is not a runtime constructor")
                      tag (.get ^Field (:tag ctx) raw)
                      left? (= tag (:tag left))
                      _ (need (or left? (= tag (:tag right))) "Unknown branch constructor")
                      layout (if left? left right) fields (node-fields! ctx raw layout)
                      child (get type (if sum? (if left? "left" "right") (if left? "error" "value")))]
                  (enter! raw)
                  (try (let [decoded (visit child (aget ^objects fields (first (:positions layout))) (inc depth))]
                         (if left? (LeanChoice/left decoded) (LeanChoice/right decoded)))
                       (finally (leave! raw))))
                (throw (ex-info "Unsupported result codec" {:code "UnsupportedSignature"})))]
                (account! decoded) decoded))]
      {:visit visit :charge charge! :enter enter! :leave leave! :index index})))

(defn decode
  "Decode borrowed result data. The caller owns and eventually releases ONLY
   its actual result root; no descendant credit is acquired or released here."
  [ctx type codec-witnesses raw-value]
  (signature/validate! {"arguments" [] "result" type "effect" "pure"})
  ((:visit (decoder ctx codec-witnesses)) type raw-value 0))

(defn decode-io
  "Decode a v2 IO result using genuine EST.Out layouts. Legacy IO Unit remains
   the caller's existing separately authenticated codec path, not a default here."
  [ctx actual-entry raw-envelope]
  (let [descriptor (signature/validate! (entry/descriptor actual-entry))
        _ (need (= "io" (get descriptor "effect")) "Entry is not an IO signature")
        {:keys [visit charge enter leave index]} (decoder ctx (get actual-entry "codecWitnesses"))
        ok (constructor index "io" "ok" 1 1) error (constructor index "io" "error" 1 1)]
    (charge 0)
    (need (= (:node-class ctx) (class raw-envelope)) "IO result is not an actual runtime constructor")
    (let [tag (.get ^Field (:tag ctx) raw-envelope)
          layout (cond (= tag (:tag ok)) ok (= tag (:tag error)) error
                       :else (throw (ex-info "Unknown IO result constructor" {:code "RuntimeBoundary"})))
          fields (node-fields! ctx raw-envelope layout)]
      (enter raw-envelope)
      (try (if (= tag (:tag ok))
             {:kind :ok :value (visit (get descriptor "result") (aget ^objects fields (first (:positions layout))) 1)}
             {:kind :io-error})
           (finally (leave raw-envelope))))))
