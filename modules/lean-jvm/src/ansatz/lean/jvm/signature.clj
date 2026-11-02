(ns ansatz.lean.jvm.signature
  "Closed application signatures shared by native evidence, artifact validation
   and host codecs. These are calling descriptors, not inferred erased IR types."
  (:require [clojure.string :as str]))

(def ^:private primitive-names
  {"nat" "Nat" "int" "Int" "bool" "Bool" "string" "String" "unit" "Unit"})
(defn- scalar-name [type]
  (case (get type "kind")
    "machine-int" (str (if (get type "signed") "Int" "UInt") (get type "bits"))
    "word" (if (get type "signed") "ISize" "USize")
    "float" (if (= 32 (get type "bits")) "Float32" "Float")
    "char" "Char"
    "bytes" "ByteArray"
    nil))
(def ^:private max-arity 64)
(defn- need [ok message]
  (when-not ok (throw (ex-info message {:code "UnsupportedSignature"}))))
(defn- exact-keys! [value expected]
  (need (and (map? value) (= expected (set (keys value)))) "Unexpected signature fields"))
(defn validate!
  "Validate a bounded v2 JSON descriptor and return it unchanged. All arguments
   are explicit values; unsupported dependent/implicit/polymorphic binders must
   be rejected by the native classifier before issuing this descriptor."
  [signature]
  (exact-keys! signature #{"arguments" "result" "effect"})
  (need (and (vector? (get signature "arguments"))
             (<= (count (get signature "arguments")) max-arity)
             (#{"pure" "io"} (get signature "effect"))) "Unsupported arity or effect")
  (let [remaining (volatile! 512)]
    (letfn [(visit [type depth]
              (need (and (< depth 32) (not (neg? (vswap! remaining dec)))) "Signature nesting/node budget exceeded")
              (need (map? type) "Expected a type descriptor")
              (let [kind (get type "kind")]
                (cond
                  (contains? primitive-names kind) (exact-keys! type #{"kind"})
                  (= "machine-int" kind)
                  (do (exact-keys! type #{"kind" "bits" "signed"})
                      (need (and (#{8 16 32 64} (get type "bits"))
                                 (instance? Boolean (get type "signed"))) "Invalid machine integer width or signedness"))
                  (= "word" kind)
                  (do (exact-keys! type #{"kind" "signed"})
                      (need (instance? Boolean (get type "signed")) "Invalid word signedness"))
                  (= "float" kind)
                  (do (exact-keys! type #{"kind" "bits"})
                      (need (#{32 64} (get type "bits")) "Invalid float width"))
                  (#{"char" "bytes"} kind) (exact-keys! type #{"kind"})
                  (#{"sum" "except"} kind)
                  (let [[a b] (if (= kind "sum") ["left" "right"] ["error" "value"])]
                    (exact-keys! type #{"kind" a b})
                    (visit (get type a) (inc depth)) (visit (get type b) (inc depth)))
                  (= "product" kind)
                  (do (exact-keys! type #{"kind" "first" "second"})
                      (visit (get type "first") (inc depth)) (visit (get type "second") (inc depth)))
                  (#{"option" "list" "array"} kind)
                  (do (exact-keys! type #{"kind" "element"}) (visit (get type "element") (inc depth)))
                  :else (need false "No host codec profile for this Lean type"))))]
      (doseq [argument (get signature "arguments")] (visit argument 0))
      (visit (get signature "result") 0)))
  signature)

(defn- typed-name [text]
  (reduce (fn [parent part] ["str" parent part]) ["anonymous"]
          (str/split text #"\.")))
(defn- constant
  ([name] (constant name []))
  ([name levels] ["const" (typed-name name) levels]))
(defn- apply-type [function & arguments]
  (reduce (fn [function argument] ["app" function argument]) function arguments))
(defn expected-type
  "Reconstruct the canonical closed Lean expression the producer must check by
   native DefEq. Argument names do not affect definitional equality."
  [signature]
  (validate! signature)
  (letfn [(type-expr [type]
            (let [kind (get type "kind")]
              (if-let [name (or (primitive-names kind) (scalar-name type))]
                (constant name)
                (case kind
                  "product" (apply-type (constant "Prod" [["zero"] ["zero"]])
                                        (type-expr (get type "first")) (type-expr (get type "second")))
                  "option" (apply-type (constant "Option" [["zero"]]) (type-expr (get type "element")))
                  "list" (apply-type (constant "List" [["zero"]]) (type-expr (get type "element")))
                  "array" (apply-type (constant "Array" [["zero"]]) (type-expr (get type "element")))
                  "sum" (apply-type (constant "Sum" [["zero"] ["zero"]])
                                    (type-expr (get type "left")) (type-expr (get type "right")))
                  "except" (apply-type (constant "Except" [["zero"] ["zero"]])
                                       (type-expr (get type "error")) (type-expr (get type "value")))))))]
    (let [result (type-expr (get signature "result"))
          result (if (= "io" (get signature "effect")) (apply-type (constant "IO") result) result)]
      (reduce (fn [body argument] ["forall" ["anonymous"] "default" (type-expr argument) body])
              result (rseq (get signature "arguments"))))))

(defn arity [signature] (count (get (validate! signature) "arguments")))
(defn runtime-arity [signature]
  (+ (arity signature) (if (= "io" (get signature "effect")) 1 0)))

(defn display [signature]
  (validate! signature)
  (letfn [(type-name [type]
            (let [kind (get type "kind")]
              (or (primitive-names kind) (scalar-name type)
                  (case kind
                    "product" (str "(" (type-name (get type "first")) " × " (type-name (get type "second")) ")")
                    "option" (str "Option (" (type-name (get type "element")) ")")
                    "list" (str "List (" (type-name (get type "element")) ")")
                    "array" (str "Array (" (type-name (get type "element")) ")")
                    "sum" (str "Sum (" (type-name (get type "left")) ") (" (type-name (get type "right")) ")")
                    "except" (str "Except (" (type-name (get type "error")) ") (" (type-name (get type "value")) ")")))))]
    (str/join " → " (concat (map type-name (get signature "arguments"))
                             [(let [result (type-name (get signature "result"))]
                                (if (= "io" (get signature "effect")) (str "IO (" result ")") result))]))))

(defn from-legacy [profile]
  (let [primitive #(hash-map "kind" %)]
    (case profile
      "nat-to-nat" {"arguments" [(primitive "nat")] "result" (primitive "nat") "effect" "pure"}
      "string-to-string" {"arguments" [(primitive "string")] "result" (primitive "string") "effect" "pure"}
      "io-unit" {"arguments" [] "result" (primitive "unit") "effect" "io"}
      (throw (ex-info "Unknown legacy checked signature" {:code "UnsupportedSignature"})))))
