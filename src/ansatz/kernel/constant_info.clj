(ns ansatz.kernel.constant-info
  "Full declaration comparison for ALREADY materialized CIs. This is neither
   kernel admission nor a bounded store hydrator. Callers must obtain complete
   values within their explicit resource policy before using this comparison."
  (:require [ansatz.kernel.constant-info-bounded :as bounded])
  (:import [ansatz.kernel ConstantInfo ConstantInfo$RecursorRule Expr Name]))

(defn- complete-names? [names]
  (and (some? names) (every? #(instance? Name %) names)))

(defn complete?
  "Required fields of every supported CI variant are present. A defs-only body,
   omitted package array or recursor RHS cannot certify full overlap. This does
   not replace kernel admission or validate declaration typing/recursion."
  [value]
  (and (instance? ConstantInfo value)
       (let [^ConstantInfo ci value]
         (and (instance? Name (.name ci))
              (complete-names? (.levelParams ci))
              (instance? Expr (.type ci))
              (case (int (.tag ci))
                0 true
                (1 2 3) (and (instance? Expr (.value ci)) (complete-names? (.all ci)))
                4 (some? (.quotKind ci))
                5 (and (complete-names? (.all ci)) (complete-names? (.ctors ci)))
                6 (instance? Name (.inductName ci))
                7 (and (complete-names? (.all ci)) (some? (.rules ci))
                       (every? (fn [rule]
                                 (and (instance? ConstantInfo$RecursorRule rule)
                                      (instance? Name (.ctor ^ConstantInfo$RecursorRule rule))
                                      (instance? Expr (.rhs ^ConstantInfo$RecursorRule rule))))
                               (.rules ci)))
                false)))))

(defn full-shape
  "All fields of the actual ConstantInfo variant, preserving body, hints, safety,
   ordered universes/all/constructors/rules and complete recursor metadata. Expr
   equality is structural, including binder names and mdata, not defeq; object
   identities and parser/store IDs are not substituted for declaration equality."
  [^ConstantInfo ci]
  (when-not (complete? ci)
    (throw (ex-info "Exact overlap requires complete ConstantInfo evidence" {})))
  (let [base [(int (.tag ci)) (.name ci) (vec (.levelParams ci)) (.type ci)]]
    (case (int (.tag ci))
      0 (conj base (.isUnsafe ci))
      1 (conj base (.value ci) (.getHintsCode ci) (int (.safety ci)) (vec (.all ci)))
      2 (conj base (.value ci) (vec (.all ci)))
      3 (conj base (.value ci) (vec (.all ci)) (.isUnsafe ci))
      4 (conj base (.quotKind ci))
      5 (conj base (int (.numParams ci)) (int (.numIndices ci)) (vec (.all ci))
              (vec (.ctors ci)) (int (.numNested ci)) (.isRec ci) (.isReflexive ci) (.isUnsafe ci))
      6 (conj base (.inductName ci) (int (.cidx ci)) (int (.numParams ci))
              (int (.numFields ci)) (.isUnsafe ci))
      7 (conj base (vec (.all ci)) (int (.numParams ci)) (int (.numIndices ci))
              (int (.numMotives ci)) (int (.numMinors ci))
              (mapv (fn [^ConstantInfo$RecursorRule rule] [(.ctor rule) (int (.nfields rule)) (.rhs rule)])
                    (.rules ci))
              (.isK ci) (.isUnsafe ci))
      (throw (ex-info "Unknown ConstantInfo variant" {})))))

(defn full-equal?
  "Exact complete-CI comparison for already bounded, materialized shapes.
   Missing fields throw rather than certifying two omissions equal. Expr equality
   recursively revisits DAGs: callers must bound its work independently. Use
   full-equal-bounded? for a bounded pair comparison. Never admits a CI."
  [left right]
  (= (full-shape left) (full-shape right)))

(defn full-equal-bounded?
  "Exact comparison with caller-supplied :pairs/:edges/:scalar-bytes/:items/:depth
   limits across bounded completeness validation and identity-memoized comparison.
   See constant-info-bounded/full-equal-bounded? for accounting and input policy.
   No hydration or kernel admission occurs."
  [left right limits]
  (bounded/full-equal-bounded? left right limits))

(defn full-equal-batch-bounded?
  "Compare a finite standard vector of two-CI vectors under one shared budget
   and identity memo. All declaration roots are validated before comparison.
   See constant-info-bounded/full-equal-batch-bounded? for the input policy."
  [ci-pairs limits]
  (bounded/full-equal-batch-bounded? ci-pairs limits))
