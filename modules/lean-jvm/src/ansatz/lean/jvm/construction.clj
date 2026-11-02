(ns ansatz.lean.jvm.construction
  "Private materialization of a fully validated host plan in one actual engine.
   The caller must journal returned roots and start under the same Project lease."
  (:import [java.lang.reflect Array Constructor Method]))

(defn materialize! [ctx engine plan]
  (let [loader (:loader ctx)
        ctor-class (Class/forName "ansatz.lean.jvm.internal.exec.Interpreter$DataCtor" true loader)
        ref-class (Class/forName "ansatz.lean.jvm.internal.exec.Interpreter$DataRef" true loader)
        object-array-class (class (object-array 0))
        ^Constructor ctor (.getConstructor ctor-class (into-array Class [Integer/TYPE object-array-class]))
        ^Constructor ref (.getConstructor ref-class (into-array Class [Integer/TYPE]))
        field-value (fn [value]
                      (if (map? value)
                        (.newInstance ref (object-array [(int (:ref value))])) value))
        recipes (:constructors plan)
        array (Array/newInstance ctor-class (int (count recipes)))]
    (doseq [[index recipe] (map-indexed vector recipes)]
      (let [fields #(object-array (map field-value (:fields recipe)))
            value (case (get recipe :kind :constructor)
                    :constructor (.newInstance ctor (object-array [(int (:tag recipe)) (fields)]))
                    :scalar (.invoke (.getMethod ctor-class "boxedScalar" (into-array Class [String Long/TYPE]))
                                     nil (object-array [(:lane recipe) (long (:bits recipe))]))
                    :array (.invoke (.getMethod ctor-class "array" (into-array Class [object-array-class]))
                                    nil (object-array [(fields)]))
                    :bytes (.invoke (.getMethod ctor-class "bytes" (into-array Class [(class (byte-array 0))]))
                                    nil (object-array [(:bytes recipe)])))]
        (Array/set array index value)))
    ;; Resolve and allocate all reflection arguments before guest construction.
    (let [^Method method (.getMethod ^Class (:class ctx) "constructDataArguments"
                                    (into-array Class [(class array) object-array-class]))
          arguments (object-array [array (object-array (map field-value (:roots plan)))])]
      (.invoke method engine arguments))))
