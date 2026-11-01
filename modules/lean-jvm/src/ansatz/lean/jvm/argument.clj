(ns ansatz.lean.jvm.argument
  "Pure host planning for scalar-free managed arguments; no guest allocation or RC operation."
  (:require [ansatz.lean.jvm.codec :as codec]
            [ansatz.lean.jvm.signature :as signature]
            [ansatz.lean.jvm.value :as value])
  (:import [java.math BigInteger] [java.util IdentityHashMap List Optional]))

(def ^:private object-array-class (class (object-array 0)))
(def ^:private maximum-occurrences 100000)
(defn- need [ok code message]
  (when-not ok (throw (ex-info message {:code code}))))
(defn- cancelled! []
  (when (.isInterrupted (Thread/currentThread))
    (throw (ex-info "Argument planning cancelled" {:code "Cancelled"}))))
(defn- snapshot-list [input expected-size]
  ;; Do not call toArray/iterator: a custom implementation may materialize an
  ;; unbounded sequence. Only the reported bounded extent is indexed here.
  (need (and (instance? List input) (not (instance? clojure.lang.ISeq input)))
        "UnsupportedArgumentType" "Expected a bounded java.util.List")
  (let [size (.size ^List input)]
    (need (<= 0 size maximum-occurrences) "ResourceLimit" "Host List exceeds argument extent budget")
    (need (or (nil? expected-size) (= size expected-size)) "InvalidArgument" "Prod expects exactly two elements")
    (let [snapshot (loop [index 0 result (transient [])]
                     (if (= index size) (persistent! result)
                       (do (cancelled!) (recur (inc index) (conj! result (.get ^List input index))))))]
      (need (= size (.size ^List input)) "InvalidArgument" "Host List extent changed during snapshot")
      snapshot)))
(defn plan
  "Validate and snapshot all explicit Object[] inputs into immutable recipes.
   Each {:ref index} selects an earlier scalar-free constructor. The trusted
   caller creates actual cohort DataRef/DataCtor objects and journals guest roots
   under the SAME Project lease before start; this value is not an admission token."
  [descriptor codec-witnesses arguments]
  (signature/validate! descriptor)
  (cancelled!)
  (need (= object-array-class (class arguments)) "UnsupportedArgumentType" "Explicit Object[] argument array required")
  (let [types (get descriptor "arguments")]
    (need (= (count types) (alength ^objects arguments)) "ArityMismatch" "Wrong number of explicit arguments")
    (let [arguments (aclone ^objects arguments)
          index (#'value/witness-index codec-witnesses) layouts (volatile! {})
          recipes (volatile! []) active (IdentityHashMap.)
          visited (volatile! 0) occurrences (volatile! 0) integer-bits (volatile! 0) string-units (volatile! 0)]
      (letfn [(type! [type]
                (let [kind (get type "kind")]
                  (case kind
                    ("nat" "int" "bool" "string" "unit") nil
                    "product"
                    (do (vswap! layouts assoc "product" (#'value/constructor index "product" "mk" 2 0))
                        (type! (get type "first")) (type! (get type "second")))
                    "option"
                    (do (vswap! layouts assoc "none" (#'value/constructor index "option" "none" 0 0)
                                "some" (#'value/constructor index "option" "some" 1 0))
                        (type! (get type "element")))
                    "list"
                    (do (vswap! layouts assoc "nil" (#'value/constructor index "list" "nil" 0 0)
                                "cons" (#'value/constructor index "list" "cons" 2 0))
                        (type! (get type "element")))
                    (need false "UnsupportedArgumentType" "Argument type has no scalar-free managed codec"))))
              (charge! [item]
                (need (<= (vswap! occurrences inc) maximum-occurrences) "ResourceLimit" "Argument field/root occurrence budget exceeded")
                (cond
                  (= Long (class item)) (vswap! integer-bits + 64)
                  (= BigInteger (class item)) (vswap! integer-bits + (.bitLength (.abs ^BigInteger item)))
                  (= String (class item)) (vswap! string-units + (.length ^String item)))
                (need (<= @integer-bits 4194304) "ResourceLimit" "Argument aggregate integer budget exceeded")
                (need (<= @string-units 1048576) "ResourceLimit" "Argument aggregate String budget exceeded"))
              (emit! [layout logical-fields]
                (let [fields (reduce (fn [fields [position item]] (assoc fields position item))
                                     (vec (repeat (:size layout) nil)) (map vector (:positions layout) logical-fields))
                      reference {:ref (count @recipes)}]
                  (doseq [item fields] (charge! item))
                  (vswap! recipes conj {:tag (long (:tag layout)) :fields fields}) reference))
              (enter! [input]
                (need (not (.containsKey active input)) "InvalidArgument" "Cyclic host argument cannot become a managed tree")
                (.put active input true))
              (visit [type input depth]
                (cancelled!)
                (need (< depth 128) "ResourceLimit" "Host argument nesting exceeds budget")
                (need (<= (vswap! visited inc) maximum-occurrences) "ResourceLimit" "Host argument occurrence budget exceeded")
                (case (get type "kind")
                  ("nat" "int" "bool" "string" "unit") (codec/encode-leaf type input)
                  "product"
                  (do (enter! input)
                      (try (let [fields (snapshot-list input 2)]
                             (emit! (get @layouts "product")
                                    [(visit (get type "first") (nth fields 0) (inc depth))
                                     (visit (get type "second") (nth fields 1) (inc depth))]))
                           (finally (.remove active input))))
                  "option"
                  (do (need (= Optional (class input)) "UnsupportedArgumentType" "Option expects java.util.Optional")
                      (if (.isPresent ^Optional input)
                        (do (enter! input)
                            (try (emit! (get @layouts "some") [(visit (get type "element") (.get ^Optional input) (inc depth))])
                                 (finally (.remove active input))))
                        (long (:tag (get @layouts "none")))))
                  "list"
                  (do (enter! input)
                      (try (let [elements (snapshot-list input nil)
                                 heads (mapv #(visit (get type "element") % (inc depth)) elements)]
                             (reduce (fn [tail head] (emit! (get @layouts "cons") [head tail]))
                                     (long (:tag (get @layouts "nil"))) (rseq heads)))
                           (finally (.remove active input))))))]
        ;; Validate every argument type/layout, including empty/None inhabitants.
        (doseq [type types] (type! type))
        (let [roots (mapv (fn [type input] (visit type input 0)) types arguments)]
          (doseq [root roots] (charge! root))
          {:constructors @recipes :roots roots})))))
