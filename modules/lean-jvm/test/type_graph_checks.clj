(ns ansatz-lean-jvm-type-graph-checks
  "Self-issued model data only: none is a native declaration/layout certificate."
  (:require [clojure.test :refer [deftest is testing run-tests]]
            [clojure.walk :as walk]
            [ansatz.lean.jvm.type-graph :as graph]))

(defn- n [& leaves] (reduce (fn [p leaf] ["str" p leaf]) ["anonymous"] leaves))
(def sha (apply str (repeat 64 "a")))
(def nat {"kind" "nat"})
(defn- ref-type [id] {"kind" "nominal" "id" id})
(defn- field [t] {"name" ["anonymous"] "type" t})
(defn- ctor [name types] {"name" name "fields" (mapv field types)})
(defn- definition [id name args ctors]
  {"id" id "origin" {"module" (n "Example") "productSha256" sha}
   "name" name "universes" [] "arguments" args "constructors" ctors})
(defn- model [roots ds]
  {"schema" "lean-jvm-type-graph/3" "roots" roots "definitions" ds})
(defn- tree []
  (model [(ref-type 0)]
         [(definition 0 (n "Example" "Tree") []
                      [(ctor (n "Example" "Tree" "leaf") [nat])
                       (ctor (n "Example" "Tree" "node")
                             [{"kind" "list" "element" (ref-type 0)}])])]))
(defn- reason [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e
                 (is (= "InvalidTypeGraph" (:code (ex-data e)))) (:reason (ex-data e)))))
(defn- rejects [x] (some? (reason #(graph/validate! x))))

(deftest closed-builtins-and-regular-recursion
  (let [g (tree)] (is (identical? g (graph/validate! g))))
  (let [types [nat {"kind" "machine-int" "bits" 64 "signed" false}
               {"kind" "word" "signed" true} {"kind" "float" "bits" 32}
               {"kind" "product" "first" {"kind" "bytes"}
                "second" {"kind" "except" "error" {"kind" "string"}
                          "value" {"kind" "option" "element" {"kind" "unit"}}}}]]
    (is (= types (get (graph/validate! (model types [])) "roots"))))
  ;; A nonrecursive generic type nested in its own closed parameter is finite,
  ;; unlike changing recursive constructor arguments.
  (let [name (n "Example" "Box") c (n "Example" "Box" "mk")
        ds [(definition 4 name [nat] [(ctor c [nat])])
            (definition 9 name [(ref-type 4)] [(ctor c [(ref-type 4)])])]]
    (is (= 2 (count (get (graph/validate! (model [(ref-type 9)] ds)) "definitions"))))))

(deftest strict-keys-descriptors-and-bounds
  (doseq [bad [(assoc (tree) "extra" true)
               (dissoc (tree) "roots")
               (assoc (tree) "schema" "lean-jvm-type-graph/2")
               (assoc (tree) "roots" [])
               (assoc (tree) "roots" [(ref-type 0) (ref-type 0)])
               (assoc-in (tree) ["definitions" 0 "parameters"] [])
               (assoc-in (tree) ["definitions" 0 "universes"] [256])
               (assoc-in (tree) ["definitions" 0 "universes"] [1.0])
               (assoc-in (tree) ["definitions" 0 "arguments"] (vec (repeat 65 nat)))
               (assoc-in (tree) ["definitions" 0 "constructors" 0 "fields"] (vec (repeat 65 (field nat))))
               (assoc-in (tree) ["definitions" 0 "id"] 18446744073709551616N)]]
    (is (rejects bad)))
  (doseq [type [{"kind" "proof"} {"kind" "indexed" "index" 0}
               {"kind" "function"} {"kind" "variable" "index" 0}
               {"kind" "machine-int" "bits" 7 "signed" false}
               {"kind" "float" "bits" 64 "signed" false}
               {"kind" "word" "signed" 1}
               {"kind" "nominal" "id" -1}
               {"kind" "nominal" "id" 0 "arguments" []}]]
    (is (rejects (model [type] []))))
  (let [nested (nth (iterate #(hash-map "kind" "list" "element" %) nat) 32)]
    (is (= :type-depth (reason #(graph/validate! (model [nested] []))))))
  (let [d (first (get (tree) "definitions"))]
    (is (rejects (model [(ref-type 0)] (vec (repeat 257 d)))))
  (let [g (tree) ct (get-in g ["definitions" 0 "constructors" 0])]
    (is (rejects (assoc-in g ["definitions" 0 "constructors"] [ct ct]))))))

(deftest logical-enum-count-is-not-an-allocated-node-tag
  (let [enum (fn [size]
               (model [(ref-type 0)]
                      [(definition 0 (n "LargeEnum") []
                                   (mapv #(ctor ["num" (n "LargeEnum") (str %)] []) (range size)))]))]
    (is (= 245 (count (get-in (graph/validate! (enum 245)) ["definitions" 0 "constructors"]))))
    (is (rejects (enum 1025)))))

(deftest lossless-names-and-provenance
  (let [g (tree)]
    (doseq [bad [["num" ["anonymous"] "01"]
                 ["num" ["anonymous"] "18446744073709551616"]
                 ["num" ["anonymous"] 1] ["str" ["anonymous"] 1]
                 ["str" ["anonymous"] (str (char 0xd800))]
                 ["anonymous" "extra"] ["anonymous"]]]
      (is (rejects (assoc-in g ["definitions" 0 "name"] bad))))
    (doseq [origin [{"module" (n "Example") "productSha256" "a"}
                    {"module" (n "Example") "productSha256" (.toUpperCase sha)}
                    {"module" (n "Example") "productSha256" sha "path" "untrusted"}]]
      (is (rejects (assoc-in g ["definitions" 0 "origin"] origin))))
    (is (not= (graph/type-digest g (ref-type 0))
              (graph/type-digest (assoc-in g ["definitions" 0 "origin" "productSha256"]
                                         (apply str (repeat 64 "b"))) (ref-type 0))))
    (is (not= (graph/logical-digest (assoc-in g ["definitions" 0 "name"] (n "A.B")))
              (graph/logical-digest (assoc-in g ["definitions" 0 "name"] (n "A" "B")))))
    (is (= (graph/validate! (assoc-in g ["definitions" 0 "name"]
                                    ["num" (n "Example") "18446744073709551615"]))
           (assoc-in g ["definitions" 0 "name"] ["num" (n "Example") "18446744073709551615"])))))

(deftest closure-duplicate-applications-and-unsupported-recursion
  (let [g (tree) d (first (get g "definitions"))]
    (is (= :missing-reference (reason #(graph/validate! (assoc g "roots" [(ref-type 8)])))))
    (is (= :duplicate-id (reason #(graph/validate! (update g "definitions" conj d)))))
    (is (= :unreachable-definition
           (reason #(graph/validate! (update g "definitions" conj
                                           (definition 1 (n "Other") [] [(ctor (n "Other" "mk") [])]))))))
    (is (= :duplicate-application
           (reason #(graph/validate! (model [(ref-type 0) (ref-type 1)]
                                           [(assoc d "constructors" [(ctor (n "Example" "Tree" "leaf") [])])
                                            (assoc d "id" 1 "constructors" [(ctor (n "Example" "Tree" "leaf") [])])]))))))
  (let [a (definition 0 (n "A") [] [(ctor (n "A" "mk") [(ref-type 1)])])
        b (definition 1 (n "B") [] [(ctor (n "B" "mk") [(ref-type 0)])])]
    (is (= :nonregular-cycle (reason #(graph/validate! (model [(ref-type 0)] [a b])))))
    (is (= :recursive-argument
           (reason #(graph/validate! (model [(ref-type 0)] [(assoc a "arguments" [(ref-type 0)]
                                                                 "constructors" [(ctor (n "A" "mk") [])])]))))))
  (let [name (n "Changing")
        a (definition 0 name [nat] [(ctor (n "Changing" "mk") [(ref-type 1)])])
        b (definition 1 name [{"kind" "bool"}] [(ctor (n "Changing" "mk") [])])]
    (is (= :changed-recursive-application
           (reason #(graph/validate! (model [(ref-type 0)] [a b])))))))

(deftest canonical-digests-do-not-make-selected-entries-type-identity
  (let [g (tree)
        renumbered (walk/postwalk #(if (and (map? %) (contains? % "id")) (assoc % "id" 13) %) g)
        other (definition 7 (n "Other") [] [(ctor (n "Other" "mk") [])])
        expanded (-> g (update "roots" conj (ref-type 7)) (update "definitions" conj other))]
    (is (= (graph/canonical-graph g) (graph/canonical-graph renumbered)))
    (is (= (graph/logical-digest g) (graph/logical-digest renumbered)))
    (is (= (graph/logical-digest expanded)
           (graph/logical-digest (update expanded "definitions" #(vec (reverse %))))))
    (is (not= (graph/logical-digest g) (graph/logical-digest expanded)))
    (is (= (graph/type-digest g (ref-type 0))
           (graph/type-digest expanded (ref-type 0))
           (graph/type-digest renumbered (ref-type 13))))
    (let [roots-reversed (update expanded "roots" #(vec (reverse %)))]
      (is (not= (graph/logical-digest expanded) (graph/logical-digest roots-reversed)))
      (is (= (graph/type-digest expanded (ref-type 0))
             (graph/type-digest roots-reversed (ref-type 0)))))
    ;; A transitive definition need not be selected as a top-level root.
    (let [outer (definition 7 (n "Outer") [] [(ctor (n "Outer" "mk") [(ref-type 0)])])
          wrapped (model [(ref-type 7)] [outer (first (get g "definitions"))])]
      (is (= (graph/type-digest g (ref-type 0)) (graph/type-digest wrapped (ref-type 0)))))))

(deftest bounded-composed-graphs-use-worklists-not-composed-recursion
  ;; 256 nominal hops, each through fourteen builtin wrappers. Each inline type
  ;; is shallow, but recursively composing traversals would need thousands of
  ;; JVM frames. This remains within every configured model budget.
  (let [wrap #(nth (iterate (fn [t] {"kind" "list" "element" t}) %) 14)
        ds (mapv (fn [i]
                   (definition i (n "Chain" (str i))
                               (if (= i 255) [] [(wrap (ref-type (inc i)))])
                               [(ctor (n "Chain" (str i) "mk") [])])) (range 256))
        g (model [(ref-type 0)] ds)]
    (is (= 256 (count (get (graph/canonical-graph g) "definitions"))))
    (is (= (graph/logical-digest g) (graph/type-digest g (ref-type 0)))))
  (let [wrapped (nth (iterate #(hash-map "kind" "list" "element" %) nat) 30)
        ds (mapv #(definition % (n "Wide" (str %)) []
                              [(ctor (n "Wide" (str %) "mk") (repeat 64 wrapped))]) (range 3))]
    (is (= :edges (reason #(graph/validate! (model (mapv ref-type (range 3)) ds))))))
  (is (= "e1e94c326d7e0eb0acd9b8673ff6dd014a6d24319fc3f0cf26d8baf02fcc11e7"
         (graph/logical-digest (model [nat] [])))))

(defn- layout-plan [g]
  {"schema" "lean-jvm-layout-references/3" "logicalDigest" (graph/logical-digest g)
   "representationDigest" sha
   "definitions"
   [{"definition" 0 "applicationPath" ["applications" 0]
     "constructors"
     (mapv (fn [i] {"constructor" i "layoutPath" ["families" 0 "constructors" i]
                    "fields" [{"field" 0 "layoutPath" ["families" 0 "constructors" i "fields" 0]}]})
           [0 1])}]})

(deftest layout-references-are-structural-not-storage-authority
  (let [g (tree) p (layout-plan g)]
    (is (= p (graph/validate-layout-references! g p)))
    (doseq [bad [(assoc p "logicalDigest" (apply str (repeat 64 "b")))
                 (assoc p "representationDigest" "not-a-digest")
                 (assoc p "offset" 0)
                 (assoc p "definitions" [])
                 (update p "definitions" conj (first (get p "definitions")))
                 (assoc-in p ["definitions" 0 "applicationPath"] ["anything" 0])
                 (assoc-in p ["definitions" 0 "constructors" 0 "layoutPath"] ["families" 0 "constructors" 1024])
                 (assoc-in p ["definitions" 0 "constructors" 0 "fields" 0 "layoutPath"]
                           ["families" 1 "constructors" 0 "fields" 0])
                 (assoc-in p ["definitions" 0 "constructors" 0 "fields" 0 "byteOffset"] 0)]]
      (is (some? (reason #(graph/validate-layout-references! g bad)))))
    ;; Even a well-shaped digest is only a claimed link here. A future native
    ;; representation verifier must authenticate/check the document it names.
    (is (= (apply str (repeat 64 "c"))
           (get (graph/validate-layout-references! g (assoc p "representationDigest"
                                                          (apply str (repeat 64 "c"))))
                "representationDigest")))))

(defn check! [] (run-tests 'ansatz-lean-jvm-type-graph-checks))
