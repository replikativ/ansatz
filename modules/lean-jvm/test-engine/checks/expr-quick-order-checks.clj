(ns java-ir-expr-quick-order-checks
 "Atomic source LT; forced-cache structural cases are labeled models."
 (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
  [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
  [java-ir-expr-equality-checks :as eq] [java-ir-extern-checks :as x]
  [java-ir-host-checks :as h] [java-ir-generation-checks :as g]
  [java-ir-continuation-checks :as k] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-expr-quick-order-runtime/")
(defn records [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn raw-name [] (get-in (first (records)) ["row" "name"]))
(defn helpers []
 [(c/decl "model-quick-borrow" [(assoc (c/p 1 "object") :borrow true) (assoc (c/p 2 "object") :borrow true)] "uint8"
    (c/let-ir 3 "uint8" {:fap {:c (raw-name) :ys [(c/v 1) (c/v 2)]}} (c/ret 3)))])
(defn context ([] (context []))
 ([extra] (binding [eq/*basis* *basis*]
   (eq/context (concat (map #(get % "row") (records)) (helpers) extra)))))
(defn model-context [] (let [ctx (context)] (assoc ctx :engine (j/machine ctx))))
(defn lt [ctx a b] (j/call ctx (:engine ctx) "model-quick-borrow" [a b]))
(defn pair [ctx a b] [(lt ctx a b) (lt ctx b a)])
(defn low-hash [ctx n]
 (let [bs ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) n)]
  (reduce + (for [i (range 4)] (bit-shift-left (long (bit-and 255 (aget bs i))) (* i 8))))))

(deftest authentic-two-owned-wrapper-raw-abi-and-hook-evidence
 (let [p (json/read-str (slurp (str directory "provenance.json")))]
  (is (= 2 (count (records))))
  (doseq [[file sha] (get p "files")] (is (= sha (corpus/sha256 (str directory file)))))
  (let [raw (get-in (first (records)) ["row" "ir" "extern"])]
   (is (= [["object" "object"] [true true] "uint8"]
     [(mapv #(get % "ty") (get raw "xs")) (mapv #(get % "borrow") (get raw "xs")) (get raw "type")])))))

(deftest genuine-constructors-eqv-binder-policy-and-owning-wrapper-ap
 (let [ctx (model-context) e (:engine ctx)
       nm #(j/call ctx e "Lean.Name.str._override" [0 %])
       bvar #(j/call ctx e "Lean.Expr.bvar._override" [%])
       lam #(j/call ctx e "Lean.Expr.lam._override" [(nm %1) (j/call ctx e "Lean.Expr.sort._override" [0]) (bvar 0) %2])
       a (lam "x" 0) b (lam "y" 1) z (bvar 0) one (bvar 1) before (k/counters ctx e)]
  (is (= [0 0] (pair ctx a b))) (is (= before (k/counters ctx e)))
  (is (not= (low-hash ctx z) (low-hash ctx one)))
  (is (= (if (< (low-hash ctx z) (low-hash ctx one)) [1 0] [0 1]) (pair ctx z one)))
  (let [closure (j/make-closure! ctx e "Lean.Expr.quickLt._boxed" [])]
   (j/retain! ctx e a) (j/retain! ctx e b)
   (is (= 0 (j/call ctx e "apply-two" [closure a b])))
   (is (true? (h/private-value closure "dead"))))
  (doseq [v [a b z one]] (is (= 1 (c/rc ctx v))) (j/release! ctx e v)) (j/close! ctx e)))

(deftest models-kind-before-hash-and-low32-before-structural-fields
 (let [ctx (model-context) e (:engine ctx) b (eq/model-builder ctx) add (:add b) ex (:expr b) nm (:name b)
       n (nm "n")
       cases [[(add 0 [0] 8 4294967295 0) (add 1 [n] 8 0 0) [1 0]]
              [(add 0 [0] 8 2 0) (add 0 [100] 8 1 0) [0 1]]
              [(add 0 [7] 8 (biginteger "18446744069414584321") 0) (add 0 [7] 8 1 0) [0 0]]]
       roots ((:finish b) (vec (mapcat #(take 2 %) cases)))]
  (doseq [[i [_ _ expected]] (map-indexed vector cases)]
   (is (= expected (pair ctx (roots (* 2 i)) (roots (inc (* 2 i)))))))
  (j/close! ctx e)))

(deftest models-all-expr-selectors-use-equality-to-choose-the-child
 (let [ctx (model-context) e (:engine ctx) b (eq/model-builder ctx) add (:add b) ex (:expr b) nm (:name b) ls (:list b)
       n (nm "n") m (nm "m") z (ex 0 [0]) one (ex 0 [1])
       cases [[z one [1 0]] [(ex 1 [m]) (ex 1 [n]) [1 0]] [(ex 2 [m]) (ex 2 [n]) [1 0]]
              [(ex 4 [m 0]) (ex 4 [n 0]) [1 0]]
              [(ex 5 [z one]) (ex 5 [one z]) [1 0]]
              [(ex 6 [n z one]) (ex 6 [m z one]) [0 0]]
              [(ex 7 [n z one]) (add 7 [m z one] 16 0 3) [0 0]]
              [(ex 6 [n z z]) (ex 6 [n z one]) [1 0]]
              [(ex 8 [n z z z]) (add 8 [m z z z] 9 0 1) [1 0]]
              [(ex 9 [(add 0 [7] 0 0 0)]) (ex 9 [(add 0 [(biginteger "18446744073709551616")] 0 0 0)]) [1 0]]
              [(ex 9 [(add 0 [7] 0 0 0)]) (ex 9 [(add 1 ["a"] 0 0 0)]) [1 0]]
              [(ex 11 [n 0 z]) (ex 11 [n 1 z]) [1 0]]
              [(ex 11 [m 9 z]) (ex 11 [n 0 z]) [1 0]]
              [(ex 11 [n 9 z]) (ex 11 [m 0 one]) [1 0]]]
       roots ((:finish b) (vec (mapcat #(take 2 %) cases)))]
  (doseq [[i [_ _ expected]] (map-indexed vector cases)]
   (is (= expected (pair ctx (roots (* 2 i)) (roots (inc (* 2 i)))))))
  (j/close! ctx e)))

(deftest models-level-depth-precedes-kind-hash-and-list-heads-use-structural-equality
 (let [ctx (model-context) e (:engine ctx) b (eq/model-builder ctx) add (:add b) ex (:expr b) nm (:name b) ls (:list b)
       n (nm "n") m (nm "m")
       low (add 5 [n] 8 4294967295 0) high (add 1 [0] 8 (bit-shift-left 1 40) 0)
       u (add 4 [m] 8 0 0) v (add 4 [n] 8 0 0)
       maxuv (add 2 [u v] 8 0 0) maxvu (add 2 [v u] 8 0 0)
       cases [[(ex 3 [low]) (ex 3 [high]) [1 0]]
              [(ex 3 [u]) (ex 3 [v]) [1 0]]
              [(ex 3 [maxuv]) (ex 3 [maxvu]) [1 0]]
              [(ex 4 [n (ls [u v])]) (ex 4 [n (ls [u u])]) [0 1]]
              [(ex 4 [n (ls [u])]) (ex 4 [n (ls [u v])]) [1 0]]]
       roots ((:finish b) (vec (mapcat #(take 2 %) cases)))]
  (doseq [[i [_ _ expected]] (map-indexed vector cases)]
   (is (= expected (pair ctx (roots (* 2 i)) (roots (inc (* 2 i)))))))
  (j/close! ctx e)))

(deftest models-structural-name-numeric-before-string-and-unsigned-utf8-order
 (let [ctx (model-context) e (:engine ctx) b (eq/model-builder ctx) add (:add b) ex (:expr b) nm (:name b)
       num #(add 2 [%1 %2] 8 0 0) strn #(add 1 [%1 %2] 8 0 0) prefix (nm "P")
       cases [[(ex 1 [(num prefix 9)]) (ex 1 [(strn prefix "0")]) [1 0]]
              [(ex 1 [prefix]) (ex 1 [(num prefix 0)]) [1 0]]
              [(ex 1 [(num prefix 9)]) (ex 1 [(num prefix (biginteger "18446744073709551616"))]) [1 0]]
              [(ex 1 [(nm "\uE000")]) (ex 1 [(nm "𐀀")]) [1 0]]
              [(ex 9 [(add 1 ["a\u0000b"] 0 0 0)]) (ex 9 [(add 1 ["a\u0000c"] 0 0 0)]) [1 0]]
              [(ex 9 [(add 1 ["λ"] 0 0 0)]) (ex 9 [(add 1 ["μ"] 0 0 0)]) [1 0]]]
       roots ((:finish b) (vec (mapcat #(take 2 %) cases)))]
  (doseq [[i [_ _ expected]] (map-indexed vector cases)]
   (is (= expected (pair ctx (roots (* 2 i)) (roots (inc (* 2 i)))))))
  (j/close! ctx e)))

(deftest models-metadata-incomparability-continues-list-but-does-not-choose-other-expr-child
 (let [ctx (model-context) e (:engine ctx) b (eq/model-builder ctx) add (:add b) ex (:expr b) nm (:name b) ls (:list b)
       k (nm "k") tail (nm "tail") z (ex 0 [0]) one (ex 0 [1])
       dv (fn [tag v] (if (= tag 1) (add tag [] 1 v 0) (add tag [v] 0 0 0)))
       md (fn [entries] (ex 10 [(ls (map #(add 0 % 0 0 0) entries)) z]))
       i1 (md [[k (dv 4 (j/graph-int ctx -9))]]) i2 (md [[k (dv 4 (j/graph-int ctx 9))]])
       s1 (md [[k (dv 5 0)]]) s2 (md [[k (dv 5 (add 2 [0 "different"] 0 0 0))]])
       cases [[i1 i2 [0 0]] [s1 s2 [0 0]]
              [(md [[k (dv 4 (j/graph-int ctx -9))] [tail (dv 3 1)]])
               (md [[k (dv 4 (j/graph-int ctx 9))] [tail (dv 3 2)]]) [1 0]]
              [(ex 5 [i1 z]) (ex 5 [i2 one]) [0 0]]
              [(ex 11 [k 0 i1]) (ex 11 [tail 1 i2]) [0 0]]]
       roots ((:finish b) (vec (mapcat #(take 2 %) cases)))]
  (doseq [[i [_ _ expected]] (map-indexed vector cases)]
   (is (= expected (pair ctx (roots (* 2 i)) (roots (inc (* 2 i)))))))
  (j/close! ctx e)))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-quick-order-checks)))
