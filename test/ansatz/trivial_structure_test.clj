(ns ansatz.trivial-structure-test
  "Lean's trivial-structure representation (Compiler/LCNF/Irrelevant.lean
   computeHasTrivialStructure?, v4.33.1): a one-constructor, non-recursive inductive with
   exactly one computationally relevant field is represented by that field at runtime.
   Records with an explicitly chosen representation (`a/structure`, malli `[:map …]`) and
   constructors with a codegen-registry lowering keep theirs."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.codegen :as cg]
            [ansatz.codegen.native :as native]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]))

(use-fixtures :once
  (fn [f]
    (let [saved-env @a/ansatz-env
          saved-arity @a/arity-registry
          saved-codegen @a/codegen-registry
          saved-structures @a/structure-registry
          saved-instances @a/ansatz-instance-index]
      (try
        (binding [*ns* (the-ns 'ansatz.trivial-structure-test) a/*verbose* false]
          (a/load-init!)
          (f))
        (finally
          (reset! a/ansatz-env saved-env)
          (reset! a/arity-registry saved-arity)
          (reset! a/codegen-registry saved-codegen)
          (reset! a/structure-registry saved-structures)
          (reset! a/ansatz-instance-index saved-instances))))))

(defn- field [t] (native/trivial-structure-field (a/env) t))
(defn- run-fn [sym] @(ns-resolve 'ansatz.trivial-structure-test sym))

(deftest lean-trivial-structure-classification
  (testing "one relevant field: represented by it"
    (doseq [[t i] {"Fin" 0 "Char" 0 "BitVec" 0 "String.Pos.Raw" 0 "Subtype" 0
                   "ULift" 0 "PLift" 0 "Inhabited" 0 "Add" 0 "HAdd" 0}]
      (is (= i (field t)) t)))
  (testing "not trivial"
    (doseq [t ["Prod" "Option" "PUnit" "Decidable" "Monad" "Sigma" "PSigma"
               "Nat" "List"                ; recursive / several constructors
               "Exists" "And" "Eq"         ; propositions are erased already
               "String" "Array" "UInt32"]] ; runtime builtin types
      (is (nil? (field t)) t))))

(deftest user-inductives-follow-the-rule
  (a/inductive TsWrap [] (mk [x Nat]))
  (a/inductive TsBounded [] (mk [x Nat] [h (< x 100)]))
  (a/inductive TsTriple [] (mk [a Nat] [b Nat] [c Nat]))
  (a/inductive TsFuel [] (stop) (more [f TsFuel]))
  (is (= 0 (field "TsWrap")))
  (is (= 0 (field "TsBounded")) "a proof field is irrelevant")
  (is (nil? (field "TsTriple")))
  (is (nil? (field "TsFuel")))
  (a/defn ts-make [n :- Nat] TsWrap (TsWrap.mk (* n 2)))
  (a/defn ts-read [w :- TsWrap] Nat (match w [(mk x) (+ x 1)]))
  (a/defn ts-triple [n :- Nat] TsTriple (TsTriple.mk n (+ n 1) (+ n 2)))
  (a/defn ts-sum [t :- TsTriple] Nat (match t [(mk a b c) (+ a (+ b c))]))
  (testing "the wrapper is its field at runtime; construction and matching agree"
    (is (= 8 ((run-fn 'ts-make) 4)))
    (is (= 9 ((run-fn 'ts-read) ((run-fn 'ts-make) 4))))
    (is (= 8 ((run-fn 'ts-read) 7))))
  (testing "several relevant fields keep the vector representation"
    (is (= [1 2 3] ((run-fn 'ts-triple) 1)))
    (is (= 6 ((run-fn 'ts-sum) [1 2 3]))))
  (testing "projection and construction lower to the field"
    (let [mk (e/const' (name/from-string "TsBounded.mk") [])
          v (e/app* mk (e/lit-nat (biginteger 5)) (e/const' (name/from-string "True.intro") []))]
      (is (= 5 (eval (cg/ansatz->clj (a/env) v []))))
      (is (= 5 (eval (cg/ansatz->clj (a/env) (e/proj (name/from-string "TsBounded") 0 v) []))))
      (is (nil? (eval (cg/ansatz->clj (a/env) (e/proj (name/from-string "TsBounded") 1 v) [])))))))

(deftest chosen-representations-are-kept
  (testing "a registered record with one field stays a record"
    (a/structure TsBox [] (val Nat))
    (is (nil? (field "TsBox")))
    (a/defn ts-box [n :- Nat] TsBox (TsBox.mk n))
    (is (= 3 (:val ((run-fn 'ts-box) 3))))
    (is (record? ((run-fn 'ts-box) 3))))
  (testing "a constructor with a codegen-registry lowering keeps it"
    (a/inductive TsTagged [] (mk [x Nat]))
    (swap! a/codegen-registry assoc "TsTagged.mk"
           (fn [_ _ _] (list 'fn ['x] (list 'clojure.core/hash-map :tagged 'x))))
    (try
      (is (nil? (field "TsTagged")))
      (finally (swap! a/codegen-registry dissoc "TsTagged.mk")))))

(deftest instances-of-one-method-classes-are-their-method
  (let [inst (e/app* (e/const' (name/from-string "instInhabitedNat") []))]
    (is (= 0 (eval (cg/ansatz->clj (a/env) inst []))))
    (is (= 0 (eval (cg/ansatz->clj (a/env) (e/proj (name/from-string "Inhabited") 0 inst) []))))))
