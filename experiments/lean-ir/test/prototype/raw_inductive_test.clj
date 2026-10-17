(ns prototype.raw-inductive-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.module-data :as data] [prototype.imported-kernel :as imported]
            [prototype.machine :as m] [prototype.kernel-declaration :as declaration] [prototype.kernel-bridge-test :as guest]
            [ansatz.kernel.expr :as e] [ansatz.kernel.level :as l] [ansatz.kernel.name :as n])
  (:import [ansatz.kernel RawInductiveGenerator RawInductiveGenerator$Source RawInductiveGenerator$Type
            RawInductiveGenerator$Constructor ConstantInfo Env Expr TypeChecker Name]))
(defn ctor [name type] (RawInductiveGenerator$Constructor. (n/from-string name) type))
(defn type-input [name type ctors]
  (RawInductiveGenerator$Type. (n/from-string name) type (into-array RawInductiveGenerator$Constructor ctors)))
(defn source [levels parameters types]
  (RawInductiveGenerator$Source. (into-array Name (map n/from-string levels)) parameters
                                (into-array RawInductiveGenerator$Type types) false))
(defn constant [name] (e/const' name []))
(defn forall [name type body] (e/forall' name type body :default))
(def type1 (e/sort' (l/succ l/zero)))
(defn generate [env input] (RawInductiveGenerator/generate env input 1000000))
(defn constants [result] (into {} (map (fn [^ConstantInfo ci] [(str (.name ci)) ci])) (.constants result)))

(deftest native-tiny-family-is-generated-completely-and-matches-imported-types
  (let [input (source [] 0 [(type-input "Tiny" type1 [(ctor "Tiny.mk" (constant (n/from-string "Tiny")))])])
        before (Env.) result (generate before input) actual (constants result)
        loaded (data/load-file (m/world {}) "fixtures/imported-kernel-native.jsonl")
        expected (into {} (map (fn [{:keys [^ConstantInfo constant]}] [(str (.name constant)) constant]))
                       (imported/module-constants (:world loaded) (first (:roots loaded))))]
    (is (= #{"Tiny" "Tiny.mk" "Tiny.rec"} (set (keys actual))))
    (is (empty? (.allConstants before)))
    (doseq [name ["Tiny" "Tiny.mk" "Tiny.rec"]]
      (let [^ConstantInfo a (get actual name) ^ConstantInfo b (get expected name)]
        (is (= (.tag b) (.tag a)))
        (is (.equals (.type b) (.type a)))
        (is (= (vec (.levelParams b)) (vec (.levelParams a))))))
    (is (= 1 (count (.rules ^ConstantInfo (get actual "Tiny.rec")))))))

(deftest empty-types-predicates-and-k-targets-have-real-recursors
  (doseq [[label sort ctors k?] [["EmptyType" type1 [] false]
                                ["EmptyProp" (e/sort' l/zero) [] false]
                                ["UnitProp" (e/sort' l/zero) ["UnitProp.intro"] true]]]
    (let [result (generate (Env.) (source [] 0 [(type-input label sort
                                          (mapv #(ctor % (constant (n/from-string label))) ctors))]))
          cs (constants result) ^ConstantInfo rec (get cs (str label ".rec"))]
      (is (some? rec))
      (is (= k? (.isK rec)))
      (is (= (count ctors) (count (.rules rec)))))))

(deftest ordinary-recursion-and-indexed-constructor-computations-are-checked
  (let [nat (n/from-string "Nat") nt (constant nat)
        input (source [] 0 [(type-input "Nat" type1 [(ctor "Nat.zero" nt)
                                (ctor "Nat.succ" (forall "n" nt nt))])])
        nat-result (generate (Env.) input) cs (constants nat-result)
        indexed (n/from-string "AtZero")
        indexed-type (forall "n" nt type1)
        input (source [] 0 [(type-input "AtZero" indexed-type
                          [(ctor "AtZero.zero" (e/app (constant indexed) (e/lit-nat 0)))])])
        result (generate (.env nat-result) input) actual (constants result)]
    (is (.isRec ^ConstantInfo (get cs "Nat")))
    (is (= 1 (.numFields ^ConstantInfo (get cs "Nat.succ"))))
    (is (= 2 (count (.rules ^ConstantInfo (get cs "Nat.rec")))))
    (is (= 1 (.numIndices ^ConstantInfo (get actual "AtZero"))))
    (is (= 1 (.numIndices ^ConstantInfo (get actual "AtZero.rec"))))))

(deftest malformed-source-and-missing-family-generation-fail-closed
  (let [t (constant (n/from-string "Bad"))
        valid (source [] 0 [(type-input "Bad" type1 [(ctor "Bad.mk" t)])])]
    (is (thrown? Exception (generate (Env.) (source [] 0 []))))
    (is (thrown? Exception (generate (Env.) (source ["u" "u"] 0 [(type-input "Bad" type1 [])]))))
    (is (thrown? Exception (generate (Env.) (source [] 0 [(type-input "Bad" type1 [(ctor "Bad" t)])]))))
    (is (thrown? Exception (generate (Env.) (source [] 0 [(type-input "Bad" type1 [(ctor "Bad.mk" (constant (n/from-string "Other")))])]))))
    (is (thrown? Exception (generate (Env.) (source [] 0 [(type-input "Bad" type1 [(ctor "Bad.mk" (forall "negative" (forall "x" t type1) t))])]))))
    (is (thrown? Exception (RawInductiveGenerator/generate (Env.) valid 0)))
    (let [checked (generate (Env.) valid)]
      (is (thrown? Exception (generate (.env checked) valid))))))

(deftest native-ordinary-indexed-mutual-families-have-exact-metadata-and-binders
  ;; Recover ONLY raw names/types/ordered constructors from an authentic pinned
  ;; native artifact. Index counts, flags, recursor types/rules and annotations
  ;; below are generated independently, then compared to the native output.
  (let [loaded (data/load-file (m/world {}) "fixtures/raw-inductive-native.jsonl")
        expected (into {} (map (fn [{:keys [^ConstantInfo constant]}] [(str (.name constant)) constant]))
                       (imported/module-constants (:world loaded) (first (:roots loaded))))
        groups [[[] 0 ["TinyEnum"]] [[] 0 ["EmptyType"]] [[] 0 ["EmptyProp"]]
                [[] 0 ["UnitProp"]] [[] 0 ["MyNat"]] [[] 0 ["AtZero"]] [[] 0 ["Even" "Odd"]]
                [["u"] 1 ["PolyList"]] [[] 0 ["FunctionalTree"]] [["u"] 2 ["SmallEq"]]]]
    (reduce
      (fn [env [levels parameters group]]
        (let [types (mapv (fn [label]
                            (let [^ConstantInfo ind (get expected label)]
                              (type-input label (.type ind)
                                (mapv (fn [name] (let [^ConstantInfo ci (get expected (str name))]
                                                  (ctor (str name) (.type ci)))) (.ctors ind))))) group)
              result (generate env (source levels parameters types))
              actual (constants result)]
          (doseq [[label ^ConstantInfo ci] actual]
            (let [^ConstantInfo native (get expected label)]
              (is (some? native))
              (is (= (.tag native) (.tag ci)))
              (is (= (vec (.levelParams native)) (vec (.levelParams ci))))
              (is (.equals (.type native) (.type ci)) (str label " native=" (.type native) " actual=" (.type ci)))
              (when (.isInduct ci)
                (is (= [(.numParams native) (.numIndices native) (.numNested native) (.isRec native) (.isReflexive native)]
                       [(.numParams ci) (.numIndices ci) (.numNested ci) (.isRec ci) (.isReflexive ci)])))
              (when (.isCtor ci)
                (is (= [(.inductName native) (.cidx native) (.numFields native)]
                       [(.inductName ci) (.cidx ci) (.numFields ci)])))
              (when (.isRecursor ci)
                (is (= [(.numParams native) (.numIndices native) (.numMotives native) (.numMinors native) (.isK native)]
                       [(.numParams ci) (.numIndices ci) (.numMotives ci) (.numMinors ci) (.isK ci)]))
                (is (= (count (.rules native)) (count (.rules ci))))
                (doseq [[native-rule actual-rule] (map vector (.rules native) (.rules ci))]
                  (is (= [(.ctor native-rule) (.nfields native-rule)] [(.ctor actual-rule) (.nfields actual-rule)]))
                  (is (.equals (.rhs native-rule) (.rhs actual-rule)))))))
          (.env result))) (Env.) groups)))


(defn guest-list [world values]
  (reduce (fn [[world tail] value] (guest/ctor world 1 [value tail] 0))
          [world guest/nil-tag] (reverse values)))
(defn native-source-declaration
  ([group num-params] (native-source-declaration "fixtures/raw-inductive-native.jsonl" group num-params))
  ([path group num-params]
  (let [loaded (data/load-file (m/world {}) path)
        entries (imported/module-constants (:world loaded) (first (:roots loaded)))
        refs (into {} (map (fn [{:keys [guest ^ConstantInfo constant]}] [(str (.name constant)) guest])) entries)
        ci (into {} (map (fn [{:keys [^ConstantInfo constant]}] [(str (.name constant)) constant])) entries)
        base (fn [world label]
               (let [wrapper (get refs label) payload (first (:fields (m/node world wrapper)))]
                 (:fields (m/node world (first (:fields (m/node world payload)))))))
        [world types]
        (reduce (fn [[world out] label]
                  (let [[name _ type] (base world label)
                        [world ctors]
                        (reduce (fn [[world out] ctor-name]
                                  (let [[name _ type] (base world (str ctor-name))
                                        [world ctor] (guest/ctor world 0 [name type] 0)]
                                    [world (conj out ctor)])) [world []] (.ctors ^ConstantInfo (get ci label)))
                        [world ctors] (guest-list world ctors)
                        [world type] (guest/ctor world 0 [name type ctors] 0)]
                    [world (conj out type)])) [(:world loaded) []] group)
        [world types] (guest-list world types)
        [_ parameters _] (base world (first group))
        [world declaration] (guest/ctor world 6 [parameters num-params types] 1)]
    {:world world :declaration declaration :expected ci})))

(deftest guest-source-projection-generates-families-and-preserves-original-type-roots
  (doseq [[group params] [[["TinyEnum"] 0] [["UnitProp"] 0] [["PolyList"] 1] [["SmallEq"] 2]]]
    (let [{:keys [world declaration expected]} (native-source-declaration group params)
          ;; These independent source families do not depend on prior user types.
          result (declaration/generate-inductive world (Env.) declaration)
          original (:original-expressions result)]
      (is (identical? world (:world result)))
      (is (= declaration (:guest-declaration result)))
      (is (pos? (.size ^java.util.IdentityHashMap original)))
      (doseq [^ConstantInfo ci (:constants result)]
        (is (= (imported/checking-shape (get expected (str (.name ci))))
               (imported/checking-shape ci)))))))

(deftest lossy-source-provenance-is-rejected-before-checking-projection
  (let [{:keys [world declaration]} (native-source-declaration ["TinyEnum"] 0)
        types (nth (:fields (m/node world declaration)) 2)
        type (first (:fields (m/node world types)))
        expression (second (:fields (m/node world type)))
        replace-type (fn [world value] (assoc-in world [:heap (:id type) :fields 1] value))]
    (let [[world metadata] (guest/ctor world 10 [0 expression] 8)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"metadata provenance"
            (declaration/generate-inductive (replace-type world metadata) (Env.) declaration))))
    (let [[world name] (guest/guest-name world "local")
          [world binding] (guest/ctor world 8 [name expression expression expression] 9)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"metadata provenance"
            (declaration/generate-inductive (replace-type world binding) (Env.) declaration))))
    (let [level (first (:fields (m/node world expression)))
          [world maximum] (guest/ctor world 2 [level guest/nil-tag] 8)
          [world normalized] (guest/ctor world 3 [maximum] 8)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"noncanonical universe provenance"
            (declaration/generate-inductive (replace-type world normalized) (Env.) declaration))))))
