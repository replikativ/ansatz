(ns prototype.kernel-bridge-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.kernel-bridge :as bridge]
            [prototype.machine :as m]
            [prototype.scalar :as scalar]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as level]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel Expr Level Name Env]))

(def nil-tag (m/->Tag 0))
(defn ctor [world tag fields scalar-size]
  (if (zero? scalar-size) (m/allocate world :ctor tag (vec fields))
    (let [layout {:objects (count fields) :usize 0 :ssize scalar-size}
          [world ref] (m/scalar-constructor world tag (vec fields) layout)
          bytes (into {} (map #(vector (+ (* 8 (count fields)) %) 0) (range scalar-size)))]
      [(assoc-in world [:heap (:id ref) :scalar-bytes] bytes) ref])))
(defn scalar! [world ref offset type value]
  (let [node (m/node world ref)]
    (assoc-in world [:heap (:id ref) :scalar-bytes]
      (scalar/write-bytes (:layout node) (:scalar-bytes node)
        {:index (count (:fields node)) :offset offset :type type :region :scalar} value))))
(defn guest-name [world text] (ctor world 1 [nil-tag text] 8))
(defn literal [world n]
  (let [[world lit] (ctor world 0 [n] 0)] (ctor world 9 [lit] 8)))
(defn constant [world text]
  (let [[world n] (guest-name world text)] (ctor world 4 [n nil-tag] 8)))
(defn declaration [world text type value]
  (let [[world n] (guest-name world text)
        [world c] (ctor world 0 [n nil-tag type] 0)
        [world all] (ctor world 1 [n nil-tag] 0)
        [world definition] (ctor world 0 [c value nil-tag all] 1)
        world (scalar! world definition 0 "uint8" 1)]
    (ctor world 1 [definition] 0)))

(defn checked-nat-environment []
  ;; Actual inductive admission/generation, without a downloaded proof corpus.
  (let [nat (name/from-string "Nat") zero (name/from-string "Nat.zero") succ (name/from-string "Nat.succ")
        nat-type (e/const' nat [])
        ind (env/mk-induct nat [] (e/sort' (level/succ level/zero)) :ctors [zero succ] :rec? true)
        z (env/mk-ctor zero [] nat-type nat 0 0 0)
        s (env/mk-ctor succ [] (e/forall' (name/anonymous) nat-type nat-type :default) nat 1 0 1)]
    (env/check-inductive-bundle (env/empty-env) (env/mk-inductive-bundle [] 0 false [ind] [z s] []) 1000000)))

(deftest actual-guest-layout-projects-and-checks-a-nat-definition
  (let [before-env (checked-nat-environment)
        [world type] (constant (m/world {}) "Nat")
        [world body] (literal world 42)
        [world decl] (declaration world "answer" type body)
        before-world world
        admitted (bridge/admit-definition world before-env decl)]
    (is (= 42N (.o0 ^Expr (.value (:constant admitted)))))
    (is (= (name/from-string "answer") (.name (:constant admitted))))
    (is (identical? world (:world admitted)))
    (is (= decl (:guest-declaration admitted)))
    (is (nil? (.lookup ^Env before-env (name/from-string "answer"))))
    (is (some? (.lookup ^Env (:env admitted) (name/from-string "answer"))))
    (is (= before-world world))
    (is (thrown? Exception (bridge/admit-definition world (:env admitted) decl)))))

(deftest strict-admission-rejects-ill-typed-and-missing-constants
  (let [en (checked-nat-environment)
        [world nat] (constant (m/world {}) "Nat")
        [world prop] (ctor world 3 [nil-tag] 8)
        [world bad] (declaration world "bad" nat prop)
        [world missing] (constant world "Missing")
        [world lit] (literal world 42)
        [world unknown] (declaration world "unknown" missing lit)]
    (is (thrown? Exception (bridge/admit-definition world en bad)))
    (is (thrown? Exception (bridge/admit-definition world en unknown)))
    (is (nil? (.lookup ^Env en (name/from-string "bad"))))
    (is (nil? (.lookup ^Env en (name/from-string "unknown"))))))

(deftest guest-metadata-is-preserved-only-in-original-objects
  (let [[world nat] (constant (m/world {}) "Nat")
        [world lit] (literal world 1)
        [world binder] (guest-name world "x")
        [world let-ref] (ctor world 8 [binder nat lit lit] 9)
        world (scalar! world let-ref 8 "uint8" 1)
        [world metadata] (ctor world 0 ["ignored checker metadata"] 0)
        [world wrapped] (ctor world 10 [metadata let-ref] 8)
        projected (bridge/project-expr world wrapped)]
    (is (= Expr/LET (.tag ^Expr projected)))
    (is (= 1 (m/read-scalar-node (m/node world let-ref) {:index 4 :offset 8 :type "uint8" :region :scalar})))
    (is (= ["ignored checker metadata"] (:fields (m/node world metadata))))
    (is (= "x" (str (.o0 ^Expr projected))))))

(deftest world-local-memos-preserve-dag-sharing-without-aliasing-forks
  (let [[world lit] (literal (m/world {}) 1)
        [world app] (ctor world 5 [lit lit] 8)
        result (bridge/project-with-stats world :expr app)
        ^Expr projected (:value result)
        literal-ref (first (:fields (m/node world lit)))
        fork (assoc-in world [:heap (:id literal-ref) :fields] [2])]
    (is (identical? (.o0 projected) (.o1 projected)))
    (is (= 1N (.o0 ^Expr (bridge/project-expr world lit))))
    (is (= 2N (.o0 ^Expr (bridge/project-expr fork lit))))
    (is (= 4 (:projected-nodes result)))))

(deftest deep-projection-uses-an-explicit-stack
  (let [[world lit] (literal (m/world {}) 0)
        [world root] (loop [n 0 world world current lit]
                       (if (= n 12000) [world current]
                         (let [[world app] (ctor world 5 [current lit] 8)]
                           (recur (inc n) world app))))
        ^Expr result (bridge/project-expr world root)]
    (is (= 12000 (loop [n 0 cur result]
                   (if (= Expr/APP (.tag ^Expr cur)) (recur (inc n) (.o0 ^Expr cur)) n))))))

(deftest unsupported-values-cycles-and-layouts-fail-explicitly
  (let [[world name] (ctor (m/world {}) 2 [nil-tag 9223372036854775808N] 8)
        [world fvar] (ctor world 1 [nil-tag] 8)
        [world mvar] (ctor world 2 [nil-tag] 8)
        [world level-mvar] (ctor world 5 [nil-tag] 8)
        [world bvar] (ctor world 0 [1048575] 8)
        [world lit] (literal world 42)
        [world cycle] (ctor world 5 [lit lit] 8)
        cyclic (assoc-in world [:heap (:id cycle) :fields 0] cycle)
        malformed (assoc-in world [:heap (:id lit) :layout :ssize] 9)
        uninitialized (assoc-in world [:heap (:id lit) :scalar-bytes] {})]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"long representation" (bridge/project-name world name)))
    (doseq [value [fvar mvar]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unresolved" (bridge/project-expr world value))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"metavariable" (bridge/project-level world level-mvar)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"metadata range" (bridge/project-expr world bvar)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Cyclic" (bridge/project-expr cyclic cycle)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"layout" (bridge/project-expr malformed lit)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"(uninitialized|constructor layout)" (bridge/project-expr uninitialized lit)))))

(deftest raw-level-normalization-is-only-a-checker-projection
  (let [[world raw-max] (ctor (m/world {}) 2 [nil-tag nil-tag] 8)]
    (is (= Level/ZERO (.tag ^Level (bridge/project-level world raw-max))))
    (is (= 2 (:tag (m/node world raw-max))))))

(deftest binders-literals-and-projections-use-pinned-field-and-scalar-order
  (let [[world nat] (constant (m/world {}) "Nat")
        [world binder] (guest-name world "x")
        [world bound] (ctor world 0 [0] 8)
        [world lam] (ctor world 6 [binder nat bound] 9)
        world (scalar! world lam 8 "uint8" 2)
        [world pi] (ctor world 7 [binder nat nat] 9)
        [world string-lit] (ctor world 1 ["λ😀"] 0)
        [world string-expr] (ctor world 9 [string-lit] 8)
        [world projection] (ctor world 11 [binder 1 nat] 8)
        ^Expr result (bridge/project-expr world lam)]
    (is (= Expr/LAM (.tag result)))
    (is (= :strict-implicit (.o3 result)))
    (is (= 0 (.longVal ^Expr (.o2 result))))
    (is (= Expr/FORALL (.tag ^Expr (bridge/project-expr world pi))))
    (is (= "λ😀" (.o0 ^Expr (bridge/project-expr world string-expr))))
    (is (= 1 (.longVal ^Expr (bridge/project-expr world projection))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Loose bound variable"
          (bridge/project-expr world bound)))))

(deftest unsupported-admission-metadata-fails-before-kernel-publication
  (let [en (checked-nat-environment)
        [world nat] (constant (m/world {}) "Nat")
        [world body] (literal world 42)
        [world decl] (declaration world "restricted" nat body)
        definition (first (:fields (m/node world decl)))
        unsafe-world (scalar! world definition 0 "uint8" 0)
        [world hints] (ctor world 2 [] 4)
        regular-zero (assoc-in world [:heap (:id definition) :fields 2] hints)
        regular-large (scalar! regular-zero hints 0 "uint32" 4294967295)
        wrong-kind (assoc-in world [:heap (:id decl) :tag] 2)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"safe single"
          (bridge/admit-definition unsafe-world en decl)))
    (is (= 0 (.getHintsCode ^ansatz.kernel.ConstantInfo (:constant (bridge/admit-definition regular-zero en decl)))))
    (is (= 4294967295 (.getHintsCode ^ansatz.kernel.ConstantInfo (:constant (bridge/admit-definition regular-large en decl)))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"layout" (bridge/admit-definition wrong-kind en decl)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"fuel" (bridge/admit-definition world en decl 0)))
    (is (nil? (.lookup ^Env en (name/from-string "restricted"))))))

(defn axiom-declaration [world text type]
  (let [[world n] (guest-name world text)
        [world constant] (ctor world 0 [n nil-tag type] 0)
        [world axiom] (ctor world 0 [constant] 1)]
    (ctor world 0 [axiom] 0)))

(deftest safe-axiom-admission-checks-types-and-preserves-forks
  (let [[world one] (ctor (m/world {}) 1 [nil-tag] 8)
        [world sort] (ctor world 3 [one] 8)
        [world decl] (axiom-declaration world "HostedSort" sort)
        empty (env/empty-env)
        first-admission (bridge/admit-axiom world empty decl)
        [world hosted-sort] (constant world "HostedSort")
        [world dependent] (axiom-declaration world "hostedValue" hosted-sort)
        second-input-world world
        second-admission (bridge/admit-axiom world (:env first-admission) dependent)
        [world unknown] (constant world "UnknownType")
        [world invalid] (axiom-declaration world "invalid" unknown)
        axiom (first (:fields (m/node world decl)))
        unsafe-world (scalar! world axiom 0 "uint8" 1)]
    (is (nil? (.lookup ^Env empty (name/from-string "HostedSort"))))
    (is (some? (.lookup ^Env (:env first-admission) (name/from-string "HostedSort"))))
    (is (nil? (.lookup ^Env (:env first-admission) (name/from-string "hostedValue"))))
    (is (some? (.lookup ^Env (:env second-admission) (name/from-string "hostedValue"))))
    (is (= dependent (:guest-declaration second-admission)))
    (is (identical? second-input-world (:world second-admission)))
    (is (thrown? Exception (bridge/admit-axiom world (:env first-admission) decl)))
    (is (thrown? Exception (bridge/admit-axiom world empty dependent)))
    (is (thrown? Exception (bridge/admit-axiom world empty invalid)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"safe axioms"
          (bridge/admit-axiom unsafe-world empty decl)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"fuel"
          (bridge/admit-axiom world empty decl 0)))))

(defn compiler-marker [world text type]
  (let [[world declaration] (axiom-declaration world text type)
        axiom (first (:fields (m/node world declaration)))]
    [(scalar! world axiom 0 "uint8" 1) declaration]))

(deftest exact-compiler-markers-are-strictly-checked-with-unsafe-metadata-preserved
  (doseq [text ["lcAny" "lcErased" "lcVoid"]]
    (let [[world one] (ctor (m/world {}) 1 [nil-tag] 8)
          [world type] (ctor world 3 [one] 8)
          [world declaration] (compiler-marker world text type)
          before world empty (env/empty-env)
          admitted (bridge/admit-compiler-marker world empty declaration)
          constant (:constant admitted)]
      (is (bridge/compiler-marker-declaration? world declaration))
      (is (= (name/from-string text) (.name constant)))
      (is (true? (.isUnsafe constant)))
      (is (empty? (.levelParams constant)))
      (is (= Expr/SORT (.tag ^Expr (.type constant))))
      (is (nil? (.lookup ^Env empty (name/from-string text))))
      (is (some? (.lookup ^Env (:env admitted) (name/from-string text))))
      (is (identical? before (:world admitted)))
      (is (= declaration (:guest-declaration admitted)))
      (is (thrown? Exception (bridge/admit-compiler-marker world (:env admitted) declaration)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"safe axioms" (bridge/admit-axiom world empty declaration)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"fuel" (bridge/admit-compiler-marker world empty declaration 0))))))

(deftest nearby-unsafe-axioms-cannot-use-the-compiler-marker-capability
  (let [[world one] (ctor (m/world {}) 1 [nil-tag] 8)
        [world type] (ctor world 3 [one] 8)
        [world declaration] (compiler-marker world "lcAny" type)
        axiom (first (:fields (m/node world declaration)))
        constant (first (:fields (m/node world axiom)))
        [world other-name] (guest-name world "notACompilerMarker")
        [world namespace] (guest-name world "Nested")
        [world nested-name] (ctor world 1 [namespace "lcAny"] 8)
        [world param] (guest-name world "u")
        [world params] (ctor world 1 [param nil-tag] 0)
        [world prop] (ctor world 3 [nil-tag] 8)
        [world maximum] (ctor world 2 [one nil-tag] 8)
        [world normalized-equivalent] (ctor world 3 [maximum] 8)
        [world metadata] (ctor world 0 [nil-tag] 0)
        [world wrapped] (ctor world 10 [metadata type] 8)
        name-ref (first (:fields (m/node world constant)))
        invalid-payload (nth (iterate vector :invalid-string) 4000)
        variants [(assoc-in world [:heap (:id name-ref) :fields 1] invalid-payload)
                  (assoc-in world [:heap (:id constant) :fields 0] other-name)
                  (assoc-in world [:heap (:id constant) :fields 0] nested-name)
                  (assoc-in world [:heap (:id constant) :fields 1] params)
                  (assoc-in world [:heap (:id constant) :fields 2] prop)
                  (assoc-in world [:heap (:id constant) :fields 2] normalized-equivalent)
                  (assoc-in world [:heap (:id constant) :fields 2] wrapped)
                  (scalar! world axiom 0 "uint8" 0)]]
    (doseq [world variants]
      (is (false? (bridge/compiler-marker-declaration? world declaration)))
      (is (thrown? clojure.lang.ExceptionInfo (bridge/admit-compiler-marker world (env/empty-env) declaration))))))
