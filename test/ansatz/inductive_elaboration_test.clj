(ns ansatz.inductive-elaboration-test
  (:require [clojure.string]
            [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.inductive :as ind]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.test-env :as test-env]))

(use-fixtures :each
  (fn [f]
    (let [saved @a/ansatz-env]
      (try
        (reset! a/ansatz-env @test-env/checked-bundled-init-env)
        (f)
        (finally (reset! a/ansatz-env saved))))))

(defn- ctor-type [n]
  (.type (env/lookup (a/env) (name/from-string n))))

(deftest proposition-fields-and-boolean-indices
  ;; Paired with test/lean/inductive_elaboration.lean.
  (a/inductive Bounded [] (mk [n Nat] [h (<= n 3)]))
  (a/inductive Flagged [] :indices [b Bool]
               (off :where [false]) (on :where [true]))
  (a/inductive BoundedExplicit [] (mk [n Nat] [h (LE.le Nat instLENat n 3)]))
  (a/inductive FlaggedExplicit [] :indices [b Bool]
               (off :where [Bool.false]) (on :where [Bool.true]))
  (is (= (e/forall-type (e/forall-body (ctor-type "Bounded.mk")))
         (e/forall-type (e/forall-body (ctor-type "BoundedExplicit.mk")))))
  (is (= (second (e/get-app-fn-args (ctor-type "Flagged.off")))
         (second (e/get-app-fn-args (ctor-type "FlaggedExplicit.off")))))
  (is (= (second (e/get-app-fn-args (ctor-type "Flagged.on")))
         (second (e/get-app-fn-args (ctor-type "FlaggedExplicit.on")))))
  (a/defn bounded-constructor [n :- Nat h :- (<= n 3)]
    Bounded (Bounded.mk n h))
  (a/defn flagged-off [] (Flagged false) Flagged.off)
  (a/defn flagged-on [] (Flagged true) Flagged.on)
  (a/theorem bounded-constructor-equality [n :- Nat h :- (<= n 3)]
             (= (bounded-constructor n h) (Bounded.mk n h)) (rfl))
  (a/theorem flagged-off-equality []
             (= (Flagged false) (flagged-off) Flagged.off) (rfl))
  (a/theorem flagged-on-equality []
             (= (Flagged true) (flagged-on) Flagged.on) (rfl))
  (is (= "(∀ : Nat, (∀ : (LE.le.{0} Nat instLENat #0 3), Bounded))"
         (e/->string (ctor-type "Bounded.mk"))))
  (is (= "(Flagged Bool.false)" (e/->string (ctor-type "Flagged.off"))))
  (is (= "(Flagged Bool.true)" (e/->string (ctor-type "Flagged.on")))))

(deftest comparisons-use-the-operand-type
  (a/inductive IntBounded [] (mk [x Int] [h (<= x 3)]))
  (a/defn int-bounded-constructor [x :- Int h :- (<= x 3)]
    IntBounded (IntBounded.mk x h))
  (is (clojure.string/includes? (e/->string (ctor-type "IntBounded.mk")) "instLEInt")))

(deftest binder-holes-are-inferred-before-abstraction
  (a/inductive InferredField [] (mk [x _] [h (= Nat x x)]))
  (a/inductive InferredHeader [x _ h (= Nat x x)] (mk))
  (is (= "Nat" (e/->string (e/forall-type (ctor-type "InferredField.mk")))))
  (is (= "Nat" (e/->string (e/forall-type (ctor-type "InferredHeader.mk"))))))

(deftest unresolved-recursive-parameter-hole-is-an-elaboration-error
  (let [error (try
                (a/inductive RecursiveHole [A Type]
                             (mk [x A] [xs (RecursiveHole _)]))
                nil
                (catch clojure.lang.ExceptionInfo ex ex))]
    (is (= :elab-error (:kind (ex-data error))))
    (is (re-find #"don't know how to synthesize placeholder" (or (some-> error ex-message) "")))
    (is (seq (:mvars (ex-data error)))))
  (is (nil? (env/lookup (a/env) (name/from-string "RecursiveHole")))))

(deftest recursive-parameter-hole-is-solved-by-the-index
  (a/inductive SolvedRecursive [A Type] :indices [x A]
               (leaf [x A] :where [x])
               (mk [x A] [xs (SolvedRecursive _ x)] :where [x]))
  (a/defn solved-recursive-constructor [A :- Type x :- A xs :- (SolvedRecursive A x)]
    (SolvedRecursive A x) (SolvedRecursive.mk x xs))
  (let [type (ctor-type "SolvedRecursive.mk")
        after-fields (e/forall-body (e/forall-body type))]
    (is (e/forall? after-fields))
    (is (= "(SolvedRecursive #1 #0)" (e/->string (e/forall-type after-fields))))
    (is (= "(SolvedRecursive #2 #1)" (e/->string (e/forall-body after-fields))))))

(deftest dependent-headers-fields-and-inferred-implicits
  (a/inductive DepBound [n Nat p (<= n 3)]
               (mk [xs (List Nat)] [h (= (Option.some n) (Option.some n))]))
  (a/inductive Witnessed [] :indices [n Nat h (<= n 3)]
               (mk [n Nat] [h (<= n 3)] :where [n h]))
  (a/inductive IndexedElement [A Type] :indices [x A]
               (mk [x A] :where [x]))
  (a/defn indexed-element-constructor [A :- Type x :- A]
    (IndexedElement A x) (IndexedElement.mk x))
  (a/inductive Dependent [A Type]
               (mk [x A] [h (= x x)] [d (Decidable (= x x))]))
  (a/defn witnessed-constructor [n :- Nat h :- (<= n 3)]
    (Witnessed n h) (Witnessed.mk n h))
  (a/defn dependent-constructor
    [A :- Type x :- A h :- (= x x) d :- (Decidable (= x x))]
    (Dependent A) (Dependent.mk x h d))
  (is (some? (ctor-type "DepBound.mk")))
  (is (some? (ctor-type "Witnessed.mk"))))

(deftest constructor-binders-can-shadow-header-names
  (a/inductive Shadowed [n Nat] (mk [n Nat]))
  (a/inductive ShadowFamily [] (mk [ShadowFamily Nat]))
  (a/defn shadowed-constructor [outer :- Nat inner :- Nat] (Shadowed outer)
    (Shadowed.mk outer inner))
  (is (= "(∀ : Nat, (∀ : Nat, (Shadowed #1)))"
         (e/->string (ctor-type "Shadowed.mk")))))

(deftest recursive-parameters-are-fixed
  (a/inductive ImplicitRecursive [A Type]
               (nil) (cons [x A] [xs (ImplicitRecursive A)]))
  (a/defn implicit-recursive-constructor [] (ImplicitRecursive Nat)
    (ImplicitRecursive.cons 1 ImplicitRecursive.nil))
  (let [type (ctor-type "ImplicitRecursive.cons")
        field-type (e/forall-type (e/forall-body (e/forall-body type)))]
    (is (= "(ImplicitRecursive #1)" (e/->string field-type)))))

(deftest arithmetic-indices-recursion-nesting-and-universes
  (a/inductive Counted [A (Type u)] :indices [n Nat]
               (nil :where [0])
               (cons [x A] [n Nat] [xs (Counted A n)] :where [(+ n 1)]))
  (a/inductive Branches [] (node [children (List Branches)]))
  (a/defn counted-constructor [n :- Nat xs :- (Counted Nat n)]
    (Counted Nat (+ n 1)) (Counted.cons 7 n xs))
  (is (= 1 (count (.levelParams (env/lookup (a/env) (name/from-string "Counted"))))))
  (is (some? (env/lookup (a/env) (name/from-string "Branches.rec")))))

(deftest programmatic-expression-types
  (let [nat (e/const' (name/from-string "Nat") [])]
    (ind/define-inductive (a/env) "ExprFields" [] [['mk ['n nat]]])
    (is (= (e/forall' "n" nat (e/const' (name/from-string "ExprFields") []) :default)
           (ctor-type "ExprFields.mk")))))

(deftest invalid-indices-fields-and-negative-occurrences
  (doseq [[family params ctors opts]
          '[["BadIndex" [] [[mk [] [3]]] [:indices [b Bool]]]
            ["WrongIndex" [] [[mk [n Nat] [n]]] [:indices [b Bool]]]
            ["BadIndexCount" [] [[mk []]] [:indices [b Bool]]]
            ["BadField" [] [[mk [h 3]]] []]
            ["Varying" [A Type] [[mk [xs (Varying Nat)]]] []]
            ["Negative" [] [[mk [f (=> Negative Nat)]]] []]]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (apply ind/define-inductive (a/env) family params ctors opts))))
  (doseq [n ["BadIndex" "WrongIndex" "BadIndexCount" "BadField" "Varying" "Negative"]]
    (is (nil? (env/lookup (a/env) (name/from-string n))))))

(deftest partial-family-applications-are-predicate-arguments
  ;; Paired with test/lean/partial_inductive_application.lean.
  (a/inductive PartialR [roots (List Nat)] :in Prop :indices [x Nat]
               (mk [x Nat] [h (List.Mem Nat x roots)] :where [x]))
  (a/theorem use-predicate [P :- (=> Nat Prop) x :- Nat h :- (P x)] (P x)
             (exact h))
  (a/theorem partial-family-exact
             [roots :- (List Nat) x :- Nat h :- (PartialR roots x)] (PartialR roots x)
             (exact (use-predicate (PartialR roots) x h)))
  (a/theorem partial-family-apply
             [roots :- (List Nat) x :- Nat h :- (PartialR roots x)] (PartialR roots x)
             (apply (use-predicate (PartialR roots) x)) (exact h))
  (a/theorem partial-family-have
             [roots :- (List Nat) x :- Nat h :- (PartialR roots x)] (PartialR roots x)
             (have hx (PartialR roots x) := (use-predicate (PartialR roots) x h)) (exact hx))
  (a/defn partial-family-body [roots :- (List Nat)] (=> Nat Prop) (PartialR roots))
  (a/theorem partial-family-eta [roots :- (List Nat)]
             (= (=> Nat Prop) (partial-family-body roots) (fn [x :- Nat] (PartialR roots x)))
             (rfl))
  (is (= :default (e/forall-info (ctor-type "PartialR")))))

(deftest partial-types-functions-and-constructors-are-arguments
  (a/structure PartialBox [A Type B Type] (left A) (right B))
  (a/defn use-type [F :- (=> Type Type)] Type (F Nat))
  (a/defn partial-structure [] Type (use-type (PartialBox Nat)))
  (a/theorem partial-structure-equality []
             (= Type (partial-structure) (PartialBox Nat Nat)) (rfl))
  (a/defn use-function [f :- (=> Nat Nat) x :- Nat] Nat (f x))
  (a/theorem partial-function-equality []
             (= Nat (use-function (Nat.add 1) 2) 3) (rfl))
  (a/defn use-constructor [f :- (=> (List Nat) (List Nat)) xs :- (List Nat)]
    (List Nat) (f xs))
  (a/theorem partial-constructor-equality [xs :- (List Nat)]
             (= (List Nat) (use-constructor (List.cons 1) xs) (List.cons Nat 1 xs)) (rfl))
  ;; Construct the @-prefixed symbol because Clojure reads @ as deref.
  (a/prove-theorem 'partial-explicit-constructor-equality '[xs :- (List Nat)]
                   (list '= '(List Nat)
                         (list 'use-constructor (list (symbol "@List.cons") 'Nat 1) 'xs)
                         '(List.cons Nat 1 xs))
                   '[(rfl)])
  (is (= :implicit (e/forall-info (ctor-type "PartialBox.mk"))))
  (is (= :default (e/forall-info (ctor-type "PartialBox")))))
