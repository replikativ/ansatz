(ns ansatz.kernel.expression-identity-test
  "Actual expression stores, declaration admission and structural caches. Local
   integer addresses never establish pointer equality across reconstructed nodes."
  (:require [clojure.test :refer [deftest is testing]])
  (:import [ansatz.kernel Expr ExprStore Level Name Env TypeChecker ConstantInfo
            LeanExprKey ExprMap ExprPairSet]
           [java.util ArrayList]))

(defn with-sort-stores [left-level right-level f]
  (with-open [left (ExprStore. (ArrayList.) (doto (ArrayList.) (.add left-level)))
              right (ExprStore. (ArrayList.) (doto (ArrayList.) (.add right-level)))]
    (.storeSort left 0 0)
    (.storeSort right 0 0)
    (.finishParsing left)
    (.finishParsing right)
    (f left right (.resolve left 0) (.resolve right 0))))

(defn declaration-fixture [^Expr declared-type ^Expr expected-type]
  (let [a (Name/fromString "ExpressionIdentity.a")
        result (Name/fromString "ExpressionIdentity.result")
        base (TypeChecker/checkConstant (Env.)
                                        (ConstantInfo/mkAxiom a (object-array []) declared-type false))]
    [base (ConstantInfo/mkDefWithHints result (object-array []) expected-type
                                       (Expr/mkConst a [] false) -1 (byte 0) (object-array [result]))]))

(deftest independent-store-address-collision-does-not-admit-wrong-universe
  (with-sort-stores
    Level/ZERO_LEVEL (Level/succ Level/ZERO_LEVEL)
    (fn [^ExprStore left _ ^Expr x ^Expr y]
      (is (= 0 (.-storeId x) (.-storeId y)))
      (is (not (identical? x y)))
      (is (not (.equals x y)))
      (is (false? (.isEqp x y)))
      (is (false? (.isDefEq (TypeChecker. (Env.)) x y)))
      (is (.isEqp x (.resolve left 0)) "a real cache hit preserves pointer identity")
      (let [[base bad] (declaration-fixture x y)]
        (is (thrown? Exception (TypeChecker/checkConstant base bad)))))))

(deftest equal-independent-nodes-still-compare-and-admit-via-structural-equality
  (with-sort-stores
    Level/ZERO_LEVEL Level/ZERO_LEVEL
    (fn [_ _ ^Expr x ^Expr y]
      (is (not (identical? x y)))
      (is (false? (.isEqp x y)))
      (is (.equals (LeanExprKey. x) (LeanExprKey. y)))
      (is (.isDefEq (TypeChecker. (Env.)) x y))
      (let [[base valid] (declaration-fixture x y)]
        (is (some? (.lookup (TypeChecker/checkConstant base valid) (.name ^ConstantInfo valid))))))))

(deftest binder-domain-comparison-does-not-skip-colliding-local-addresses
  (with-sort-stores
    Level/ZERO_LEVEL (Level/succ Level/ZERO_LEVEL)
    (fn [_ _ x y]
      (let [n (Name/fromString "x") body (Expr/bvar 0)
            pi-left (Expr/forall n x body :default)
            pi-right (Expr/forall n y body :default)
            lam-left (Expr/lam n x body :default)
            lam-right (Expr/lam n y body :default)]
        (is (false? (.isDefEq (TypeChecker. (Env.)) pi-left pi-right)))
        (is (false? (.isDefEq (TypeChecker. (Env.)) lam-left lam-right)))))))

(deftest structural-cache-hash-collisions-do-not-reuse-another-stores-value
  ;; Aa/BB have equal Java string hashes. Real stored literals therefore test
  ;; the payload gate after the caches' hash gate, rather than different buckets.
  (with-open [left (ExprStore. (ArrayList.) (ArrayList.))
              right (ExprStore. (ArrayList.) (ArrayList.))]
    (.storeLitStr left 0 "Aa")
    (.storeLitStr right 0 "BB")
    (.finishParsing left)
    (.finishParsing right)
    (let [a (.resolve left 0) b (.resolve right 0)
          cache (ExprMap. 4) pairs (ExprPairSet. 4)]
      (is (= (.structuralHash a) (.structuralHash b)))
      (is (= (.-storeId a) (.-storeId b)))
      (is (false? (.isEqp a b)))
      (is (not (.equals (LeanExprKey. a) (LeanExprKey. b))))
      (.put cache a :left)
      (is (nil? (.get cache b)))
      (.put cache b :right)
      (is (= 2 (.size cache)))
      (is (= :left (.get cache a)))
      (is (= :right (.get cache b)))
      (.add pairs a a)
      (is (false? (.contains pairs b a)))
      (is (false? (.contains pairs a b)))
      (is (.contains pairs a a)))))

(deftest same-store-cache-eviction-retains-structural-equality-without-false-pointer-identity
  (let [field (.getDeclaredField ExprStore "CACHE_SIZE")]
    (.setAccessible field true)
    (let [collision-id (.getInt field nil)]
      (with-open [store (ExprStore. (ArrayList.) (doto (ArrayList.) (.add Level/ZERO_LEVEL)))]
        (.storeSort store 0 0)
        (.storeSort store collision-id 0)
        (.finishParsing store)
        (let [old (.resolve store 0)]
          (.resolve store collision-id)
          (let [fresh (.resolve store 0) cache (ExprMap. 4)]
            (is (not (identical? old fresh)) "actual direct-cache collision rehydrates the node")
            (is (= 0 (.-storeId old) (.-storeId fresh)))
            (is (false? (.isEqp old fresh)))
            (is (.equals (LeanExprKey. old) (LeanExprKey. fresh)))
            (is (.isDefEq (TypeChecker. (Env.)) old fresh))
            (.put cache old :retained)
            (is (= :retained (.get cache fresh)))))))))

(deftest share-common-propagates-only-diagnostic-addresses
  (with-open [store (ExprStore. (ArrayList.) (ArrayList.))
              other (ExprStore. (ArrayList.) (doto (ArrayList.) (.add Level/ZERO_LEVEL)))]
    (.storeBvar store 0 0)
    (.storeBvar store 1 0)
    (.storeApp store 2 0 1)
    (.storeSort other 2 0)
    (.finishParsing store)
    (.finishParsing other)
    (let [original (.resolve store 2) shared (Expr/shareCommon original) unrelated (.resolve other 2)]
      (is (not (identical? original shared)) "sharing rebuilds the application after canonicalizing its children")
      (is (identical? (.o0 shared) (.o1 shared)))
      (is (= 2 (.-storeId shared) (.-storeId unrelated)))
      (is (false? (.isEqp shared unrelated)))
      (is (.equals original shared)))))
