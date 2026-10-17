(ns ansatz.kernel.constructor-parent-test
  "Constructor validation in a temporary mutual header environment.
   These fixtures exercise the kernel checking phase, not bundle admission or
   source recursor generation. Native oracle: ConstructorParentOracle.lean."
  (:require [clojure.test :refer [deftest is testing]])
  (:import [ansatz.kernel ConstantInfo Env Expr Level Name TypeChecker]
           [java.lang.reflect InvocationTargetException]))

(defn- check-constructor [env ctor]
  (let [method (.getDeclaredMethod TypeChecker "checkConstructorDeclaration"
                                   (into-array Class [Env ConstantInfo Long/TYPE]))]
    (.setAccessible method true)
    (try (.invoke method nil (object-array [env ctor (long 1000000)]))
         (catch InvocationTargetException e (throw (.getCause e))))))

(defn- fixture [unsafe?]
  (let [a (Name/fromString "ParentA") b (Name/fromString "ParentB")
        ca (Name/fromString "ParentA.mk") cb (Name/fromString "ParentB.mk")
        params (object-array []) all (object-array [a b])
        type (Expr/sort (Level/succ Level/ZERO_LEVEL) false)
        ind (fn [n c] (ConstantInfo/mkInduct n params type 0 0 all
                                             (into-array Name [c]) 0 false false unsafe?))
        env (-> (Env.) (.addConstant (ind a ca)) (.addConstant (ind b cb)))
        ctor (fn [n parent result]
               (ConstantInfo/mkCtor n params (Expr/mkConst result params false)
                                    parent 0 0 0 unsafe?))]
    {:env env :valid [(ctor ca a a) (ctor cb b b)]
     :wrong [(ctor ca a b) (ctor cb b a)]}))

(deftest constructor-must-return-its-own-mutual-parent
  (doseq [unsafe? [false true]]
    (testing (str "parent check applies with unsafe=" unsafe?)
      (let [{:keys [env valid wrong]} (fixture unsafe?)]
        (doseq [ctor valid]
          (is (nil? (check-constructor env ctor))))
        (doseq [ctor wrong]
          (is (thrown-with-msg? RuntimeException #"return type is not an application of"
                                (check-constructor env ctor))))))))
