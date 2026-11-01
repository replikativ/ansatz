(ns prototype.mutual-universe-contract-test
  (:require [clojure.test :refer [deftest is testing]])
  (:import [ansatz.kernel ConstantInfo Env Expr Level Name TypeChecker]))

;; Direct Java checker regression: these are independently well-typed headers and
;; bodies, not a guest-layout model. Pinned Lean environment.cpp add_mutual requires
;; the SAME ORDERED universe list across the entire block before body checking.
(defn- definition [label params safety]
  (let [params (mapv #(Name/fromString %) params)
        level (if (seq params) (Level/param (first params)) Level/ZERO_LEVEL)]
    (ConstantInfo/mkDef (Name/fromString label) (object-array params)
      (Expr/sort (Level/succ level) (boolean (seq params)))
      (Expr/sort level (boolean (seq params)))
      1 (byte safety) (object-array [(Name/fromString "f") (Name/fromString "g")]))))

(deftest mismatched-universe-parameter-lists-reject-atomically
  (doseq [safety [1 2]
          [left right label] [[["u"] ["v"] "names"]
                              [["u" "v"] ["v" "u"] "order"]
                              [["u"] ["u" "v"] "arity"]]]
    (testing (str label " safety=" safety)
      (let [env (Env.) f (definition "f" left safety) g (definition "g" right safety)]
        ;; Both are valid on their own: only the block-level contract rejects.
        (is (some? (TypeChecker/checkMutualDefinitions env [f] 100000)))
        (is (some? (TypeChecker/checkMutualDefinitions env [g] 100000)))
        (is (thrown-with-msg? RuntimeException #"same universe level parameters"
              (TypeChecker/checkMutualDefinitions env [f g] 100000)))
        (is (nil? (.lookup env (.name f))))
        (is (nil? (.lookup env (.name g))))))))

(deftest matching-universe-lists-admit-both-definitions
  (doseq [safety [1 2] params [[] ["u"] ["u" "v"]]]
    (let [env (Env.) f (definition "f" params safety) g (definition "g" params safety)
          checked (TypeChecker/checkMutualDefinitions env [f g] 100000)]
      (is (identical? f (.lookup checked (.name f))))
      (is (identical? g (.lookup checked (.name g))))
      (is (nil? (.lookup env (.name f))))
      (is (nil? (.lookup env (.name g)))))))
