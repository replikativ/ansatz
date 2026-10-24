(ns ansatz.export.expression-identity-test
  "The ordinary Clojure DAG resolver must obey the same Java pointer identity
   rule as ExprStore, including independently captured revisions of one backend."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.export.storage :as storage])
  (:import [ansatz.kernel Level Env TypeChecker]
           [java.nio ByteBuffer]))

(def sort-raw (.array (doto (ByteBuffer/allocate 5) (.put (byte 1)) (.putInt 0))))

(deftest independent-resolvers-never-turn-reused-ids-into-equality
  (with-redefs [storage/store-get (fn [_ _] sort-raw)]
    (let [resolve-left (storage/create-expr-resolver :left (constantly nil) (constantly Level/ZERO_LEVEL))
          resolve-right (storage/create-expr-resolver :right (constantly nil)
                                                     (constantly (Level/succ Level/ZERO_LEVEL)))
          left (resolve-left 0) right (resolve-right 0)]
      (is (= 0 (.-storeId left) (.-storeId right)))
      (is (false? (.isEqp left right)))
      (is (false? (.isDefEq (TypeChecker. (Env.)) left right)))
      (is (identical? left (resolve-left 0))))))

(deftest captured-revisions-of-the-same-backend-do-not-share-pointer-identity
  (let [revision (atom Level/ZERO_LEVEL)]
    (with-redefs [storage/store-get (fn [_ _] sort-raw)]
      (let [resolve-old (storage/create-expr-resolver :same-backend (constantly nil) (constantly @revision))
            old (resolve-old 0)]
        (reset! revision (Level/succ Level/ZERO_LEVEL))
        (let [resolve-new (storage/create-expr-resolver :same-backend (constantly nil) (constantly @revision))
              fresh (resolve-new 0)]
          (is (= (.-storeId old) (.-storeId fresh)))
          (is (false? (.isEqp old fresh)))
          (is (false? (.isDefEq (TypeChecker. (Env.)) old fresh)))
          (is (identical? old (resolve-old 0))))))))
