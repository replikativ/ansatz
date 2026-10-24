(ns ansatz.bounded-ci-comparison-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.kernel.constant-info :as ci]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as l]
            [ansatz.kernel.name :as n]
            [ansatz.constant-info-comparison-test :as fixtures])
  (:import [ansatz.kernel ConstantInfo Expr Level Name]
           [java.math BigInteger]))

(def limits {:pairs 10000 :edges 100000 :scalar-bytes 100000 :items 100000 :depth 256})
(defn theorem [body] (env/mk-thm (n/from-string "test") [] fixtures/type' body))
(defn error-data [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo error (ex-data error))))

(deftest compares-all-complete-variants-and-rejects-incomplete-identical-inputs
  (doseq [[a b] (map vector (fixtures/variants) (fixtures/variants))]
    (is (ci/full-equal-bounded? a b limits))
    (is (ci/full-equal-bounded? a a limits)))
  (let [without-body (ConstantInfo/mkThm (n/from-string "t") (object-array []) fixtures/type' nil (object-array []))
        missing-rules (env/mk-recursor (n/from-string "r") [] fixtures/type')
        missing-all (theorem fixtures/body)
        missing-universes (ConstantInfo/mkAxiom (n/from-string "a") nil fixtures/type' false)]
    (set! (.rules ^ConstantInfo missing-rules) nil)
    (set! (.all ^ConstantInfo missing-all) nil)
    (doseq [a [without-body missing-rules missing-all missing-universes]]
      (is (some? (error-data #(ci/full-equal-bounded? a a limits)))))))

(deftest compares-every-variant-specific-metadata-field
  (doseq [[index changes]
          [[0 {"isUnsafe" true}]
           [1 {"safety" (byte 1) "all" (object-array [(n/from-string "other")]) "hints" (int -1)}]
           [2 {"all" (object-array [(n/from-string "other")])}]
           [3 {"isUnsafe" true "all" (object-array [(n/from-string "other")])}]
           [4 {"quotKind" :ctor}]
           [5 {"numParams" (int 1) "numIndices" (int 1) "numNested" (int 1)
               "isRec" true "isReflexive" true "isUnsafe" true
               "all" (object-array [(n/from-string "other")]) "ctors" (into-array Name [(n/from-string "other")])}]
           [6 {"inductName" (n/from-string "other") "cidx" (int 1) "numParams" (int 1)
               "numFields" (int 1) "isUnsafe" true}]
           [7 {"numParams" (int 1) "numIndices" (int 1) "numMotives" (int 2) "numMinors" (int 1)
               "isK" true "isUnsafe" true "all" (object-array [(n/from-string "other")])}]]
          [field value] changes]
    (let [a (nth (fixtures/variants) index) b (nth (fixtures/variants) index)]
      (.set (.getField ConstantInfo field) b value)
      (is (false? (ci/full-equal-bounded? a b limits)) field)))
  (doseq [rule [(env/mk-recursor-rule (n/from-string "other") 0 fixtures/body)
                (env/mk-recursor-rule (n/from-string "I.mk") 1 fixtures/body)
                (env/mk-recursor-rule (n/from-string "I.mk") 0 fixtures/type')]]
    (let [a (last (fixtures/variants)) b (last (fixtures/variants))]
      (set! (.rules ^ConstantInfo b) (into-array ansatz.kernel.ConstantInfo$RecursorRule [rule]))
      (is (false? (ci/full-equal-bounded? a b limits))))))

(deftest expression-and-name-payloads-are-exact-despite-hash-and-store-id-collisions
  ;; Java String hash collision propagates through literal hashes.
  (let [a (Expr/litStr "Aa") b (Expr/litStr "BB")]
    (is (= (.data a) (.data b)))
    (set! (.storeId a) 7) (set! (.storeId b) 7)
    (is (false? (ci/full-equal-bounded? (theorem a) (theorem b) limits))))
  (let [sort (Expr/sort Level/ZERO_LEVEL false)
        natural (Expr/litNat BigInteger/ZERO)]
    (is (false? (ci/full-equal-bounded? (theorem sort) (theorem natural) limits))))
  (doseq [[a b] [[(e/lam (n/from-string "a") fixtures/type' fixtures/body :default)
                  (e/lam (n/from-string "b") fixtures/type' fixtures/body :default)]
                 [(e/lam (n/from-string "a") fixtures/type' fixtures/body :default)
                  (e/lam (n/from-string "a") fixtures/type' fixtures/body :implicit)]
                 [(Expr/mkConst (n/from-string "c") [] false) (Expr/mkConst (n/from-string "d") [] false)]]]
    (is (false? (ci/full-equal-bounded? (theorem a) (theorem b) limits)))))

(deftest sharing-is-linear-and-independent-of-source-local-ids
  (let [dag (fn [] (nth (iterate #(Expr/app % %) (Expr/bvar 0)) 80))
        a (dag) b (dag)]
    (is (ci/full-equal-bounded? (theorem a) (theorem b) (assoc limits :pairs 500 :items 2000 :edges 4000)))
    (is (= :pairs (:limit (error-data #(ci/full-equal-bounded? (theorem a) (theorem b) (assoc limits :pairs 1))))))
    (is (= :depth (:limit (error-data #(ci/full-equal-bounded? (theorem a) (theorem b) (assoc limits :depth 20))))))))

(deftest all-explicit-budgets-are-required-and-enforced-before-identity-shortcuts
  (let [a (theorem (Expr/litStr (apply str (repeat 100 "x")))) b (theorem (Expr/litStr (apply str (repeat 100 "x"))))]
    (doseq [key (keys limits)]
      (is (some? (error-data #(ci/full-equal-bounded? a b (dissoc limits key)))))
      (is (some? (error-data #(ci/full-equal-bounded? a b (assoc limits key 0))))))
    (doseq [key [:items :edges :scalar-bytes :depth]]
      (is (= key (:limit (error-data #(ci/full-equal-bounded? a a (assoc limits key 1)))))))
    (is (= :pairs (:limit (error-data #(ci/full-equal-bounded? a b (assoc limits :pairs 1)))))))
  (let [large (ConstantInfo/mkAxiom (n/from-string "a") (object-array (repeat 10000 (n/from-string "u"))) fixtures/type' false)]
    (is (= :items (:limit (error-data #(ci/full-equal-bounded? large large (assoc limits :items 100))))))))

(deftest unsupported-metadata-and-collections-fail-closed
  (doseq [payload [{:arbitrary fixtures/body} "metadata" (Object.)]]
    (let [a (theorem (Expr/mdata payload fixtures/body))]
      (is (some? (error-data #(ci/full-equal-bounded? a a limits))))))
  (is (ci/full-equal-bounded? (theorem (Expr/mdata nil fixtures/body))
                              (theorem (Expr/mdata nil fixtures/body)) limits))
  (let [bad (theorem (Expr/mkConst (n/from-string "c") nil false))]
    (is (some? (error-data #(ci/full-equal-bounded? bad bad limits))))))

(deftest scalar-storage-budgets-precede-leaf-comparison
  (let [big (.shiftLeft BigInteger/ONE 100000)
        a (theorem (Expr/litNat big))]
    (is (= :scalar-bytes (:limit (error-data #(ci/full-equal-bounded? a a (assoc limits :scalar-bytes 100))))))))

(deftest compares-every-expression-tag-and-both-level-array-representations
  (let [nm (n/from-string "x") t fixtures/type' b fixtures/body
        models (fn [] [(Expr/bvar 3) (Expr/sort Level/ZERO_LEVEL false)
                       (Expr/mkConst nm [] false) (Expr/app t b)
                       (Expr/lam nm t b :default) (Expr/forall nm t b :implicit)
                       (Expr/mkLet nm t b b) (Expr/litNat BigInteger/TEN)
                       (Expr/litStr "literal") (Expr/mdata nil b) (Expr/proj nm 2 b)
                       (Expr/fvar 10) (Expr/mvar 11)])]
    (doseq [[a b] (map vector (models) (models))]
      (is (ci/full-equal-bounded? (theorem a) (theorem b) limits)))
    (let [u (Level/param (n/from-string "u")) v (Level/param (n/from-string "v"))
          dag (fn [] (Level/imax (Level/max u v) u))
          a (Expr/mkConst nm [(dag)] true)
          b (Expr/mkConst nm (object-array [(dag)]) true)
          c (Expr/mkConst nm [(Level/imax (Level/max u v) v)] true)]
      (is (ci/full-equal-bounded? (theorem a) (theorem b) limits))
      (is (false? (ci/full-equal-bounded? (theorem a) (theorem c) limits))))))

(deftest common-declaration-fields-and-universe-order-are-exact
  (let [u (n/from-string "u") v (n/from-string "v")
        make (fn [nm lps type] (env/mk-axiom (n/from-string nm) lps type))
        a (make "a" [u v] fixtures/type')]
    (doseq [b [(make "b" [u v] fixtures/type')
               (make "a" [v u] fixtures/type')
               (make "a" [u] fixtures/type')
               (make "a" [u v] fixtures/body)]]
      (is (false? (ci/full-equal-bounded? a b limits))))))

(deftest batches-share-one-budget-and-one-comparison-memo
  (let [make-pair (fn [ch]
                    [(theorem (Expr/litStr (apply str (repeat 100 ch))))
                     (theorem (Expr/litStr (apply str (repeat 100 ch))))])
        first-pair (make-pair "x") second-pair (make-pair "y")
        budget (assoc limits :scalar-bytes 1000)]
    (doseq [[a b] [first-pair second-pair]]
      (is (ci/full-equal-bounded? a b budget)))
    (is (= :scalar-bytes
           (:limit (error-data #(ci/full-equal-batch-bounded? [first-pair second-pair] budget))))))
  (let [dag (fn [] (nth (iterate #(Expr/app % %) (Expr/bvar 0)) 80))
        pair [(theorem (dag)) (theorem (dag))]]
    (is (ci/full-equal-batch-bounded? (vec (repeat 16 pair)) (assoc limits :pairs 100))))
  (is (ci/full-equal-batch-bounded? [] limits)))

(deftest batch-container-limits-and-all-root-completeness-precede-comparison
  (is (= :items
         (:limit (error-data #(ci/full-equal-batch-bounded? (vec (repeat 10000 [nil nil]))
                                                            (assoc limits :items 10))))))
  (let [incomplete (ConstantInfo/mkThm (n/from-string "incomplete") (object-array [])
                                       fixtures/type' nil (object-array []))]
    (is (some? (error-data #(ci/full-equal-batch-bounded?
                             [[(theorem fixtures/body) (theorem fixtures/type')]
                              [incomplete incomplete]] limits)))))
  (doseq [batch ['() [[fixtures/body]] [[fixtures/body fixtures/body fixtures/body]]]]
    (is (some? (error-data #(ci/full-equal-batch-bounded? batch limits))))))

(deftest custom-persistent-vectors-are-rejected-without-count-or-nth
  (let [reads (atom 0)
        custom (proxy [clojure.lang.APersistentVector] []
                 (count [] (swap! reads inc) (throw (AssertionError. "custom count must not run")))
                 (nth [i] (swap! reads inc) (throw (AssertionError. "custom nth must not run"))))
        normal (theorem fixtures/body)]
    (is (some? (error-data #(ci/full-equal-batch-bounded? custom limits))))
    (is (some? (error-data #(ci/full-equal-batch-bounded? [custom] limits))))
    ;; Model an arbitrary Java client payload without invoking Expr's factory
    ;; on the custom collection. This is a refusal test, not admission evidence.
    (let [constant (Expr/mkConst (n/from-string "c") [] false)
          field (.getField Expr "o1")]
      (.setAccessible field true)
      (.set field constant custom)
      (is (some? (error-data #(ci/full-equal-bounded? (theorem constant) normal limits)))))
    (is (zero? @reads))))

(deftest custom-big-integer-payloads-are-rejected-before-size-methods
  (let [reads (atom 0)
        custom (proxy [BigInteger] ["0"]
                 (bitLength [] (swap! reads inc) (throw (AssertionError. "custom bitLength must not run"))))
        a (theorem (Expr/litNat custom))]
    (is (some? (error-data #(ci/full-equal-bounded? a a limits))))
    (is (zero? @reads))))

(deftest validation-heights-do-not-depend-on-primitive-box-identity
  (doseq [body [(Expr/bvar 2000) (Expr/fvar 3000) (Expr/mvar 4000)
                (Expr/proj (Name/mkNum Name/ANONYMOUS_NAME 666) 5000 fixtures/body)]]
    (is (ci/full-equal-bounded? (theorem body) (theorem body) limits)))
  (let [make (fn [] (env/mk-def (Name/mkNum Name/ANONYMOUS_NAME 777) [] fixtures/type'
                                (Expr/bvar 6000) :hints {:regular 4294967295N}))]
    (is (ci/full-equal-bounded? (make) (make) limits)))
  (let [make (fn [] (env/mk-induct (n/from-string "large") [] fixtures/type'
                                   :num-params 2000 :num-indices 3000 :num-nested 4000))]
    (is (ci/full-equal-bounded? (make) (make) limits))))

(deftest actual-expression-store-level-list-carriers-have-the-same-bounded-contract
  (let [name (n/from-string "c") level (l/param (n/from-string "u"))
        make (fn [values] (theorem (Expr/mkConst name values (boolean (seq values)))))]
    (doseq [[native normal] [[(java.util.Collections/emptyList) []]
                              [(java.util.Arrays/asList (object-array [level])) [level]]]]
      (is (ci/full-equal-bounded? (make native) (make normal) limits))
      (is (ci/full-equal-bounded? (make normal) (make native) limits))
      (is (= :items (:limit (error-data #(ci/full-equal-bounded? (make native) (make native)
                                                               (assoc limits :items 1)))))))
    (let [reads (atom 0)
          custom (proxy [java.util.AbstractList] []
                   (size [] (swap! reads inc) (throw (AssertionError. "custom size must not run")))
                   (get [_] (swap! reads inc) (throw (AssertionError. "custom get must not run"))))
          constant (Expr/mkConst name [] false)
          field (.getField Expr "o1")]
      (.setAccessible field true) (.set field constant custom)
      (is (some? (error-data #(ci/full-equal-bounded? (theorem constant) (theorem constant) limits))))
      (is (zero? @reads)))))
