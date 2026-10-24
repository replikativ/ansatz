(ns ansatz.constant-info-comparison-test
  "Already-materialized CI models; no kernel acceptance or store hydration claim."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.kernel.constant-info :as ci]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as l]
            [ansatz.kernel.name :as n])
  (:import [ansatz.kernel ConstantInfo Expr Name]))
(defn name' [s] (n/from-string s))
(def type' (e/sort' (l/succ l/zero)))
(def body (e/sort' l/zero))
(defn variants []
  [(env/mk-axiom (name' "A") [] type')
   (env/mk-def (name' "d") [] type' body :hints {:regular 0})
   (env/mk-thm (name' "t") [] type' body)
   (env/mk-opaque (name' "o") [] type' body)
   (env/mk-quot (name' "q") [] type' :type)
   (env/mk-induct (name' "I") [] type' :ctors [(name' "I.mk")])
   (env/mk-ctor (name' "I.mk") [] type' (name' "I") 0 0 0)
   (env/mk-recursor (name' "I.rec") [] type' :all [(name' "I")]
                    :rules [(env/mk-recursor-rule (name' "I.mk") 0 body)])])
(deftest all-eight-variants-compare-by-full-structural-evidence
  (doseq [[left right] (map vector (variants) (variants))]
    (is (not (identical? left right))))
  (doseq [[left right] (map vector (variants) (variants))]
    (is (ci/full-equal? left right)))
  (let [a (env/mk-def (name' "d") [] type' body :hints {:regular 0})
        b (env/mk-def (name' "d") [] type' body :hints :abbrev)
        c (env/mk-def (name' "d") [] type' body :hints {:regular 4294967295N})]
    (is (not (ci/full-equal? a b)))
    (is (not (ci/full-equal? a c))))
  (is (not (ci/full-equal? (env/mk-axiom (name' "A") [] type')
                           (env/mk-axiom (name' "A") [] type' :unsafe? true))))
  (is (not (ci/full-equal? (env/mk-thm (name' "t") [] type' body)
                           (env/mk-thm (name' "t") [] type' type'))))
  (is (not (ci/full-equal? (env/mk-recursor (name' "I.rec") [] type' :num-motives 1)
                           (env/mk-recursor (name' "I.rec") [] type' :num-motives 2)))))
(deftest omitted-proof-bodies-never-certify-exact-overlap
  (let [empty (ConstantInfo/mkThm (name' "t") (object-array []) type' nil (object-array []))
        complete (env/mk-thm (name' "t") [] type' body)]
    (is (false? (ci/complete? empty)))
    (is (ci/complete? complete))
    (is (thrown? clojure.lang.ExceptionInfo (ci/full-equal? empty empty)))
    (is (thrown? clojure.lang.ExceptionInfo (ci/full-equal? empty complete)))))

(deftest omitted-package-metadata-and-recursor-rhs-are-not-complete
  (let [no-universes (ConstantInfo/mkAxiom (name' "a") nil type' false)
        no-all (env/mk-thm (name' "t") [] type' body)
        no-rhs (env/mk-recursor (name' "I.rec") [] type'
                                :rules [(env/mk-recursor-rule (name' "I.mk") 0 nil)])
        no-rules (env/mk-recursor (name' "I.rec") [] type')
        no-ctors (env/mk-induct (name' "I") [] type')]
    (set! (.-all ^ConstantInfo no-all) nil)
    (set! (.-rules ^ConstantInfo no-rules) nil)
    (set! (.-ctors ^ConstantInfo no-ctors) nil)
    (doseq [incomplete [no-universes no-all no-rhs no-rules no-ctors]]
      (is (false? (ci/complete? incomplete)))
      (is (thrown? clojure.lang.ExceptionInfo (ci/full-equal? incomplete incomplete))))))

(deftest unsupported-ci-tag-is-never-complete
  ;; Defensive API test: normal factories never issue this unsupported variant.
  (let [^java.lang.reflect.Constructor constructor
        (.getDeclaredConstructor ConstantInfo
                                 (into-array Class [Byte/TYPE Name (class (object-array [])) Expr]))]
    (.setAccessible constructor true)
    (let [unsupported (.newInstance constructor
                                    (object-array [(byte 99) (name' "unknown") (object-array []) type']))]
      (is (false? (ci/complete? unsupported)))
      (is (thrown? clojure.lang.ExceptionInfo (ci/full-equal? unsupported unsupported))))))
