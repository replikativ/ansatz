(ns ansatz.kernel.cases-on-test
  "Initial JVM-generator fixtures; native819816 full-shape oracles are separate.
   Families below are actually generated and checked by the source kernel."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.kernel.cases-on :as cases]
            [ansatz.kernel.constant-info :as ci]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as l])
  (:import [ansatz.kernel Env Name Expr ConstantInfo TypeChecker Reducer
            RawInductiveGenerator RawInductiveGenerator$Source
            RawInductiveGenerator$Type RawInductiveGenerator$Constructor]))

(defn n [text] (Name/fromString text))
(def type0 (e/sort' (l/succ l/zero)))
(defn c [text] (e/const' (n text) []))
(defn parameter [id text type] {:id id :name (n text) :type type})
(defn pi [locals body]
  (reduce (fn [body {:keys [id name type]}]
            (e/forall' name type (e/abstract1 body id) :default)) body (rseq (vec locals))))
(defn family [^Env env levels np types]
  (.env (RawInductiveGenerator/generate
          env (RawInductiveGenerator$Source.
                (into-array Name levels) np
                (into-array RawInductiveGenerator$Type
                  (for [[name type constructors] types]
                    (RawInductiveGenerator$Type.
                      (n name) type
                      (into-array RawInductiveGenerator$Constructor
                        (for [[name type] constructors]
                          (RawInductiveGenerator$Constructor. (n name) type)))))) false)
          (long 1000000))))
(defn enum-env []
  (family (Env.) [] 0
          [["CaseColour" type0 [["CaseColour.red" (c "CaseColour")]
                                 ["CaseColour.blue" (c "CaseColour")]]]]))
(defn punit-env []
  (let [u (n "u") level (l/param u)]
    (family (Env.) [u] 0
            [["PUnit" (e/sort' level)
              [["PUnit.unit" (e/const' (n "PUnit") [level])]]]])))
(defn nat-env [env]
  (family env [] 0
          [["Nat" type0 [["Nat.zero" (c "Nat")]
                          ["Nat.succ" (pi [(parameter 0 "n" (c "Nat"))] (c "Nat"))]]]]))
(defn checked! [^Env env text]
  (let [name (n text) ^ConstantInfo generated (cases/make-declaration env name)
        ^ConstantInfo recursor (.lookup env (Name/mkStr name "rec"))
        next (TypeChecker/checkConstant env generated)]
    (is (nil? (.lookup env (.name generated))))
    (is (identical? generated (.lookup next (.name generated))))
    (is (= (vec (.levelParams recursor)) (vec (.levelParams generated))))
    (is (= ConstantInfo/REDUCIBILITY_ABBREV (.getHintsCode generated)))
    (is (= [(Name/mkStr name "casesOn")] (vec (.all generated))))
    (is (zero? (.safety generated)))
    next))

(deftest enum-definition-checks-and-reduces-both-branches
  (let [base (enum-env)
        ^ConstantInfo recursor (.lookup base (n "CaseColour.rec"))
        before (ci/full-shape recursor)
        base (reduce (fn [env name]
                       (TypeChecker/checkConstant env
                         (ConstantInfo/mkAxiom (n name) (object-array []) (e/sort' l/zero) false)))
                     base ["P" "Q"])
        loaded (checked! base "CaseColour")
        motive (e/lam (n "x") (c "CaseColour") (e/sort' l/zero) :default)]
    (doseq [[constructor expected] [["red" "P"] ["blue" "Q"]]]
      (let [call (e/app* (e/const' (n "CaseColour.casesOn") [(l/succ l/zero)])
                        motive (c (str "CaseColour." constructor)) (c "P") (c "Q"))]
        (is (= (e/sort' l/zero) (.whnf (Reducer. loaded) (.inferType (TypeChecker. loaded) call))))
        (is (= (c expected) (.whnf (Reducer. loaded) call)))))
    (is (= before (ci/full-shape recursor)))))

(deftest polymorphic-structure-and-box-definitions-check
  (let [u (n "u") level (l/param u) sort (e/sort' (l/succ level))
        alpha (e/fvar 0) value (e/fvar 1)
        a (parameter 0 "alpha" sort)
        b (parameter 1 "value" alpha)
        env (family (Env.) [u] 1
                    [["CaseBox" (pi [a] sort)
                      [["CaseBox.wrap" (pi [a b] (e/app (e/const' (n "CaseBox") [level]) alpha))]]]])]
    (checked! env "CaseBox"))
  (let [base (nat-env (Env.))
        fields [(parameter 0 "left" (c "Nat")) (parameter 1 "right" (c "Nat"))]
        env (family base [] 0 [["CasePair" type0 [["CasePair.mk" (pi fields (c "CasePair"))]]]])]
    (checked! env "CasePair")))

(deftest indexed-and-mutual-definitions-check
  (let [base (nat-env (punit-env))
        u (n "u") level (l/param u) sort (e/sort' (l/succ level))
        alpha (e/fvar 0) index (e/fvar 1)
        a (parameter 0 "alpha" sort) i (parameter 1 "index" (c "Nat"))
        item (parameter 2 "head" alpha)
        sized (fn [idx] (e/app* (e/const' (n "CaseSized") [level]) alpha idx))
        tail (parameter 3 "tail" (sized index))
        env (family base [u] 1
                    [["CaseSized" (pi [a i] sort)
                      [["CaseSized.nil" (pi [a] (sized (c "Nat.zero")))]
                       ["CaseSized.cons" (pi [a i item tail] (sized (e/app (c "Nat.succ") index)))]]]])]
    (checked! env "CaseSized"))
  (let [base (nat-env (punit-env))
        env (family base [] 0
                    [["CasePing" type0
                      [["CasePing.stop" (pi [(parameter 0 "n" (c "Nat"))] (c "CasePing"))]
                       ["CasePing.next" (pi [(parameter 0 "p" (c "CasePong"))] (c "CasePing"))]]]
                     ["CasePong" type0
                      [["CasePong.next" (pi [(parameter 0 "p" (c "CasePing"))] (c "CasePong"))]]]])]
    (checked! env "CasePing")
    (checked! env "CasePong")))

(deftest invalid-inputs-and-resource-limits-fail-without-admission
  (let [env (enum-env)]
    (doseq [[name expected] [["Missing" :cases-on/unknown-constant]
                             ["CaseColour.red" :cases-on/not-inductive]]]
      (is (= expected (:type (ex-data (try (cases/make-declaration env (n name))
                                          (catch clojure.lang.ExceptionInfo cause cause)))))))
    (doseq [options [{:max-work 1} {:max-locals 1} {:max-work 0} {:unknown 1}]]
      (is (thrown? clojure.lang.ExceptionInfo (cases/make-declaration env (n "CaseColour") options))))
    (is (nil? (.lookup env (n "CaseColour.casesOn"))))))

(deftest shared-open-dag-transforms-are-bounded-and-preserve-sharing
  ;; A naive recursive abstract1 expands this graph exponentially. The private
  ;; algorithm visits each identity/depth pair once and preserves child sharing.
  (doseq [[operation leaf argument]
          [[:abstract (e/fvar 7) 7] [:instantiate (e/bvar 0) (e/fvar 7)]]]
    (let [dag (nth (iterate #(e/app % %) leaf) 28)
          remaining (volatile! 100)
          result (#'cases/rewrite dag operation argument remaining)]
      (is (pos? @remaining))
      (is (identical? (e/app-fn result) (e/app-arg result)))
      (is (thrown? clojure.lang.ExceptionInfo
                   (#'cases/rewrite dag operation argument (volatile! 5))))))
  (let [leaf (e/fvar 7)
        body (e/forall' (n "x") type0 (e/app leaf (e/bvar 0)) :implicit)
        actual (#'cases/rewrite body :abstract 7 (volatile! 100))]
    (is (= (e/abstract1 body 7) actual))))

(deftest consumed-name-level-and-binder-bounds-precede-kernel-lookups
  (let [calls (atom 0)
        env (.withExternalLookup (Env.) (fn [_] (swap! calls inc) nil) 0)
        deep-name (nth (iterate #(Name/mkStr % "segment") Name/ANONYMOUS_NAME) 257)]
    (is (= :cases-on/depth-limit
           (:type (ex-data (try (cases/make-declaration env deep-name)
                               (catch clojure.lang.ExceptionInfo failure failure))))))
    (is (zero? @calls)))
  (doseq [expression [(e/sort' (nth (iterate l/succ l/zero) 257))
                      (nth (iterate #(e/forall' (n "x") type0 % :default) type0) 257)]]
    (is (= :cases-on/depth-limit
           (:type (ex-data (try (#'cases/preflight-expression! expression (volatile! 100000))
                               (catch clojure.lang.ExceptionInfo failure failure)))))))
  (is (= :cases-on/open-expression
         (:type (ex-data (try (#'cases/preflight-expression! (e/sort' (l/mvar 7)) (volatile! 100))
                             (catch clojure.lang.ExceptionInfo failure failure))))))
  (is (= :cases-on/work-limit
         (:type (ex-data (try (#'cases/bounded-name! (n "a-long-name-segment") (volatile! 5))
                             (catch clojure.lang.ExceptionInfo failure failure))))))
  (is (thrown? clojure.lang.ExceptionInfo
               (#'cases/bounded-levels! (lazy-seq (throw (Exception. "must not force"))) (volatile! 100)))))

(deftest functional-recursion-keeps-the-constructor-field-but-drops-its-induction-hypothesis
  (let [base (nat-env (Env.))
        recursive-field (e/forall' (n "index") (c "Nat") (c "CaseTree") :implicit)
        env (family base [] 0
                    [["CaseTree" type0
                      [["CaseTree.leaf" (c "CaseTree")]
                       ["CaseTree.node" (pi [(parameter 0 "children" recursive-field)] (c "CaseTree"))]]]])]
    (checked! env "CaseTree")))

(deftest authentic-expression-store-level-carriers-are-bounded-without-custom-list-callbacks
  (doseq [values [(java.util.Collections/emptyList)
                  (java.util.Arrays/asList (object-array [(l/succ l/zero)]))]]
    (is (nil? (#'cases/bounded-levels! values (volatile! 100)))))
  (let [custom (proxy [java.util.AbstractList] []
                 (size [] (throw (Exception. "custom size must not execute")))
                 (get [_] (throw (Exception. "custom get must not execute"))))]
    (is (= :cases-on/malformed-levels
           (:type (ex-data (try (#'cases/bounded-levels! custom (volatile! 100))
                               (catch clojure.lang.ExceptionInfo failure failure))))))))
