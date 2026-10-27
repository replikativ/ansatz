(ns ansatz.surface.lean-matchers-test
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.config :as config]
            [ansatz.codegen :as codegen]
            [ansatz.inductive :as ind]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta.match.matcher-info :as mi]
            [ansatz.tactic.instance :as instance]))

(def base (delay (binding [a/*verbose* false] (a/load-init!))))
(def string-env
  (delay
    (with-open [in (java.util.zip.GZIPInputStream.
                    (java.io.FileInputStream. "test-data/kernel-reference/matcher-values.ndjson.gz"))]
      (parser/with-parser-state
        (parser/parse-ndjson-string (slurp in))
        (fn [parsed]
          ;; The declaration export does not include Lean's instance registry.
          (instance/add-instance (:env (replay/replay (:decls parsed) :stop-on-error? true))
                                 (name/from-string "instDecidableEqString")))))))
(use-fixtures :each
  (fn [f]
    (let [saved @a/ansatz-env]
      (try
        (reset! a/ansatz-env @base)
        (binding [a/*verbose* false config/*lean-matchers* true] (f))
        (finally (reset! a/ansatz-env saved))))))

(defn- decl [n] (env/lookup (a/env) (name/from-string n)))

(deftest option-off-retains-direct-recursor-bodies
  (binding [config/*lean-matchers* false]
    (let [f (a/define-verified 'matcher-off '[^Bool b] 'Nat '(match b [false 13] [true 21]))]
      (is (= 13 (f false)))
      (is (= 21 (f true)))
      (is (nil? (decl "matcher-off.match_1"))))))

(deftest generated-boolean-matcher-is-installed-with-its-definition
  (let [f (a/define-verified 'matcher-bool '[^Bool b] 'Nat '(match b [false 13] [true 21]))
        ci (decl "matcher-bool.match_1")]
    (is (= 13 (f false)))
    (is (= 21 (f true)))
    (is (some? ci))
    (is (some? (mi/get-matcher-info-core? (a/env) "matcher-bool.match_1")))
    (is (= "matcher-bool.match_1"
           (str (e/const-name (e/get-app-fn (e/lam-body (.value (decl "matcher-bool"))))))))))

(deftest inferred-return-types-preserve-the-inference-pass-environment
  (let [f (a/define-verified 'matcher-inferred '[^Bool b] '_ '(match b [false 3] [true 4]))]
    (is (= 3 (f false)))
    (is (= 4 (f true)))
    (is (some? (decl "matcher-inferred.match_1")))))

(deftest codegen-recognizes-registered-matchers-without-a-name-or-hint-convention
  (a/define-verified 'matcher-for-metadata '[^Bool b] 'Nat '(match b [false 13] [true 21]))
  (let [original (decl "matcher-for-metadata.match_1")
        n (name/from-string "registeredMatcher")
        ci (env/mk-def n (vec (.levelParams original)) (.type original) (.value original) :hints {:regular 1})
        out (-> (env/check-constant (a/env) ci)
                (mi/add-matcher-info n (mi/get-matcher-info-core? (a/env) "matcher-for-metadata.match_1")))
        bool (e/const' (name/from-string "Bool") [])
        nat (e/const' (name/from-string "Nat") [])
        unit (e/const' (name/from-string "Unit") [])
        term (e/lam "b" bool
                    (e/app* (e/const' n [(lvl/succ lvl/zero)])
                            (e/lam "_" bool nat :default) (e/bvar 0)
                            (e/lam "_" unit (e/lit-nat 13) :default)
                            (e/lam "_" unit (e/lit-nat 21) :default)) :default)
        f (eval (codegen/ansatz->clj out term []))]
    (is (= 13 (f false)))
    (is (= 21 (f true)))))

(deftest nested-patterns-bind-the-produced-locals
  (let [f (a/define-verified 'matcher-nested '[^{:- (List Nat)} xs] 'Nat
                             '(match xs [nil 0] [(cons x nil) x] [(cons x (cons y ys)) y]))]
    (is (= 0 (f nil)))
    (is (= 4 (f '(4))))
    (is (= 9 (f '(4 9 12))))))

(deftest literal-values-and-wildcards-compile-to-executable-code
  (let [f (a/define-verified 'matcher-literal '[^Nat n] 'Nat
                             '(match n [0 10] [1 20] [k (+ k 2)]))]
    (is (= 10 (f 0)))
    (is (= 20 (f 1)))
    (is (= 7 (f 5)))))

(deftest string-values-use-decidable-equality-and-a-wildcard-fallback
  ;; String.decEq is not in the medium bundle; use its checked Lean-exported closure.
  (reset! a/ansatz-env @string-env)
  (let [f (a/define-verified 'matcher-string '[^String s] 'Nat
                             '(match s ["yes" 1] ["no" 2] [_ 0]))]
    (is (= 1 (f "yes")))
    (is (= 2 (f "no")))
    (is (= 0 (f "other")))))

(deftest product-patterns-pass-both-generated-fields-to-the-alternative
  (let [f (a/define-verified 'matcher-product '[^{:- (Prod Nat Nat)} p] 'Nat
                             '(match p [(Prod.mk x y) (+ x y)]))]
    (is (= 13 (f [4 9])))))

(deftest nested-match-expressions-share-the-returned-auxiliary-environment
  (let [f (a/define-verified 'matcher-branches '[^Bool b ^Nat n] 'Nat
                             '(match b
                                [false (match n [Nat.zero 5] [(Nat.succ k) k])]
                                [true (match n [Nat.zero 7] [(Nat.succ k) (+ k 1)])]))]
    (is (= 5 (f false 0)))
    (is (= 3 (f false 4)))
    (is (= 7 (f true 0)))
    (is (= 4 (f true 4)))
    (doseq [i [1 2 3]]
      (is (some? (decl (str "matcher-branches.match_" i)))))))

(deftest multiple-discriminants-follow-row-order
  (let [f (a/define-verified 'matcher-pair '[^Nat a ^Nat b] 'Nat
                             '(match [a b]
                                [[0 _] 100]
                                [[(Nat.succ n) 0] n]
                                [[(Nat.succ n) (Nat.succ m)] (+ n m)]))]
    (is (= 100 (f 0 3)))
    (is (= 3 (f 4 0)))
    (is (= 5 (f 4 3)))))

(deftest overlapping-constructor-alternatives-use-the-first-match
  (let [f (a/define-verified 'matcher-overlap '[^Nat n] 'Nat
                             '(match n [(Nat.succ Nat.zero) 10] [(Nat.succ k) k] [Nat.zero 20]))]
    (is (= 20 (f 0)))
    (is (= 10 (f 1)))
    (is (= 3 (f 4)))
    (is (= [[0 1]] (:overlaps (mi/get-matcher-info-core? (a/env) "matcher-overlap.match_1"))))))

(deftest enum-cases-and-catchalls-use-the-generated-cases-on
  (reset! a/ansatz-env (ind/define-inductive (a/env) "MatcherEnum" []
                                            [['red []] ['green []] ['blue []]]))
  (let [f (a/define-verified 'matcher-enum '[^{:- MatcherEnum} x] 'Nat
                             '(match x [red 7] [green 8] [_ 9]))]
    (is (= 7 (f nil)))
    (is (= 8 (f 1)))
    (is (= 9 (f 2)))))

(deftest indexed-family-patterns-generalize-the-index-discriminant
  (reset! a/ansatz-env
          (ind/define-inductive (a/env) "MatcherVec" '[a Type]
                                [['nil [] [0]] ['cons '[n Nat x a xs (MatcherVec a n)] ['(Nat.succ n)]]]
                                :indices '[n Nat]))
  (let [f (a/define-verified 'matcher-vector '[^Nat n ^{:- (MatcherVec Nat n)} v] 'Nat
                             '(match v [nil 0] [(cons k x xs) x]))
        info (mi/get-matcher-info-core? (a/env) "matcher-vector.match_1")]
    (is (= 2 (:num-discrs info)))
    (is (= 0 (f 0 nil)))
    (is (= 17 (f 1 [0 17 nil])))))

(deftest recursive-definition-continues-to-use-the-existing-path
  (let [f (a/define-verified 'matcher-recursive '[^Nat n] 'Nat
                             '(match n [Nat.zero 0] [(Nat.succ k) (+ (matcher-recursive k) 1)]))]
    (is (= 7 (f 7)))
    (is (nil? (mi/get-matcher-info-core? (a/env) "matcher-recursive.match_1")))))

(deftest missing-and-redundant-alternatives-fail-before-global-installation
  (let [before (a/env)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"non-exhaustive"
                          (a/define-verified 'matcher-incomplete '[^Bool b] 'Nat '(match b [false 10]))))
    (is (identical? before (a/env)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"redundant"
                          (a/define-verified 'matcher-redundant '[^Bool b] 'Nat '(match b [_ 10] [true 20]))))
    (is (identical? before (a/env)))))


(deftest dependent-boolean-hypotheses-become-matcher-discriminants
  (a/define-verified 'matcher-dependent-bool '[^Bool b ^{:- (Eq b b)} h]
                     '(Eq b b) '(match b [false h] [true h]))
  (let [ci (decl "matcher-dependent-bool")
        bool (e/const' (name/from-string "Bool") [])]
    (is (= 2 (:num-discrs (mi/get-matcher-info-core? (a/env) "matcher-dependent-bool.match_1"))))
    (doseq [ctor ["Bool.false" "Bool.true"]]
      (let [b (e/const' (name/from-string ctor) [])
            h (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)]) bool b)]
        (is (tc/is-def-eq (tc/mk-tc-state (a/env)) (e/app* (.value ci) b h) h))))))

(deftest dependent-natural-hypotheses-are-typed-at-the-constructor-pattern
  (a/define-verified 'matcher-dependent-nat '[^Nat n ^{:- (Eq n n)} h]
                     '(Eq n n) '(match n [Nat.zero h] [(Nat.succ k) h]))
  (let [ci (decl "matcher-dependent-nat")
        nat (e/const' (name/from-string "Nat") [])]
    (is (= 2 (:num-discrs (mi/get-matcher-info-core? (a/env) "matcher-dependent-nat.match_1"))))
    (doseq [n [0 7]]
      (let [n (e/lit-nat n)
            h (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)]) nat n)]
        (is (tc/is-def-eq (tc/mk-tc-state (a/env)) (e/app* (.value ci) n h) h))))))

(deftest fixed-successor-indices-realize-missing-constructor-no-confusion
  ;; Start with the plain load-init! fixture, without construction prewarming.
  (is (nil? (decl "Nat.succ.noConfusion")))
  (reset! a/ansatz-env
          (ind/define-inductive (a/env) "ProbeVec" '[a Type]
                                [['nil [] [0]] ['cons '[n Nat x a xs (ProbeVec a n)] ['(Nat.succ n)]]]
                                :indices '[n Nat]))
  (let [f (a/define-verified 'matcher-fixed-vector '[^Nat n ^{:- (ProbeVec Nat (Nat.succ n))} v]
                             'Nat '(match v [(cons k x xs) x]))]
    (is (some? (decl "Nat.succ.noConfusion")))
    (is (= 17 (f 0 [0 17 nil])))
    (is (= 23 (f 1 [1 23 [0 17 nil]])))))

(deftest dependent-local-generalization-follows-transitive-hypothesis-dependencies
  (a/define-verified 'matcher-dependent-chain
                     '[^Bool b ^{:- (Eq b b)} h ^{:- (Eq h h)} p]
                     '(Eq h h) '(match b [false p] [true p]))
  (let [ci (decl "matcher-dependent-chain")
        b (e/const' (name/from-string "Bool.false") [])
        bool (e/const' (name/from-string "Bool") [])
        eq (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) bool b b)
        h (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)]) bool b)
        p (e/app* (e/const' (name/from-string "Eq.refl") [lvl/zero]) eq h)]
    (is (= 3 (:num-discrs (mi/get-matcher-info-core? (a/env) "matcher-dependent-chain.match_1"))))
    (is (tc/is-def-eq (tc/mk-tc-state (a/env)) (e/app* (.value ci) b h p) p))))

(deftest explicit-pattern-bindings-shadow-generalized-hypotheses
  (a/define-verified 'matcher-pattern-shadow '[^Nat n ^{:- (Eq n n)} h]
                     'Nat '(match n [Nat.zero 13] [(Nat.succ h) h]))
  (let [ci (decl "matcher-pattern-shadow")
        nat (e/const' (name/from-string "Nat") [])]
    (doseq [[n expected] [[0 13] [7 6]]]
      (let [n (e/lit-nat n)
            h (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)]) nat n)]
        (is (tc/is-def-eq (tc/mk-tc-state (a/env))
                         (e/app* (.value ci) n h) (e/lit-nat expected)))))))

(deftest matcher-environments-preserve-typed-proof-local-lets
  (let [f (a/define-verified 'matcher-proof-lets '[^Bool b ^Nat n] 'Nat
                             '(let [x Nat (match b [false n] [true (+ n 1)])]
                                (let [p (Eq x x) (Eq.refl x)]
                                  (let [q (Eq p p) (Eq.refl p)] x))))]
    (is (= 7 (f false 7)))
    (is (= 8 (f true 7)))
    (is (some? (decl "matcher-proof-lets.match_1")))))

(deftest matcher-return-annotations-elaborate-as-types
  (a/define-verified 'matcher-proof-return '[^Bool b ^Nat n] '(= n n)
                     '(match b [false (Eq.refl n)] [true (Eq.refl n)]))
  (let [ci (decl "matcher-proof-return")
        nat (e/const' (name/from-string "Nat") [])
        n (e/lit-nat 7)
        h (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)]) nat n)]
    (doseq [ctor ["Bool.false" "Bool.true"]]
      (is (tc/is-def-eq (tc/mk-tc-state (a/env))
                       (e/app* (.value ci) (e/const' (name/from-string ctor) []) n) h)))))
