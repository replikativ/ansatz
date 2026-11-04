(ns ansatz.rewrite-projection-test
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta :as meta]
            [ansatz.meta.kabstract :as ka]))

(use-fixtures :once
  (fn [t]
    (let [saved @a/ansatz-env]
      (try
        (reset! a/ansatz-env @test-env/checked-bundled-init-env)
        (binding [*ns* (the-ns 'ansatz.rewrite-projection-test)]
          (a/structure RewriteOut [] (wv Nat) (ok Bool))
          (a/structure RewriteNested [] (out RewriteOut))
          (a/defn rewrite-out-f [n :- Nat] RewriteOut (RewriteOut.mk n true))
          (t))
        (finally (reset! a/ansatz-env saved))))))

(defn- verified? [nm]
  (let [ci (env/lookup (a/env) (name/from-string nm))]
    (and ci (env/verifies? (a/env) (.type ci) (.value ci)))))

(deftest rewrite-under-projections
  (a/theorem rewrite_function_projection [n :- Nat,
                                          h :- (= (rewrite-out-f n) (RewriteOut.mk 0 false))]
             (= (:wv (rewrite-out-f n)) 0)
             (rw [h]))
  (a/theorem rewrite_projection [x :- RewriteOut, h :- (= x (RewriteOut.mk 0 false))]
             (= (:wv x) 0)
             (rw [h]))
  (a/theorem rewrite_nested_projection [x :- RewriteNested,
                                        h :- (= x (RewriteNested.mk (RewriteOut.mk 0 false)))]
             (= (:wv (:out x)) 0)
             (rw [h]))
  (a/theorem rewrite_projection_local [x :- RewriteOut,
                                       h :- (= x (RewriteOut.mk 0 false)),
                                       hx :- (= (:wv x) 7)]
             (= 0 7)
             (rw [h] at hx)
             (exact hx))
  (a/theorem rewrite_function_projection_local [n :- Nat,
                                                h :- (= (rewrite-out-f n) (RewriteOut.mk 0 false)),
                                                hx :- (= (:wv (rewrite-out-f n)) 7)]
             (= 0 7)
             (rw [h] at hx)
             (exact hx))
  (doseq [nm ["rewrite_function_projection_local" "rewrite_function_projection" "rewrite_projection" "rewrite_nested_projection" "rewrite_projection_local"]]
    (is (verified? nm))))

(deftest rewrite-missing-pattern-fails
  (is (thrown-with-msg? clojure.lang.ExceptionInfo
                        #"Tactic `rewrite` failed: Did not find an occurrence of the pattern"
                        (a/theorem rewrite_missing [x :- RewriteOut,
                                                    h :- (= x (RewriteOut.mk 0 false))]
                                   (= Nat 0 0)
                                   (rw [h]))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo
                        #"Did not find an occurrence of the pattern"
                        (a/theorem rewrite_missing_local [x :- RewriteOut,
                                                          h :- (= x (RewriteOut.mk 0 false)),
                                                          hx :- (= Nat 0 0)]
                                   (= Nat 0 0)
                                   (rw [h] at hx))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo
                        #"Did not find an occurrence of the pattern"
                        (a/theorem rewrite_missing_quantified
                                   [h :- (forall [n :- Nat] (= (Nat.succ n) n))]
                                   (= Nat 0 0)
                                   (rw [h])))))

(deftest abstraction-traverses-all-expression-children
  (let [st (tc/mk-tc-state (a/env))
        p (e/lit-nat 9)
        n (e/const' (name/from-string "Nat") [])
        succ (e/const' (name/from-string "Nat.succ") [])
        add (e/const' (name/from-string "Nat.add") [])
        ctor (e/const' (name/from-string "RewriteOut.mk") [])
        flag (e/const' (name/from-string "Bool.true") [])
        eq (fn [a b] (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) n a b))
        cases [[(e/proj (name/from-string "RewriteOut") 0 (e/app* ctor p flag))
                (e/proj (name/from-string "RewriteOut") 0 (e/app* ctor (e/bvar 0) flag))]
               [(e/mdata {} (e/app succ p)) (e/mdata {} (e/app succ (e/bvar 0)))]
               [(e/let' "x" n p (e/app succ (e/bvar 0)))
                (e/let' "x" n (e/bvar 0) (e/app succ (e/bvar 0)))]
               [(e/lam "x" n p :default) (e/lam "x" n (e/bvar 1) :default)]
               [(e/forall' "x" n (eq p (e/bvar 0)) :default)
                (e/forall' "x" n (eq (e/bvar 1) (e/bvar 0)) :default)]]]
    (doseq [[input expected] cases]
      (is (= expected (ka/kabstract st input p))))
    (let [pair (e/app* add p p)]
      (is (= (e/app* add p (e/bvar 0)) (ka/kabstract st pair p {:occs {:pos [2]}})))
      (is (= (e/app* add (e/bvar 0) p) (ka/kabstract st pair p {:occs {:neg [2]}}))))))

(deftest excluded-occurrence-rolls-back-metavariables
  (let [st (tc/mk-tc-state (a/env))
        n (e/const' (name/from-string "Nat") [])
        succ (e/const' (name/from-string "Nat.succ") [])
        mctx (atom (meta/add-expr-mvar-decl meta/empty-context 100 n {}))
        add (e/const' (name/from-string "Nat.add") [])
        input (e/app* add (e/app succ (e/lit-nat 1)) (e/app succ (e/lit-nat 2)))
        output (ka/kabstract st input (e/app succ (e/mvar 100))
                             {:mctx mctx :occs {:pos [2]}})]
    (is (= (e/app* add (e/app succ (e/lit-nat 1)) (e/bvar 0)) output))
    (is (= (e/lit-nat 2) (meta/expr-assignment @mctx 100)))))

(deftest rewrite-selected-occurrences
  (a/theorem rewrite_second_occurrence [n :- Nat, m :- Nat, h :- (= n m), hm :- (= n m)]
             (= n n)
             (rewrite {:occs {:pos [2]}} [h])
             (exact hm))
  (is (verified? "rewrite_second_occurrence")))

(deftest mismatching-subterm-does-not-block-later-match
  (let [st (tc/mk-tc-state (a/env))
        succ (e/const' (name/from-string "Nat.succ") [])
        add (e/const' (name/from-string "Nat.add") [])
        first-term (e/app succ (e/lit-nat 1))
        pattern (e/app succ (e/lit-nat 2))]
    (is (= (e/app* add first-term (e/bvar 0))
           (ka/kabstract st (e/app* add first-term pattern) pattern)))))

(deftest rewrite-selected-occurrences-at-local
  (a/theorem rewrite_second_occurrence_local [n :- Nat, m :- Nat, h :- (= n m),
                                              hx :- (= n n)]
             (= n m)
             (rewrite {:occs {:pos [2]}} [h] at hx)
             (exact hx))
  (is (verified? "rewrite_second_occurrence_local")))

(deftest rewrite-rejects-unsupported-configuration
  (doseq [tactic '[(rw {:transparency :reducible} [h])
                   (rw {:transparency :instances} [h])
                   (rw {:instances true} [h])
                   (rw {:transparency :default} [h] at *)]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"rewrite: unsupported configuration option"
                          (a/prove-theorem 'rewrite_unsupported_configuration
                                           '[n :- Nat, m :- Nat, h :- (= n m)]
                                           '(= n m) [tactic])))))

(deftest ^:wip rewrite-default-keeps-ordinary-definitions-opaque
  ;; Lean Rewrite.Config defaults to .reducible; closed Meta defeq still unfolds this definition.
  (a/defn hidden-id [n :- Nat] Nat n)
  (is (thrown-with-msg? clojure.lang.ExceptionInfo
                        #"Did not find an occurrence of the pattern"
                        (a/theorem hidden_match
                                   [f :- (=> Nat Nat), n :- Nat,
                                    h :- (= (f (hidden-id n)) 7)]
                                   (= (f n) 7)
                                   (rw [h])))))
