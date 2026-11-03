(ns ansatz.tactic.apply-goals-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.inductive :as ind]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [ansatz.surface.elaborate :as elab]))

;; Lean pair: test/lean/apply_goals.lean (Lean 4 v4.33.1).
(defn- expr [form] (elab/elaborate @test-env/checked-bundled-init-env form))
(defn- with-local-head [type]
  (let [[ps _] (proof/start-proof @test-env/checked-bundled-init-env
                                  (e/forall' "f" type (expr 'True) :default))
        ps (basic/intro ps "f")
        id (ffirst (:lctx (proof/current-goal ps)))]
    [ps (e/fvar id)]))
(defn- vector-of-goals [ps]
  (mapv (fn [id] [id (proof/mvar-type ps id)
                  (name/->string (proof/mvar-user-name ps id))]) (:goals ps)))

(deftest dependent-witnesses-follow-proofs-in-stable-telescope-order
  (let [env (ind/define-inductive @test-env/checked-bundled-init-env "Pack" []
              '[[mk [ty Type x ty hx (= ty x x) ht True]]]
              :in 'Prop)
        [ps _] (proof/start-proof env (e/const' (name/from-string "Pack") []))
        head (e/const' (name/from-string "Pack.mk") [])
        start (:next-id ps)
        [ty x hx ht] (range start (+ start 4))
        expected {ty [ty (e/sort' (lvl/succ lvl/zero)) "ty"]
                  x [x (e/mvar ty) "x"]
                  hx [hx (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                                 (e/mvar ty) (e/mvar x) (e/mvar x)) "hx"]
                  ht [ht (expr 'True) "ht"]}]
    (doseq [[mode ids] [[:non-dependent-first [hx ht ty x]]
                        [:non-dependent-only [hx ht]]
                        [:all [ty x hx ht]]]]
      (is (= (mapv expected ids)
             (vector-of-goals (basic/apply-tac ps head {:new-goals mode})))))
    (let [ps (-> ps
                 (basic/apply-tac head)
                 (basic/exact (e/app* (e/const' (name/from-string "Eq.refl")
                                                [(lvl/succ lvl/zero)])
                                      (expr 'Nat) (e/lit-nat 0)))
                 (basic/exact (expr 'True.intro)))]
      (is (proof/solved? ps))
      (is (some? (extract/verify ps))))))

(deftest independent-prop-premises-retain-telescope-order
  (let [[ps head] (with-local-head (expr '(forall [ha :- True, hb :- False] True)))
        a (:next-id ps) b (inc a)]
    (is (= [[a (expr 'True) "ha"] [b (expr 'False) "hb"]]
           (vector-of-goals (basic/apply-tac ps head))))))

(deftest implicit-witness-visible-until-proof-determines-it
  (let [type (e/forall' "n" (expr 'Nat)
                        (e/forall' "h" (e/app* (e/const' (name/from-string "Eq")
                                                         [(lvl/succ lvl/zero)])
                                               (expr 'Nat) (e/bvar 0) (e/lit-nat 0))
                                   (expr 'True) :default) :implicit)
        [ps head] (with-local-head type)
        n (:next-id ps) h (inc n)
        ps (basic/apply-tac ps head)]
    (is (= [[h (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                       (expr 'Nat) (e/mvar n) (e/lit-nat 0)) "h"]
            [n (expr 'Nat) "n"]]
           (vector-of-goals ps)))
    (let [ps (basic/exact ps (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                                     (expr 'Nat) (e/lit-nat 0)))]
      (is (proof/solved? ps))
      (is (some? (extract/verify ps))))))

(deftest assigned-instances-do-not-become-goals
  (let [type (e/forall' "inst" (expr '(Inhabited Nat))
                        (e/forall' "h" (expr 'True) (expr 'True) :default)
                        :inst-implicit)
        [ps head] (with-local-head type)
        ps (basic/apply-tac ps head)
        ids (into {} (keep (fn [id]
                             (when-let [tag (proof/mvar-user-name ps id)]
                               [(name/->string tag) id])) (proof/mvar-ids ps)))]
    (is (proof/mvar-assigned? ps (ids "inst")))
    (is (= [[(ids "h") (expr 'True) "h"]] (vector-of-goals ps)))
    (is (some? (extract/verify (basic/exact ps (expr 'True.intro)))))))

(deftest head-expression-holes-are-appended-once
  (let [[ps _] (proof/start-proof @test-env/checked-bundled-init-env (expr 'True))
        [ps head] (proof/fresh-mvar ps (expr '(forall [h :- True] True)) {})
        ps (proof/set-mvar-user-name ps head (name/from-string "head"))
        arg (:next-id ps)
        ps (basic/apply-tac ps (e/mvar head))]
    (is (= [[arg (expr 'True) "[anonymous]"]
            [head (expr '(forall [h :- True] True)) "head"]]
           (vector-of-goals ps))))
  ;; A head hole may already be listed among the proof state's goals.
  (let [[ps _] (proof/start-proof @test-env/checked-bundled-init-env (expr 'True))
        [ps head] (proof/fresh-mvar ps (expr 'True) {})
        ps (basic/apply-tac ps (e/mvar head))]
    (is (= [head] (:goals ps)))))

(defn- scoped-tag [base]
  (name/mk-num (name/mk-str (name/mk-str (name/mk-str base "_@") "X") "_hyg") 42))

(deftest apply-preserves-structured-binder-tags
  ;; Lean counterparts: test/lean/apply_tags.lean.
  (let [main (name/mk-str (name/anonymous) "main")
        h (name/mk-str (name/anonymous) "h")]
    (doseq [[parent binder expected]
            (concat
             (for [component ["001" "9223372036854775808" "literal.dot"]
                   binder [component (name/mk-str (name/anonymous) component)]]
               [main binder (name/mk-str main component)])
             [[main (scoped-tag h) (name/mk-str main "h")]
              [(scoped-tag main) h (scoped-tag (name/mk-str main "h"))]
              [(scoped-tag main) (scoped-tag h) (scoped-tag (name/mk-str main "h"))]])]
      (let [type (e/forall' binder (expr 'True)
                            (e/forall' "hb" (expr 'True) (expr 'True) :default) :default)
            [ps head] (with-local-head type)
            ps (proof/set-mvar-user-name ps (:id (proof/current-goal ps)) parent)
            ps (basic/apply-tac ps head)
            [first-goal second-goal] (:goals ps)]
        (is (= expected (proof/mvar-user-name ps first-goal)))
        (is (= (if (= parent main) (name/mk-str main "hb")
                   (scoped-tag (name/mk-str main "hb")))
               (proof/mvar-user-name ps second-goal)))
        (is (some? (extract/verify
                    (-> ps (basic/exact (expr 'True.intro))
                        (basic/exact (expr 'True.intro))))))))))
