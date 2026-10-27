(ns ansatz.tactic.simp-let-test
  "Rewrite substitution under lets; Lean reference: test/lean/simp_let.lean."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.tactic.simp :as simp]))

(deftest rewrite-substitution-traverses-let-types-values-and-bodies
  (let [nat (e/const' (name/from-string "Nat") [])
        seven (e/lit-nat 7)
        ;; Parameters A, x; let T := A; let y : A := x; let z : T := y; x.
        rhs (e/let' "T" (e/sort' (lvl/succ lvl/zero)) (e/bvar 1)
                    (e/let' "y" (e/bvar 2) (e/bvar 1)
                            (e/let' "z" (e/bvar 1) (e/bvar 0) (e/bvar 3))))
        result (#'simp/apply-subst rhs {1 nat 0 seven} 2)]
    (is (= (e/instantiate rhs [nat seven]) result))
    (is (not (e/has-loose-bvars? result)))
    (is (identical? result (#'simp/apply-subst result {0 seven} 1)))))

(def ^:private frame-defs
  '[(ansatz.core/structure FrameState [] (local Bool) (kept Bool) (extra Bool))
    (ansatz.core/defn nested-predicate [b :- Bool] Bool
      (let [f (fn [x :- Bool] x), y (f b)] y))
    (ansatz.core/defn frame-step [s :- FrameState, id :- Nat] FrameState
      (FrameState.mk (:local s) (:kept s) false))
    (ansatz.core/theorem local-frame [s :- FrameState, id :- Nat]
                         (= (:local (frame-step s id)) (:local s)) (rfl))
    (ansatz.core/theorem kept-preserved [s :- FrameState, id :- Nat]
                         (=> (= (:kept s) true) (= (:kept (frame-step s id)) true))
                         (intro h) (exact h))
    (ansatz.core/defn flat-inv [s :- FrameState] Bool
      (Bool.and (nested-predicate (:local s))
                (Bool.and (nested-predicate (:local s))
                          (Bool.and (nested-predicate (:local s))
                                    (Bool.and (nested-predicate (:local s))
                                              (Bool.and (nested-predicate (:local s))
                                                        (Bool.and (nested-predicate (:local s))
                                                                  (Bool.and (nested-predicate (:local s)) (:kept s)))))))))])

(deftest simp-all-preserves-flat-invariant-with-nested-lets
  (let [saved-env @a/ansatz-env
        saved-index @a/ansatz-instance-index]
    (try
      (a/load-init!)
      (binding [a/*verbose* false
                *ns* (the-ns 'ansatz.tactic.simp-let-test)]
        (run! eval frame-defs)
        (a/prove-theorem 'projection-frame
                         '[s :- FrameState, t :- FrameState, h :- (= s t)]
                         '(= (:local s) (:local t))
                         '[(simp only [h])])
        (a/prove-theorem 'flat-preserved '[s :- FrameState, id :- Nat]
                         '(=> (= (flat-inv s) true)
                              (= (flat-inv (frame-step s id)) true))
                         '[(intro hs)
                           (simp_all [flat-inv local-frame kept-preserved])])
        (doseq [n ["projection-frame" "flat-preserved"]]
          (let [ci (env/lookup (a/env) (name/from-string n))]
            (is (some? ci))
            (is (env/verifies? (a/env) (.type ci) (.value ci))))))
      (finally
        (reset! a/ansatz-env saved-env)
        (reset! a/ansatz-instance-index saved-index)))))
