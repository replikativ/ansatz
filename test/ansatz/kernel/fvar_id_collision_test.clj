(ns ansatz.kernel.fvar-id-collision-test
  "Kernel caches are sound only if a free variable id names ONE local declaration for the
   life of a TypeChecker (Lean type_checker.h: \"free variables are globally unique with fixed
   types\"). Lean guarantees that with disjoint name generators (inductive.cpp's g_ind_fresh vs
   the checker's g_kernel_fresh). InductiveChecker (and RawInductiveGenerator.propOnly) instead
   number their locals with their own counter in the SAME id space as TypeChecker.freshId, so
   an id the checker used internally — for a binder while inferring a Pi — is handed out again
   for a different local. The infer-only cache then answers for the new local with the old
   local's type.

   Concretely, elimOnlyAtUniverseZero infers the sort of each constructor field. For
     StaleBox.mk : (f : (p : Prop) → p → p) → (T : Type) → (t : T) → StaleBox T
   inferring f's type caches `p ↦ Prop` under fvar id k+1; T then receives id k+1; inferring
   the sort of t's type `T` hits that entry and calls the data field `t` a proof — so the
   kernel generates a LARGE-eliminating recursor for a Prop whose constructor stores data,
   and False follows by proof irrelevance. Lean admits StaleBox.rec only into Prop.

   Fixed by giving the checker its own id range (TypeChecker.KERNEL_FRESH_BASE)."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel TypeChecker]))

(defn- n [s] (name/from-string s))
(def ^:private prop (e/sort' lvl/zero))
(def ^:private type1 (e/sort' (lvl/succ lvl/zero)))
;; f : (p : Prop) → p → p — a Prop-valued field whose type binds a variable
(def ^:private f-type
  (e/forall-default (n "p") prop (e/forall-default (n "h") (e/bvar 0) (e/bvar 1))))

(defn- box-bundle
  "I : Type → Prop with one constructor of three fields. :stale puts f first (its binder id
   is then reused for T); :ctl puts f last (nothing is allocated after it)."
  [ind order]
  (let [I (e/const' (n ind) [])
        ind-ci (env/mk-induct (n ind) [] (e/forall-default (n "X") type1 prop)
                              :num-params 0 :num-indices 1 :ctors [(n (str ind ".mk"))])
        ctor-type (case order
                    :stale (e/forall-default
                            (n "f") f-type
                            (e/forall-default (n "T") type1
                                              (e/forall-default (n "t") (e/bvar 0) (e/app I (e/bvar 1)))))
                    :ctl (e/forall-default
                          (n "T") type1
                          (e/forall-default (n "t") (e/bvar 0)
                                            (e/forall-default (n "f") f-type (e/app I (e/bvar 2))))))]
    (env/mk-inductive-bundle [] 0 false [ind-ci]
                             [(env/mk-ctor (n (str ind ".mk")) [] ctor-type (n ind) 0 0 3)] [])))

(defn- motive-sort [rec-type]
  (loop [t (e/forall-type rec-type)] (if (e/forall? t) (recur (e/forall-body t)) (e/sort-level t))))

(defn- expected-motive-sort [base ind order]
  (motive-sort (TypeChecker/debugExpectedRecursorType base (box-bundle ind order) 0 1000000)))

(deftest data-carrying-prop-eliminates-only-into-prop
  (let [base @test-env/bundled-init-env]
    (testing "control: field order without an internal binder before the data field"
      (is (= lvl/zero (expected-motive-sort base "CtlBox" :ctl))))
    (testing "a reused fvar id must not turn the data field t : T into a proof"
      (is (= lvl/zero (expected-motive-sort base "StaleBox" :stale))))))

(deftest stale-fvar-type-does-not-prove-false
  (let [base @test-env/bundled-init-env
        b0 (box-bundle "StaleBox" :stale)
        rec-type (TypeChecker/debugExpectedRecursorType base b0 0 1000000)
        mk-rec (fn [rules]
                 (env/mk-recursor (n "StaleBox.rec") [(n "u")] rec-type
                                  :all [(n "StaleBox")] :num-params 0 :num-indices 1
                                  :num-motives 1 :num-minors 1 :rules rules :k? false))
        bundle-with (fn [rec] (env/mk-inductive-bundle [] 0 false (vec (.inductives b0)) (vec (.ctors b0)) [rec]))
        rules (vec (TypeChecker/generateExpectedRecursorRules base (bundle-with (mk-rec [])) 0 1000000))
        admitted (try (env/check-inductive-bundle base (bundle-with (mk-rec rules)))
                      (catch Throwable _ nil))]
    (testing "a large-eliminating StaleBox.rec is not admitted"
      (is (nil? admitted)))
    (when admitted
      (let [SB (e/const' (n "StaleBox") [])
            l1 (lvl/succ lvl/zero)
            motive (e/lam-default (n "X") type1 (e/lam-default (n "b") (e/app SB (e/bvar 0)) (e/bvar 1)))
            minor (e/lam-default (n "f") f-type
                                 (e/lam-default (n "T") type1 (e/lam-default (n "t") (e/bvar 0) (e/bvar 0))))
            get-t (fn [X b] (e/app* (e/const' (n "StaleBox.rec") [l1]) motive minor X b))
            idp (e/lam-default (n "p") prop (e/lam-default (n "h") (e/bvar 0) (e/bvar 0)))
            mk (e/const' (n "StaleBox.mk") [])
            b1 (e/app* mk idp prop (e/const' (n "True") []))
            b2 (e/app* mk idp prop (e/const' (n "False") []))
            ;; congrArg (get Prop) (rfl : b1 = b2) — b1 ≡ b2 by proof irrelevance
            bad (e/app* (e/const' (n "congrArg") [lvl/zero l1])
                        (e/app SB prop) prop b1 b2
                        (e/lam-default (n "b") (e/app SB prop) (get-t prop (e/bvar 0)))
                        (e/app* (e/const' (n "Eq.refl") [lvl/zero]) (e/app SB prop) b1))
            goal (e/app* (e/const' (n "Eq") [l1]) prop (e/const' (n "True") []) (e/const' (n "False") []))]
        (testing "True = False is not provable from it"
          (is (not (env/verifies? admitted goal bad))))))))
