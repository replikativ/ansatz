(ns ansatz.kernel.fvar-id-collision-test
  "Kernel caches are sound only if a free variable id names ONE local declaration for the
   life of a TypeChecker (Lean type_checker.h: \"free variables are globally unique with fixed
   types\"). Lean guarantees that with disjoint name generators (inductive.cpp's g_ind_fresh vs
   the checker's g_kernel_fresh). The inductive checker once numbered its locals with its own
   counter in the SAME id space as TypeChecker.freshId, so
   an id the checker used internally — for a binder while inferring a Pi — is handed out again
   for a different local. The infer-only cache then answers for the new local with the old
   local's type.

   Concretely, elimOnlyAtUniverseZero infers the sort of each constructor field. For
     StaleBox.mk : (f : (p : Prop) → p → p) → (T : Type) → (t : T) → StaleBox T
   inferring f's type caches `p ↦ Prop` under fvar id k+1; T then receives id k+1; inferring
   the sort of t's type `T` hits that entry and calls the data field `t` a proof — so the
   kernel generates a LARGE-eliminating recursor for a Prop whose constructor stores data,
   and False follows by proof irrelevance. Lean admits StaleBox.rec only into Prop.

   Fixed by giving the checker its own id range (TypeChecker.KERNEL_FRESH_BASE); AddInductive's
   LocalCtx numbers its locals below it."
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

(defn- box-decl
  "I : Type → Prop with one constructor of three fields. :stale puts f first (its binder id
   is then reused for T); :ctl puts f last (nothing is allocated after it)."
  [ind order]
  (let [I (e/const' (n ind) [])
        ctor-type (case order
                    :stale (e/forall-default
                            (n "f") f-type
                            (e/forall-default (n "T") type1
                                              (e/forall-default (n "t") (e/bvar 0) (e/app I (e/bvar 1)))))
                    :ctl (e/forall-default
                          (n "T") type1
                          (e/forall-default (n "t") (e/bvar 0)
                                            (e/forall-default (n "f") f-type (e/app I (e/bvar 2))))))]
    (env/mk-inductive-decl [] 0 false [[ind (e/forall-default (n "X") type1 prop)
                                        [[(str ind ".mk") ctor-type]]]])))

(defn- motive-sort [rec-type]
  (loop [t (e/forall-type rec-type)] (if (e/forall? t) (recur (e/forall-body t)) (e/sort-level t))))

(defn- expected-motive-sort [base ind order]
  (let [env (env/add-inductive base (box-decl ind order) 1000000)]
    (motive-sort (.type ^ansatz.kernel.ConstantInfo (env/lookup env (n (str ind ".rec")))))))

(deftest data-carrying-prop-eliminates-only-into-prop
  (let [base @test-env/bundled-init-env]
    (testing "control: field order without an internal binder before the data field"
      (is (= lvl/zero (expected-motive-sort base "CtlBox" :ctl))))
    (testing "a reused fvar id must not turn the data field t : T into a proof"
      (is (= lvl/zero (expected-motive-sort base "StaleBox" :stale))))))

(deftest stale-fvar-type-does-not-prove-false
  (let [base @test-env/bundled-init-env
        d (box-decl "StaleBox" :stale)
        [ind ctor ^ansatz.kernel.ConstantInfo rec] (env/inductive-decl-constants (env/add-inductive base d 1000000) d)
        rt (.type rec)
        ;; the same recursor, but eliminating into every universe
        large (e/forall' (e/forall-name rt)
                         (e/forall-default (n "X") type1
                                           (e/forall-default (n "t") (e/app (e/const' (n "StaleBox") []) (e/bvar 0))
                                                             (e/sort' (lvl/param (n "u")))))
                         (e/forall-body rt) (e/forall-info rt))
        tampered (env/mk-recursor (n "StaleBox.rec") [(n "u")] large
                                  :all [(n "StaleBox")] :num-params 0 :num-indices 1
                                  :num-motives 1 :num-minors 1 :rules (vec (.rules rec)) :k? false)
        admitted (try (env/check-inductive-bundle base (env/mk-inductive-bundle [] 0 false [ind] [ctor] [tampered]))
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
