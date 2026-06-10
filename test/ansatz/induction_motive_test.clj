(ns ansatz.induction-motive-test
  "basic/induction (and cases) must assemble a correct MOTIVE for non-trivial inductives. Two
   cases that previously built a degenerate/mistyped motive — kept as regressions:
     (1) MULTI-INDEX Prop inductives (List.Perm l1 l2): the major premise's type was abstracted by
         a sequential `abstract1` reduce, which does NOT shift loose bvars — so Perm l1 l2 collapsed
         to Perm #0 #0, a degenerate motive. Fixed by abstracting the indices SIMULTANEOUSLY
         (abstract-many) in both `induction` and `cases`.
     (2) NESTED-List scrutinee (blocks : List (List α)) with `flatten blocks` in the goal: the
         assembled recursor mistyped flatten's argument. Covered here by inducting on a List(List α)
         with flatten in a Prop motive.
   Each proof below goes through basic/induction (NOT a manual recursor) and is checked with the
   AUTHORITATIVE check-constant (env/verifies?)."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.extract :as extract]))

(defn- nm [s] (name/from-string s))
(def ^:private z lvl/zero) (def ^:private L1 (lvl/succ z)) (def ^:private type0 (e/sort' L1))
(defn- fvid [ps n] (some (fn [[id d]] (when (= n (:name d)) id)) (:lctx (proof/current-goal ps))))
(defn- listOf [a] (e/app (e/const' (nm "List") [z]) a))
(defn- nilOf [a] (e/app (e/const' (nm "List.nil") [z]) a))
(defn- permOf [a l r] (e/app* (e/const' (nm "List.Perm") [z]) a l r))
(defn- flattenOf [a ls] (e/app* (e/const' (nm "List.flatten") [z]) a ls))
(defn- natT [] (e/const' (nm "Nat") []))
(defn- lengthOf [a l] (e/app* (e/const' (nm "List.length") [z]) a l))
(defn- focus [ps gid] (assoc ps :goals [gid]))
(defn- ihs [cg] (filter (fn [[_ d]] (clojure.string/starts-with? (str (:name d)) "ih")) (:lctx cg)))
;; destructure (Eq.{1} ty X Y) → [ty X Y]
(defn- eq-parts [t] (let [[_ args] (e/get-app-fn-args t)] (when (= 3 (count args)) (vec args))))

(defn- once [f]
  (when-let [kenv @test-env/init-full-env] (reset! a/ansatz-env kenv))
  (f))
(clojure.test/use-fixtures :once once)
(defn- ready? [] (some? @test-env/init-full-env))

;; BUG #1 — multi-index Prop induction: prove  Perm l1 l2 → length l1 = length l2  via induction on p.
(defn- prove-perm-length []
  (let [A (e/fvar 1) l1 (e/fvar 2) l2 (e/fvar 3)
        goal (-> (e/app* (e/const' (nm "Eq") [L1]) (natT) (lengthOf A l1) (lengthOf A l2))
                 (#(e/forall' "p" (permOf A l1 l2) % :default))
                 (#(e/forall' "l2" (listOf A) (e/abstract1 % 3) :default))
                 (#(e/forall' "l1" (listOf A) (e/abstract1 % 2) :default))
                 (#(e/forall' "A" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["A" "l1" "l2" "p"])
        ps (basic/induction ps (fvid ps "p"))
        ps (reduce
            (fn [ps gid]
              (let [psg (focus ps gid)
                    cg (proof/current-goal psg)
                    ih-ids (mapv first (ihs cg))]
                (case (count ih-ids)
                  0 (basic/rfl psg)                                   ; nil + swap close by def-eq
                  1 (let [ihid (first ih-ids)
                          [ty X Y] (eq-parts (:type (second (first (filter #(= ihid (first %)) (:lctx cg))))))
                          succ (e/const' (nm "Nat.succ") [])]
                      (basic/exact psg (e/app* (e/const' (nm "congrArg") [L1 L1]) (natT) (natT) X Y succ (e/fvar ihid))))
                  2 (let [[p-id q-id] ih-ids
                          ihp-ty (:type (second (first (filter #(= p-id (first %)) (:lctx cg)))))
                          ihq-ty (:type (second (first (filter #(= q-id (first %)) (:lctx cg)))))
                          [_ a b] (eq-parts ihp-ty) [_ _ c] (eq-parts ihq-ty)]
                      (basic/exact psg (e/app* (e/const' (nm "Eq.trans") [L1]) (natT) a b c (e/fvar p-id) (e/fvar q-id)))))))
            ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

;; BUG #2 — nested-List scrutinee with flatten in a (Prop) motive: prove
;;   ∀ Y (blocks : List(List Y)), Perm (flatten blocks) (flatten blocks)  via induction on blocks.
(defn- prove-flatten-self-perm []
  (let [Y (e/fvar 1) blocks (e/fvar 2)
        goal (-> (permOf Y (flattenOf Y blocks) (flattenOf Y blocks))
                 (#(e/forall' "blocks" (listOf (listOf Y)) (e/abstract1 % 2) :default))
                 (#(e/forall' "Y" type0 (e/abstract1 % 1) :default)))
        [ps _] (proof/start-proof (a/env) goal)
        ps (basic/intros ps ["Y" "blocks"])
        ps (basic/induction ps (fvid ps "blocks"))
        ps (reduce (fn [ps gid]
                     (let [psg (focus ps gid)
                           Y' (e/fvar (fvid psg "Y"))
                           cg (proof/current-goal psg)
                           [_ lhs _] (eq-parts (:type cg))]   ; Perm Y LHS RHS — reuse parts shape
                       (basic/exact psg (e/app* (e/const' (nm "List.Perm.refl") [z]) Y' lhs))))
                   ps (vec (:goals ps)))]
    [goal (when (proof/solved? ps) (extract/extract ps))]))

(deftest induction-multi-index-perm-motive
  (when (ready?)
    (testing "induction on List.Perm l1 l2 builds a NON-degenerate motive (length_eq goes through)"
      (let [[g pf] (prove-perm-length)]
        (is (some? pf) "proof extracted")
        (is (and pf (kenv/verifies? (a/env) g pf)) "Perm l1 l2 → length l1 = length l2 (via basic/induction)")))))

(deftest induction-nested-list-flatten-motive
  (when (ready?)
    (testing "induction on List(List Y) with flatten in a Prop motive assembles correctly"
      (let [[g pf] (prove-flatten-self-perm)]
        (is (some? pf) "proof extracted")
        (is (and pf (kenv/verifies? (a/env) g pf)) "Perm (flatten blocks)(flatten blocks) (via basic/induction)")))))
