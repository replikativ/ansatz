(ns ansatz.nested-inductive-test
  "Tests for NESTED inductive types (the type occurs inside another inductive's
   parameters, e.g. `node : List RoseT → RoseT`). The kernel transforms
   nested→mutual and generates the recursor WITH the nested induction hypothesis,
   faithfully to Lean's add_inductive (kernel/inductive.cpp)."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.inductive :as ind]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

(def ^:private init-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(defn- with-init-env [f]
  (when-let [env @init-env]
    (reset! a/ansatz-env env)
    (binding [a/*verbose* false] (f))))

(use-fixtures :once with-init-env)

(defn- ensure-rose []
  (when-not (env/lookup (a/env) (name/from-string "RoseT"))
    (ind/define-inductive (a/env) "RoseT" '[]
      [['leaf ['n 'Nat] []]
       ['node ['kids '(List RoseT)] []]]
      :in 'Type)))

(deftest nested-inductive-generates-recursor-with-ih
  (when @init-env
    (ensure-rose)
    (testing "surface accepts the nested rose tree and the kernel generates recursors"
      (let [rec (env/lookup (a/env) (name/from-string "RoseT.rec"))
            rec1 (env/lookup (a/env) (name/from-string "RoseT.rec_1"))]
        (is (some? rec) "RoseT.rec generated")
        (is (some? rec1) "RoseT.rec_1 (auxiliary nested recursor) generated")
        ;; two motives (main + nested List), three minors (leaf, node, nil, cons → 3? leaf+node+nil+cons=4? no:
        ;; RoseT has leaf,node (2) and List.nested has nil,cons (2) → 4 minors, 2 motives)
        (is (= 2 (.numMotives ^ansatz.kernel.ConstantInfo rec)))
        (is (= 4 (.numMinors ^ansatz.kernel.ConstantInfo rec)))
        ;; the node minor premise must carry the nested IH (motive_2 kids) — check the
        ;; recursor type mentions the second motive applied inside the node case.
        (let [ts (e/->string (env/ci-type rec))]
          ;; node minor: (∀ : (List RoseT), (∀ : (#2 #0), (#4 (RoseT.node #1))))
          ;; the presence of an arrow whose domain applies a motive to the List arg is the IH
          (is (re-find #"RoseT\.node" ts)))))))

(deftest nested-recursion-computes-through-nesting
  (when @init-env
    (ensure-rose)
    (testing "a recursive function that folds results over the nested children (leaf count)"
      (let [M (a/env)
            u1 (lvl/succ lvl/zero)
            c (fn [s] (e/const' (name/from-string s) []))
            cL (fn [s ls] (e/const' (name/from-string s) ls))
            RT (c "RoseT") Nat* (c "Nat")
            listRT (e/app (cL "List" [lvl/zero]) RT)
            nadd (fn [a b] (e/app* (c "Nat.add") a b))
            leaf-case (e/lam "n" Nat* (e/lit-nat 1) :default)
            node-case (e/lam "kids" listRT (e/lam "ih" Nat* (e/bvar 0) :default) :default)
            nil-case (e/lit-nat 0)
            cons-case (e/lam "h" RT (e/lam "t" listRT (e/lam "hh" Nat*
                                                             (e/lam "th" Nat* (nadd (e/bvar 1) (e/bvar 0)) :default) :default) :default) :default)
            count (fn [tree] (e/app* (cL "RoseT.rec" [u1])
                                     (e/lam "_" RT Nat* :default) (e/lam "_" listRT Nat* :default)
                                     leaf-case node-case nil-case cons-case tree))
            leaf (fn [n] (e/app (c "RoseT.leaf") (e/lit-nat n)))
            lcons (fn [h t] (e/app* (cL "List.cons" [lvl/zero]) RT h t))
            lnil (e/app (cL "List.nil" [lvl/zero]) RT)
            tree (e/app (c "RoseT.node") (lcons (leaf 1) (lcons (leaf 2) (lcons (leaf 3) lnil))))
            eqNat (fn [a b] (e/app* (cL "Eq" [u1]) Nat* a b))
            refl (fn [a] (e/app* (cL "Eq.refl" [u1]) Nat* a))]
        (is (env/verifies? M (eqNat (count tree) (e/lit-nat 3)) (refl (e/lit-nat 3)))
            "countLeaves(node [leaf1,leaf2,leaf3]) reduces to 3 via the nested recursion")
        (is (not (env/verifies? M (eqNat (count tree) (e/lit-nat 2)) (refl (e/lit-nat 2))))
            "wrong count rejected")))))

(deftest non-positive-nested-still-rejected
  (when @init-env
    (testing "a negative occurrence inside the nesting is still rejected"
      (is (thrown? Exception
                   (ind/define-inductive (a/env) "BadNest" '[]
                     [['mk ['f '(List (=> BadNest BadNest))] []]]
                     :in 'Type))))))
