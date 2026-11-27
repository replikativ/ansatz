(ns ansatz.sizeof-test
  "Lean's SizeOf construction (Meta/SizeOf.lean) for DSL inductives and structures.
   Lean parity: test/lean-parity/dsl/size_of.lean (observed with Lean v4.36.0)."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.test-env :as test-env]
            [ansatz.core :as a]
            [ansatz.inductive :as ind]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]))

(defn- with-init-env [f]
  (let [saved @a/ansatz-env]
    (try (reset! a/ansatz-env @test-env/bundled-init-env)
         (binding [*ns* (the-ns 'ansatz.sizeof-test) a/*verbose* false]
           (run! eval
                 '[(ansatz.core/inductive SzOpt [α Type] (none) (some [a α]))
                   (ansatz.core/inductive SzWrap [] (w [v (SzOpt Nat)]))
                   (ansatz.core/inductive SzTree [] (leaf) (node [l SzTree] [r SzTree] [k Nat]))
                   (ansatz.core/inductive SzFlag [] (mk [b Bool] [f (=> Nat Nat)] [g (=> Unit Nat)]))
                   (ansatz.core/structure SzPos [] (n Nat) (h (< 0 n)))])
           (f))
         (finally (reset! a/ansatz-env saved)))))

(use-fixtures :once with-init-env)

(defn- ci [n] (env/lookup (a/env) (name/from-string n)))
(defn- c [n] (e/const' (name/from-string n) []))
(def ^:private l1 (lvl/succ lvl/zero))
(defn- size-of [t inst x] (e/app* (e/const' (name/from-string "SizeOf.sizeOf") [l1]) t inst x))
(defn- infos [t] (loop [t t acc []] (if (e/forall? t) (recur (e/forall-body t) (conj acc (e/forall-info t))) acc)))
(defn- conclusion [t] (if (e/forall? t) (recur (e/forall-body t)) t))
(defn- summands
  "The summands of a left-nested `1 + a + b + …`."
  [x]
  (let [[h as] (e/get-app-fn-args x)]
    (if (and (e/const? h) (= "HAdd.hAdd" (str (e/const-name h))))
      (conj (summands (nth as 4)) (nth as 5))
      [x])))

(deftest applied-field-type-uses-synthesized-instance
  (testing "a parameter gets a local [SizeOf α] dictionary (Lean mkLocalInstances)"
    (is (= [:implicit :inst-implicit :default] (infos (.type (ci "SzOpt._sizeOf_1")))))
    (is (= [:default :inst-implicit] (infos (.type (ci "SzOpt._sizeOf_inst")))) "instance takes the parameter explicitly")
    (is (= [:implicit :inst-implicit :default] (infos (.type (ci "SzOpt.some.sizeOf_spec"))))))
  (testing "`SzWrap.w (v : SzOpt Nat)`: the spec is `1 + sizeOf v` at `SzOpt._sizeOf_inst Nat instSizeOfNat`"
    (let [rhs (nth (e/get-app-args (conclusion (.type (ci "SzWrap.w.sizeOf_spec")))) 2)
          [one sv] (summands rhs)
          [_ inst _] (e/get-app-args sv)]
      (is (= (e/lit-nat 1) one))
      (is (= (e/app* (c "SzOpt._sizeOf_inst") (c "Nat") (c "instSizeOfNat")) inst))))
  (testing "sizeOf (SzWrap.w (SzOpt.some 3)) = 5 in the kernel, as in Lean"
    (let [t (e/app (c "SzWrap.w") (e/app* (c "SzOpt.some") (c "Nat") (e/lit-nat 3)))]
      (is (tc/is-def-eq (tc/mk-tc-state (a/env)) (size-of (c "SzWrap") (c "SzWrap._sizeOf_inst") t) (e/lit-nat 5)))))
  (testing "the instances are registered and the specs are kernel-checked @[simp] theorems"
    (let [registered (set (map (comp str :name) (get (env/get-extension (a/env) :instances {}) (name/from-string "SizeOf"))))]
      (doseq [n ["SzOpt" "SzWrap" "SzTree" "SzFlag" "SzPos"]]
        (is (contains? registered (str n "._sizeOf_inst")) n)))
    (doseq [n ["SzOpt.some.sizeOf_spec" "SzWrap.w.sizeOf_spec" "SzTree.node.sizeOf_spec" "SzPos.mk.sizeOf_spec"]]
      (is (.isThm (ci n)) n)
      (is (env/verifies? (a/env) (.type (ci n)) (.value (ci n))) n)
      (is (contains? (env/get-extension (a/env) :simp-lemmas #{}) n) n))))

(deftest recursive-fields-and-ignored-fields
  (testing "`_sizeOf_1` adds the induction hypotheses (typed Nat) and `sizeOf k` for the Nat field"
    (let [v (.value (ci "SzTree._sizeOf_1"))
          [_ args] (e/get-app-fn-args (e/lam-body v))
          node-minor (nth args 2)
          binders (loop [x node-minor acc []] (if (e/lam? x) (recur (e/lam-body x) (conj acc (e/lam-type x))) acc))]
      (is (= [(c "Nat") (c "Nat")] (subvec binders 3)) "l_ih r_ih : Nat")
      (is (= 4 (count (summands (loop [x node-minor] (if (e/lam? x) (recur (e/lam-body x)) x))))))))
  (testing "the spec spells recursive fields as `sizeOf l` through the type's own instance"
    (let [rhs (nth (e/get-app-args (conclusion (.type (ci "SzTree.node.sizeOf_spec")))) 2)
          insts (mapv #(second (e/get-app-args %)) (rest (summands rhs)))]
      (is (= [(c "SzTree._sizeOf_inst") (c "SzTree._sizeOf_inst") (c "instSizeOfNat")] insts))))
  (testing "a higher-order field is ignored, a `Unit → _` field is not (Lean ignoreField)"
    (let [rhs (nth (e/get-app-args (conclusion (.type (ci "SzFlag.mk.sizeOf_spec")))) 2)]
      (is (= [(c "Bool") (e/arrow (c "Unit") (c "Nat"))]
             (mapv #(first (e/get-app-args %)) (rest (summands rhs)))))))
  (testing "a structure with a proof field gets the same declarations"
    (is (= 3 (count (summands (nth (e/get-app-args (conclusion (.type (ci "SzPos.mk.sizeOf_spec")))) 2))))
        "1 + sizeOf n + sizeOf h")))

(deftest indexed-family
  (let [out (ind/define-inductive (a/env) "SzVec" '[a Type]
              [['nil [] [0]] ['cons '[n Nat x a xs (SzVec a n)] ['(Nat.succ n)]]] :indices '[n Nat])]
    (reset! a/ansatz-env out)
    (a/wf-derive-sizeof! "SzVec")
    (testing "indices are implicit arguments of `_sizeOf_1` and arguments of the instance"
      (is (= [:implicit :inst-implicit :implicit :default] (infos (.type (ci "SzVec._sizeOf_1")))))
      (is (= 3 (count (infos (.type (ci "SzVec._sizeOf_inst")))))))
    (testing "the cons spec counts every field: 1 + sizeOf n + sizeOf x + sizeOf xs"
      (let [spec (ci "SzVec.cons.sizeOf_spec")]
        (is (= 4 (count (summands (nth (e/get-app-args (conclusion (.type spec))) 2)))))
        (is (env/verifies? (a/env) (.type spec) (.value spec)))))))

(deftest installation-is-atomic
  (let [out (ind/define-inductive (a/env) "SzAtomic" [] [['mk '[n Nat]]])]
    (reset! a/ansatz-env out)
    (with-redefs [ansatz.meta.constructions.size-of/mk-size-of-spec
                  (fn [& _] (throw (ex-info "spec failure" {})))]
      (a/wf-derive-sizeof! "SzAtomic"))
    (is (nil? (ci "SzAtomic._sizeOf_1")) "a failed spec leaves no size function")
    (is (nil? (ci "SzAtomic._sizeOf_inst")) "a failed spec leaves no instance")))

(deftest runtime-uses-the-dictionary
  (binding [*ns* (the-ns 'ansatz.sizeof-test) a/*verbose* false]
    (eval (list 'ansatz.core/defn 'sz-thirty-seven '[n :- Nat] 'Nat
                (list (symbol "@SizeOf.sizeOf") 'Nat '(SizeOf.mk Nat (fn [_ :- Nat] 37)) 'n)))
    (eval '(ansatz.core/defn sz-wrap [x :- SzWrap] Nat (sizeOf x)))
    (eval '(ansatz.core/defn mk-wrap [n :- Nat] SzWrap (SzWrap.w (SzOpt.some Nat n))))
    (eval '(ansatz.core/defn sz-nat [x :- Nat] Nat (sizeOf x))))
  (is (= 37 ((resolve 'ansatz.sizeof-test/sz-thirty-seven) 3)) "Lean: @SizeOf.sizeOf Nat ⟨fun _ => 37⟩ 3 = 37")
  (is (= 5 ((resolve 'ansatz.sizeof-test/sz-wrap) ((resolve 'ansatz.sizeof-test/mk-wrap) 3))))
  (is (= 4 ((resolve 'ansatz.sizeof-test/sz-nat) 4))))
