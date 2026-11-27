(ns ansatz.binder-kinds-test
  "Binder kinds through the DSL telescope and index-to-parameter promotion (Lean
   Elab/MutualInductive.lean, Elab/Inductive.lean). Lean parity: test/lean-parity/dsl/binder_kinds.lean."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.test-env :as test-env]
            [ansatz.fixtures :as fixtures]
            [ansatz.core :as a]
            [ansatz.inductive :as ind]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]))

(defn- with-env [f]
  (reset! a/ansatz-env @test-env/bundled-init-env)
  (binding [a/*verbose* false *ns* (the-ns 'ansatz.binder-kinds-test)]
    (ind/define-inductive (a/env) "BkFam" ['^:implicit α 'Type '^:inst inst '(Inhabited α)]
      [['mk ['^:strict x 'α 'n 'Nat] '[n]]] :indices '[k Nat])
    (ind/define-inductive (a/env) "BkV" '[α Type]
      [['nil [] [0]] ['cons ['^:implicit n 'Nat 'x 'α 'xs '(BkV α n)] '[(Nat.succ n)]]]
      :indices '[k Nat])
    (a/derive-injectivity! "BkV")
    (f)))

(use-fixtures :once fixtures/isolated-session with-env)

(defn- infos [n]
  (loop [t (.type (env/lookup (a/env) (name/from-string n))) acc []]
    (if (e/forall? t) (recur (e/forall-body t) (conj acc (e/forall-info t))) acc)))

(deftest header-and-constructor-binders
  (testing "the type former keeps the header's kinds"
    (is (= [:implicit :inst-implicit :default] (infos "BkFam"))))
  (testing "constructors: explicit parameters implicit, instance kept, fields keep their kinds"
    (is (= [:implicit :inst-implicit :strict-implicit :default] (infos "BkFam.mk")))
    (is (= [:implicit :implicit :default :default] (infos "BkV.cons")))))

(deftest generated-api-binders
  (testing "recursor, casesOn, recOn: parameters and outer indices implicit"
    (is (= [:implicit :inst-implicit :implicit :default :implicit :default] (infos "BkFam.rec")))
    (is (= [:implicit :inst-implicit :implicit :implicit :default :default] (infos "BkFam.casesOn")))
    (is (= [:implicit :inst-implicit :implicit :implicit :default :default] (infos "BkFam.recOn")))
    (is (= [:implicit :implicit :implicit :default :default :default] (infos "BkV.casesOn"))))
  (testing "the minor premise shows each field's kind"
    (let [t (.type (env/lookup (a/env) (name/from-string "BkFam.casesOn")))
          minor (loop [t t k 5] (if (zero? k) (e/forall-type t) (recur (e/forall-body t) (dec k))))]
      (is (= [:strict-implicit :default] [(e/forall-info minor) (e/forall-info (e/forall-body minor))]))))
  (testing "injEq keeps the constructor's kinds, the new fields explicit"
    (is (= [:implicit :implicit :default :default :default :default] (infos "BkV.cons.injEq")))))

(deftest fixed-indices-become-parameters
  (testing "an index fixed in every constructor is promoted (Lean's Fix has one parameter)"
    (let [out (ind/define-inductive (a/env) "BkFix" [] [['wrap '[α Type a α] '[α]]] :indices '[β Type])]
      (is (= 1 (.numParams (env/lookup out (name/from-string "BkFix")))))
      (is (= [:implicit :implicit :default :default] (infos "BkFix.rec")))))
  (testing "with promotion off the field's universe is too big, as in Lean"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"rejected by the kernel"
                          (ind/define-inductive (a/env) "BkFix2" [] [['wrap '[α Type a α] '[α]]]
                            :indices '[β Type] :promote-indices? false))))
  (testing "promotion precedes universe inference (Lean's PI p h : Type, not Prop)"
    (let [out (ind/define-inductive (a/env) "BkPI" '[p Prop] [['mk '[h p] '[h]]] :indices '[i p])
          t (.type (env/lookup out (name/from-string "BkPI")))]
      (is (= 2 (.numParams (env/lookup out (name/from-string "BkPI")))))
      (is (= (e/sort' (ansatz.kernel.level/succ ansatz.kernel.level/zero))
             (loop [t t] (if (e/forall? t) (recur (e/forall-body t)) t))))))
  (testing "an index that varies is not promoted"
    (is (= 1 (.numParams (env/lookup (a/env) (name/from-string "BkV")))))))

(deftest surface-macro-carries-binder-metadata
  (binding [a/*verbose* false *ns* (the-ns 'ansatz.binder-kinds-test)]
    (eval '(ansatz.core/inductive BkBox [^:implicit α Type] (mk [^:implicit n Nat] [x α]))))
  (is (= [:implicit] (infos "BkBox")))
  (is (= [:implicit :implicit :default] (infos "BkBox.mk"))))
