(ns ansatz.dependent-field-struct-test
  "Regression: noConfusion for dependent algebraic fields must be kernel-checked."
  (:require [ansatz.test-env :as test-env]
            [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.inductive :as ind]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]))

(def ^:private init-env test-env/checked-bundled-init-env)

(defn- with-init-env [f]
  (when-let [env @init-env]
    (reset! a/ansatz-env env)
    (f)))

(clojure.test/use-fixtures :once with-init-env)

(defn- lookup [s] (env/lookup (a/env) (name/from-string s)))

(deftest dependent-axiom-field-defines
  (testing "structure with a field type that applies an earlier field (associativity axiom)"
    (ind/define-inductive (a/env) "WSemigT" '[S Type]
      [['mk '[add (=> S S S)
              assoc (forall [a S b S c S]
                            (= S (add (add a b) c) (add a (add b c))))]]])
    (is (some? (lookup "WSemigT")) "inductive admitted")
    (is (some? (lookup "WSemigT.mk")) "constructor admitted")
    (is (some? (lookup "WSemigT.rec")) "recursor admitted")
    (doseq [suffix ["noConfusionType" "noConfusion" "mk.noConfusion"]]
      (is (some? (lookup (str "WSemigT." suffix)))
          "dependent-field noConfusion is generated and kernel-checked"))))

(deftest dependent-field-via-structure-macro
  (testing "the surface (a/structure …) macro handles a dependent commutativity axiom"
    (a/structure WMagmaT [S Type]
                 (op (=> S S S))
                 (comm (forall [a S b S] (= S (op a b) (op b a)))))
    (is (some? (lookup "WMagmaT")))
    (is (some? (lookup "WMagmaT.mk")))
    ;; projections still generate
    (is (some? (lookup "WMagmaT.op")))
    (is (some? (lookup "WMagmaT.comm")))))

(defn- result-type [s n]
  (nth (iterate e/forall-body (.type (lookup s))) n))

(deftest dependent-accessor-types-use-named-projections
  (a/structure DepAccessor [S Type]
               (value S) (witness (= S value value))
               (law (= (= S value value) witness witness)))
  (let [k #(e/const' (name/from-string %) [])
        self (e/bvar 0)
        param (e/bvar 1)
        value (e/app* (k "DepAccessor.value") param self)
        witness (e/app* (k "DepAccessor.witness") param self)
        witness-type (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                             param value value)]
    (is (= witness-type (result-type "DepAccessor.witness" 2)))
    (is (= (e/app* (e/const' (name/from-string "Eq") [lvl/zero]) witness-type witness witness)
           (result-type "DepAccessor.law" 2)))))

(deftest class-law-types-use-named-projections
  (a/class LawAccessor [S Type] (zero S) (law (= S zero zero)))
  (let [k #(e/const' (name/from-string %) [])
        param (e/bvar 1)
        zero (e/app* (k "LawAccessor.zero") param (e/bvar 0))]
    (is (= (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) param zero zero)
           (result-type "LawAccessor.law" 2)))))

(deftest accessor-types-preserve-dependent-parameters
  (a/structure ParamAccessor [S Type x S]
               (value S) (law (= S value x)))
  (let [k #(e/const' (name/from-string %) [])
        param (e/bvar 2)
        x (e/bvar 1)
        value (e/app* (k "ParamAccessor.value") param x (e/bvar 0))]
    (is (= (e/const' (name/from-string "ParamAccessor") [])
           (e/get-app-fn (e/forall-type
                          (nth (iterate e/forall-body (.type (lookup "ParamAccessor.value"))) 2)))))
    (is (= (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) param value x)
           (result-type "ParamAccessor.law" 3)))))

(deftest accessor-types-without-parameters
  (a/structure ClosedAccessor [] (value Nat) (law (= Nat value value)))
  (let [k #(e/const' (name/from-string %) [])
        value (e/app (k "ClosedAccessor.value") (e/bvar 0))]
    (is (= (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) (k "Nat") value value)
           (result-type "ClosedAccessor.law" 1)))))

(deftest inherited-law-types-use-named-subobject-projections
  (a/structure ParentAccessor [S Type] (zero S))
  (a/structure ChildAccessor [S Type] :extends (ParentAccessor S)
               (value S) (law (= S value zero)))
  (let [k #(e/const' (name/from-string %) [])
        param (e/bvar 1)
        self (e/bvar 0)
        parent (e/app* (k "ChildAccessor.toParentAccessor") param self)
        zero (e/app* (k "ParentAccessor.zero") param parent)
        value (e/app* (k "ChildAccessor.value") param self)]
    (is (= (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) param value zero)
           (result-type "ChildAccessor.law" 2)))))
