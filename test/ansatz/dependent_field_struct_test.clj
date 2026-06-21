(ns ansatz.dependent-field-struct-test
  "Regression: structures whose field types APPLY an earlier field — i.e. typeclass-style
   records carrying algebraic axioms like `add_assoc : ∀ a b c, add (add a b) c = …`.

   These define correctly: the inductive, constructors, recursor, casesOn, recOn are all
   kernel-checked. The only auxiliary that the current builder cannot derive for such a
   dependent field is noConfusion — it is warned-and-skipped (an auxiliary, not core), so
   the declaration still succeeds. This pins that behaviour so the typeclass front door
   (WSemiring etc.) stays open."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.inductive :as ind]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
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
    (f)))

(use-fixtures :once with-init-env)

(defn- lookup [s] (env/lookup (a/env) (name/from-string s)))

(deftest dependent-axiom-field-defines
  (testing "structure with a field type that applies an earlier field (associativity axiom)"
    ;; Both kernels admit the constructor type; only noConfusion is skipped.
    (ind/define-inductive (a/env) "WSemigT" '[S Type]
      [['mk '[add (=> S S S)
              assoc (forall [a S b S c S]
                            (= S (add (add a b) c) (add a (add b c))))]]])
    (is (some? (lookup "WSemigT")) "inductive admitted")
    (is (some? (lookup "WSemigT.mk")) "constructor admitted")
    (is (some? (lookup "WSemigT.rec")) "recursor admitted")
    ;; noConfusion is the only auxiliary the dependent-field builder cannot derive yet.
    (is (nil? (lookup "WSemigT.noConfusionType"))
        "noConfusion warned-and-skipped (auxiliary), declaration still succeeds")))

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
