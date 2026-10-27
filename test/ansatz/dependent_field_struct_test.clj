(ns ansatz.dependent-field-struct-test
  "Regression: noConfusion for dependent algebraic fields must be kernel-checked."
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
