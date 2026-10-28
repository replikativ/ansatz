(ns ansatz.meta.match.matcher-app-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta.constructions.util :as u]
            [ansatz.meta.match.matcher-app :as matcher-app]))

(deftest matcher-add-arg-refines-dependent-type
  (let [saved @a/ansatz-env]
    (try
      (binding [a/*verbose* false] (a/load-init!))
      (a/define-verified 'transportProbe '[^Bool b] 'Nat
        '(match b [false 13] [true 21]))
      (let [environment (a/env)
            f (env/lookup! environment (name/from-string "transportProbe"))
            ctx (u/context environment)
            bool (u/const' "Bool" [])
            b (u/local-decl ctx "b" bool)
            body (e/instantiate1 (e/lam-body (.value f)) b)
            app (matcher-app/match-matcher-app? environment body)
            refl (u/app (u/const' "Eq.refl" [(lvl/succ lvl/zero)]) [bool b])
            transported (matcher-app/add-arg ctx app refl)
            term (matcher-app/to-expr transported)]
        (is (= 2 (count (:alternatives transported))))
        (is (tc/is-def-eq @ctx (u/infer-type ctx term) (u/const' "Nat" [])))
        (is (some? (env/check-constant environment
                                       (env/mk-def (name/from-string "transportProbe.checked") []
                                                   (e/forall' "b" bool (u/const' "Nat" []) :default)
                                                   (u/mk-lambda-fvars ctx [b] term))))))
      (finally (reset! a/ansatz-env saved)))))
