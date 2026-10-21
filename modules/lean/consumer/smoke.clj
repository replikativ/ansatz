(require '[ansatz.lean :as lean])
(import '[ansatz.kernel Name])
(assert (.isStr (lean/name "Test.42")))
(assert (.isNum (lean/name ["Test.with.dot" 42])))
(assert (= "#<Failure>"
           (let [error (try (lean/open {:provider (fn [_] {})})
                            (catch clojure.lang.ExceptionInfo cause cause))]
             (pr-str (:lean/failure (ex-data error))))))
(println :optional-clojure-jar-smoke-passed)
