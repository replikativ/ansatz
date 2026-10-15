(ns ansatz.load-export-test
  "`a/load-export!`: a lean4export NDJSON becomes the session env without a store —
   kernel-checked by default, and an export that does not check is refused."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]))

(deftest load-export-checks-and-installs
  (binding [a/*verbose* false]
    (testing "a well-typed export is checked and becomes the session env"
      (let [r (a/load-export! "test-data/Nat.add_succ.ndjson")]
        (is (= 32 (:declarations r)))
        (is (some? (env/lookup (a/env) (name/from-string "Nat.add_succ"))))))
    (testing "an export with an ill-typed declaration is refused, the session env is kept"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"does not check"
            (a/load-export! "test-data/arena/002_badDef.ndjson")))
      (is (some? (env/lookup (a/env) (name/from-string "Nat.add_succ")))))
    (testing "trust mode admits without re-checking"
      (is (= 1 (:declarations (a/load-export! "test-data/arena/002_badDef.ndjson" :verify? false)))))))
