(ns ansatz.attrs-test
  "Inheriting Lean's @[simp]/@[csimp]/@[extern] attributes (dumped by scripts/dump_attrs.lean as
   NDJSON) into Env extensions. The Lean dump is exercised manually; here we test the IMPORT side
   deterministically with inline NDJSON lines — names present in the bundled Init load into the
   matching extension, absent names are skipped, and the original env is unchanged (branching)."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.attrs :as attrs]))

(use-fixtures :once (fn [f] (a/load-init!) (binding [a/*verbose* false] (f))))

(deftest import-attrs-populates-extensions-intersected-with-store
  (let [lines ["{\"kind\":\"simp\",\"name\":\"Nat.add_zero\"}"        ; present in Init
               "{\"kind\":\"simp\",\"name\":\"decide_true\"}"         ; present in Init
               "{\"kind\":\"simp\",\"name\":\"Totally.Bogus.Absent\"}" ; absent → skipped
               "{\"kind\":\"csimp\",\"name\":\"Nat.add_zero\"}"]      ; routes to :csimp
        [e' stats] (attrs/import-attrs (a/env) lines)
        simp-set (env/get-extension e' :simp-lemmas #{})]
    (is (contains? simp-set "Nat.add_zero") "a real Lean @[simp] lemma landed in :simp-lemmas")
    (is (contains? simp-set "decide_true"))
    (is (= 2 (count simp-set)) "only the two present simp lemmas (absent one skipped)")
    (is (contains? (env/get-extension e' :csimp #{}) "Nat.add_zero") "csimp routes to its own extension")
    (is (pos? (:skipped stats)) "the absent name was skipped (graceful version-drift handling)")
    (is (empty? (env/get-extension (a/env) :simp-lemmas #{}))
        "the ORIGINAL env is unchanged — extensions branch with the immutable env")))
