(ns ansatz.attrs-test
  "Inheriting Lean's @[simp]/@[csimp]/@[extern] attributes (dumped by scripts/dump_attrs.lean as
   NDJSON) into Env extensions. The Lean dump is exercised manually; here we test the IMPORT side
   deterministically with inline NDJSON lines — names present in the bundled Init load into the
   matching extension, absent names are skipped, and the original env is unchanged (branching)."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.attrs :as attrs]))

(use-fixtures :once (fn [f] (a/load-init!) (binding [a/*verbose* false] (f))))

(deftest import-attrs-populates-extensions-intersected-with-store
  (let [lines ["{\"kind\":\"simp\",\"name\":\"Nat.add_zero\"}"        ; present in Init
               "{\"kind\":\"simp\",\"name\":\"decide_true\"}"         ; present in Init
               "{\"kind\":\"simp\",\"name\":\"Totally.Bogus.Absent\"}" ; absent → skipped
               "{\"kind\":\"csimp\",\"name\":\"Nat.succ\",\"target\":\"Nat.add\"}" ; map kind: f→g
               "{\"kind\":\"extern\",\"name\":\"Nat.add\"}"]          ; set kind
        [e' stats] (attrs/import-attrs (a/env) lines)
        simp-set (env/get-extension e' :simp-lemmas #{})]
    (is (contains? simp-set "Nat.add_zero") "a real Lean @[simp] lemma landed in :simp-lemmas")
    (is (contains? simp-set "decide_true"))
    (is (= 2 (count simp-set)) "only the two present simp lemmas (absent one skipped)")
    (is (= "Nat.add" (get (env/get-extension e' :csimp {}) "Nat.succ"))
        "csimp is a {from → to} map carrying the replacement target")
    (is (contains? (env/get-extension e' :extern #{}) "Nat.add") "extern is a name set")
    (is (pos? (:skipped stats)) "the absent name was skipped (graceful version-drift handling)")
    (is (empty? (env/get-extension (a/env) :simp-lemmas #{}))
        "the ORIGINAL env is unchanged — extensions branch with the immutable env")))

(deftest inherited-simp-set-drives-a-rewrite-defaults-cannot
  ;; Option.some.injEq : (some a = some b) = (a = b) is @[simp] in Lean's Init but NOT in ansatz's
  ;; hand-curated default-simp-lemmas. Proves (simp) consults the inherited :simp-lemmas extension:
  ;; with free a,b the goal is unreachable by the defaults, but closes once the lemma is inherited.
  (binding [a/*verbose* false]
    (let [params '[a :- Nat, b :- Nat]
          goal   '(= Prop (= (Option Nat) (Option.some a) (Option.some b)) (= Nat a b))
          base   @a/ansatz-env]
      (try
        (is (thrown? Throwable (a/prove-theorem 'opt-inj-base params goal '[(simp)]))
            "defaults alone cannot close (some a = some b) = (a = b)")
        (reset! a/ansatz-env
                (first (attrs/import-attrs base ["{\"kind\":\"simp\",\"name\":\"Option.some.injEq\"}"])))
        (a/prove-theorem 'opt-inj-inherited params goal '[(simp)])
        (is (some? (env/lookup (a/env) (name/from-string "opt-inj-inherited")))
            "after inheriting Option.some.injEq, (simp) closes it — the inherited @[simp] set drives the rewrite")
        (finally (reset! a/ansatz-env base))))))
