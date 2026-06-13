(ns ansatz.attrs-test
  "Inheriting Lean's @[simp]/@[csimp]/@[extern] attributes (dumped by scripts/dump_attrs.lean as
   NDJSON, bundled as resources/ansatz/init-attrs.ndjson.gz) into Env extensions. load-init!
   auto-imports them, so the inherited set is ON BY DEFAULT (intersected with the store)."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.attrs :as attrs]))

(use-fixtures :once (fn [f] (a/load-init!) (binding [a/*verbose* false] (f))))

(deftest load-init-auto-inherits-lean-attributes
  ;; load-init! ran attrs/load-bundled-attrs!, so the env carries Lean's @[simp] corpus (intersected
  ;; with the bundled Init — a few hundred lemmas), not just the hand-curated core.
  (let [simp-set (env/get-extension (a/env) :simp-lemmas #{})]
    (is (contains? simp-set "Nat.add_zero") "a core @[simp] lemma is inherited")
    (is (contains? simp-set "Option.some.injEq") "and one NOT in the hand-curated default set")
    (is (> (count simp-set) 100) "the inherited set is the real Lean corpus, not the ~40 hand-curated")))

(deftest import-attrs-routing-and-purity
  ;; import-attrs is a PURE env→env function: present names land in the right extension (csimp/impl
  ;; as {from→to} maps, others as sets), absent names skip, and the base env is left untouched.
  (let [lines ["{\"kind\":\"simp\",\"name\":\"Nat.add_zero\"}"          ; present
               "{\"kind\":\"simp\",\"name\":\"Totally.Bogus.Absent\"}"  ; absent → skipped
               "{\"kind\":\"csimp\",\"name\":\"Nat.succ\",\"target\":\"Nat.add\"}" ; map kind: f→g
               "{\"kind\":\"extern\",\"name\":\"Nat.add\"}"]            ; set kind
        e0      (a/env)
        before  (count (env/get-extension e0 :simp-lemmas #{}))
        [e' stats] (attrs/import-attrs e0 lines)]
    (is (contains? (env/get-extension e' :simp-lemmas #{}) "Nat.add_zero") "present simp lemma lands")
    (is (= "Nat.add" (get (env/get-extension e' :csimp {}) "Nat.succ")) "csimp is a {from→to} map")
    (is (contains? (env/get-extension e' :extern #{}) "Nat.add") "extern is a name set")
    (is (pos? (:skipped stats)) "absent name skipped (graceful version-drift handling)")
    (is (= before (count (env/get-extension e0 :simp-lemmas #{})))
        "the base env is unchanged — import-attrs is pure; extensions branch with the immutable env")))

(deftest inherited-simp-set-is-on-by-default
  ;; Option.some.injEq : (some a = some b) = (a = b) is @[simp] in Lean but NOT hand-curated.
  ;; With the inherited set auto-loaded, (simp) closes the goal with NO explicit import — Lean's
  ;; @[simp] set is the default simp set. (Free a,b, so it's unreachable by the hand-curated core.)
  (binding [a/*verbose* false]
    (a/prove-theorem 'opt-inj-default '[a :- Nat, b :- Nat]
                     '(= Prop (= (Option Nat) (Option.some a) (Option.some b)) (= Nat a b)) '[(simp)])
    (is (some? (env/lookup (a/env) (name/from-string "opt-inj-default")))
        "(simp) closed it using the auto-inherited Option.some.injEq — Lean's @[simp] set is on by default")))
