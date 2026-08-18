(ns ansatz.tactic.tactic-constants-test
  "Store-completeness check for the REWRITING tactics — the sibling of
   `ansatz.tactic.omega-constants-test`, which covers only the constants omega names.

   That test would not have caught the gap this namespace exists for, because simp and
   grind do not name their lemmas in a Clojure table the way omega does: they inherit
   Lean's whole @[simp] corpus from `resources/ansatz/init-attrs.ndjson.gz` and
   `ansatz.attrs/import-attrs` INTERSECTS it with the loaded store, silently dropping every
   name the store does not carry. A truncated store therefore does not fail — it produces a
   simp set that quietly does less, and only goals nobody has a test for notice.

   What it cost: the store carried `Bool.and_eq_true`, `Bool.and_self`, `Bool.and_true`,
   `Bool.and_false` and NOTHING from the `or` half — no `Bool.or_eq_true`, no
   `Bool.or_self`, no `Bool.true_or`/`false_or`, no `Bool.or_eq_false_iff`. Since Clojure's
   `or` is the primitive every Boolean-returning predicate is built from, `(a && b) = true`
   split into a conjunction and `(a || b) = true` did not split at all: Boolean-returning
   functions were effectively unprovable. `simp.clj`'s own hand-curated `default-simp-lemmas`
   was in the same state — `Nat.ble_eq`, `ite_true`, `ite_false`, `dite_true`, `dite_false`,
   `Bool.true_or`, `Bool.or_true`, `Bool.false_or`, `Bool.or_false`, `Bool.not_false` all
   named a constant that was not there.

   So: assert what the TACTICS need, from both directions —
     1. every name simp's default set spells resolves;
     2. Lean's Boolean/decidable simp family survives the store intersection whole;
     3. the constants grind's Bool→Prop bridge builds its proof term out of resolve;
     4. Lean's @[simp] PRIORITIES come across, because two of the Bool lemmas are confluent
        only by virtue of being `@[simp low]`."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [ansatz.core :as a]
            [ansatz.attrs :as attrs]
            [ansatz.kernel.env :as env]))

;; ---------------------------------------------------------------------------
;; The Boolean / decidable-branching simp family
;; ---------------------------------------------------------------------------
;; This is the same rule scripts/init-store-roots.py uses to pick the roots — asserted here
;; from the other side, against the store that was actually built. KEEP/DROP must stay in
;; step with that script; a divergence shows up as a failure here, which is the point.

(def ^:private family-keep
  #"^Bool\.|decide|^Nat\.(ble_eq|blt_eq|beq_eq|beq_refl)$|^(beq_true|beq_false|heq_eq_eq)$|^(ite|dite|cond|if|dif)_|_(ite|dite|cond)_|^(left|right)_(eq|iff)_(ite|dite)_iff$|^apply_(ite|dite)$")

(def ^:private family-drop
  "Entries that reach outside the medium tier: the fixed-width integer and container
   bridges, and `Bool.sizeOf_eq_one`, which would drag in the `SizeOf` development ansatz
   deliberately ships its own copy of."
  #"toBitVec|toNat|toInt|toUInt|toISize|BitVec|UInt|ISize|Int8|Int16|Int32|Int64|USize|Float|^List\.|^Array\.|^Vector\.|^Option\.|^Std\.|^Nat\.decide_|sizeOf")

(defn- attrs-lines []
  (when-let [res (io/resource "ansatz/init-attrs.ndjson.gz")]
    (with-open [in (java.util.zip.GZIPInputStream. (.openStream res))]
      (str/split-lines (slurp in)))))

(defn- simp-entries
  "[name priority] for every @[simp] entry in the bundled Init attribute corpus. The corpus
   is dumped from the FULL Init, so it is also the oracle for what the store is missing."
  []
  (keep (fn [l]
          (when-let [[_ n] (re-find #"\"kind\":\"simp\",\"name\":\"([^\"]+)\"" l)]
            [n (some-> (second (re-find #"\"prio\":(\d+)" l)) parse-long)]))
        (attrs-lines)))

(defn- private-var [ns-sym sym]
  @(ns-resolve (do (require ns-sym) ns-sym) sym))

(deftest simp-default-lemma-set-resolves
  (testing "every lemma simp's default set names is actually in the bundled store"
    (binding [a/*verbose* false]
      (a/load-init!)
      (let [names (concat (private-var 'ansatz.tactic.simp 'default-simp-lemmas)
                          (private-var 'ansatz.tactic.simp 'simp-only-builtins))
            missing (into (sorted-set) (remove a/has-constant?) names)]
        (is (< 20 (count names)) "found simp's default lemma names")
        (is (empty? missing)
            (str "simp's default set names " (count missing) " constant(s) absent from the "
                 "bundled store: " (str/join ", " missing)
                 " — each one is a rewrite simp silently cannot do. scripts/init-store-roots.py "
                 "reads this very list (see simp_default_set_names), so the fix is either "
                 "re-running it + scripts/regen-bundled-store.sh, or correcting the spelling: "
                 "`eq_self_iff_true` was Mathlib's name for core's `eq_self` and resolved "
                 "against nothing at all."))))))

(deftest boolean-simp-family-survives-the-store-intersection
  (testing "Lean's Bool / decide / ite-dite @[simp] family is carried whole"
    (binding [a/*verbose* false]
      (a/load-init!)
      (let [family (into (sorted-set)
                         (comp (map first)
                               (filter #(re-find family-keep %))
                               (remove #(re-find family-drop %)))
                         (simp-entries))
            missing (into (sorted-set) (remove a/has-constant?) family)]
        (is (< 150 (count family))
            "found Lean's Boolean simp family in the bundled attribute corpus")
        (is (empty? missing)
            (str (count missing) " of Lean's " (count family) " Boolean/decidable @[simp] "
                 "lemmas do not resolve in the bundled store, so ansatz.attrs drops them and "
                 "simp/grind silently lose those rewrites: " (str/join ", " (take 25 missing))
                 " — re-run scripts/init-store-roots.py + scripts/regen-bundled-store.sh."))))))

(def ^:private bool-prop-bridge-constants
  "What `ansatz.tactic.grind/try-bool-eq-to-iff` builds its proof term out of, plus the
   lemmas the bridged goal is then decomposed with. A Bool goal `e = false` / `e₁ = e₂`
   carries no propositional structure at all; without these the whole Boolean simp set —
   every lemma of which is stated about `_ = true` — has nothing to attach to."
  ["Bool.coe_iff_coe" "Iff" "Iff.mp"
   "Bool.or_eq_true" "Bool.and_eq_true" "Bool.or_eq_false_iff" "Bool.and_eq_false_imp"
   "Bool.not_eq_true" "Bool.of_not_eq_true" "Bool.false_eq_true" "Bool.true_eq_false"
   "Bool.or_self" "Bool.and_self" "Bool.true_or" "Bool.false_or" "Bool.or_true"
   "Bool.or_false" "Bool.true_and" "Bool.false_and" "Bool.and_true" "Bool.and_false"
   "Bool.not_not" "Bool.not_or" "Bool.not_and"
   "Nat.blt_eq" "Nat.ble_eq" "Nat.beq_eq" "Nat.beq_refl" "Nat.lt_irrefl"
   "decide_eq_true_eq" "decide_eq_false_iff_not" "decide_true" "decide_false"
   "ite_self" "dite_eq_ite" "ite_true" "ite_false" "dite_true" "dite_false"])

(deftest bool-prop-bridge-constants-present
  (testing "the constants grind's Bool→Prop goal bridge needs"
    (binding [a/*verbose* false]
      (a/load-init!)
      (doseq [n bool-prop-bridge-constants]
        (is (a/has-constant? n)
            (str n " must be present — grind's Bool→Prop bridge emits it, or simp needs it "
                 "to decompose the bridged goal"))))))

(deftest simp-priorities-are-inherited
  (testing "Lean's @[simp low] priorities come across; without them simp oscillates"
    ;; `Bool.false_eq : (false = b) = (b = false)` and `Bool.true_eq : (true = b) = (b = true)`
    ;; rewrite each other's output. Lean marks both `@[simp low]` so that `Bool.false_eq_true`
    ;; and `Bool.true_eq_false` (default priority, both collapsing to `False`) fire first. At a
    ;; flat priority simp ping-pongs `(false = true)` ↔ `(true = false)` until it gives up, and
    ;; every `<bool expr> = false` goal dies there.
    (binding [a/*verbose* false]
      (a/load-init!)
      (let [prios (env/get-extension (a/env) :simp-priorities {})]
        (is (seq prios)
            "the bundled attribute corpus records no @[simp] priorities at all — regenerate it
             with scripts/regen-bundled-attrs.sh (scripts/dump_attrs.lean emits \"prio\")")
        (doseq [n ["Bool.false_eq" "Bool.true_eq"]]
          (is (< (get prios n Long/MAX_VALUE) attrs/default-simp-priority)
              (str n " must be inherited BELOW the default simp priority ("
                   attrs/default-simp-priority "); it is `@[simp low]` in Lean and only "
                   "confluent because of it")))))))

(deftest the-or-half-of-the-bool-simp-set-stays-shipped
  (testing "the exact asymmetry that made Boolean-returning functions unprovable"
    ;; Pinned by name: the store used to carry the `and` half of each of these pairs and not
    ;; the `or` half. Nothing about the pairing is enforced by the generated root rule, so
    ;; pin it here — this is the shape of the regression, not just its instance.
    (binding [a/*verbose* false]
      (a/load-init!)
      (doseq [[andy orry] [["Bool.and_eq_true" "Bool.or_eq_true"]
                           ["Bool.and_self"    "Bool.or_self"]
                           ["Bool.and_true"    "Bool.or_false"]
                           ["Bool.and_false"   "Bool.or_true"]
                           ["Bool.true_and"    "Bool.true_or"]
                           ["Bool.false_and"   "Bool.false_or"]
                           ["Nat.blt_eq"       "Nat.ble_eq"]]]
        (is (a/has-constant? andy) (str andy " must be present"))
        (is (a/has-constant? orry)
            (str orry " must be present — its partner " andy " is, and shipping only one "
                 "half of a Bool simp pair is exactly the bug this test exists for"))))))
