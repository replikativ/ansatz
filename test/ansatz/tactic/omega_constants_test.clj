(ns ansatz.tactic.omega-constants-test
  "Store-completeness check for the omega tactic.

   `ansatz.tactic.omega-proof` names every lemma it can emit — most of them in one
   table (`omega-names`), a few inline as `(name/from-string \"…\")`. A name that does
   not resolve in the environment is a silent capability hole: the proof term
   referencing it is built and then rejected — or, more often, the whole branch is
   swallowed by a `try` and omega merely reports that it could not derive a
   contradiction. Nothing else in the suite notices, because the affected goals are
   exactly the ones nobody has a passing test for.

   So: assert that EVERY referenced name resolves in the environment ansatz actually
   ships (`test-env/bundled-init-env` — resources/ansatz/init-medium.ndjson.gz, the
   dependency closure of scripts/init-store-roots.txt). There is no allow-list. If a
   name does not resolve, either add it to the root manifest and regenerate the store,
   or — as was the case for five of them — the name is a Mathlib spelling or a typo
   and the reference is what needs fixing."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.tactic.omega-proof]))

(defn- table-names
  "Constant names in `omega-proof`'s `omega-names` table."
  []
  (into #{} (map (comp name/->string val))
        @(ns-resolve 'ansatz.tactic.omega-proof 'omega-names)))

(defn- inline-names
  "Constant names spelled inline in omega_proof.clj as (name/from-string \"…\").
   Read from source: they are just as load-bearing as the table entries, and
   `Nat.div_mul_cancel` (the Nat divisibility fact) is only referenced that way."
  []
  (if-let [src (io/resource "ansatz/tactic/omega_proof.clj")]
    (into #{} (map second) (re-seq #"name/from-string \"([^\"]+)\"" (slurp src)))
    #{}))

(defn- referenced-names [] (into (table-names) (inline-names)))

(deftest omega-names-resolve-in-bundled-init
  (testing "every constant omega can emit resolves — no exceptions"
    (let [e @test-env/bundled-init-env
          referenced (referenced-names)
          resolves? (fn [n] (some? (env/lookup e (name/from-string n))))
          missing (into (sorted-set) (remove resolves?) referenced)]
      (is (< 100 (count referenced))
          "found the constant references to check (both the table and the inline literals)")
      (is (empty? missing)
          (str "omega references " (count missing) " constant(s) absent from the bundled "
               "store: " (str/join ", " missing)
               " — either the store lost a declaration (add the root to "
               "scripts/init-store-roots.txt and re-run scripts/regen-bundled-store.sh), "
               "or the reference is misspelled. Do NOT re-introduce an allow-list: every "
               "entry on the old one was a real, silently-dead capability.")))))

(deftest omega-names-that-were-wrong-stay-fixed
  (testing "the five names that never existed in Lean core are not referenced again"
    ;; `not_and_or`, `not_imp` and `iff_iff_and_or_not_and_not` are MATHLIB spellings;
    ;; `Int.ofNat.eq_def` names an equation lemma for a CONSTRUCTOR, which cannot exist;
    ;; `Lean.Omega.Coeffs.bmod_coeffs` puts `bmod_coeffs` in the wrong namespace (it is
    ;; `Lean.Omega.bmod_coeffs`, which is the name `Lean.Omega.bmod_sat`'s own conclusion
    ;; uses — getting it wrong is what kept hard-equality elimination dead).
    (let [referenced (referenced-names)]
      (doseq [bad ["not_and_or" "not_imp" "iff_iff_and_or_not_and_not"
                   "Int.ofNat.eq_def" "Lean.Omega.Coeffs.bmod_coeffs"]]
        (is (not (contains? referenced bad))
            (str bad " is not a Lean core constant — see scripts/init-store-roots.txt "
                 "for the name to use instead"))))))

(deftest bmod-and-div-bound-constants-present
  (testing "the constants hard-equality elimination and Int division bounds need"
    (let [e @test-env/bundled-init-env]
      (doseq [n [;; bmod / hard-equality elimination
                 "Lean.Omega.bmod_sat" "Lean.Omega.bmod_coeffs"
                 "Lean.Omega.bmod_div_term" "Lean.Omega.IntList.bmod"
                 "Lean.Omega.Coeffs.set"
                 ;; Int division bounds
                 "Int.mul_ediv_self_le" "Int.lt_mul_ediv_self_add"
                 ;; the COMPUTABLE decidable instances those bounds' side conditions
                 ;; are discharged with. `Classical.propDecidable` would leave `decide`
                 ;; stuck on `Classical.choice` and the kernel would reject the Eq.refl.
                 "Int.decLt" "Int.decEq" "instDecidableNot"
                 ;; the five renames' targets
                 "Classical.not_and_iff_not_or_not" "Classical.not_imp"
                 "Decidable.iff_iff_and_or_not_and_not" "Int.ofNat_eq_natCast"]]
        (is (some? (env/lookup e (name/from-string n)))
            (str n " must be present"))))))

(deftest bool-bridge-and-minmax-constants-present
  (testing "the lemmas the Bool→Prop bridge and min/max splitting depend on are exported"
    (let [e @test-env/bundled-init-env]
      (doseq [n ["Nat.ble" "Nat.blt"
                 "Nat.le_of_ble_eq_true" "Nat.not_le_of_not_ble_eq_true"
                 "Bool.noConfusion"
                 "Min.min" "Max.max" "minOfLe" "maxOfLe"
                 "if_pos" "if_neg" "Decidable.em" "Or.elim" "Or.inl" "Or.inr"
                 "And.intro"]]
        (is (some? (env/lookup e (name/from-string n)))
            (str n " must be present — omega emits it unconditionally"))))))
