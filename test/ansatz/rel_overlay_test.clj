;; The relational env-OVERLAY: extend the env with declaration-holes above the
;; fixed oracle (Barliman-style env-relationality, done efficiently — known
;; names take the fast oracle path, overlay names are relational holes). A
;; lemma can be DECLARED, USED like any env lemma, SHARED across goals, and
;; SYNTHESIZED later; certify commits it (synthesized → checked def, else axiom).
(ns ansatz.rel-overlay-test
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.rel :as r]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.reduce :as red]
            [ansatz.provenance :as prov]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

(def ^:private env*
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(def ^:dynamic *env* nil)
(use-fixtures :once
  (fn [f]
    (binding [*env* (or @env* (throw (ex-info "init-medium.ndjson not found" {})))]
      (f))))

(def ^:private le0 (e/const' (nm/from-string "LE.le") [lvl/zero]))
(def ^:private inst (e/const' (nm/from-string "instLENat") []))
(def ^:private nat (e/const' (nm/from-string "Nat") []))
(defn- nle [a b] (reduce e/app le0 [nat inst a b]))

;; n m k : Nat, h1 : n ≤ m, h2 : m ≤ k
(def ^:private n (e/fvar 10))
(def ^:private m (e/fvar 11))
(def ^:private k (e/fvar 12))
(def ^:private lctx*
  (delay (-> (red/empty-lctx)
             (red/lctx-add-local 10 "n" nat) (red/lctx-add-local 11 "m" nat) (red/lctx-add-local 12 "k" nat)
             (red/lctx-add-local 20 "h1" (nle n m)) (red/lctx-add-local 21 "h2" (nle m k)))))
;; mytrans's type = the real Nat.le_trans statement (declared in the OVERLAY,
;; not the env — so its use is env-relational).
(defn- trans-ty [] (.type (kenv/lookup *env* (nm/from-string "Nat.le_trans"))))

(defn- prove-with-overlay [decls-thunk-goal]
  (first (r/run 1 (r/state *env* :lctx @lctx*) decls-thunk-goal)))

(deftest overlay-lemma-used-and-assumed
  (testing "declare a lemma-hole, prove a goal with it; certify admits it as an axiom"
    (let [s (prove-with-overlay
             (fn [st]
               ((r/declareo "mytrans" (trans-ty)
                            (fn [] (r/fresh (nle n k)
                                            (fn [g] (r/all (r/applyo g "mytrans" (fn [obs] (apply r/all (map r/assumptiono obs))))
                                                           (fn [s2] (r/unit (assoc s2 ::g g))))))))
                st)))
          c (r/certify s (::g s))]
      (is (some? s) "proved n≤k via the overlay lemma")
      (is (:ok? c) "kernel-certified GIVEN the overlay lemma")
      (is (= ["mytrans"] (:assumed c)) "mytrans admitted as an axiom (not yet synthesized)"))))

(deftest overlay-lemma-synthesized-becomes-def
  (testing "synthesizing the overlay lemma's value upgrades it to a checked def"
    (let [s (prove-with-overlay
             (fn [st]
               ((r/declareo "mytrans" (trans-ty)
                            (fn [] (r/fresh (nle n k)
                                            (fn [g] (r/all (r/applyo g "mytrans" (fn [obs] (apply r/all (map r/assumptiono obs))))
                                                           (fn [s2] (r/unit (assoc s2 ::g g))))))))
                st)))
          ;; the search would produce this value; here we alias to the real lemma
          s' (r/set-overlay-value s "mytrans" (e/const' (nm/from-string "Nat.le_trans") []))
          c (r/certify s' (::g s'))]
      (is (:ok? c) "still kernel-certified")
      (is (= [] (:assumed c)) "no assumptions — mytrans is now a checked def"))))

(deftest overlay-lemma-is-an-automatic-proveo-candidate
  (testing "a declared overlay lemma is used by proveo WITHOUT being listed —
            env and overlay are one candidate space"
    (let [s (prove-with-overlay
             (fn [st]
               ((r/declareo "mytrans" (trans-ty)
                            (fn [] (r/fresh (nle n k)
                                            ;; NOTE: empty lemma list — mytrans comes from the overlay
                                            (fn [g] (r/all (r/proveo g [] 3)
                                                           (fn [s2] (r/unit (assoc s2 ::g g))))))))
                st)))]
      (is (some? s) "proved n≤k using the overlay lemma with no explicit candidates")
      (is (:ok? (r/certify s (::g s)))))))

;; ∀ n:Nat, n ≤ n  — a lemma the search can PROVE (via Nat.le_refl)
(def ^:private refl-ty
  (delay (e/forall' "n" nat (nle (e/bvar 0) (e/bvar 0)) :default)))

(deftest inhabito-introduces-pi-goals
  (testing "proveo (a preset of inhabito) proves a ∀-goal DIRECTLY via the
            driver's Π-introduction rule — no manual telescope. This is the
            unified inhabitation operation handling a checking-mode goal."
    (let [s (first (r/run 1 (r/state *env*)
                          (r/fresh @refl-ty
                                   (fn [g] (r/all (r/proveo g [[1 "Nat.le_refl"]] 3)
                                                  (fn [s2] (r/unit (assoc s2 ::g g))))))))
          c (when s (r/certify s (::g s)))]
      (is (some? s) "proved ∀n, n≤n by introducing n and applying refl")
      (is (:ok? c) "kernel-certified as (λ n. Nat.le_refl n) : ∀ n, n≤n"))))

(deftest synthesize-overlay-value-by-search
  (testing "declare a lemma-hole, SYNTHESIZE its proof by search (not alias),
            use it, and certify — a search-proven def, no assumptions"
    (let [a (e/fvar 30)
          lctx (red/lctx-add-local (red/empty-lctx) 30 "a" nat)
          s (first (r/run 1 (r/state *env* :lctx lctx)
                          (fn [st]
                            ((r/declareo "myrefl" @refl-ty
                                         (fn []
                                           (r/synthesizeo
                                            "myrefl"
                                            (fn [g] (r/proveo g [[1 "Nat.le_refl"]] 2))
                                            (fn []
                                              (r/fresh (nle a a)
                                                       (fn [gg]
                                                         (r/all (r/applyo gg "myrefl" (fn [_] r/succeed))
                                                                (fn [s2] (r/unit (assoc s2 ::g gg))))))))))
                             st))))
          c (when s (r/certify s (::g s)))]
      (is (some? s) "search proved the overlay lemma AND used it in the goal")
      (is (some? (get-in s [:overlay "myrefl" :value])) "myrefl's value was synthesized")
      (is (:ok? c) "kernel-certified")
      (is (= [] (:assumed c)) "no assumptions — myrefl is a search-proven def"))))

(deftest probability-of-provability-from-uncertain-premises
  (testing "two UNCERTAIN overlay lemmas (credence axioms) each prove the goal;
            under ProofsProb the measure over the proof space is the exact
            probability-of-provability P(L1 ∨ L2), correlation-aware"
    (let [ltype (e/forall' "x" nat (e/forall' "y" nat (nle (e/bvar 1) (e/bvar 0)) :default) :default)
          a (e/fvar 40) b (e/fvar 41)
          lctx (-> (red/empty-lctx) (red/lctx-add-local 40 "a" nat) (red/lctx-add-local 41 "b" nat))
          states (r/run 5 (r/state *env* :lctx lctx :prov prov/proofs-prov)
                        (fn [st]
                          ((r/declareo "L1" ltype
                                       (fn [] (r/declareo "L2" ltype
                                                          (fn [] (r/fresh (nle a b)
                                                                          (fn [g] (r/proveo g [] 3))))
                                                          :credence 0.6))
                                       :credence 0.8)
                           st)))]
      (is (<= 2 (count states)) "goal proved via each uncertain lemma")
      (is (< 0.91 (r/combined-measure prov/proofs-prov states) 0.93)
          "P(L1@0.8 ∨ L2@0.6) = 1-(1-0.8)(1-0.6) = 0.92 — probability the goal is provable"))))

(defn- proveo-moves
  "proveo's move-set (assumption leaf + one refiner per lemma), for bestfirst."
  [lemmas]
  (fn [_s g]
    {:leaves [[8 (r/assumptiono g)]]
     :refiners (vec (for [[w nm] lemmas] [w (fn [g k] (r/applyo g nm k))]))}))

(deftest bestfirst-finds-proof-among-distractors
  (testing "best-first priority frontier proves a 4-chain a≤d with le_trans mixed
            among distractor candidates that all conclusion-unify — the frontier
            expands the most-promising partial proof and stops, where fair
            interleave would explode over candidates × depth"
    (let [a (e/fvar 60) b (e/fvar 61) cc (e/fvar 62) d (e/fvar 63)
          lctx (-> (red/empty-lctx)
                   (red/lctx-add-local 60 "a" nat) (red/lctx-add-local 61 "b" nat)
                   (red/lctx-add-local 62 "c" nat) (red/lctx-add-local 63 "d" nat)
                   (red/lctx-add-local 64 "h1" (nle a b)) (red/lctx-add-local 65 "h2" (nle b cc))
                   (red/lctx-add-local 66 "h3" (nle cc d)))
          ;; le_trans + distractors whose conclusions also unify with _ ≤ _
          lemmas [[1 "Nat.le_trans"] [1 "Nat.le_refl"] [1 "Nat.zero_le"]
                  [1 "Nat.le_of_lt"] [1 "Nat.le_succ"]]
          s1 (first (r/run 1 (r/state *env* :lctx lctx)
                           (r/fresh (nle a d) (fn [g] (fn [s] (r/unit (assoc s ::g g)))))))
          g (::g s1)
          sols (r/bestfirst g (proveo-moves lemmas) 6 s1 :max-nodes 8000 :limit 1)
          s (first sols)
          c (when s (r/certify s g))]
      (is (some? s) "best-first found a proof of a≤d among the distractors")
      (is (:ok? c) "kernel-certified")
      (is (= [] (:assumed c))))))

(deftest overlay-lemma-shared-across-goals
  (testing "ONE overlay lemma, used by TWO goals, synthesized once"
    (let [s (prove-with-overlay
             (fn [st]
               ((r/declareo "mytrans" (trans-ty)
                            (fn [] (r/fresh (nle n k)
                                            (fn [g1] (r/fresh (nle n k)
                                                              (fn [g2] (r/all
                                                                        (r/applyo g1 "mytrans" (fn [o] (apply r/all (map r/assumptiono o))))
                                                                        (r/applyo g2 "mytrans" (fn [o] (apply r/all (map r/assumptiono o))))
                                                                        (fn [s2] (r/unit (assoc s2 ::g1 g1 ::g2 g2))))))))))
                st)))
          s' (r/set-overlay-value s "mytrans" (e/const' (nm/from-string "Nat.le_trans") []))]
      (is (= ["mytrans"] (keys (:overlay s))) "exactly one shared overlay declaration")
      (is (:ok? (r/certify s' (::g1 s))) "goal 1 certified with the shared lemma")
      (is (:ok? (r/certify s' (::g2 s))) "goal 2 certified with the SAME shared lemma"))))
