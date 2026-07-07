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
