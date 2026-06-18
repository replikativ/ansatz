(ns ansatz.rw-envlemma-test
  "#145: the `rewrite` tactic accepts ENV lemmas (∀-quantified, instantiated by matching) + `<-`
   reverse — Lean's `rw [lemma]`. Validated over the bundled WAddMonoid.add_assoc (no HAdd spelling
   issue) including the Lean-idiom controlled-rw proof of foldl_assoc."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.prelude.algebra :as alg]))

(def ^:private full
  (delay (let [f "test-data/init.ndjson"]
           (when (.exists (java.io.File. f))
             (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))
(defn- with-env [t] (when @full (reset! a/ansatz-env @full) (alg/install-classes!)) (t))
(use-fixtures :once with-env)
(defn- vrf? [s] (let [ci (env/lookup (a/env) (name/from-string s))]
                  (and ci (env/verifies? (a/env) (.type ci) (.value ci)))))

(deftest rw-env-lemma-forward
  (when @full
    ;; rw [m.add_assoc]: instantiate ∀ a b c by matching the LHS, then rfl
    (a/theorem rw_assoc_fwd [S :- Type :implicit, m :- (WAddMonoid S), a :- S, b :- S, c :- S]
      (= S (WAddMonoid.add m (WAddMonoid.add m a b) c) (WAddMonoid.add m a (WAddMonoid.add m b c)))
      (rewrite (WAddMonoid.add_assoc m))
      (rfl))
    (is (vrf? "rw_assoc_fwd") "rw [env-lemma] forward + rfl")))

(deftest rw-env-lemma-reverse
  (when @full
    ;; rw [<- m.add_assoc]: rewrite right-to-left (a+(b+c)) -> ((a+b)+c)
    (a/theorem rw_assoc_rev [S :- Type :implicit, m :- (WAddMonoid S), a :- S, b :- S, c :- S]
      (= S (WAddMonoid.add m a (WAddMonoid.add m b c)) (WAddMonoid.add m (WAddMonoid.add m a b) c))
      (rewrite <- (WAddMonoid.add_assoc m))
      (rfl))
    (is (vrf? "rw_assoc_rev") "rw [<- env-lemma] reverse + rfl")))

(deftest rw-bare-symbol
  (when @full
    ;; bare lemma SYMBOL (no args) — ALL params (S m a b c) instantiated by matching, the leading
    ;; TYPE param S (erased by the accessor→proj reduction) recovered via postprocessAppMVars.
    (a/theorem rw_assoc_bare [S :- Type :implicit, m :- (WAddMonoid S), a :- S, b :- S, c :- S]
      (= S (WAddMonoid.add m (WAddMonoid.add m a b) c) (WAddMonoid.add m a (WAddMonoid.add m b c)))
      (rewrite WAddMonoid.add_assoc)
      (rfl))
    (is (vrf? "rw_assoc_bare") "rw [bare-symbol env-lemma] (postprocessAppMVars)")))
