(ns ansatz.foldl-assoc-generic-test
  "Option A: prove foldl_assoc GENERICALLY over the bundled WAddMonoid associativity axiom.
   The bundled `(WAddMonoid.add_assoc m)` fires through the proj-isDefEq simp matcher (#144) and is
   directional (not perm-gated), so it re-associates the accumulator to expose the generalized IH —
   sidestepping the raw-Nat.add-vs-(+) mismatch that blocks `Nat.add_assoc` on raw-op goals.
   Pairs with `(induction xs generalizing b)`. This is the pattern for the wandler foldl-law cluster."
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

(defn- has? [s] (some? (env/lookup (a/env) (name/from-string s))))
(defn- verifies? [s]
  (let [ci (env/lookup (a/env) (name/from-string s))]
    (and ci (env/verifies? (a/env) (.type ci) (.value ci)))))

(deftest foldl-assoc-generic
  (when @full
    ;; ∀ {S}(m:WAddMonoid S)(a b:S)(xs:List S),
    ;;   foldl m.add (m.add a b) xs = m.add a (foldl m.add b xs)
    (a/theorem foldl_assoc_w [S :- Type :implicit, m :- (WAddMonoid S), a :- S, b :- S, xs :- (List S)]
               (= S (List.foldl (WAddMonoid.add m) (WAddMonoid.add m a b) xs)
                  (WAddMonoid.add m a (List.foldl (WAddMonoid.add m) b xs)))
               (induction xs generalizing b)
               (all_goals (simp_all [List.foldl_nil List.foldl_cons (WAddMonoid.add_assoc m)])))
    (is (has? "foldl_assoc_w") "generic foldl_assoc over WAddMonoid installed")
    (is (verifies? "foldl_assoc_w") "kernel-checks (check-constant, authoritative)")))
