(ns ansatz.prelude.list-test
  "The polymorphic `wsum` (fold over a WAddMonoid) authored thinly and kernel-verified over the
   full Init store — exercises POLYMORPHIC structural recursion (Lean-style fixed prefix {S} + an
   instance param m), which previously failed (`(a/defn lenS [S :- Type, xs :- (List S)] …)` →
   type-mismatch / WF-misroute). The function now verifies and runs.

   The WSemiring big-operator LAW (sum_map_mul_left) is authored in ansatz.prelude.list/install!
   but its thin `(induction xs) <;> simp [wsum.eq_1 wsum.eq_2 …]` proof needs constructor-keyed
   equation lemmas; auto-generating those for a polymorphic+instance def still has fvar-leaks in
   the equation compiler (task #142 follow-on), so the law is attempted-but-deferred. This test
   pins the part that works and documents the boundary."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.prelude.list :as plist]))

;; Full Init store — wsum's List equation lemmas (List.map_nil/_cons) live here, not in init-medium.
(def ^:private full
  (delay (let [f "test-data/init.ndjson"]
           (when (.exists (java.io.File. f))
             (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(defn- with-env [t]
  (if-let [e @full]
    (do (reset! a/ansatz-env e) (plist/install!) (t))
    (println "  (skipping prelude.list-test — test-data/init.ndjson not present)")))
(use-fixtures :once with-env)

(defn- has? [s] (some? (env/lookup (a/env) (name/from-string s))))
(defn- verifies? [s]
  ;; Authoritative proof check for a theorem (Prop-typed): re-run check-constant via mk-thm.
  (let [ci (env/lookup (a/env) (name/from-string s))]
    (and ci (env/verifies? (a/env) (.type ci) (.value ci)))))
(defn- def-verifies? [s]
  ;; Authoritative: re-run the Java kernel check-constant on the def (type + body) under a fresh
  ;; name. a/defn already check-constants on install (so `has?` implies a pass), this re-asserts it.
  (let [ci (env/lookup (a/env) (name/from-string s))]
    (boolean
     (and ci
          (try (env/check-constant (a/env)
                                   (env/mk-def (name/from-string "__wsum_chk__") [] (.type ci) (.value ci)))
               true (catch Throwable _ false))))))

(deftest wsum-polymorphic-recursion-verifies
  (when @full
    (testing "polymorphic structural recursion ({S} + instance m) defines + kernel-verifies"
      (is (has? "wsum"))
      (is (def-verifies? "wsum") "wsum kernel-checks (check-constant, authoritative)"))
    (testing "constructor-keyed equation lemmas auto-generate + verify (polymorphic+instance eq-gen)"
      (is (has? "wsum.eq_1") "nil equation lemma")
      (is (has? "wsum.eq_2") "cons equation lemma")
      (is (verifies? "wsum.eq_1") "nil equation lemma kernel-checks")
      (is (verifies? "wsum.eq_2") "cons equation lemma kernel-checks"))))

(deftest wsum-map-mul-left-law
  (when @full
    (testing "the WSemiring loop-invariant-hoist law, authored thinly (induction + simp)"
      (is (has? "wsum_map_mul_left") "∑ (b * f x) = b * ∑ f x was installed")
      (is (verifies? "wsum_map_mul_left")
          "the law kernel-checks (check-constant, authoritative)"))))

(deftest sum-filter-map-law
  (when @full
    (testing "filter folds into a guarded sum — the bridge for join reorder (Fubini)"
      ;; Proof mirrors lean-wandler `cases hp : p y <;> simp [hp]`, exercising the faithful
      ;; substituting `cases hp (p head)` (split S3) + simp's instance-whnf reduceIte.
      (is (has? "sum_filter_map") "∑ (map h (filter p ys)) = ∑ (map (λy. if p y then h y else 0) ys)")
      (is (verifies? "sum_filter_map")
          "the law kernel-checks (check-constant, authoritative)"))))

(deftest wsum-reverse-law
  (when @full
    (testing "∑ is order-insensitive over a commutative monoid (the Map.join bucket-reverse bridge)"
      (is (has? "wsum_reverse") "∑ (reverse l) = ∑ l")
      (is (verifies? "wsum_reverse")
          "the law kernel-checks (check-constant, authoritative)"))))

(deftest foldl-cons-acc-law
  (when @full
    (testing "foldl(· :: ·) acc l = reverse l ++ acc — exposes Map.join's foldl-built bucket as reverse"
      ;; Accumulator-generalized (induction l generalizing acc): the IH must range over acc.
      (is (has? "foldl_cons_acc") "foldl (· :: ·) acc l = (reverse l) ++ acc")
      (is (verifies? "foldl_cons_acc")
          "the law kernel-checks (check-constant, authoritative)"))
    (testing "foldl(::)[] = reverse + ∑(map g (foldl(::)[] l)) = ∑(map g l) — the bucket-reverse wash"
      (is (has? "foldl_cons_nil"))
      (is (verifies? "foldl_cons_nil"))
      (is (has? "wsum_map_foldl_cons"))
      (is (verifies? "wsum_map_foldl_cons")
          "the per-bucket reverse-wash helper, kernel-verified"))))

(deftest lookup-filter-ne-law
  (when @full
    (testing "lookup k (filter (·.fst ≠ k') l) = lookup k l when k ≠ k' — assoc-list lookup foundation"
      ;; Exercises faithful dsimp (iota after a scrutinee-rewrite) + structure-extends parent-projection
      ;; instance synthesis (ReflBEq via DecidableEq→LawfulBEq→ReflBEq); replaces a ~90-LOC term proof.
      (is (has? "List.lookup_filter_ne") "lookup-through-a-different-key-filter is identity")
      (is (verifies? "List.lookup_filter_ne")
          "the law kernel-checks (check-constant, authoritative)"))
    (testing "lookup-after-insert (cond via bif): the head pair, else lookup-through-the-filter"
      (is (has? "List.lookup_insert") "lookup k ((k',v)::filter) = bif (k==k') (some v) (lookup k l)")
      (is (verifies? "List.lookup_insert")
          "the law kernel-checks (check-constant, authoritative)"))
    (testing "beq_comm — a == b = b == a (DecidableEq-derived beq, via decide_eq_decide + eq_comm)"
      (is (has? "beq_comm"))
      (is (verifies? "beq_comm")
          "the law kernel-checks; bridges a join's key predicate to the swapped-drive form"))))
