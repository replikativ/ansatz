(ns ansatz.tactic.local-context-test
  "LocalContext.findFromUserName? and Split.withEqs; Lean pairs in local_context.lean."
  (:require [clojure.test :refer [deftest is use-fixtures testing]]
            [ansatz.core :as a]
            [ansatz.config :as config]
            [ansatz.meta :as meta]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.reduce :as red]
            [ansatz.surface.elaborate :as elab]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.proof :as proof]))

(use-fixtures :once
  (fn [t]
    (let [saved @a/ansatz-env]
      (try (a/load-init!) (t) (finally (reset! a/ansatz-env saved))))))

(def padding '[a0 :- Nat, a1 :- Nat, a2 :- Nat, a3 :- Nat,
               a4 :- Nat, a5 :- Nat, a6 :- Nat, a7 :- Nat])

(defn- proves [nm params goal tactics]
  (binding [a/*verbose* false]
    (a/prove-theorem nm (into padding params) goal tactics)
    (is true)))

(deftest newest-shadow-resolves-in-terms-and-tactics
  (proves 'shadow_exact '[h :- (= Nat 0 0)]
          '(=> (= Nat 1 1) (= Nat 1 1)) '[(intro h) (exact h)])
  (proves 'shadow_clear '[h :- False] '(=> True False)
          '[(intro h) (clear h) (exact h)])
  (proves 'shadow_revert '[h :- False] '(=> True True)
          '[(intro h) (revert h) (intro e) (exact e)])
  (proves 'shadow_subst '[h :- True, x :- Nat] '(=> (= x 1) (= x 1))
          '[(intro h) (subst h) (rfl)])
  (proves 'shadow_cases '[h :- True] '(=> (And True False) False)
          '[(intro h) (cases h) (rename_i ht hf) (exact hf)])
  (proves 'shadow_rewrite '[h :- True, x :- Nat, eqx :- (= x 1)]
          '(=> (= x 2) (= Nat 1 2))
          '[(intro h) (rw [eqx] at h) (exact h)])
  (proves 'shadow_simp '[h :- True, x :- Nat]
          '(=> (= (+ x 0) 1) (= x 1))
          '[(intro h) (simp only [Nat.add_zero] at h) (exact h)]))

(deftest context-iteration-and-assumption-use-declaration-order
  (let [ty (elab/elaborate (a/env) '(= Nat 1 1))
        [ps _] (proof/start-proof (a/env) ty)
        ;; Deliberately supply a hash map in scrambled insertion order.
        lctx (into {} (for [id [7 2 12 4 10 1 6 9 3 11 5 8]]
                        [id {:id id :tag :local :name "h" :type ty}]))
        ps (-> ps (assoc :next-id 20)
               (update :meta-mctx meta/set-expr-mvar-lctx
                       (:id (proof/current-goal ps)) lctx))
        ps' (basic/assumption ps)]
    (is (= (range 1 13) (keys (:lctx (proof/current-goal ps)))))
    (is (= 12 (e/fvar-id (elab/elaborate-in-context (a/env) lctx 'h))))
    (is (= 12 (:id (red/find-from-user-name? (into (sorted-map-by >) lctx) 'h))))
    (is (= 12 (e/fvar-id (extract/extract ps'))))
    (is (= 11 (:id (red/find-from-user-name? (assoc-in lctx [12 :inaccessible] true) 'h))))))

(deftest split-equations-require-explicit-naming
  (let [ty (elab/elaborate (a/env)
                           '(forall [b :- Bool] (= Nat (if b 0 1) 1)))
        [ps _] (proof/start-proof (a/env) ty)
        ps (-> ps (basic/intro "b") (a/run-tactic '(split)))
        g (proof/current-goal ps)]
    (doseq [nm '[h hc heq]]
      (is (nil? (red/find-from-user-name? (:lctx g) nm)))
      (is (thrown? clojure.lang.ExceptionInfo (a/run-tactic ps (list 'revert nm)))))
    (is (some :inaccessible (vals (:lctx g))))
    (let [named (a/run-tactic ps '(rename_i eqb))]
      (is (some? (red/find-from-user-name? (:lctx (proof/current-goal named)) 'eqb)))))
  (proves 'split_named_equations '[b :- Bool] '(Or (= b false) (= b true))
          '[(have hh (= Nat (if b 0 1) (if b 0 1))) (rfl)
            (split at hh) (rename_i heq) (left) (exact heq)
            (next [heq] (right) (exact heq))]))

(deftest split-matcher-fields-are-inaccessible-until-named
  (binding [a/*verbose* false config/*lean-matchers* true]
    (a/define-verified 'scope-match '[o :- (Option Nat)] 'Nat
      '(match o [none 0] [(some x) x]))
    (let [ty (elab/elaborate (a/env)
                             '(forall [o :- (Option Nat)] (= (scope-match o) (scope-match o))))
          [ps _] (proof/start-proof (a/env) ty)
          ps (-> ps (basic/intro "o")
                 (a/run-tactic '(unfold scope-match))
                 (a/run-tactic '(split)))
          ps (reduce (fn [ps gid]
                       (let [g (proof/current-goal (assoc ps :goals [gid]))
                             generated (filter (comp :inaccessible val) (:lctx g))]
                         (is (seq generated))
                         (doseq [[_ d] generated]
                           (is (nil? (red/find-from-user-name? (:lctx g) (:name d)))))
                         ps)) ps (:goals ps))
          ps (basic/all-goals ps #(a/run-tactic % '(rfl)))]
      (is (some? (extract/verify ps))))))

(deftest split-keeps-decomposed-equations-inaccessible
  (binding [a/*verbose* false config/*lean-matchers* true]
    (a/define-verified 'scope-eq-match '[n :- Nat] 'Nat
      '(match n [(Nat.succ Nat.zero) 10] [(Nat.succ k) k] [Nat.zero 20]))
    (let [ty (elab/elaborate (a/env)
                             '(forall [n :- Nat, f :- (=> Nat Nat)]
                                      (= (scope-eq-match (Nat.succ (f n)))
                                         (scope-eq-match (Nat.succ (f n))))))
          [ps _] (proof/start-proof (a/env) ty)
          ps (-> ps (basic/intros ["n" "f"])
                 (a/run-tactic '(unfold scope-eq-match)))
          old-ids (set (keys (:lctx (proof/current-goal ps))))
          decompositions (atom 0)
          unify-eq basic/unify-eq
          ps (with-redefs [basic/unify-eq
                           (fn [& args]
                             (let [r (apply unify-eq args)]
                               (swap! decompositions + (:num-new-eqs r))
                               r))]
               (a/run-tactic ps '(split)))]
      (is (pos? @decompositions))
      (doseq [g (proof/goals ps)
              [fid d] (:lctx g)
              :when (not (old-ids fid))]
        (is (:inaccessible d))
        (is (nil? (red/find-from-user-name? (:lctx g) (:name d)))))
      (is (some? (extract/verify (basic/all-goals ps #(a/run-tactic % '(rfl)))))))))

(deftest ignored-rcases-fields-remain-inaccessible
  (let [ty (elab/elaborate (a/env) '(forall [h :- (And True False)] False))
        [ps _] (proof/start-proof (a/env) ty)
        ps (-> ps (basic/intro "h") (a/run-tactic '(rcases h [ht _])))
        g (proof/current-goal ps)
        ignored (first (filter :inaccessible (vals (:lctx g))))]
    (is (some? ignored))
    (is (nil? (red/find-from-user-name? (:lctx g) (:name ignored))))
    (is (some? (extract/verify (-> ps (a/run-tactic '(rename_i hf))
                                   (a/run-tactic '(exact hf))))))))

(deftest elimination-preserves-dependent-scoped-names
  (doseq [tactic '[(cases n) (induction n)]]
    (let [ty (elab/elaborate (a/env) '(forall [n :- Nat] (=> (= n n) True)))
          [ps _] (proof/start-proof (a/env) ty)
          ps (-> ps (a/run-tactic '(intro n)) (a/run-tactic '(intro)))
          original (last (vals (:lctx (proof/current-goal ps))))
          ps (a/run-tactic ps tactic)]
      (doseq [g (proof/goals ps)]
        (let [reintroduced (first (filter #(= (:name original) (:name %)) (vals (:lctx g))))]
          (is (:inaccessible reintroduced))
          (is (= (red/user-name-key original) (red/user-name-key reintroduced)))
          (is (nil? (red/find-from-user-name? (:lctx g) (:name original))))))
      (is (some? (extract/verify
                  (basic/all-goals ps #(-> % (a/run-tactic '(rename_i eqn))
                                           (a/run-tactic '(exact True.intro))))))))))

(deftest substitution-preserves-dependent-scoped-names
  (doseq [tactic '[(cases eqn) (subst eqn)]]
    (let [ty (elab/elaborate (a/env)
                             '(forall [n :- Nat, m :- Nat, eqn :- (= n m)] (=> (= n n) True)))
          [ps _] (proof/start-proof (a/env) ty)
          ps (-> ps (basic/intros ["n" "m" "eqn"]) (a/run-tactic '(intro)))
          original (last (vals (:lctx (proof/current-goal ps))))
          ps (a/run-tactic ps tactic)
          g (proof/current-goal ps)
          reintroduced (first (filter #(= (:name original) (:name %)) (vals (:lctx g))))]
      (is (:inaccessible reintroduced))
      (is (= (red/user-name-key original) (red/user-name-key reintroduced)))
      (is (nil? (red/find-from-user-name? (:lctx g) (:name original))))
      (is (some? (extract/verify (-> ps (a/run-tactic '(rename_i hidden))
                                     (a/run-tactic '(exact True.intro)))))))))

(deftest rename-inaccessibles-compares-full-names
  (let [ty (elab/elaborate (a/env)
                           (list 'forall '[p :- Prop, d :- (Decidable p), h :- False]
                                 (list '= 'Nat (list (symbol "@ite") 'Nat 'p 'd 0 1) 0)))
        [ps _] (proof/start-proof (a/env) ty)
        ps (basic/intros ps ["p" "d" "h"])
        original (red/find-from-user-name? (:lctx (proof/current-goal ps)) 'h)
        ps (a/run-tactic ps '(split))]
    (doseq [g (proof/goals ps)]
      (let [branch (assoc ps :goals [(:id g)])]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"too many"
                              (a/run-tactic branch '(rename_i old new))))
        (let [renamed (a/run-tactic branch '(rename_i condition))]
          (is (= (:id original) (:id (red/find-from-user-name? (:lctx (proof/current-goal renamed)) 'h)))))))
    (is (some? (extract/verify (basic/all-goals ps #(-> % (a/run-tactic '(rename_i condition))
                                                        (a/run-tactic '(cases h)))))))))

(deftest located-matcher-split-preserves-reverted-scoped-names
  (let [ty (elab/elaborate (a/env)
                           '(forall [b :- Bool]
                                    (=> (= Nat (List.filter.match_1 (fn [x :- Bool] Nat) b
                                                                    (fn [u :- Unit] 0) (fn [u :- Unit] 1)) 0)
                                        True)))
        [ps _] (proof/start-proof (a/env) ty)
        ps (-> ps (a/run-tactic '(intro b)) (a/run-tactic '(intro)))
        original (last (vals (:lctx (proof/current-goal ps))))
        ps (basic/split-local-decl ps (:id original))]
    (doseq [g (proof/goals ps)]
      (let [reintroduced (first (filter #(= (:name original) (:name %)) (vals (:lctx g))))]
        (is (:inaccessible reintroduced))
        (is (= (red/user-name-key original) (red/user-name-key reintroduced)))))
    (is (some? (extract/verify
                (basic/all-goals ps #(-> % (a/run-tactic '(rename_i eqn))
                                         (a/run-tactic '(exact True.intro)))))))))
