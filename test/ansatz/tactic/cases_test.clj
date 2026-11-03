(ns ansatz.tactic.cases-test
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.meta :as meta]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.env :as env]
            [ansatz.test-env :as test-env]))

(def observed (atom []))
(use-fixtures :once
  (fn [f]
    (binding [a/*verbose* false] (a/load-init!))
    (a/register-tactic! 'observe-cases
                        (fn [ps _] (swap! observed conj ps) ps))
    (f)))

(defn proves [params target tactics]
  (reset! observed [])
  (binding [a/*verbose* false]
    (a/prove-theorem (gensym "cases_scope_") params target tactics))
  true)

(deftest cases-replaces-only-the-main-goal
  (is (proves '[b :- Bool] '(And (= b b) (= b b))
              '[(constructor) (observe-cases) (cases b) (observe-cases)
                (all_goals (rfl))]))
  (let [[before after] @observed
        sibling (second (:goals before))]
    (is (= 3 (count (:goals after))))
    (is (= (proof/mvar-decl before sibling) (proof/mvar-decl after sibling)))
    (is (= sibling (last (:goals after))))
    (is (every? #(not-any? (fn [[_ d]] (= "b" (:name d))) (:lctx %))
                (take 2 (proof/goals after))))))

(deftest all-goals-cases-splits-each-sibling
  (is (proves '[b :- Bool] '(And (= b b) (= b b))
              '[(constructor) (all_goals (cases b)) (observe-cases)
                (all_goals (rfl))]))
  (is (= 4 (count (:goals (first @observed)))))
  (is (every? #(not-any? (fn [[_ d]] (= "b" (:name d))) (:lctx %))
              (proof/goals (first @observed)))))

(deftest constructor-fields-stay-in-their-branch
  (is (proves '[n :- Nat] '(And (= n n) (= n n))
              '[(constructor) (observe-cases) (cases n) (observe-cases)
                (all_goals (rfl))]))
  (let [[before after] @observed
        sibling (second (:goals before))
        sibling-lctx (proof/mvar-lctx after sibling)
        branch-ids (mapcat #(keys (:lctx %)) (take 2 (proof/goals after)))
        fresh (remove (set (keys (proof/mvar-lctx before sibling))) branch-ids)]
    (is (seq fresh))
    (is (not-any? #(contains? sibling-lctx %) fresh))))

(deftest cases-has-fields-without-induction-hypotheses
  (is (proves '[n :- Nat] '(= n n)
              '[(cases n) (observe-cases) (all_goals (rfl))]))
  (let [branches (proof/goals (first @observed))]
    (is (= [0 1] (mapv (comp count :lctx) branches)))
    (is (not-any? #(clojure.string/starts-with? (str (:name %)) "ih_")
                  (mapcat (comp vals :lctx) branches))))
  (binding [a/*verbose* false]
    (a/inductive CasesChain [] :in Prop (base) (step [hx CasesChain])))
  (is (proves '[h :- CasesChain] 'CasesChain
              '[(cases h) (observe-cases) (exact CasesChain.base) (rename_i hx) (exact hx)]))
  (is (= [0 1] (mapv (comp count :lctx) (proof/goals (first @observed)))))
  (is (proves '[h :- CasesChain] 'CasesChain
              '[(cases h :with
                       (base (exact CasesChain.base))
                       ((step hx) (exact hx)))])))

(deftest term-index-keeps-the-original-variable-name
  (binding [a/*verbose* false]
    (a/inductive CasesIndexed [] :in Prop :indices [n Nat]
                 (mk [x Nat] :where [(Nat.succ x)])))
  (is (proves '[f :- Nat, h :- (CasesIndexed (Nat.succ f))] '(= f f)
              '[(cases h) (exact (Eq.refl Nat f))]))
  (is (proves '[f :- Nat, h :- (CasesIndexed (Nat.succ f))] '(= f f)
              '[(cases h :with ((mk x) (exact (Eq.refl Nat f))))]))
  (is (proves '[f :- Nat, h :- (CasesIndexed (Nat.succ f))] '(= f f)
              '[(rcases h [x]) (exact (Eq.refl Nat f))])))

(deftest cases-field-names-and-dependent-hypotheses
  (is (proves '[n :- Nat, P :- (=> Nat Prop), h :- (P n)] '(P n)
              '[(cases n :with
                       (zero (exact h))
                       ((succ k) (exact h)))]))
  (is (proves '[n :- Nat, P :- (=> Nat Prop), h :- (forall [k :- Nat] (=> (= n k) (P k)))] '(P n)
              '[(cases eqn n :with
                       (zero (exact (h 0 eqn)))
                       ((succ k) (exact (h (Nat.succ k) eqn))))]))
  (is (proves '[n :- Nat] '(= n n)
              '[(cases n) (case zero (rfl))
                (case (succ k) (exact (Eq.refl Nat (Nat.succ k))))])))

(deftest cases-indexed-vectors-and-equality
  (binding [a/*verbose* false]
    (a/inductive CasesVec [A Type] :indices [n Nat]
                 (nil :where [Nat.zero])
                 (cons [x A] [n Nat] [xs (CasesVec A n)] :where [(Nat.succ n)])))
  (is (proves '[n :- Nat, v :- (CasesVec Nat (Nat.succ n))] '(= n n)
              '[(cases v) (exact (Eq.refl Nat n))]))
  (is (proves '[v :- (CasesVec Nat (Nat.succ Nat.zero))]
              '(Exists Nat (fn [x :- Nat] (= x x)))
              '[(cases v :with
                       ((cons x k xs)
                        (have tail (CasesVec Nat Nat.zero)) (exact xs)
                        (exact (Exists.intro Nat (fn [x :- Nat] (= x x)) x (Eq.refl Nat x)))))]))
  (is (proves '[v :- (CasesVec Nat (Nat.succ Nat.zero))]
              '(Exists Nat (fn [x :- Nat] (= x x)))
              '[(rcases v (or [] [x k xs]))
                (have tail (CasesVec Nat Nat.zero)) (exact xs)
                (exact (Exists.intro Nat (fn [x :- Nat] (= x x)) x (Eq.refl Nat x)))]))
  (is (proves '[x :- Nat, y :- Nat, h :- (= x y)] '(= x y)
              '[(cases h) (exact (Eq.refl Nat x))])))

(deftest cases-fresh-supply-includes-sibling-locals
  (is (proves '[n :- Nat] '(And (= n n) (= n n))
              '[(constructor) (observe-cases) (all_goals (rfl))]))
  (let [ps (first @observed)
        sibling (second (:goals ps))
        lctx (proof/mvar-lctx ps sibling)
        [major decl] (first (filter #(= "n" (:name (val %))) lctx))
        ps (update ps :meta-mctx meta/set-expr-mvar-lctx sibling
                   (assoc lctx 9000000 (assoc decl :id 9000000 :name "sibling-local")))
        result (basic/cases ps major)
        branches (take 2 (proof/goals result))]
    (is (= (proof/mvar-decl ps sibling) (proof/mvar-decl result sibling)))
    (is (every? #(> (:id %) 9000000) branches))
    (is (> (:next-id result) (apply max (mapcat (comp keys :lctx) branches))))))

(deftest cases-realizes-omitted-cases-on-auxiliaries
  (let [saved (a/env)
        auxiliary (name/from-string "HEq.casesOn")]
    (try
      (reset! a/ansatz-env @test-env/checked-bundled-init-env)
      (is (nil? (env/lookup (a/env) auxiliary)))
      (is (proves '[x :- Nat, y :- Nat, h :- (HEq Nat x Nat y)] '(= x y)
                  '[(observe-cases) (cases h) (observe-cases) (exact (Eq.refl Nat x))]))
      (let [[before after] @observed
            major (first (for [[fid d] (:lctx (proof/current-goal before))
                               :when (= "h" (:name d))] fid))]
        (is (nil? (env/lookup (:env before) auxiliary)))
        (is (some? (env/lookup (:env after) auxiliary)))
        (is (= 1 (count (:goals after))))
        (is (not (contains? (:lctx (proof/current-goal after)) major))))
      (finally (reset! a/ansatz-env saved)))))

(deftest cases-preserves-the-branch-target-definition
  (is (proves '[b :- Bool, n :- Nat] '(<= (if b n n) n)
              '[(cases b) (observe-cases) (all_goals (exact (Nat.le_refl n)))]))
  ;; Reducing the terminal telescope body would eagerly unfold LE.le to
  ;; Nat.le, changing subsequent simp/dsimp behaviour.
  (is (= ["LE.le" "LE.le"]
         (mapv #(str (e/const-name (e/get-app-fn (:type %))))
               (proof/goals (first @observed))))))

(deftest cases-preserves-parent-tag-scopes
  ;; Lean Meta/Tactic/Util.lean appendTag preserves the parent's macro scopes.
  (is (proves '[b :- Bool] '(= b b) '[(observe-cases) (rfl)]))
  (let [ps (first @observed)
        goal (proof/current-goal ps)
        fid (first (keys (:lctx goal)))
        base (name/mk-str (name/anonymous) "parent")
        scoped (fn [n] (name/mk-num (name/mk-str (name/mk-str (name/mk-str n "_@") "X") "_hyg") 42))
        ps (proof/set-mvar-user-name ps (:id goal) (scoped base))
        result (basic/cases ps fid)]
    (is (= [(scoped (name/mk-str base "false")) (scoped (name/mk-str base "true"))]
           (mapv #(proof/mvar-user-name result %) (:goals result))))))

(deftest cases-alternatives-name-explicit-fields
  (is (proves '[n :- Nat, m :- Nat, h :- (Nat.le n m)] '(Nat.le n m)
              '[(cases h :with
                       (refl (exact (Nat.le_refl n)))
                       ((step hp) (observe-cases) (exact (Nat.le.step hp))))]))
  (let [lctx (:lctx (proof/current-goal (first @observed)))
        implicit-fields (filter #(= :implicit (:info %)) (vals lctx))]
    (is (= 1 (count implicit-fields)))
    (is (every? :inaccessible implicit-fields))
    (is (false? (:inaccessible (first (filter #(= "hp" (:name %)) (vals lctx)))))))
  (is (proves '[n :- Nat, m :- Nat, h :- (Nat.le n m)] '(Nat.le n m)
              '[(cases h :with
                       (refl (exact (Nat.le_refl n)))
                       ((@step k hp) (observe-cases)
                                     (have bound (Nat.le n k)) (exact hp)
                                     (exact (Nat.le.step bound))))]))
  (let [lctx (:lctx (proof/current-goal (first @observed)))]
    (is (false? (:inaccessible (first (filter #(= "k" (:name %)) (vals lctx))))))))

(deftest cases-generalizes-reflexive-indices
  (doseq [[target finish] [['(= x x) '(exact (Eq.refl Nat x))]
                           ['True '(exact True.intro)]
                           ['(= h h) '(exact (Eq.refl (Eq Nat x x) (Eq.refl Nat x)))]]]
    (is (proves '[x :- Nat, h :- (= x x)] target
                ['(observe-cases) '(cases h) '(observe-cases) finish]))
    (let [[before after] @observed
          lctx (:lctx (proof/current-goal before))
          fid (first (for [[fid d] lctx :when (= "x" (:name d))] fid))
          major (first (for [[fid d] lctx :when (= "h" (:name d))] fid))
          branch (proof/current-goal after)]
      (is (= 1 (count (:goals after))))
      (is (= "x" (get-in branch [:lctx fid :name])))
      (is (not (contains? (:lctx branch) major)))))
  (is (proves '[x :- Nat, h :- (= (Nat.add x Nat.zero) x)] '(= x x)
              '[(cases h) (exact (Eq.refl Nat x))])))

(deftest cases-generalizes-indices-occurring-in-parameters
  (binding [a/*verbose* false]
    (a/inductive CasesFixed [n Nat] :in Prop :indices [m Nat]
                 (refl :where [n])))
  (is (proves '[n :- Nat, h :- (CasesFixed n n)] '(= n n)
              '[(observe-cases) (cases h) (observe-cases) (exact (Eq.refl Nat n))]))
  (let [[before after] @observed
        major (first (for [[fid d] (:lctx (proof/current-goal before))
                           :when (= "h" (:name d))] fid))]
    (is (not (contains? (:lctx (proof/current-goal after)) major))))
  (is (proves '[x :- Nat, h :- (= x x), hh :- (= h h)] '(= h h)
              '[(cases h) (exact hh)])))
