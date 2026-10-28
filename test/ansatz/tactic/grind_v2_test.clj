(ns ansatz.tactic.grind-v2-test
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.eqns :as eqns]
            [ansatz.conformance-support :as cs]
            [ansatz.grind-conformance-test :as conformance]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.match-eqns :as match-eqns]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.grind :as legacy]
            [ansatz.tactic.grind.action :as action]
            [ansatz.tactic.grind.solvers :as solvers]
            [ansatz.tactic.omega :as omega]
            [ansatz.tactic.omega-proof :as omega-proof]
            [ansatz.tactic.grind.main :as main]
            [ansatz.tactic.grind.ctor :as ctor]
            [ansatz.tactic.grind.theorem :as theorem]
            [ansatz.tactic.grind.egraph :as eg]))

(use-fixtures :once (fn [f] (a/load-init! :verify? true) (binding [a/*verbose* false] (f))))

(defn- check-script [script]
  (with-redefs [legacy/grind main/grind]
    (is (= :ok (cs/attempt script 10000)) (str (first script)))))

(deftest logical-refutation-proofs
  ;; prove-theorem checks the extracted closed proof using check-constant.
  (doseq [script
          '[[v2_trans [a :- Nat, b :- Nat, c :- Nat, h1 :- (= b a), h2 :- (= b c)]
             (= a c) [(grind)]]
            [v2_congr [f :- (=> Nat Nat), a :- Nat, b :- Nat, h :- (= a b)]
             (= (f a) (f b)) [(grind)]]
            [v2_function_congr [f :- (=> Nat Nat), g :- (=> Nat Nat), a :- Nat, h :- (= f g)]
             (= (f a) (g a)) [(grind)]]
            [v2_and_comm [p :- Prop, q :- Prop] (Iff (And p q) (And q p)) [(grind)]]
            [v2_bool [a :- Bool, b :- Bool]
             (=> (= a true) (= b false) (= a b) False) [(grind)]]
            [v2_if [b :- Bool, x :- Nat, y :- Nat, h :- (= b true)]
             (= (if b x y) x) [(grind)]]
            [v2_exists [p :- (=> Nat Prop), h :- (Exists Nat p), hn :- (forall [x :- Nat] (Not (p x)))]
             False [(grind)]]
            [v2_and [p :- Prop, q :- Prop, h :- (And p q)] q [(grind)]]
            [v2_or [p :- Prop, q :- Prop, h :- (Or p q), hn :- (Not p)] q [(grind)]]
            [v2_modus [p :- Prop, q :- Prop, h :- (=> p q), hp :- p] q [(grind)]]
            [v2_ematch [f :- (=> Nat Nat), h :- (forall [x :- Nat] (= (f x) x)), a :- Nat]
             (= (f (f a)) a) [(grind)]]
            [v2_forward [p :- (=> Nat Prop), q :- (=> Nat Prop), h :- (forall [x :- Nat] (=> (p x) (q x))), a :- Nat, ha :- (p a)]
             (q a) [(grind)]]
            [v2_branches [p :- Prop, q :- Prop]
             (=> (Or p q) (Or p (Not q)) (Or (Not p) q) (Or (Not p) (Not q)) False)
             [(grind)]]]]
    (check-script script)))

(deftest only-tactic-errors-are-not-applicable
  (is (nil? (action/attempt #(action/fail! "not applicable" {}))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"metadata"
                        (action/attempt #(throw (ex-info "metadata" {:kind :bad-metadata})))))
  (is (thrown? NullPointerException (action/attempt #(throw (NullPointerException. "bug")))))
  (let [[ps _] (proof/start-proof (a/env) (e/const' (name/from-string "False") []))]
    (with-redefs [ctor/propagate (fn [& _] (throw (NullPointerException. "engine bug")))]
      (is (thrown-with-msg? NullPointerException #"engine bug" (main/grind ps))))))

(deftest joint-local-function-multipatterns
  (let [p (e/fvar 100) q (e/fvar 101) a (e/fvar 102) b (e/fvar 103)
        graph (-> (eg/mk-grind-state (env/empty-env))
                  (eg/internalize (e/app p a) 0)
                  (eg/internalize (e/app q b) 0))
        thm {:patterns [(e/app p (e/bvar 0)) (e/app q (e/bvar 0))] :level-params []}
        config action/defaults]
    (is (empty? (theorem/matches graph thm config)) "different assignments cannot satisfy a joint match")
    (let [joined (eg/internalize graph (e/app q a) 0)
          matches (theorem/matches joined thm config)]
      (is (= 1 (count matches)))
      (is (= a (get-in (first matches) [:assignment :vars 0])))
      (is (not (eg/get-enode graph (e/app q a))) "fork did not modify the original graph"))
    (let [generated (eg/internalize graph (e/app q a) 8)]
      (is (empty? (theorem/matches generated thm config)) "generation gate is strict")
      (is (= 8 (:gen (first (theorem/matches generated thm (assoc config :gen 9)))))))))

(deftest named-budgets
  (doseq [budget [:splits :instances :ematch :iterations]]
    (let [error (try (action/budget! (assoc action/defaults budget 0) budget 0)
                     (catch clojure.lang.ExceptionInfo ex ex))]
      (is (= :tactic-error (:kind (ex-data error))))
      (is (= budget (:limit (ex-data error))))))
  (with-redefs [legacy/grind (fn [ps hints] (main/grind ps hints {:instances 0}))]
    (is (re-find #"instances budget exhausted"
                 (cs/attempt '[v2_instance_limit [f :- (=> Nat Nat), h :- (forall [x :- Nat] (= (f x) x)), a :- Nat]
                               (= (f (f a)) a) [(grind)]] 10000)))))

(deftest hint-vector-adapter
  (let [handler (get @a/tactic-registry 'grind) seen (atom nil)]
    (with-redefs [legacy/grind (fn [ps hints] (reset! seen hints) ps)]
      (handler {} '[[f g]])
      (is (= ["f" "g"] @seen))
      (handler {} '["f" "g"])
      (is (= ["f" "g"] @seen)))))

(deftest search-budget-exhaustion
  (with-redefs [legacy/grind (fn [ps hints] (main/grind ps hints {:gen 1}))]
    (is (re-find #"gen budget exhausted"
                 (cs/attempt '[v2_generation_limit [p :- (=> Nat Prop), g :- (=> Nat Nat), a :- Nat,
                                                    h :- (forall [x :- Nat] (=> (p x) (p (g x)))), ha :- (p a)]
                               (p (g (g a))) [(grind)]] 10000))))
  (with-redefs [legacy/grind (fn [ps hints] (main/grind ps hints {:splits 0}))]
    (is (re-find #"splits budget exhausted"
                 (cs/attempt '[v2_split_limit [p :- Prop, q :- Prop]
                               (=> (Or p q) (Or p (Not q)) (Or (Not p) q) (Or (Not p) (Not q)) False)
                               [(grind)]] 10000)))))

(deftest unsuccessful-proof-does-not-change-environment
  (with-redefs [legacy/grind main/grind]
    (let [before @a/ansatz-env
          result (cs/attempt '[v2_invalid_branch [p :- Prop, q :- Prop, h :- (Or p q)] p [(grind)]] 10000)]
      (is (re-find #"stuck" result))
      (is (identical? before @a/ansatz-env) "failed proof leaves the environment untouched"))))

(deftest regression-local-quantified-facts
  (doseq [script
          '[[regr_irrelevant
             [p :- Prop, hp :- p, h :- (forall [x :- Nat] (= x x))]
             p [(grind)]]
            [regr_and_forall
             [p :- (=> Nat Prop), a :- Nat, h :- (And (forall [x :- Nat] (p x)) True)]
             (p a) [(grind)]]
            [regr_or_forall
             [p :- (=> Nat Prop), a :- Nat,
              h :- (Or (forall [x :- Nat] (p x)) (forall [x :- Nat] (p x)))]
             (p a) [(grind)]]
            [regr_graph_forall
             [p :- (=> Nat Prop), q :- (=> Nat Prop), a :- Nat,
              h :- (forall [x :- Nat] (p x)),
              heq :- (Eq Prop (forall [x :- Nat] (p x)) (forall [x :- Nat] (q x)))]
             (q a) [(grind)]]
            [regr_nested
             [p :- (=> Nat Prop), q :- (=> Nat Prop), f :- (=> Nat Nat), a :- Nat, b :- Nat,
              h :- (forall [x :- Nat] (=> (p (f x)) (q x))), heq :- (= (f a) b), hp :- (p b)]
             (q a) [(grind)]]
            [regr_nested_backtrack
             [p :- (=> Nat Nat Prop), q :- (=> Nat Prop), f :- (=> Nat Nat), a :- Nat, b :- Nat, c :- Nat,
              h :- (forall [x :- Nat] (=> (p (f x) x) (q x))),
              ha :- (= (f a) b), hc :- (= (f c) b), hp :- (p b a)]
             (q a) [(grind)]]]]
    (check-script script)))

(deftest pattern-unavailable-is-not-malformed-metadata
  (let [nat (e/const' (name/from-string "Nat") [])
        eq (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
        type (e/forall' "x" nat (e/app* eq nat (e/bvar 0) (e/bvar 0)) :default)
        st (tc/mk-tc-state (a/env))]
    (is (nil? (theorem/compile-theorem st [:local 900] (e/fvar 900) type [])))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"malformed theorem patterns"
                          (theorem/compile-theorem st [:local 900] (e/fvar 900) type [] [(e/bvar 0)])))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not a proposition"
                          (theorem/compile-theorem st [:local 900] (e/fvar 900)
                                                   (e/forall' "x" nat nat :default) [])))))

(deftest actual-alternatives-have-isolated-search-state
  ;; Neither disjunct is known. Each alternative activates its own forall and
  ;; instantiates it at a, contradicting the corresponding negative fact. The
  ;; synthetic local ID (and hence instance key) is intentionally the same in
  ;; both alternatives, so leaking seen-instances would prevent the second proof.
  (let [splits (atom []) entries (atom []) instances (atom [])
        split-next @#'main/split-next solve main/solve instantiate @#'main/instantiate]
    (with-redefs-fn
      {#'main/split-next (fn [branch candidate]
                           (swap! splits conj {:parent branch :candidate candidate})
                           (split-next branch candidate))
       #'main/solve (fn [branch]
                      (when (some #(e/forall? (:prop %)) (:raw-facts branch))
                        (swap! entries conj branch))
                      (solve branch))
       #'main/instantiate (fn [branch]
                            (let [result (instantiate branch)]
                              (when (> (:num-instances result) (:num-instances branch))
                                (swap! instances conj {:before branch :after result}))
                              result))}
      #(check-script '[regr_fork
                       [p :- (=> Nat Prop), q :- (=> Nat Prop), a :- Nat,
                        h :- (Or (forall [x :- Nat] (p x)) (forall [x :- Nat] (q x))),
                        np :- (Not (p a)), nq :- (Not (q a))]
                       False [(grind)]]))
    (is (= 1 (count @splits)) "the kernel-checked proof really split")
    (is (= 2 (count @entries)) "both alternatives executed")
    (is (= 2 (count @instances)) "both alternatives generated their own instance")
    (let [{:keys [parent candidate]} (first @splits)
          [left right] @entries
          [li ri] @instances]
      (is (= :or (:kind candidate)))
      (doseq [alternative @entries]
        (is (identical? (:graph parent) (:graph alternative)) "fork starts from the parent graph")
        (is (= (:facts parent) (:facts alternative)))
        (is (= (:theorems parent) (:theorems alternative)))
        (is (= (:seen parent) (:seen alternative)))
        (is (= (:num-instances parent) (:num-instances alternative))))
      (is (not (identical? (:tc left) (:tc right))) "proof contexts are separate")
      (is (not= (:lctx (:tc left)) (:lctx (:tc right))) "the local has the alternative's type")
      (is (= [0 1] (mapv :num-splits @entries)))
      (is (= [1 1] (mapv #(get-in % [:raw-facts 0 :gen]) @entries)))
      (doseq [{:keys [before after]} @instances]
        (is (= 1 (count (:theorems before))))
        (is (= 1 (get-in before [:theorems 0 :gen])) "activation retains split generation")
        (is (= 2 (get-in after [:raw-facts 0 :gen])) "instance generation includes activation")
        (is (empty? (:seen before)))
        (is (= 1 (count (:seen after)))))
      (is (= (:seen (:after li)) (:seen (:after ri))) "the same key is independently usable in each sibling")
      (is (empty? (:seen parent)))
      (is (empty? (:theorems parent))))))

(deftest structure-projection-from-constructor-class
  (eval '(ansatz.core/structure V2Pair [] (x Nat) (y Nat)))
  (check-script '[v2_projection [p :- V2Pair, x :- Nat, y :- Nat, h :- (= p (V2Pair.mk x y))]
                  (= (:x p) x) [(grind)]]))

(deftest symmetric-equality-proposition-proof
  ;; Nested surface `=` is executable Bool equality; use the raw Prop statement.
  (let [nat (e/const' (name/from-string "Nat") [])
        eq (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
        a (e/bvar 1) b (e/bvar 0)
        body (e/app* eq (e/sort' lvl/zero) (e/app* eq nat a b) (e/app* eq nat b a))
        goal (e/forall' "a" nat (e/forall' "b" nat body :default) :default)
        [ps _] (proof/start-proof (a/env) goal)
        solved (main/grind ps)
        term (extract/extract solved)]
    (is (proof/solved? solved))
    (is (some? (env/check-constant (a/env)
                                   (env/mk-thm (name/from-string "v2_raw_symmetry") [] goal term))))))

(deftest stage2-required-conformance
  (with-redefs [legacy/grind main/grind]
    (cs/check-suite "grind_v2 stage2"
                    (cs/run-suite 'ansatz.grind-conformance-test @#'conformance/defs
                                  (keep-indexed (fn [i script] (when-not (#{16 17} i) script))
                                                @#'conformance/theorems)
                                  :timeout-ms 20000)
                    {})))

(deftest bool-discriminant-split-proof
  (check-script '[v2_unknown_if [b :- Bool, x :- Nat] (= (if b x x) x) [(grind)]]))

(deftest refuted-quantifier-propagation
  (doseq [script
          '[[regr_neg_forall
             [p :- (=> Nat Prop), h :- (Not (forall [x :- Nat] (p x)))]
             (Exists Nat (fn [x :- Nat] (Not (p x)))) [(grind)]]
            [regr_neg_exists
             [p :- (=> Nat Prop), a :- Nat, h :- (Not (Exists Nat p))]
             (Not (p a)) [(grind)]]
            [regr_false_forall
             [p :- (=> Nat Prop), h :- (Eq Prop (forall [x :- Nat] (p x)) False)]
             (Exists Nat (fn [x :- Nat] (Not (p x)))) [(grind)]]
            [regr_false_exists
             [p :- (=> Nat Prop), a :- Nat, h :- (Eq Prop (Exists Nat p) False)]
             (Not (p a)) [(grind)]]]]
    (check-script script)))

(deftest definition-equation-inventory
  (let [before (a/env)]
    (try
      (a/define-verified 'iv-app '[xs :- (List Nat), ys :- (List Nat)] '(List Nat)
        '(match xs [nil ys] [(cons h t) (List.cons Nat h (iv-app t ys))]))
      (a/define-verified 'iv-choose '[xs :- (List Nat), b :- Bool] 'Nat
        '(match xs [nil 0] [(cons h t) (if b h 0)]))
      (a/define-verified 'iv-id '[x :- Nat] 'Nat 'x)
      (is (nil? (eqns/eqns-for before "iv-app")) "the inventory is persistent")
      (is (= ["iv-app.eq_1" "iv-app.eq_2"] (mapv name/->string (eqns/eqns-for (a/env) 'iv-app))))
      (is (= ["iv-id.eq_1"] (mapv name/->string (eqns/eqns-for (a/env) 'iv-id))))
      (let [names (mapv name/->string (eqns/eqns-for (a/env) "iv-choose"))]
        ;; Lean's default nonrecursive Eqns.getEqnsFor? installs one unfold equation;
        ;; equations for its matcher are generated separately on demand.
        (is (= ["iv-choose.eq_1"] names))
        (let [matcher "iv-choose.match_1"
              eqs (:eqn-names (match-eqns/get-equations-for matcher))]
          (is (= 2 (count eqs)))
          (is (= eqs (mapv name/->string (eqns/eqns-for (a/env) matcher))))))
      (doseq [definition ["iv-app" "iv-choose" "iv-id"]]
        (is (empty? (eqns/errors-for (a/env) definition)))
        (doseq [nm (eqns/eqns-for (a/env) definition)]
          (let [ci (env/lookup (a/env) nm)]
            (is (= :thm (env/ci-tag ci)))
            (is (some? (env/check-constant (a/env)
                                           (env/mk-thm (name/from-string (str "iv-check-" (name/->string nm)))
                                                       (vec (.levelParams ci)) (.type ci) (.value ci))))))))
      (let [st (tc/mk-tc-state (a/env))]
        (is (= (eqns/eqns-for (a/env) "iv-app")
               (mapv :origin (theorem/for-hint st "iv-app")))))
      (check-script '[iv_equation [h :- Nat, t :- (List Nat), ys :- (List Nat)]
                      (= (iv-app (List.cons Nat h t) ys) (List.cons Nat h (iv-app t ys)))
                      [(grind [iv-app])]])
      (check-script '[iv_simple [x :- Nat] (= (iv-id x) x) [(grind [iv-id])]])
      (finally (reset! a/ansatz-env before)))))

(deftest failed-equation-inventory-is-diagnostic
  (let [before (a/env) check env/check-constant]
    (try
      (with-redefs [env/check-constant
                    (fn [environment ci]
                      (if (= "iv-failed.eq_1" (name/->string (.name ci)))
                        (throw (ex-info "injected equation admission failure" {:kind :test-failure}))
                        (check environment ci)))]
        (a/define-verified 'iv-failed '[xs :- (List Nat)] 'Nat
          '(match xs [nil 0] [(cons h t) h])))
      (is (empty? (eqns/eqns-for (a/env) "iv-failed")))
      (is (= "iv-failed.eq_1" (:lemma (first (eqns/errors-for (a/env) "iv-failed")))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"equation generation errors"
                            (theorem/for-hint (tc/mk-tc-state (a/env)) "iv-failed")))
      (finally (reset! a/ansatz-env before)))))

(deftest elementary-nat-normalization
  (check-script '[v2_nat_add [a :- Nat, b :- Nat]
                  (= (+ (+ a b) 1) (+ (+ a 1) b)) [(grind)]]))

(deftest bool-branch-keeps-the-recursive-call-node
  (let [before (a/env)]
    (try
      (a/define-verified 'iv-branch-app '[xs :- (List Nat), ys :- (List Nat)] '(List Nat)
        '(match xs [nil ys] [(cons h t) (List.cons Nat h (iv-branch-app t ys))]))
      (check-script '[v2_recursive_branch [xs :- (List Nat), b :- Bool,
                                           h :- (= (iv-branch-app xs (List.nil Nat)) xs)]
                      (= (if b (iv-branch-app xs (List.nil Nat)) xs) xs) [(grind)]])
      (finally (reset! a/ansatz-env before)))))

(deftest normalization-depth-is-a-named-limit
  (with-redefs [legacy/grind (fn [ps hints] (main/grind ps hints {:max-rec-depth 1}))]
    (is (re-find #"maximum recursion depth exceeded"
                 (cs/attempt '[v2_norm_limit [a :- Nat, b :- Nat]
                               (= (+ a b) (+ b a)) [(grind)]] 10000)))))

(deftest equality-true-propagates-to-endpoints
  (check-script '[v2_beq_chain [a :- Nat, b :- Nat, c :- Nat,
                                h1 :- (= (Nat.beq a b) true), h2 :- (= (Nat.beq b c) true)]
                  (= a c) [(grind)]]))

(deftest boolean-order-bridge-is-automatic
  (check-script '[v2_ble_bridge [a :- Nat, b :- Nat, h :- (= (Nat.ble a b) true)]
                  (<= a b) [(grind)]])
  (check-script '[regr_nat_order_complement [a :- Nat, b :- Nat, h :- (Not (<= a b))]
                  (<= b a) [(grind)]]))

(deftest round3-implication-and-value-regressions
  (doseq [script
          '[[regr_imp_cases [p :- Prop, q :- Prop, h1 :- (=> p q), h2 :- (=> (Not p) q)]
             q [(grind)]]
            [regr_contraposition [p :- Prop, q :- Prop, r :- Prop,
                                  h1 :- (=> p q), h2 :- (=> (Not p) r), hn :- (Not q)]
             r [(grind)]]
            [regr_nat_conflict [a :- Nat, h0 :- (= a 0), h1 :- (= a 1)]
             False [(grind)]]]]
    (check-script script))
  (check-script '[regr_string_conflict
                  [s :- String, h0 :- (= s "a"), h1 :- (= s "b")]
                  False [(grind)]]))

(deftest inductive-predicate-introduction-and-cases
  (let [before (a/env)]
    (try
      (eval '(ansatz.core/inductive RegrTag [] :in Prop :indices [l (List Nat)]
                                    (empty :where [(nil)])
                                    (single [x Nat] :where [(cons x nil)])))
      (check-script '[regr_pred_goal [x :- Nat] (RegrTag (List.cons Nat x (List.nil Nat))) [(grind)]])
      (check-script '[regr_pred_hyp [l :- (List Nat), h :- (RegrTag l),
                                     hn :- (Not (= l (List.nil Nat))),
                                     hs :- (forall [x :- Nat] (Not (= l (List.cons Nat x (List.nil Nat)))))]
                      False [(grind)]])
      (finally (reset! a/ansatz-env before)))))

(deftest congruence-retains-shared-intermediate-arguments
  (check-script '[regr_partial_congr [f :- (=> Nat Nat Nat Nat), g :- (=> Nat Nat Nat Nat),
                                      x :- Nat, y :- Nat, z :- Nat, h :- (= f g)]
                  (= (f x y z) (g x y z)) [(grind)]]))

(deftest implication-split-option-executes-the-path
  (let [splits (atom 0) split-next @#'main/split-next]
    (with-redefs [legacy/grind (fn [ps hints] (main/grind ps hints {:split-imp true}))
                  main/split-next (fn [branch candidate]
                                    (when (= :imp (:kind candidate)) (swap! splits inc))
                                    (split-next branch candidate))]
      (is (= :ok (cs/attempt
                  '[regr_imp_split [p :- Prop, q :- Prop,
                                    h1 :- (=> p q), h2 :- (=> p (Not q)),
                                    h3 :- (=> (Not p) q), h4 :- (=> (Not p) (Not q))]
                    False [(grind)]] 10000)))
      (is (pos? @splits) "the proof executes the implication split path"))))

(deftest arithmetic-predicates-do-not-unroll-by-default
  (with-redefs [legacy/grind (fn [ps hints] (main/grind ps hints {:splits 0}))]
    (is (re-find #"grind_v2: stuck"
                 (cs/attempt '[regr_arith_cases_default
                               [a :- Nat, b :- Nat, h :- (<= a b)] False [(grind)]] 10000))
        "a satisfiable arithmetic fact must not start inductive cases or spend the split budget")))

(deftest ground-preprocessing-without-solvers
  ;; Paired in test/lean/grind_solvers.lean. With solvers disabled, these proofs
  ;; require preprocessing to connect the closed computation to its value.
  (a/defn v2-ground-quot [n Nat] Nat (quot n 2))
  (with-redefs [solvers/check (constantly nil)]
    (doseq [script
            '[[v2_ground_definition [] (= Nat (v2-ground-quot 0) 0) [(grind)]]
              [v2_ground_nat [] (= Nat (+ (quot 17 3) (rem 17 3)) 7) [(grind)]]
              [v2_ground_int [] (= Int (Int.add (Int.neg (Int.ofNat 9)) (Int.ofNat 4)) (Int.neg (Int.ofNat 5))) [(grind)]]
              [v2_ground_bool [] (= Bool (Nat.blt 3 7) true) [(grind)]]
              [v2_ground_prop [] (< Nat 3 7) [(grind)]]
              [v2_ground_false [] (Not (< Nat 9 3)) [(grind)]]
              [v2_ground_subterm [n :- Nat] (And (< Nat 3 7) (= n n)) [(grind)]]]]
      (check-script script))))

(deftest arithmetic-branch-facts
  ;; Disjunctive bounds are part of the asserted branch state.
  (check-script
   '[v2_arith_branches [a :- Nat, b :- Nat,
                        h :- (Or (< a b) (< b a))]
     (Not (= a b)) [(grind)]])
  ;; Omega does not instantiate universal hypotheses. The arithmetic fact must
  ;; come from grind's E-matcher and be passed with its derived proof.
  (check-script
   '[v2_arith_ematch [f :- (=> Nat Nat), n :- Nat,
                      h :- (forall [x :- Nat] (= (f x) 0)), hn :- (< n (f n))]
     False [(grind)]]))

(deftest solver-not-applicable-and-faults
  (let [[ps _] (proof/start-proof (a/env) (e/const' (name/from-string "False") []))
        branch {:ps ps :tc (tc/mk-tc-state (a/env)) :facts {}}]
    (is (nil? (solvers/check branch)) "consistent branch is an ordinary mismatch")
    (with-redefs [omega-proof/decides? (fn [& _] (throw (NullPointerException. "search bug")))]
      (is (thrown-with-msg? NullPointerException #"search bug" (solvers/check branch))))
    (with-redefs [omega-proof/decides? (constantly true)
                  omega/omega (fn [_] (throw (ex-info "certificate bug" {:kind :tactic-error})))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"certificate bug" (solvers/check branch))))))

(deftest regression-dependent-ground-preprocessing
  ;; Regression: simp must preserve the dependent Decidable and
  ;; branch domains when normalizing the closed condition. Kernel checks admission.
  (check-script
   '[regr_ground_dite []
     (= Nat (dite (< Nat 3 7)
                  (fn [h :- (< Nat 3 7)] 1)
                  (fn [h :- (Not (< Nat 3 7))] 2)) 1)
     [(grind)]]))

(deftest regression-applied-conditionals
  (doseq [script
          '[[regr_ite_apply
             [p :- Prop, d :- (Decidable p), hp :- p,
              f :- (=> Nat Nat), g :- (=> Nat Nat), x :- Nat]
             (= ((ite p f g) x) (f x)) [(grind)]]
            [regr_ite_apply_false
             [p :- Prop, d :- (Decidable p), hp :- (Not p),
              f :- (=> Nat Nat Nat), g :- (=> Nat Nat Nat), x :- Nat, y :- Nat]
             (= ((ite p f g) x y) (g x y)) [(grind)]]
            [regr_dite_apply
             [p :- Prop, d :- (Decidable p), hp :- p,
              f :- (=> p Nat Nat), g :- (=> (Not p) Nat Nat), x :- Nat]
             (= ((dite p f g) x) (f hp x)) [(grind)]]
            [regr_dite_apply_false
             [p :- Prop, d :- (Decidable p), hp :- (Not p),
              f :- (=> Nat Nat Nat), g :- (=> Nat Nat Nat), x :- Nat, y :- Nat]
             (= ((dite p (fn [h :- p] f) (fn [h :- (Not p)] g)) x y) (g x y)) [(grind)]]]]
    (check-script script)))

(deftest regression-applied-conditional-split
  (let [splits (atom 0) split-next @#'main/split-next]
    (with-redefs [main/split-next (fn [branch candidate]
                                    (when (= :imp (:kind candidate)) (swap! splits inc))
                                    (split-next branch candidate))]
      (check-script
       '[regr_ite_apply_split
         [p :- Prop, d :- (Decidable p), f :- (=> Nat Nat), g :- (=> Nat Nat), x :- Nat]
         (Or (= ((ite p f g) x) (f x)) (= ((ite p f g) x) (g x))) [(grind)]])
      (is (pos? @splits) "applied conditional executes the condition split path"))))
