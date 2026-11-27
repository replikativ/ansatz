(ns ansatz.tactic.splitter-no-confusion-test
  "The equation simplification of the matcher splitter (basic/unify-eq, Lean injectionCore) goes
   through the shared AppBuilder.mkNoConfusion: indexed families, heterogeneous majors, and proof
   fields that contribute no equality. Lean parity: test/lean-parity/dsl/splitter_no_confusion.lean."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.config :as config]
            [ansatz.inductive :as ind]
            [ansatz.surface.elaborate :as elab]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.proof :as proof]
            [ansatz.test-env :as test-env]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]))

(def ^:private unify-log (atom []))

(defn- with-env [f]
  (let [saved @a/ansatz-env
        saved-tactic (get @a/tactic-registry 'unify-h)]
    (try
      (reset! a/ansatz-env @test-env/bundled-init-env)
      (binding [a/*verbose* false]
        ;; D α : Nat → Type with both constructors at index (n+1), as in the parity file
        (ind/define-inductive (a/env) "SplD" '[α Type]
          [['a '[n Nat x α] ['(Nat.succ n)]] ['b '[n Nat x α y α] ['(Nat.succ n)]]] :indices '[k Nat])
        (ind/define-inductive (a/env) "SplP" [] [['mk '[n Nat h (< 0 n)]]])
        (ind/define-inductive (a/env) "SplS" [] [['l '[n Nat]] ['r '[n Nat]]])
        (ind/define-inductive (a/env) "SplI" [] [['a '[n Nat] ['(Nat.succ n)]] ['b '[n Nat] ['(Nat.succ n)]]]
          :indices '[k Nat])
        ;; no noConfusion at definition: the splitter realizes it on demand
        (ind/define-inductive (a/env) "SplQ" [] [['q '[n Nat]] ['r '[n Nat]]] :no-confusion? false))
      (a/register-tactic! 'unify-h
                          (fn [ps _]
                            (let [g (proof/current-goal ps)
                                  hid (some (fn [[id d]] (when (= "h" (str (:name d))) id)) (:lctx g))
                                  r (basic/unify-eq ps hid)]
                              (swap! unify-log conj (select-keys r [:status :num-new-eqs]))
                              (:ps r))))
      (f)
      (finally
        (reset! a/ansatz-env saved)
        (if saved-tactic
          (swap! a/tactic-registry assoc 'unify-h saved-tactic)
          (swap! a/tactic-registry dissoc 'unify-h))))))

(use-fixtures :once with-env)

(defn- prove [params target tactics]
  (reset! unify-log [])
  (binding [a/*verbose* false]
    (a/prove-theorem (gensym "splitter_nc_") params target tactics))
  @unify-log)

(deftest different-constructors-of-an-indexed-family
  (testing "noConfusion_of_Nat over SplD.ctorIdx applied to the parameter AND the index"
    (is (= [{:status :solved :num-new-eqs 0}]
           (prove '[x :- Nat, y :- Nat, z :- Nat, h :- (= (SplD Nat 1) (SplD.a 0 x) (SplD.b 0 y z))]
                  'False '[(unify-h)])))))

(deftest same-constructor-of-an-indexed-family
  (testing "the per-constructor noConfusion takes the index equality and `heq_of_eq h`"
    (is (= [{:status :continue :num-new-eqs 2}]
           (prove '[x :- Nat, y :- Nat, h :- (= (SplD Nat 1) (SplD.a 0 x) (SplD.a 0 y))]
                  '(= Nat x y) '[(unify-h) (intro hn hx) (exact (eq_of_heq hx))])))))

(deftest proof-fields-contribute-no-equality
  (testing "Lean injectionCore: numFields - getCtorNumPropFields new equalities"
    (is (= [{:status :continue :num-new-eqs 1}]
           (prove '[n :- Nat, m :- Nat, hn :- (< 0 n), hm :- (< 0 m), h :- (= SplP (SplP.mk n hn) (SplP.mk m hm))]
                  '(= Nat n m) '[(unify-h) (intro e) (exact e)])))))

(deftest nat-constructors
  (is (= [{:status :continue :num-new-eqs 1}]
         (prove '[n :- Nat, m :- Nat, h :- (= Nat (Nat.succ n) (Nat.succ m))] '(= Nat n m)
                '[(unify-h) (intro e) (exact e)])))
  (is (= [{:status :solved :num-new-eqs 0}]
         (prove '[n :- Nat, h :- (= Nat (Nat.succ n) 0)] 'False '[(unify-h)]))))

(deftest split-on-an-indexed-family
  (testing "`split` on a match over SplD simplifies its branch equations; the surviving branch uses them"
    (binding [a/*verbose* false config/*lean-matchers* true]
      (a/define-verified 'spl-tag '[d :- (SplD Nat 1)] 'Nat '(match d (SplD.a n x) 0 (SplD.b n x y) x))
      (let [ty (elab/elaborate (a/env) '(forall [x :- Nat, y :- Nat, f :- (=> Nat Nat)]
                                                (= (spl-tag (SplD.b 0 (f x) y)) (f x))))
            [ps _] (proof/start-proof (a/env) ty)
            ps (-> ps (basic/intros ["x" "y" "f"]) (a/run-tactic '(unfold spl-tag)))
            ps (a/run-tactic ps '(split))]
        (is (= 1 (count (proof/goals ps))) "the SplD.a branch is impossible")
        (is (some? (extract/verify (basic/all-goals ps #(a/run-tactic % '(rfl))))))))))

(deftest parameterless-indexed-family
  (is (= [{:status :solved :num-new-eqs 0}]
         (prove '[h :- (= (SplI 1) (SplI.a 0) (SplI.b 0))] 'False '[(unify-h)]))))

(deftest partially-applied-constructors-are-not-values
  (testing "`SplS.l = SplS.r` is an equality of functions: no constructor clash"
    (let [ty (elab/elaborate (a/env) '(forall [h :- (= (=> Nat SplS) SplS.l SplS.r)] False))
          [ps _] (proof/start-proof (a/env) ty)
          ps (basic/intro ps "h")
          hid (some (fn [[id d]] (when (= "h" (str (:name d))) id)) (:lctx (proof/current-goal ps)))]
      (is (= :tactic-error (try (basic/unify-eq ps hid) nil
                                (catch clojure.lang.ExceptionInfo ex (:kind (ex-data ex)))))))))

(deftest constructors-exposed-by-structure-eta
  (testing "the builder receives the sides as unify-eq recognized them"
    (is (= [{:status :solved :num-new-eqs 0}]
           (prove ['p :- '(Prod Nat Nat), 'n :- 'Nat,
                   'h :- (list '= 'Nat (list (symbol "@Prod.rec.{1,0,0}") 'Nat 'Nat '(fn [_ :- (Prod Nat Nat)] Nat)
                                             '(fn [a :- Nat, b :- Nat] Nat.zero) 'p)
                               '(Nat.succ n))]
                  'False '[(unify-h)])))))

(def ^:private no-ctor-idx-env
  ;; the bundled Init without Nat.ctorIdx, as a dependency closure may omit it (trust replay)
  (delay
    (parser/with-parser-state
      (parser/parse-ndjson-string @test-env/bundled-init-text)
      (fn [parsed]
        (test-env/with-instance-registry
          (:env (replay/replay (remove #(= "Nat.ctorIdx" (str (.name ^ansatz.kernel.ConstantInfo %))) (:decls parsed))
                               :verify? false :stop-on-error? true)))))))

(deftest a-nat-clash-without-ctor-idx
  (let [saved @a/ansatz-env]
    (try
      (reset! a/ansatz-env @no-ctor-idx-env)
      (is (nil? (env/lookup (a/env) (name/from-string "Nat.ctorIdx"))))
      (is (= [{:status :solved :num-new-eqs 0}]
             (prove '[n :- Nat, h :- (= Nat (Nat.succ n) 0)] 'False '[(unify-h)]))
          "Nat.noConfusion closes it, as before")
      (finally (reset! a/ansatz-env saved)))))

(deftest a-realized-no-confusion-survives-a-later-split
  (testing "SplQ.q.noConfusion realized by the first split is still there for the final check"
    (binding [a/*verbose* false config/*lean-matchers* true]
      (is (nil? (env/lookup (a/env) (name/from-string "SplQ.q.noConfusion"))))
      (a/define-verified 'spl-q '[d :- SplQ] 'Nat '(match d (SplQ.q n) n (SplQ.r n) 0))
      (a/define-verified 'spl-b '[b :- Bool] 'Nat '(match b true 1 false 0))
      (let [ty (elab/elaborate (a/env) '(forall [x :- Nat, f :- (=> Nat Nat), b :- Bool]
                                                (= (+ (spl-q (SplQ.q (f x))) (spl-b b))
                                                   (+ (f x) (spl-b b)))))
            [ps _] (proof/start-proof (a/env) ty)
            ps (-> ps (basic/intros ["x" "f" "b"]) (a/run-tactic '(unfold spl-q)) (a/run-tactic '(split)))
            ps (-> ps (a/run-tactic '(unfold spl-b)) (a/run-tactic '(split)))]
        (is (some? (env/lookup (a/env) (name/from-string "SplQ.q.noConfusion"))))
        (is (some? (extract/verify (basic/all-goals ps #(a/run-tactic % '(rfl))))))))))
