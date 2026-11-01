(ns ansatz.tactic.instance-lean-test
  "Instance synthesis against Lean 4's own behaviour. Each case is a small in-memory environment
   (bundled Init plus a few axioms) whose expected result was established by running the same
   declarations through Lean 4.33.1 (`#synth`, `show_term`, `DiscrTree.getUnify`); the Lean
   source of every case is quoted in its docstring."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.test-env :as test-env]
            [ansatz.config :as config]
            [ansatz.meta :as meta]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.instance :as inst]
            [ansatz.tactic.instance-index :as ii]))

(defn- base [] (or @test-env/checked-bundled-init-env (throw (ex-info "bundled Init unavailable" {}))))

(def ^:private nm name/from-string)
(defn- c [s & ls] (e/const' (nm s) (vec ls)))
(def ^:private u1 (lvl/succ lvl/zero))
(def ^:private type0 (e/sort' u1))
(def ^:private type1 (e/sort' (lvl/succ u1)))
(defn- pi [n d b & [bi]] (e/forall' n d b (or bi :default)))

(defn- with-decls
  "Bundled Init plus axioms [name type] (or [name type :def value] for an abbrev), the classes
   `classes`, and a registry of [class instance priority] rows in declaration order."
  [decls classes rows]
  (let [env (reduce (fn [en [n ty kind value lps]]
                      (env/check-constant en (if (= kind :def)
                                               (env/mk-def (nm n) (or lps []) ty value :hints :abbrev)
                                               (env/mk-axiom (nm n) (or lps []) ty))))
                    (base) decls)
        env (env/with-extension env :classes (into (env/get-extension env :classes #{}) classes))
        registry (inst/parse-instance-tsv (map (fn [[cl i p]] (str cl "\t" i "\t" (or p 1000))) rows))]
    [env registry]))

(defn- synth
  ([env registry goal] (synth (tc/mk-tc-state env) env registry goal))
  ([st env registry goal] (inst/synthesize* st env registry goal 0)))

(defn- head-name [x] (some-> x e/get-app-fn e/const-name name/->string))

(deftest lean-name-hash-and-order
  (testing "Lean's Name.hash (printed by Lean 4.33.1), which orders DiscrTree children"
    (is (= (unchecked-long 11442535297760353691) (ii/lean-name-hash (nm "Nat"))))
    (is (= (unchecked-long 7316284823769321069) (ii/lean-name-hash (nm "LE.le"))))
    (is (= (unchecked-long 13235980228967245028) (ii/lean-name-hash (nm "instAddNat"))))
    (is (= 564683908580357674 (ii/lean-name-hash (name/mk-num (nm "x") 3))))
    (is (= 1 (ii/name-quick-cmp (nm "Nat") (nm "Int"))) "`Nat.quickLt Int` is false, `Int.quickLt Nat` true")))

(deftest instance-keys-and-synth-order-match-lean
  (testing "mkInstanceKey and computeSynthOrder of Init instances, as Lean prints them"
    (let [env (base)
          ctx (ii/mk-ctx env (inst/index-for env))
          show (fn [k] (case (k 0) :const (str (k 1) "/" (k 2)) :star "*" (pr-str k)))
          data (fn [n] (let [d (ii/entry-data ctx (nm n))] [(mapv show (:keys d)) (:synth-order d)]))]
      (is (= [["Decidable/1" "Eq/3" "Nat/0" "*" "*"] []] (data "instDecidableEqNat")))
      (is (= [["Decidable/1" "And/2" "*" "*"] [2 3]] (data "instDecidableAnd")))
      (is (= [["OfNat/2" "Nat/0" "*"] []] (data "instOfNatNat")))
      (is (= [["HAdd/3" "*" "*" "*"] [1]] (data "instHAdd")))
      (is (= [["Decidable/1" "LE.le/4" "Nat/0" "*" "*" "*"] []] (data "Nat.decLe")))
      (is (= [["Decidable/1" "Eq/3" "List/1" "*" "*" "*"] [1]] (data "instDecidableEqList")))
      (is (= [["BEq/1" "*"] [1]] (data "instBEqOfDecidableEq"))))))

(deftest synth-order-out-params-first
  (testing "`instance fl [Mul' A] [Mul' B] [MulHomClass' F A B] : FunLike' F A B` (A, B out-params):
            Lean's synthOrder is #[5, 3, 4]"
    (let [[env registry] (with-decls [["Mul'" (pi "A" type0 type0)]
                                      ["FunLike'" (pi "F" type0 (pi "A" (e/app (c "outParam" (lvl/succ u1)) type0)
                                                                    (pi "B" (e/app (c "outParam" (lvl/succ u1)) type0) type0)))]
                                      ["MulHomClass'" (pi "F" type0 (pi "A" (e/app (c "outParam" (lvl/succ u1)) type0)
                                                                        (pi "B" (e/app (c "outParam" (lvl/succ u1)) type0) type0)))]
                                      ["fl" (pi "F" type0 (pi "A" type0 (pi "B" type0
                                                                            (pi "i1" (e/app (c "Mul'") (e/bvar 1))
                                                                                (pi "i2" (e/app (c "Mul'") (e/bvar 1))
                                                                                    (pi "i3" (e/app* (c "MulHomClass'") (e/bvar 4) (e/bvar 3) (e/bvar 2))
                                                                                        (e/app* (c "FunLike'") (e/bvar 5) (e/bvar 4) (e/bvar 3))
                                                                                        :inst-implicit) :inst-implicit) :inst-implicit)
                                                                            :implicit) :implicit) :implicit)]]
                           #{"Mul'" "FunLike'" "MulHomClass'"}
                           [["FunLike'" "fl"]])
          ctx (ii/mk-ctx env registry)]
      (is (= [5 3 4] (:synth-order (ii/entry-data ctx (nm "fl"))))))))

(deftest candidate-order-is-lean-get-unify
  (testing "class PairC (α β : Type); specific : PairC Nat Bool; specificInt : PairC Nat Int;
            generic : PairC Nat β; specificString : PairC Nat String (in that order).
            Lean's getUnify on `PairC Nat ?m` returns [generic, specificString, specificInt,
            specific] (children by name hash) and on `PairC Nat Bool` [generic, specific]; the
            try order is the reverse"
    (let [[env registry] (with-decls [["PairC" (pi "a" type0 (pi "b" type0 type0))]
                                      ["specific" (e/app* (c "PairC") (c "Nat") (c "Bool"))]
                                      ["specificInt" (e/app* (c "PairC") (c "Nat") (c "Int"))]
                                      ["generic" (pi "β" type0 (e/app* (c "PairC") (c "Nat") (e/bvar 0)) :implicit)]
                                      ["specificString" (e/app* (c "PairC") (c "Nat") (c "String"))]]
                           #{"PairC"}
                           [["PairC" "specific"] ["PairC" "specificInt"] ["PairC" "generic"] ["PairC" "specificString"]])
          st (tc/mk-tc-state env)
          names #(mapv str %)]
      (is (= ["specific" "generic"] (names (inst/candidates env registry (e/app* (c "PairC") (c "Nat") (c "Bool"))))))
      (let [mctx (meta/add-expr-mvar-decl meta/empty-context 77 type0 (:lctx st))
            ctx (#'inst/synth-ctx env registry)]
        (is (= ["specific" "specificInt" "specificString" "generic"]
               (mapv (comp str :name :global)
                     (rseq (#'inst/get-instances* ctx mctx st (e/app* (c "PairC") (c "Nat") (e/mvar 77))))))))
      (testing "getMatch (query metavariables match only stars): Lean returns [generic] for
                `PairC Nat ?m` and [generic, specific] for `PairC Nat Bool`"
        (let [mctx (meta/add-expr-mvar-decl meta/empty-context 78 type0 (:lctx st))
              state (:state (#'inst/synth-ctx env registry))
              roots #(#'inst/root-trie state %)]
          (is (= ["generic"] (mapv (comp str :name) (ii/get-match mctx st roots (e/app* (c "PairC") (c "Nat") (e/mvar 78))))))
          (is (= ["generic" "specific"] (mapv (comp str :name) (ii/get-match mctx st roots (e/app* (c "PairC") (c "Nat") (c "Bool"))))))))
      (testing "an older specific instance beats a newer generic one at equal priority
                (Lean: #synth PairC Nat Bool = specific, PairC Nat Nat = generic)"
        (is (= "specific" (head-name (synth env registry (e/app* (c "PairC") (c "Nat") (c "Bool"))))))
        (is (= "specificInt" (head-name (synth env registry (e/app* (c "PairC") (c "Nat") (c "Int"))))))
        (is (= "generic" (head-name (synth env registry (e/app* (c "PairC") (c "Nat") (c "Nat"))))))))))

(deftest reducible-alias-in-keys
  (testing "abbrev Alias := Type; class K (α : Type 1); class Missing;
            instance (priority := high) kType : K Type; instance kGen [Missing] : K α.
            Lean: #synth K Alias = kType (keys are normalised by reducible whnf)"
    (let [[env registry] (with-decls [["Alias" type1 :def type0]
                                      ["K" (pi "α" type1 type0)]
                                      ["Missing" type0]
                                      ["kType" (e/app (c "K") type0)]
                                      ["kGen" (pi "α" type1 (pi "m" (c "Missing") (e/app (c "K") (e/bvar 1)) :inst-implicit) :implicit)]]
                           #{"K" "Missing"}
                           [["K" "kType" 10000] ["K" "kGen" 1000]])]
      (is (= (c "kType") (synth env registry (e/app (c "K") (c "Alias")))))
      (is (= (c "kType") (synth env registry (e/app (c "K") type0)))))))

(deftest semi-out-param-readiness
  (testing "class Source (α : semiOutParam Type); class Target (α : outParam Type);
            instance srcNat : Source Nat; instance tgt [Source α] : Target α.
            Lean: #synth Target Nat = tgt"
    (let [[env registry] (with-decls [["Source" (pi "α" (e/app (c "semiOutParam" (lvl/succ u1)) type0) type0)]
                                      ["Target" (pi "α" (e/app (c "outParam" (lvl/succ u1)) type0) type0)]
                                      ["srcNat" (e/app (c "Source") (c "Nat"))]
                                      ["tgt" (pi "α" type0 (pi "s" (e/app (c "Source") (e/bvar 0)) (e/app (c "Target") (e/bvar 1)) :inst-implicit) :implicit)]]
                           #{"Source" "Target"}
                           [["Source" "srcNat"] ["Target" "tgt"]])]
      (is (= (e/app* (c "tgt") (c "Nat") (c "srcNat")) (synth env registry (e/app (c "Target") (c "Nat"))))))))

(deftest out-param-cycle-is-tabled
  (testing "class Foo (α : Type) (β : outParam Type); instance base : Foo Nat Bool;
            instance (priority := high) loop [Foo α β] : Foo α β.
            Lean: #synth Foo Nat Bool = base — the loop's subgoal is the goal itself, a consumer of
            its own table entry, not a deeper copy"
    (let [[env registry] (with-decls [["Foo" (pi "α" type0 (pi "β" (e/app (c "outParam" (lvl/succ u1)) type0) type0))]
                                      ["base" (e/app* (c "Foo") (c "Nat") (c "Bool"))]
                                      ["loop" (pi "α" type0 (pi "β" type0 (pi "i" (e/app* (c "Foo") (e/bvar 1) (e/bvar 0))
                                                                              (e/app* (c "Foo") (e/bvar 2) (e/bvar 1)) :inst-implicit)
                                                                :implicit) :implicit)]]
                           #{"Foo"}
                           [["Foo" "base"] ["Foo" "loop" 10000]])]
      (is (= (c "base") (synth env registry (e/app* (c "Foo") (c "Nat") (c "Bool")))))
      (testing "and no answer for a goal only the loop matches"
        (is (nil? (synth env registry (e/app* (c "Foo") (c "Int") (c "Bool")))))))))

(deftest root-out-param-no-backtracking
  (testing "class Out (α : Type) (β : outParam Type); instance (priority := high) outNat : Out Nat Nat;
            instance outBool : Out Nat Bool. Lean: #synth Out Nat Bool FAILS (the first answer for
            `Out Nat ?β` is outNat, which conflicts, and the search is not resumed);
            #synth Out Nat Nat = outNat"
    (let [[env registry] (with-decls [["Out" (pi "α" type0 (pi "β" (e/app (c "outParam" (lvl/succ u1)) type0) type0))]
                                      ["outNat" (e/app* (c "Out") (c "Nat") (c "Nat"))]
                                      ["outBool" (e/app* (c "Out") (c "Nat") (c "Bool"))]]
                           #{"Out"}
                           [["Out" "outNat" 10000] ["Out" "outBool"]])]
      (is (nil? (synth env registry (e/app* (c "Out") (c "Nat") (c "Bool")))))
      (is (= (c "outNat") (synth env registry (e/app* (c "Out") (c "Nat") (c "Nat"))))))))

(deftest quantified-goal
  (testing "class C; instance ci : C. Lean: #synth (Nat → C) = fun a => ci"
    (let [[env registry] (with-decls [["C" type0] ["ci" (c "C")]] #{"C"} [["C" "ci"]])
          r (synth env registry (pi "a" (c "Nat") (c "C")))]
      (is (= (e/lam "a" (c "Nat") (c "ci") :default) r))
      (is (tc/is-def-eq (tc/mk-tc-state env) (tc/infer-type (tc/mk-tc-state env) r) (pi "a" (c "Nat") (c "C")))))))

(deftest local-instances-newest-first-and-polymorphic
  (testing "example [i1 : D] [i2 : D] : D := inferInstance — Lean picks i2"
    (let [[env registry] (with-decls [["D" type0]] #{"D"} [])
          st (tc/mk-tc-state-with-locals env {100 {:name "i1" :type (c "D")} 101 {:name "i2" :type (c "D")}})]
      (is (= (e/fvar 101) (synth st env registry (c "D"))))))
  (testing "example [h : ∀ n : Nat, CN n] : CN 3 := inferInstance — Lean: h 3"
    (let [[env registry] (with-decls [["CN" (pi "n" (c "Nat") type0)]] #{"CN"} [])
          st (tc/mk-tc-state-with-locals env {100 {:name "h" :type (pi "n" (c "Nat") (e/app (c "CN") (e/bvar 0)))}})]
      (is (= (e/app (e/fvar 100) (e/lit-nat 3)) (synth st env registry (e/app (c "CN") (e/lit-nat 3))))))))

(deftest explicit-arguments-are-not-subgoals
  (testing "def User.toD : C → E; attribute [instance] User.toD; instance ci : C.
            Lean: #synth E fails — only instance-implicit binders are synthesized, whatever the
            declaration is called"
    (let [[env registry] (with-decls [["C" type0] ["E" type0] ["ci" (c "C")] ["User.toD" (pi "x" (c "C") (c "E"))]]
                           #{"C" "E"}
                           [["C" "ci"] ["E" "User.toD"]])]
      (is (nil? (synth env registry (c "E")))))))

(deftest cache-respects-local-instances-and-registry
  (let [[env registry] (with-decls [["C" type0] ["ci" (c "C")]] #{"C"} [["C" "ci"]])
        empty-registry {}]
    (testing "a local instance answers; after attach-lctx drops it, the cached answer is not reused"
      (let [st (tc/mk-tc-state-with-locals env {100 {:name "i" :type (c "C")}})]
        (is (= (e/fvar 100) (synth st env empty-registry (c "C"))))
        (let [st' (tc/attach-lctx st (red/empty-lctx))]
          (is (nil? (synth st' env empty-registry (c "C"))))
          (testing "…and a cached failure does not survive adding it back"
            (is (= (e/fvar 100) (synth (tc/attach-lctx st' (:lctx st)) env empty-registry (c "C"))))))))
    (testing "a registry change is a different problem on the same tc-state"
      (let [st (tc/mk-tc-state env)]
        (is (nil? (synth st env empty-registry (c "C"))))
        (is (= (c "ci") (synth st env registry (c "C"))))))))

(deftest deep-chains-and-the-result-size-bound
  (testing "class Ch (α : Type); instance ch0 : Ch Nat; instance chS [Ch α] : Ch (List α).
            Lean (synthInstance.maxSize 128): Ch (List^127 Nat) succeeds, Ch (List^128 Nat) fails"
    (let [[env registry] (with-decls [["Ch" (pi "α" type0 type0)]
                                      ["ch0" (e/app (c "Ch") (c "Nat"))]
                                      ["chS" (pi "α" type0 (pi "i" (e/app (c "Ch") (e/bvar 0)) (e/app (c "Ch") (e/app (c "List" lvl/zero) (e/bvar 1))) :inst-implicit) :implicit)]]
                           #{"Ch"}
                           [["Ch" "ch0"] ["Ch" "chS"]])
          lists (fn [k] (nth (iterate #(e/app (c "List" lvl/zero) %) (c "Nat")) k))]
      (is (some? (synth env registry (e/app (c "Ch") (lists 20)))) "deeper than the old depth bound of 16")
      (is (some? (synth env registry (e/app (c "Ch") (lists 127)))))
      (is (nil? (synth env registry (e/app (c "Ch") (lists 128))))))))

(deftest universe-output-parameters
  (testing "class U.{u} (α : Type) (β : outParam (Type u)); instance instU : U.{2} Nat (ULift.{2} Nat).
            Lean: `U Nat _` (universe and type unknown) synthesizes instU, fixing u := 2"
    (let [u (nm "u")
          [env registry] (with-decls [["U" (pi "α" type0 (pi "β" (e/app (c "outParam" (lvl/succ (lvl/succ (lvl/param u)))) (e/sort' (lvl/succ (lvl/param u)))) type0)) nil nil [u]]
                                      ["instU" (e/app* (c "U" (lvl/from-nat 2)) (c "Nat") (e/app (c "ULift" (lvl/from-nat 2) lvl/zero) (c "Nat")))]]
                           #{"U"}
                           [["U" "instU"]])
          st (tc/mk-tc-state env)
          mctx (-> meta/empty-context (meta/add-level-mvar-decl 500))
          mctx (meta/add-expr-mvar-decl mctx 501 (e/sort' (lvl/succ (lvl/mvar 500))) (:lctx st))
          [mctx r] (inst/synth-instance mctx st registry (e/app* (c "U" (lvl/mvar 500)) (c "Nat") (e/mvar 501)))]
      (is (= (c "instU") r))
      (is (= 2 (lvl/to-nat (meta/zonk-level mctx (lvl/mvar 500)))))
      (is (= (e/app (c "ULift" (lvl/from-nat 2) lvl/zero) (c "Nat")) (meta/zonk-expr mctx (e/mvar 501)))))))

(deftest undetermined-universes-are-not-defaulted
  (testing "class Q (α : Type); instance instQ.{w} [Inh PUnit.{w+1}] : Q Nat.
            Lean: #synth Q Nat = @instQ.{?u} … — the universe stays a metavariable"
    (let [w (nm "w")
          [env registry] (with-decls [["Q" (pi "α" type0 type0)]
                                      ["Inh" (pi "α" (e/sort' (lvl/param w)) type0) nil nil [w]]
                                      ["inhP" (e/app (c "Inh" (lvl/succ (lvl/param w))) (c "PUnit" (lvl/succ (lvl/param w)))) nil nil [w]]
                                      ["instQ" (pi "i" (e/app (c "Inh" (lvl/succ (lvl/param w))) (c "PUnit" (lvl/succ (lvl/param w))))
                                                   (e/app (c "Q") (c "Nat")) :inst-implicit) nil nil [w]]]
                           #{"Q" "Inh"}
                           [["Inh" "inhP"] ["Q" "instQ"]])
          st (tc/mk-tc-state env)
          [mctx r] (inst/synth-instance meta/empty-context st registry (e/app (c "Q") (c "Nat")))]
      (is (= "instQ" (head-name r)))
      (is (seq (meta/unassigned-level-mvars mctx r)) "a level metavariable, not level zero")
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"universe levels undetermined"
                            (synth env registry (e/app (c "Q") (c "Nat"))))))))

(deftest synth-pending-uses-the-mvar-context-and-propagates-bugs
  (let [[env registry] (with-decls [["D" type0]] #{"D"} [])
        env (env/with-extension env :instances registry)
        st (tc/mk-tc-state env)
        local {100 {:tag :local :id 100 :name "i" :type (c "D")}}]
    (testing "the metavariable's own local context supplies the local instance (mvarId.withContext)"
      (let [mctx (meta/add-expr-mvar-decl meta/empty-context 7 (c "D") local)]
        (is (= (e/fvar 100) (meta/expr-assignment (inst/synth-pending-instance mctx st 7) 7)))))
    (testing "synthesized when unification is stuck on it, and a bug is not a failed unification"
      (let [env (base)
            st (tc/mk-tc-state env)
            add-nat (e/app (c "Add" lvl/zero) (c "Nat"))
            mctx (meta/add-expr-mvar-decl meta/empty-context 7 add-nat (:lctx st))
            lhs (e/app* (c "Add.add" lvl/zero) (c "Nat") (e/mvar 7) (e/lit-nat 1) (e/lit-nat 2))]
        (let [mctx' (meta/is-def-eq mctx st lhs (e/lit-nat 3))]
          (is (some? mctx'))
          (is (= (c "instAddNat") (meta/zonk-expr mctx' (e/mvar 7)))))
        (with-redefs-fn {#'inst/synth-instance* (fn [& _] (throw (NullPointerException. "injected synthesis bug")))}
          #(is (thrown-with-msg? NullPointerException #"injected synthesis bug"
                                 (meta/is-def-eq mctx st lhs (e/lit-nat 3)))))))))

(deftest resource-bound-is-an-error
  (let [[env registry] (with-decls [["Ch" (pi "α" type0 type0)]
                                    ["ch0" (e/app (c "Ch") (c "Nat"))]
                                    ["chS" (pi "α" type0 (pi "i" (e/app (c "Ch") (e/bvar 0)) (e/app (c "Ch") (e/app (c "List" lvl/zero) (e/bvar 1))) :inst-implicit) :implicit)]]
                         #{"Ch"}
                         [["Ch" "ch0"] ["Ch" "chS"]])]
    (binding [config/*synth-max-steps* 5]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"resource bound"
                            (synth env registry (e/app (c "Ch") (nth (iterate #(e/app (c "List" lvl/zero) %) (c "Nat")) 10))))))))
