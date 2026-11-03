(ns ansatz.surface.binop-test
  "Type-directed arithmetic (#78) — the Init-only half.

  Lean elaborates arithmetic through `binop%`: it reads the operand tree's type and emits the
  heterogeneous class operator, with numeric literals becoming `OfNat.ofNat T n inst`. The
  Mathlib half (`(mul Real …)`, `OfNat` at a field) is exercised by
  `ansatz.theory.convergence-test`; here we pin the parts a plain Init env can see — the
  Nat/Int class operators, n-ary folding, and compatibility with hand-built kernel operations."
  (:require [clojure.walk]
            [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.surface.elaborate :as el]
            [ansatz.codegen :as cg]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]
            [ansatz.kernel.env]
            [ansatz.kernel.name]))

(defn- init-once [f]
  (binding [a/*verbose* false] (a/load-init!) (f)))

(use-fixtures :once init-once)

(defn- elab-str [form]
  (e/->string (el/elaborate (a/env) form)))

(deftest explicit-type-arithmetic-on-nat
  (testing "Nat +, -, * use class operators; power and division retain concrete mappings"
    (is (re-find #"HMul\.hMul" (elab-str '(forall [a Nat b Nat] (= Nat (mul Nat a b) a)))))
    (is (re-find #"HAdd\.hAdd" (elab-str '(forall [a Nat b Nat] (= Nat (add Nat a b) a)))))
    (is (re-find #"HSub\.hSub" (elab-str '(forall [a Nat b Nat] (= Nat (sub Nat a b) a)))))
    (is (re-find #"Nat\.div" (elab-str '(forall [a Nat b Nat] (= Nat (div Nat a b) a)))))
    (is (re-find #"Nat\.pow" (elab-str '(forall [a Nat b Nat] (= Nat (pow Nat a b) a))))))
  (testing "and agrees with the operator spelling"
    (is (= (elab-str '(forall [a Nat b Nat] (= Nat (mul Nat a b) a)))
           (elab-str '(forall [a Nat b Nat] (= Nat (* a b) a)))))))

(deftest nary-arithmetic-folds-left
  (binding [a/*verbose* false]
    (a/defn sum3 [a Nat b Nat c Nat] Nat (+ a b c))
    (is (= 6 (sum3 1 2 3)))
    (a/defn diff3 [a Nat b Nat c Nat] Nat (- a b c))
    (is (= 5 (diff3 10 2 3)))))

(deftest explicit-type-forms-do-not-shadow-real-names
  (testing "`mul`/`add`/... are ordinary identifiers: a definition of that name still applies"
    ;; wandler's semiring surface defines several of these, so the (op T a b) forms fire only on
    ;; that exact shape and only when the name resolves to nothing. The env is restored
    ;; afterwards — these definitions would otherwise shadow `mul`/`add` for every later test.
    (let [saved @a/ansatz-env]
      (try
        (binding [a/*verbose* false]
          (a/defn mul [a Nat b Nat] Nat (* a b))
          (a/defn add [a Nat b Nat] Nat (+ a b))
          (is (= 12 (mul 3 4)))
          (is (= 7 (add 3 4)))
          (is (re-find #"mul" (elab-str '(forall [a Nat b Nat] (= Nat (mul a b) a))))))
        (finally (reset! a/ansatz-env saved))))))

(deftest apply-bridges-kernel-op-and-class-operator
  (testing "an explicit Nat.add goal still matches an Init lemma stated with HAdd"
    (binding [a/*verbose* false]
      (a/prove-theorem 'le-add-one '[n :- Nat]
                       '(<= Nat n (Nat.add n 1))
                       '[(apply Nat.le_add_right)])
      (is (some? (ansatz.kernel.env/lookup (a/env)
                                           (ansatz.kernel.name/from-string "le-add-one")))))))

(deftest generic-carriers-determine-arithmetic-and-numeral-types
  (let [saved @a/ansatz-env]
    (try
      (binding [a/*verbose* false]
        (doseq [[n goal]
                [['genericDistribute '(= R (* x (+ y z)) (+ (* x y) (* x z)))]
                 ['genericNumeral '(= R (+ x 2) (+ 2 x))]
                 ['genericExpected '(= R (+ 2 2) 4)]
                 ['genericExpectedNary '(= R (+ 1 2 3) 6)]
                 ['genericNested '(= R (* (+ 2 3) x) (* 5 x))]
                 ['genericNary '(= R (* (+ 1 2 3) x) (* 6 x))]
                 ['genericExplicit '(= R (mul R (+ 2 3) x) (* 5 x))]]]
          (a/prove-theorem n
                           '[R :- Type, s :- (Lean.Grind.CommSemiring R) :inst,
                             x :- R, y :- R, z :- R]
                           goal '[(ring)])
          (let [ci (ansatz.kernel.env/lookup! (a/env)
                                              (ansatz.kernel.name/from-string (str n)))]
            (is (ansatz.kernel.env/verifies? (a/env) (.type ci) (.value ci))
                (str n))))
        (a/prove-theorem 'genericSubtract
                         '[R :- Type, s :- (Lean.Grind.CommRing R) :inst, x :- R, y :- R]
                         '(= R (- (+ x y) y) x) '[(ring)])
        (let [ci (ansatz.kernel.env/lookup! (a/env)
                                            (ansatz.kernel.name/from-string "genericSubtract"))]
          (is (ansatz.kernel.env/verifies? (a/env) (.type ci) (.value ci)))))
      (finally (reset! a/ansatz-env saved)))))

(deftest numeral-defaulting-waits-for-ordinary-inference
  (doseq [[carrier form] [["Nat" '(List.replicate 3 2)]
                          ["Int" '(List.cons 2 (List.nil Int))]]]
    (let [term (el/elaborate (a/env) form)
          type (e/app (e/const' (ansatz.kernel.name/from-string "List") [lvl/zero])
                      (e/const' (ansatz.kernel.name/from-string carrier) []))]
      (is (some? (ansatz.kernel.env/check-constant
                  (a/env) (ansatz.kernel.env/mk-def
                           (ansatz.kernel.name/from-string (str "numeralDefault" carrier))
                           [] type term)))))))

(deftest nat-operators-use-lean-instances
  (doseq [[op method cls inst] [['+ "HAdd.hAdd" "instHAdd" "instAddNat"]
                                ['- "HSub.hSub" "instHSub" "instSubNat"]
                                ['* "HMul.hMul" "instHMul" "instMulNat"]]
          operands [[] [2] [2 3]]]
    (let [term (el/elaborate (a/env) (cons op operands))
          [head args] (e/get-app-fn-args term)
          [inst-head inst-args] (e/get-app-fn-args (nth args 3))]
      (is (= method (ansatz.kernel.name/->string (e/const-name head))))
      (is (= (+ 4 (count operands)) (count args)))
      (is (= ["Nat" "Nat" "Nat"] (mapv e/->string (take 3 args))))
      (is (= cls (ansatz.kernel.name/->string (e/const-name inst-head))))
      (is (= ["Nat" inst] (mapv e/->string inst-args))))))

(deftest nat-codegen-retains-concrete-runtime-operations
  (doseq [[op primitive] [['+ 'Nat.add] ['- 'Nat.sub] ['* 'Nat.mul]]]
    (let [compile-form #(cg/ansatz->clj (a/env) (el/elaborate (a/env) %) [])
          surface (compile-form (list 'fn '[x Nat y Nat] (list op 'x 'y)))
          concrete (compile-form (list 'fn '[x Nat y Nat] (list primitive 'x 'y)))]
      (is (= concrete surface))
      (doseq [[x y] [[0 4] [9 2] [9223372036854775807N 2]]]
        (is (= (((eval concrete) x) y) (((eval surface) x) y)))))))

(deftest simp-packs-concrete-nat-operations
  (doseq [[primitive method lemma] [['Nat.add "HAdd.hAdd" 'Nat.add_eq]
                                    ['Nat.sub "HSub.hSub" 'Nat.sub_eq]
                                    ['Nat.mul "HMul.hMul" 'Nat.mul_eq]]
          only? [false true]]
    (let [target (el/elaborate (a/env)
                               (list 'forall '[f (arrow Nat Nat) x Nat y Nat]
                                     (list '= 'Nat (list 'f (list primitive 'x 'y)) 7)))
          [ps _] (proof/start-proof (a/env) target)
          ps (basic/intros ps ["f" "x" "y"])
          before (e/->string (:type (proof/current-goal ps)))
          ps (simp/simp ps (if only? [lemma] []) {:only? only?})
          after (e/->string (:type (proof/current-goal ps)))]
      ;; No hypothesis or reflexive goal can close this proof independently of simp.
      (is (.contains before (str primitive)))
      (is (.contains after method))
      (is (not (.contains after (str primitive)))))))

(deftest nat-instance-is-ready-before-dependent-argument-checking
  (let [target (el/elaborate
                (a/env)
                '(forall [P Prop xs (List Nat) hd Nat j Nat v Nat
                          h (= (Option Nat) (List.get?Internal xs j) (Option.some Nat v))
                          ih (forall [k Nat value Nat]
                                     (arrow (= (Option Nat) (List.get?Internal (List.cons Nat hd xs) k)
                                               (Option.some Nat value)) P))] P))
        [ps _] (proof/start-proof (a/env) target)
        ps (basic/intros ps ["P" "xs" "hd" "j" "v" "h" "ih"])
        ;; Inspect the application BEFORE strict/collecting finalization can synthesize
        ;; pending instances. A completed theorem alone does not establish this timing.
        ready? (fn []
                 (let [est (#'el/attach-elab-lctx (#'el/mk-elab-state (a/env))
                                                  (:lctx (proof/current-goal ps)))
                       partial (#'el/elab-term est '(ih (+ j 1) v))
                       index (first (e/get-app-args partial))
                       pending? (#'el/has-unsolved-mvar? est index)
                       term (#'el/elab-term est '(ih (+ j 1) v h))]
                   (is (= "HAdd.hAdd" (ansatz.kernel.name/->string (e/const-name (e/get-app-fn index)))))
                   (is (e/app? term))
                   (not pending?)))
        postponed-hop (fn [est cls method A B C & args]
                        (let [u (#'el/type-sort-level est A)
                              v (#'el/type-sort-level est B)
                              w (#'el/type-sort-level est C)
                              goal (e/app* (e/const' (ansatz.kernel.name/from-string cls) [u v w]) A B C)]
                          (apply e/app* (e/const' (ansatz.kernel.name/from-string method) [u v w])
                                 A B C (#'el/inst-mvar! est goal) args)))]
    (is (ready?) "the instance must be ready while checking subsequent dependent arguments")
    (with-redefs-fn {#'el/elab-hop postponed-hop}
      #(is (not (ready?)) "control: disabling eager synthesis fails the readiness requirement"))))

(deftest nat-operator-values-preserve-primitive-calling-conventions
  (let [compile-form #(eval (cg/ansatz->clj (a/env) (el/elaborate (a/env) %) []))
        outcome (fn [f args]
                  (try
                    (let [v (apply f args)]
                      (if (fn? v) [:partial (v 2)] [:value v]))
                    (catch clojure.lang.ArityException _ :arity-error)))]
    (doseq [[op primitive] [['+ 'Nat.add] ['- 'Nat.sub] ['* 'Nat.mul]]
            [form concrete] [[op primitive] [(list op) (list primitive)]
                             [(list op 5) (list primitive 5)]]
            args [[] [5] [5 2] [5 2 3]]]
      (is (= (outcome (compile-form concrete) args) (outcome (compile-form form) args))
          (pr-str [form args])))
    (doseq [[op primitive] [['+ 'Nat.add] ['- 'Nat.sub] ['* 'Nat.mul]]]
      (let [f (compile-form (list op))]
        (is (= (f 5 2) ((f 5) 2)))
        (doseq [form [(list 'List.foldl op 10 '(List.cons Nat 5 (List.cons Nat 2 (List.nil Nat))))
                      (list 'List.map (list op 5) '(List.cons Nat 2 (List.cons Nat 3 (List.nil Nat))))]]
          (let [concrete (clojure.walk/postwalk-replace {op primitive} form)]
            (is (= (compile-form concrete) (compile-form form)))))))))
