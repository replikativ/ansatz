(ns ansatz.examples-test
  "Tests that verify the examples from examples/ directory work.
   RB tree tests run against init-medium.ndjson (no Mathlib needed).
   GD convergence tests require Mathlib store (skipped if unavailable)."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

;; ============================================================
;; Environment setup (init-medium for RB tree, Mathlib for GD)
;; ============================================================

(def ^:private init-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(def ^:private baseline-state
  (delay
    (when-let [base-env @init-env]
      (let [env (env/fork base-env)
            tsv "resources/instances.tsv"
            load-tsv (requiring-resolve 'ansatz.tactic.instance/load-instance-tsv)
            build-fn (requiring-resolve 'ansatz.tactic.instance/build-instance-index)
            idx (if (.exists (java.io.File. tsv))
                  (load-tsv tsv)
                  (build-fn env))]
        (reset! a/ansatz-env env)
        (reset! a/ansatz-instance-index idx)
        (binding [a/*verbose* false]
          (when-not (env/lookup (a/env) (name/from-string "TRBColor"))
            (eval '(ansatz.core/inductive TRBColor [] (red) (black)))
            (eval '(ansatz.core/inductive TRBTree [α Type]
                                          (leaf) (node [color TRBColor] [left (TRBTree α)] [key α] [right (TRBTree α)]))))
          (when-not (env/lookup (a/env) (name/from-string "ex-sorted"))
            (eval '(ansatz.core/defn ^Bool ex-sorted [^{:- (List Nat)} l]
                     (match l (List Nat) Bool
                            (nil true) (cons [hd tl] (match tl (List Nat) Bool
                                                            (nil true) (cons [hd2 tl2] (match (<= hd hd2) Bool Bool
                                                                                              (true ih_tail) (false false))))))))
            (eval '(ansatz.core/defn ^{:- (List Nat)} ex-insertSorted [^Nat x ^{:- (List Nat)} l]
                     (match l (List Nat) (List Nat)
                            (nil (cons x nil)) (cons [hd tl] (match (<= x hd) Bool (List Nat)
                                                                    (true (cons x l)) (false (cons hd ih_tail)))))))
            (eval '(ansatz.core/defn ^{:- (List Nat)} ex-isort [^{:- (List Nat)} l]
                     (match l (List Nat) (List Nat)
                            (nil nil) (cons [hd tl] ((ex-insertSorted hd) ih_tail)))))))
        {:env @a/ansatz-env
         :idx @a/ansatz-instance-index}))))

(defn- with-baseline-env [f]
  (when-let [{:keys [env idx]} @baseline-state]
    (reset! a/ansatz-env (env/fork env))
    (reset! a/ansatz-instance-index idx)
    (f)))

(use-fixtures :each with-baseline-env)

;; ============================================================
;; Structure tests (init-medium sufficient)
;; ============================================================

(deftest test-structure-definition
  (testing "Define structures with auto-generated projections"
    (binding [a/*verbose* false]
      ;; Parameterized structure
      (when-not (env/lookup (a/env) (name/from-string "ExPair"))
        (eval '(ansatz.core/structure ExPair [α Type β Type] (fst α) (snd β))))
      (is (some? (env/lookup (a/env) (name/from-string "ExPair"))) "ExPair defined")
      (is (some? (env/lookup (a/env) (name/from-string "ExPair.mk"))) "ExPair.mk defined")
      (is (some? (env/lookup (a/env) (name/from-string "ExPair.fst"))) "ExPair.fst projection")
      (is (some? (env/lookup (a/env) (name/from-string "ExPair.snd"))) "ExPair.snd projection")
      ;; Kernel-verify projections
      (let [tc (ansatz.kernel.TypeChecker. (a/env))]
        (.setFuel tc 50000000)
        (doseq [nm ["ExPair.fst" "ExPair.snd"]]
          (let [ci (env/lookup (a/env) (name/from-string nm))]
            (is (.isDefEq tc (.inferType tc (.value ci)) (.type ci))
                (str nm " kernel-verified"))))))))

;; ============================================================
;; Well-founded recursion tests (init-medium sufficient)
;; ============================================================

(deftest test-wf-recursion-countdown
  (testing "WF recursion: countdown with match on Nat"
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "ex-countdown"))
        (eval '(ansatz.core/defn ^Nat ex-countdown [^Nat n]
                 :termination-by n
                 (match n Nat Nat (zero 0) (succ [pred] (+ 1 (ex-countdown pred)))))))
      (is (some? (env/lookup (a/env) (name/from-string "ex-countdown")))
          "countdown defined with WF recursion")
      ;; Kernel verification: the definition type-checks
      (let [tc (ansatz.kernel.TypeChecker. (a/env))
            _ (.setFuel tc 50000000)
            ci (env/lookup (a/env) (name/from-string "ex-countdown"))]
        (is (.isDefEq tc (.inferType tc (.value ci)) (.type ci))
            "countdown kernel-verified")))))

(deftest test-wf-recursion-factorial
  (testing "WF recursion: factorial with if on Bool"
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "ex-fact"))
        (eval '(ansatz.core/defn ^Nat ex-fact [^Nat n]
                 :termination-by n
                 (if (== n 0) 1 (* n (ex-fact (- n 1)))))))
      (is (some? (env/lookup (a/env) (name/from-string "ex-fact")))
          "factorial defined with WF recursion")
      (let [tc (ansatz.kernel.TypeChecker. (a/env))
            _ (.setFuel tc 50000000)
            ci (env/lookup (a/env) (name/from-string "ex-fact"))]
        (is (.isDefEq tc (.inferType tc (.value ci)) (.type ci))
            "factorial kernel-verified")))))

(deftest test-wf-recursion-multi-arg
  (testing "WF recursion: multi-arg with compound measure"
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "ex-myadd"))
        (eval '(ansatz.core/defn ^Nat ex-myadd [^Nat x ^Nat y]
                 :termination-by (+ x y)
                 (match x Nat Nat (zero y) (succ [k] (+ 1 (ex-myadd k y)))))))
      (is (some? (env/lookup (a/env) (name/from-string "ex-myadd")))
          "multi-arg WF function defined")
      (let [tc (ansatz.kernel.TypeChecker. (a/env))
            _ (.setFuel tc 50000000)
            ci (env/lookup (a/env) (name/from-string "ex-myadd"))]
        (is (.isDefEq tc (.inferType tc (.value ci)) (.type ci))
            "multi-arg WF function kernel-verified")))))

(deftest test-wf-termination-is-checked
  (testing "`:termination-by` is an honest proof: a measure that does not decrease is rejected"
    (binding [a/*verbose* false]
      ;; eb n = eb n with measure n: the recursive arg does NOT decrease → must be rejected
      ;; (guard-aware decrease obligation `n ≠ 0 → n < n` is discharged by omega and fails).
      (let [msg (try
                  (eval '(ansatz.core/defn ^Nat ex-eb [^Nat n]
                           :termination-by n
                           (if (== n 0) 0 (ex-eb n))))
                  "NO-THROW"
                  (catch Throwable e
                    (->> (iterate #(some-> ^Throwable % .getCause) e)
                         (take-while some?) (map #(str (.getMessage ^Throwable %)))
                         (clojure.string/join " "))))]
        (is (re-find #"not provably decreasing|terminates|termination" msg)
            "non-terminating :termination-by definition is rejected with an actionable error")
        (is (not (env/lookup (a/env) (name/from-string "ex-eb")))
            "the rejected function is not added to the environment")))))

(defn- uses-wf-fix?
  "Does this definition's value contain WellFounded.Nat.fix (the kernel-enforced encoding,
   as opposed to the fuel Nat.rec encoding)?"
  [ci]
  (let [seen (atom false)]
    ((fn go [x] (when (and (not @seen) (instance? ansatz.kernel.Expr x))
                  (when (and (e/const? x)
                             (= "WellFounded.Nat.fix" (name/->string (e/const-name x))))
                    (reset! seen true))
                  (cond (e/app? x) (do (go (e/app-fn x)) (go (e/app-arg x)))
                        (e/lam? x) (do (go (e/lam-type x)) (go (e/lam-body x)))
                        (e/forall? x) (do (go (e/forall-type x)) (go (e/forall-body x))))))
     (.value ci))
    @seen))

(defn- run-nat-fn [fname ks]
  (let [r (.getReducer (doto (ansatz.kernel.TypeChecker. (a/env)) (.setFuel 80000000)))]
    (mapv #(e/->string (.whnf r (e/app (e/const' (name/from-string fname) []) (e/lit-nat %)))) ks)))

(deftest test-wf-fix-nonstructural-nested-match
  (testing "Stage 1b: non-structural nested-match recursion is encoded as kernel-ENFORCED
            WellFounded.Nat.fix (decrease proof in the term), and computes correctly"
    (binding [a/*verbose* false]
      ;; div2 recurses on n-2 (nested match) — NOT structural; the fuel encoding would also work,
      ;; but this must take the WellFounded.Nat.fix path so termination is kernel-checked, not trusted.
      (when-not (env/lookup (a/env) (name/from-string "ex-div2"))
        (eval '(ansatz.core/defn ^Nat ex-div2 [^Nat n]
                 :termination-by n
                 (match n Nat Nat (zero 0)
                        (succ [p] (match p Nat Nat (zero 0)
                                         (succ [k] (Nat.succ (ex-div2 k)))))))))
      (let [ci (env/lookup (a/env) (name/from-string "ex-div2"))]
        (is (some? ci) "div2 (n-2 recursion) defined")
        (is (uses-wf-fix? ci) "div2 is encoded with kernel-enforced WellFounded.Nat.fix")
        ;; (the definition already passed check-constant in define-verified-wf — both the encoder's
        ;;  own check and the swap! check-constant — so presence in the env implies kernel-verified)
        (is (= ["0" "0" "1" "1" "2" "2" "3"] (run-nat-fn "ex-div2" (range 7)))
            "div2 computes floor(n/2)")))))

(deftest test-wf-fix-if-guarded
  (testing "Stage 1b-A: if-guarded recursion is kernel-enforced via the dite conversion
            (lean4: ite/dite are macro_inline, so the WF translation sees Decidable.casesOn
            whose constructor fields CARRY the guard — we convert Bool.rec-over-comparison
            the same way, so omega gets ¬(n=0) for the n-1 < n decrease proof)"
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "ex-fact-fix"))
        (eval '(ansatz.core/defn ^Nat ex-fact-fix [^Nat n]
                 :termination-by n
                 (if (== n 0) 1 (* n (ex-fact-fix (- n 1)))))))
      (let [ci (env/lookup (a/env) (name/from-string "ex-fact-fix"))]
        (is (some? ci) "if-guarded factorial defined")
        (is (uses-wf-fix? ci) "factorial is encoded with kernel-enforced WellFounded.Nat.fix")
        (is (= ["1" "1" "2" "6" "24" "120"] (run-nat-fn "ex-fact-fix" (range 6)))
            "factorial computes n!"))
      ;; ≤-guard variant (Nat.ble → LE.le + Nat.decLe)
      (when-not (env/lookup (a/env) (name/from-string "ex-sumto"))
        (eval '(ansatz.core/defn ^Nat ex-sumto [^Nat n]
                 :termination-by n
                 (if (<= n 0) 0 (+ n (ex-sumto (- n 1)))))))
      (let [ci (env/lookup (a/env) (name/from-string "ex-sumto"))]
        (is (uses-wf-fix? ci) "≤-guarded sum is kernel-enforced")
        (is (= ["0" "1" "3" "6" "10" "15"] (run-nat-fn "ex-sumto" (range 6)))
            "sum-to computes triangular numbers")))))

(deftest test-wf-fix-equations
  (testing "Stage 1b-D: wf-fix functions get per-leaf eq_N defining equations via
            WellFounded.fix_eq (lean4 WF/Unfold.lean rwFixEq), usable by simp both
            symbolically and on literals"
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "ex-div2"))
        (eval '(ansatz.core/defn ^Nat ex-div2 [^Nat n]
                 :termination-by n
                 (match n Nat Nat (zero 0)
                        (succ [p] (match p Nat Nat (zero 0)
                                         (succ [k] (Nat.succ (ex-div2 k)))))))))
      ;; the three leaf equations exist (f 0 = 0, f 1 = 0, f (k+2) = (f k)+1)
      (is (some? (env/lookup (a/env) (name/from-string "ex-div2.eq_1"))) "eq_1 generated")
      (is (some? (env/lookup (a/env) (name/from-string "ex-div2.eq_2"))) "eq_2 generated")
      (is (some? (env/lookup (a/env) (name/from-string "ex-div2.eq_3"))) "eq_3 generated")
      ;; simp uses them: symbolic unfold (a wf-fix value is STUCK definitionally on a
      ;; symbolic argument — only the fix_eq equations make this provable)
      (is (try (a/prove-theorem (name/from-string "div2-eq-symbolic") '[k :- Nat]
                                '(= Nat (ex-div2 (Nat.succ (Nat.succ k))) (Nat.succ (ex-div2 k)))
                                '[(simp [ex-div2])])
               true
               (catch Throwable _ false))
          "simp unfolds ex-div2 on a symbolic constructor pattern")
      ;; and literal computation through the equations
      (is (try (a/prove-theorem (name/from-string "div2-eq-lit") '[]
                                '(= Nat (ex-div2 7) 3)
                                '[(simp [ex-div2])])
               true
               (catch Throwable _ false))
          "simp computes ex-div2 7 = 3 via the equations"))))

(deftest test-wf-fix-two-arg-packed
  (testing "Stage 3-B: two-arg WF recursion is kernel-enforced via Prod packing
            (lean4 packs through PSigma.casesOn — the packing wrapper is just another
            refinable recursor for the motive-refinement machinery), with user-facing
            2-arg eq_N equations"
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "ex-add2"))
        (eval '(ansatz.core/defn ^Nat ex-add2 [^Nat x ^Nat y]
                 :termination-by (+ x y)
                 (match x Nat Nat (zero y) (succ [k] (+ 1 (ex-add2 k y)))))))
      (let [ci (env/lookup (a/env) (name/from-string "ex-add2"))]
        (is (some? ci) "two-arg WF function defined")
        (is (uses-wf-fix? ci) "two-arg function is encoded with kernel-enforced WellFounded.Nat.fix")
        ;; computes addition
        (let [r (.getReducer (doto (ansatz.kernel.TypeChecker. (a/env)) (.setFuel 80000000)))]
          (is (= "7" (e/->string (.whnf r (e/app* (e/const' (name/from-string "ex-add2") [])
                                                  (e/lit-nat 3) (e/lit-nat 4)))))
              "ex-add2 3 4 = 7"))
        ;; per-leaf equations in the user-facing 2-arg form
        (is (some? (env/lookup (a/env) (name/from-string "ex-add2.eq_1"))) "eq_1 generated")
        (is (some? (env/lookup (a/env) (name/from-string "ex-add2.eq_2"))) "eq_2 generated")))))

(deftest test-wf-fix-lexicographic-ackermann
  (testing "Stage 3-C: LEXICOGRAPHIC termination — Ackermann, the function no single Nat
            measure can handle, is kernel-enforced via the general WellFounded.fix over
            invImage (m, n) (Prod.lex Nat.lt_wfRel Nat.lt_wfRel), each recursive call
            carrying a Prod.Lex.left / Prod.Lex.right' decrease proof in the term"
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "ex-ack"))
        (eval '(ansatz.core/defn ^Nat ex-ack [^Nat m ^Nat n]
                 :termination-by [m n]
                 (match m Nat Nat
                   (zero (+ n 1))
                   (succ [k] (match n Nat Nat
                               (zero (ex-ack k 1))
                               (succ [j] (ex-ack k (ex-ack (Nat.succ k) j)))))))))
      (let [ci (env/lookup (a/env) (name/from-string "ex-ack"))]
        (is (some? ci) "Ackermann defined with lexicographic :termination-by [m n]")
        ;; uses the GENERAL WellFounded.fix (not the Nat fast path)
        (is (let [seen (atom false)]
              ((fn go [x] (when (and (not @seen) (instance? ansatz.kernel.Expr x))
                            (when (and (e/const? x)
                                       (= "WellFounded.fix" (name/->string (e/const-name x))))
                              (reset! seen true))
                            (cond (e/app? x) (do (go (e/app-fn x)) (go (e/app-arg x)))
                                  (e/lam? x) (do (go (e/lam-type x)) (go (e/lam-body x)))
                                  (e/forall? x) (do (go (e/forall-type x)) (go (e/forall-body x))))))
               (.value ci))
              @seen)
            "Ackermann is encoded with the general WellFounded.fix (lexicographic relation)")
        ;; computes the Ackermann values
        (let [r (.getReducer (doto (ansatz.kernel.TypeChecker. (a/env)) (.setFuel 200000000)))
              ack (fn [m n] (e/->string (.whnf r (e/app* (e/const' (name/from-string "ex-ack") [])
                                                         (e/lit-nat m) (e/lit-nat n)))))]
          (is (= "3" (ack 1 1)) "ack 1 1 = 3")
          (is (= "7" (ack 2 2)) "ack 2 2 = 7")
          (is (= "61" (ack 3 3)) "ack 3 3 = 61"))
        ;; the three textbook defining equations
        (is (some? (env/lookup (a/env) (name/from-string "ex-ack.eq_1"))) "ack 0 n = n+1")
        (is (some? (env/lookup (a/env) (name/from-string "ex-ack.eq_2"))) "ack (m+1) 0 = ack m 1")
        (is (some? (env/lookup (a/env) (name/from-string "ex-ack.eq_3"))) "ack (m+1) (n+1) = ack m (ack (m+1) n)"))
      ;; a non-decreasing lexicographic measure is rejected (no fuel fallback exists for lex)
      (let [msg (try (eval '(ansatz.core/defn ^Nat ex-bad-lex [^Nat m ^Nat n]
                              :termination-by [m n]
                              (match m Nat Nat (zero 0) (succ [k] (ex-bad-lex (Nat.succ k) n)))))
                     "NO-THROW"
                     (catch Throwable e (->> (iterate #(some-> ^Throwable % .getCause) e)
                                             (take-while some?) (map #(str (.getMessage ^Throwable %)))
                                             (clojure.string/join " "))))]
        (is (re-find #"terminat|lexicographic" msg)
            "non-decreasing lexicographic measure is rejected")
        (is (not (env/lookup (a/env) (name/from-string "ex-bad-lex")))
            "the rejected function is not added to the environment")))))

(deftest test-sizeof-wf-over-lists
  (testing "sizeOf-based WF over data structures: rest∘rest recursion over List Nat is
            kernel-enforced with measure (sizeOf xs) — explicit or auto-guessed — and,
            critically, has the CORRECT semantics (the old structural path silently
            mis-compiled nested-match self-calls to the inner match's IH, turning
            pairs-counting into length-1 and div2 into n-1)"
    (binding [a/*verbose* false]
      ;; explicit sizeOf measure
      (when-not (env/lookup (a/env) (name/from-string "ex-pairs"))
        (eval '(ansatz.core/defn ^Nat ex-pairs [^{:- (List Nat)} xs]
                 :termination-by (sizeOf xs)
                 (match xs (List Nat) Nat
                   (nil 0)
                   (cons [h t] (match t (List Nat) Nat
                                 (nil 0)
                                 (cons [h2 t2] (+ 1 (ex-pairs t2)))))))))
      ;; auto-guessed (no annotation) — routes through the WF path, NOT the structural
      ;; rewrite (which is only sound when the match is the entire function body)
      (when-not (env/lookup (a/env) (name/from-string "ex-pairs-au"))
        (eval '(ansatz.core/defn ^Nat ex-pairs-au [^{:- (List Nat)} xs]
                 (match xs (List Nat) Nat
                   (nil 0)
                   (cons [h t] (match t (List Nat) Nat
                                 (nil 0)
                                 (cons [h2 t2] (+ 1 (ex-pairs-au t2)))))))))
      ;; unannotated nested-match div2 over Nat — the canonical correctness regression
      (when-not (env/lookup (a/env) (name/from-string "ex-div2-au"))
        (eval '(ansatz.core/defn ^Nat ex-div2-au [^Nat n]
                 (match n Nat Nat (zero 0)
                        (succ [p] (match p Nat Nat (zero 0)
                                         (succ [k] (Nat.succ (ex-div2-au k)))))))))
      (let [r (.getReducer (doto (ansatz.kernel.TypeChecker. (a/env)) (.setFuel 200000000)))
            lnil (e/app (e/const' (name/from-string "List.nil") [lvl/zero])
                        (e/const' (name/from-string "Nat") []))
            lcons (fn [h t] (e/app* (e/const' (name/from-string "List.cons") [lvl/zero])
                                    (e/const' (name/from-string "Nat") []) (e/lit-nat h) t))
            l6 (lcons 1 (lcons 2 (lcons 3 (lcons 4 (lcons 5 (lcons 6 lnil))))))
            run (fn [f arg] (e/->string (.whnf r (e/app (e/const' (name/from-string f) []) arg))))]
        (is (= "3" (run "ex-pairs" l6)) "explicit sizeOf: pairs of 6 elements = 3")
        (is (= "3" (run "ex-pairs-au" l6)) "auto-guessed sizeOf: pairs of 6 elements = 3")
        (is (= ["0" "0" "1" "1" "2" "2" "3" "3"]
               (mapv #(run "ex-div2-au" (e/lit-nat %)) (range 8)))
            "unannotated nested-match div2 computes floor(n/2), NOT n-1")))))

(deftest test-sizeof-custom-inductive
  (testing "Custom inductives auto-derive SizeOf (instance + rfl spec equations), so
            non-structural recursion over user-defined types auto-verifies; also covers
            the recursor-rule level-param fix (rules used `u`, recursor declared `u_1` —
            iota left levels unsubstituted, breaking all symbolic defeq on custom types)"
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "ExL"))
        (eval '(ansatz.core/inductive ExL [] (enil) (econs [h Nat] [t ExL]))))
      ;; the derived machinery exists and is kernel-checked
      (is (some? (env/lookup (a/env) (name/from-string "ExL._sizeOf_inst"))) "SizeOf instance derived")
      (is (some? (env/lookup (a/env) (name/from-string "ExL.econs.sizeOf_spec"))) "cons spec equation derived")
      ;; rest∘rest over the custom type, NO annotation — auto-guessed (sizeOf xs)
      (when-not (env/lookup (a/env) (name/from-string "ex-cpairs"))
        (eval '(ansatz.core/defn ^Nat ex-cpairs [^ExL xs]
                 (match xs ExL Nat
                   (enil 0)
                   (econs [h t] (match t ExL Nat
                                  (enil 0)
                                  (econs [h2 t2] (+ 1 (ex-cpairs t2)))))))))
      (let [ci (env/lookup (a/env) (name/from-string "ex-cpairs"))]
        (is (some? ci) "non-structural recursion over the custom type auto-verified")
        (let [r (.getReducer (doto (ansatz.kernel.TypeChecker. (a/env)) (.setFuel 200000000)))
              enil (e/const' (name/from-string "ExL.enil") [])
              econs (fn [h t] (e/app* (e/const' (name/from-string "ExL.econs") []) (e/lit-nat h) t))
              m6 (econs 1 (econs 2 (econs 3 (econs 4 (econs 5 (econs 6 enil))))))]
          (is (= "3" (e/->string (.whnf r (e/app (e/const' (name/from-string "ex-cpairs") []) m6))))
              "pairs over 6 custom-list elements = 3"))))))

(deftest test-loop-recur-hoisting
  (testing "loop/recur hoisting: general loops desugar into synthesized WF helpers routed
            through the same verified pipeline (auto-measure, including lexicographic)"
    (binding [a/*verbose* false]
      ;; accumulator loop — NOT the legacy counting shape (recur args reordered)
      (when-not (env/lookup (a/env) (name/from-string "ex-sumloop"))
        (eval '(ansatz.core/defn ^Nat ex-sumloop [^Nat n]
                 (loop [acc 0 i n]
                   (if (== i 0) acc (recur (+ acc i) (- i 1)))))))
      (is (some? (env/lookup (a/env) (name/from-string "ex-sumloop"))) "accumulator loop verified")
      ;; two counters where the inner RESETS — termination needs a lexicographic measure,
      ;; found automatically for the hoisted helper
      (when-not (env/lookup (a/env) (name/from-string "ex-lexloop"))
        (eval '(ansatz.core/defn ^Nat ex-lexloop [^Nat n]
                 (loop [a n b n]
                   (match a Nat Nat
                     (zero (match b Nat Nat (zero 0) (succ [j] (+ 1 (recur a j)))))
                     (succ [i] (+ 1 (recur i n))))))))
      (is (some? (env/lookup (a/env) (name/from-string "ex-lexloop"))) "lex loop verified")
      (let [r (.getReducer (doto (ansatz.kernel.TypeChecker. (a/env)) (.setFuel 200000000)))
            run1 (fn [f k] (e/->string (.whnf r (e/app (e/const' (name/from-string f) []) (e/lit-nat k)))))]
        (is (= "15" (run1 "ex-sumloop" 5)) "sum 1..5 = 15")
        (is (= "4" (run1 "ex-lexloop" 2)) "lexloop 2 = 4 (hand-checked)")))))

(deftest test-wf-fix-three-arg-three-tuple-lex
  (testing "N-ary: a 3-arg function with a 3-tuple lexicographic measure is kernel-enforced
            (right-nested Prod packing + recursive Prod.Lex.left/right' decrease proofs)"
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "ex-lex3"))
        (eval '(ansatz.core/defn ^Nat ex-lex3 [^Nat a ^Nat b ^Nat c]
                 :termination-by [a b c]
                 (match a Nat Nat
                   (zero (match b Nat Nat
                           (zero (match c Nat Nat (zero 0) (succ [k] (+ 1 (ex-lex3 0 0 k)))))
                           (succ [j] (+ 1 (ex-lex3 0 j (+ c 2))))))
                   (succ [i] (+ 1 (ex-lex3 i (+ b 2) (+ c 2))))))))
      (let [ci (env/lookup (a/env) (name/from-string "ex-lex3"))]
        (is (some? ci) "3-arg 3-tuple lex function defined")
        ;; lower components may INCREASE when a higher one drops — only lex can verify this
        (let [r (.getReducer (doto (ansatz.kernel.TypeChecker. (a/env)) (.setFuel 200000000)))]
          (is (= "13" (e/->string (.whnf r (e/app* (e/const' (name/from-string "ex-lex3") [])
                                                   (e/lit-nat 1) (e/lit-nat 1) (e/lit-nat 1)))))
              "lex3 1 1 1 = 13 (hand-checked: 4 + f(0,0,9) = 4 + 9)"))
        (is (some? (env/lookup (a/env) (name/from-string "ex-lex3.eq_1"))) "leaf equations generated")))))

(deftest test-wf-guess-lex-measure
  (testing "GuessLex tuples: Ackermann with NO :termination-by — the auto-measure finds the
            lexicographic pair [m n] and routes through the kernel-enforced lex encoder"
    (binding [a/*verbose* false]
      (when-not (env/lookup (a/env) (name/from-string "ex-ack-auto"))
        (eval '(ansatz.core/defn ^Nat ex-ack-auto [^Nat m ^Nat n]
                 (match m Nat Nat
                   (zero (+ n 1))
                   (succ [k] (match n Nat Nat
                               (zero (ex-ack-auto k 1))
                               (succ [j] (ex-ack-auto k (ex-ack-auto (Nat.succ k) j)))))))))
      (let [ci (env/lookup (a/env) (name/from-string "ex-ack-auto"))]
        (is (some? ci) "unannotated Ackermann auto-verified via the guessed lex measure")
        (let [r (.getReducer (doto (ansatz.kernel.TypeChecker. (a/env)) (.setFuel 200000000)))]
          (is (= "61" (e/->string (.whnf r (e/app* (e/const' (name/from-string "ex-ack-auto") [])
                                                   (e/lit-nat 3) (e/lit-nat 3)))))
              "ack-auto 3 3 = 61"))))))

;; ============================================================
;; Red-Black Tree examples (init-medium sufficient)
;; ============================================================

(deftest test-rb-inductive-types
  (testing "Define RBColor and RBTree inductive types"
    (binding [a/*verbose* false]
      (let [ind-fn (requiring-resolve 'ansatz.inductive/define-inductive)]
        (ind-fn (a/env) "ExRBColor" '[] '[["red" []] ["black" []]])
        (is (some? (env/lookup (a/env) (name/from-string "ExRBColor"))))
        (is (some? (env/lookup (a/env) (name/from-string "ExRBColor.red"))))
        (is (some? (env/lookup (a/env) (name/from-string "ExRBColor.black"))))))))

(deftest test-match-bool
  (testing "Match on Bool type compiles and runs"
    (binding [a/*verbose* false]
      (let [f (a/define-verified 'ex-is-true '[^Bool b] 'Nat
                '(match b Bool Nat (true 1) (false 0)))]
        (is (fn? f))
        (is (= 1 (f true)))
        (is (= 0 (f false)))))))

(deftest test-match-rb-size
  (testing "Recursive match on RBTree with IH compiles and runs"
    (binding [a/*verbose* false]
      ;; Types defined in fixture
      ;; Define rb-size
      (let [f (a/define-verified 'ex-rb-size '[^{:- (TRBTree Nat)} t] 'Nat
                '(match t (TRBTree Nat) Nat
                        (leaf 0)
                        (node [color left key right] (+ 1 (+ ih_left ih_right)))))]
        (is (fn? f))
        ;; Test: tree with 3 nodes
        (let [tree (reduce (fn [t k] [:black t k nil]) nil [3 1 4])]
          (is (= 3 (long (f tree)))))))))

(deftest test-match-rb-member
  (testing "Nested match with IH + outer param (rb-member)"
    (binding [a/*verbose* false]
      ;; Types defined in fixture
      (let [f (a/define-verified 'ex-rb-member
                '[^{:- (TRBTree Nat)} t ^Nat k] 'Bool
                '(match t (TRBTree Nat) Bool
                        (leaf false)
                        (node [color left key right]
                              (match (< k key) Bool Bool
                                     (true ih_left)
                                     (false (match (== k key) Bool Bool
                                                   (true true)
                                                   (false ih_right)))))))]
        (is (fn? f))
        (let [tree (reduce (fn [t k] [:black t k nil]) nil [5 3 7 1 4])]
          (is (true? ((f tree) 4)))
          (is (false? ((f tree) 42)))
          (is (true? ((f tree) 1))))))))

(deftest test-match-rb-sum
  (testing "Recursive match rb-sum compiles and runs"
    (binding [a/*verbose* false]
      (let [f (a/define-verified 'ex-rb-sum '[^{:- (TRBTree Nat)} t] 'Nat
                '(match t (TRBTree Nat) Nat
                        (leaf 0)
                        (node [color left key right] (+ key (+ ih_left ih_right)))))]
        (is (fn? f))
        (let [tree (reduce (fn [t k] [:black t k nil]) nil [3 1 4])]
          (is (= 8 (long (f tree)))))))))

(deftest test-rb-theorems
  (testing "Prove RB tree properties"
    (binding [a/*verbose* false]
      ;; Prove reflexivity for leaf
      (a/prove-theorem 'ex-leaf-eq
                       '[α Type]
                       '(= Nat 0 0)
                       '[(rfl)])
      (is true "leaf theorem proved"))))

(deftest test-rb-left-le-size
  (testing "Left subtree size bounded by node size (omega)"
    (binding [a/*verbose* false]
      ;; Uses omega to prove: rb-size l ≤ 1 + (rb-size l + rb-size r)
      (let [f (a/define-verified 'ex-rb-size3 '[^{:- (TRBTree Nat)} t] 'Nat
                '(match t (TRBTree Nat) Nat
                        (leaf 0)
                        (node [color left key right] (+ 1 (+ ih_left ih_right)))))]
        (is (fn? f))
        (a/prove-theorem 'ex-left-le-size
                         '[c :- TRBColor, l :- (TRBTree Nat), k :- Nat, r :- (TRBTree Nat)]
                         '(<= Nat (ex-rb-size3 l) (+ 1 (+ (ex-rb-size3 l) (ex-rb-size3 r))))
                         '[(omega)])
        (is true "left-le-size proved by omega")))))

(deftest test-rb-balance-rotation
  (testing "Balance1 rotation correctness (universally quantified)"
    (binding [a/*verbose* false]
      ;; Define balance1 for testing
      (a/define-verified 'ex-balance1
        '[^{:- (TRBTree Nat)} l ^Nat v ^{:- (TRBTree Nat)} r] '(TRBTree Nat)
        '(match l (TRBTree Nat) (TRBTree Nat)
                (leaf (TRBTree.node Nat (TRBColor.black) (TRBTree.leaf Nat) v r))
                (node [lc ll lk lr]
                      (match lc TRBColor (TRBTree Nat)
                             (black (TRBTree.node Nat (TRBColor.black) l v r))
                             (red
                              (match ll (TRBTree Nat) (TRBTree Nat)
                                     (leaf (TRBTree.node Nat (TRBColor.black) l v r))
                                     (node [llc lll llk llr]
                                           (match llc TRBColor (TRBTree Nat)
                                                  (black (TRBTree.node Nat (TRBColor.black) l v r))
                                                  (red (TRBTree.node Nat (TRBColor.red)
                                                                     (TRBTree.node Nat (TRBColor.black) lll llk llr)
                                                                     lk
                                                                     (TRBTree.node Nat (TRBColor.black) lr v r)))))))))))
      ;; Prove left-left rotation (universally quantified)
      (a/prove-theorem 'ex-balance1-ll
                       '[a :- (TRBTree Nat), x :- Nat, b :- (TRBTree Nat),
                         y :- Nat, c :- (TRBTree Nat), v :- Nat, r :- (TRBTree Nat)]
                       '(= (TRBTree Nat)
                           (((ex-balance1
                              (TRBTree.node Nat (TRBColor.red)
                                            (TRBTree.node Nat (TRBColor.red) a x b) y c)) v) r)
                           (TRBTree.node Nat (TRBColor.red)
                                         (TRBTree.node Nat (TRBColor.black) a x b) y
                                         (TRBTree.node Nat (TRBColor.black) c v r)))
                       '[(rfl)])
      (is true "balance1 left-left rotation proved"))))

;; ============================================================
;; Verified insertion sort (init-medium sufficient)
;; Demonstrates: equation theorems, simp_all, omega, by_cases
;; This is the foundation for F*-style refinement types:
;; sorted(isort l) = true is exactly the obligation that a
;; refinement type {l' : List Nat | sorted l'} would generate.
;; ============================================================

(deftest test-isort-definitions
  (testing "Verified sort functions compile and execute correctly"
    (binding [a/*verbose* false]
      ;; Functions defined in fixture
      (is (some? (env/lookup (a/env) (name/from-string "ex-sorted"))))
      (is (some? (env/lookup (a/env) (name/from-string "ex-insertSorted"))))
      (is (some? (env/lookup (a/env) (name/from-string "ex-isort"))))
      ;; Runtime execution — List compiles to native Clojure seqs
      (let [sorted-fn @(resolve 'ex-sorted)
            isort-fn @(resolve 'ex-isort)]
        (is (true? (sorted-fn '(1 2 3))))
        (is (false? (sorted-fn '(3 1 2))))
        (is (= '(1 2 3) (isort-fn '(3 1 2))))
        (is (= '(1 1 2 3) (isort-fn '(3 1 2 1)))))
      ;; Equation theorems generated
      (is (some? (env/lookup (a/env) (name/from-string "ex-sorted.eq_1"))))
      (is (some? (env/lookup (a/env) (name/from-string "ex-insertSorted.eq_1"))))
      (is (some? (env/lookup (a/env) (name/from-string "ex-isort.eq_1")))))))

(deftest test-isort-base
  (testing "sorted(insertSorted x []) = true (base case)"
    (binding [a/*verbose* false]
      (a/prove-theorem 'ex-insert-base '[x :- Nat]
                       '(= Bool (ex-sorted ((ex-insertSorted x) nil)) true)
                       '[(simp "ex-insertSorted" "ex-sorted")])
      (is true "base case proved by simp"))))

(deftest test-isort-singleton
  (testing "sorted(insertSorted x [y]) = true (singleton, requires by_cases + omega)"
    (binding [a/*verbose* false]
      (a/prove-theorem 'ex-insert-singleton '[x :- Nat, y :- Nat]
                       '(= Bool (ex-sorted ((ex-insertSorted x) (cons y nil))) true)
                       '[(by_cases (<= x y))
                         ;; simp_all unfolds + omega handles LE goals from hypothesis decomposition
                         (all_goals (try (simp_all "ex-insertSorted" "ex-sorted")))
                         (all_goals (try (omega)))
                         (all_goals (try (simp_all "ex-insertSorted" "ex-sorted")))
                         (all_goals (try (omega)))])
      (is true "singleton case proved by by_cases + simp_all + omega"))))

(deftest test-isort-preservation
  (testing "Sorted(insertSorted x l) by induction on Prop-valued Sorted predicate"
    (binding [a/*verbose* false]
      ;; Use fresh env for full isolation
      (let [saved-env @a/ansatz-env
            fresh-env (env/fork @init-env)
            saved-idx @a/ansatz-instance-index]
        (try
          (reset! a/ansatz-env fresh-env)
          (reset! a/ansatz-instance-index saved-idx)
          (reset! @(resolve 'ansatz.tactic.simp/fun-info-cache) {})
          ;; Define insertSorted in the fresh env
          (eval '(ansatz.core/defn ^{:- (List Nat)} ex-insertSorted [^Nat x ^{:- (List Nat)} l]
                   (match l (List Nat) (List Nat)
                          (nil (cons x nil)) (cons [hd tl] (match (<= x hd) Bool (List Nat)
                                                                  (true (cons x l)) (false (cons hd ih_tail)))))))
          ;; Define Prop-valued Sorted indexed inductive:
          ;;   Sorted : List Nat → Prop
          ;;   nil    : Sorted []
          ;;   single : ∀ a, Sorted [a]
          ;;   cons_cons : ∀ a b tl, a ≤ b → Sorted (b::tl) → Sorted (a::b::tl)
          (eval '(ansatz.core/inductive Sorted [] :in Prop :indices [l (List Nat)]
                                        (nil :where [(nil)])
                                        (single [a Nat] :where [(cons a nil)])
                                        (cons_cons [a Nat] [b Nat] [tl (List Nat)]
                                                   [hab (le a b)]
                                                   [hsorted (Sorted (cons b tl))]
                                                   :where [(cons a (cons b tl))])))
          (is (some? (env/lookup (a/env) (name/from-string "Sorted")))
              "Sorted inductive defined")
          (is (some? (env/lookup (a/env) (name/from-string "Sorted.rec")))
              "Sorted.rec generated")
          ;; Prove: ∀ x l, Sorted l → Sorted (insertSorted x l)
          ;; By induction on h : Sorted l (3 cases: nil, single, cons_cons)
          ;; Note: after (induction h), goals are [nil, single, cons_cons].
          ;; simp on nil creates a replacement goal that goes to back,
          ;; so after simp the order is [single, cons_cons, nil'].
          (let [ctx (a/make-context @a/ansatz-env @a/ansatz-instance-index)]
            (a/prove-theorem 'ex-insert-preserves
                             '[x :- Nat, l :- (List Nat), h :- (Sorted l)]
                             '(Sorted ((ex-insertSorted x) l))
                             '[(induction h)
                               ;; Nil case: insertSorted x [] = [x] → Sorted.single
                               (apply (Sorted.single x))
                               ;; Case-split on x ≤ a, unfold insertSorted
                               (all_goals (try (by_cases (<= x a))))
                               (all_goals (try (simp_all "ex-insertSorted")))
                               ;; Sub-split cons_cons case on x ≤ b
                               (all_goals (try (by_cases (<= x b))))
                               (all_goals (try (simp_all "ex-insertSorted")))
                               ;; Reduce remaining Bool.rec applications
                               (all_goals (try (simp_all "ex-insertSorted")))
                               ;; Close: constructors + arithmetic + assumptions
                               (all_goals (try (apply Sorted.cons_cons)))
                               (all_goals (try (omega)))
                               (all_goals (try (apply Sorted.single)))
                               (all_goals (try (assumption)))
                               (all_goals (try (apply Sorted.cons_cons)))
                               (all_goals (try (omega)))
                               (all_goals (try (assumption)))]
                             ctx)
            (is true "preservation theorem proved by induction on Sorted"))
          (finally
            (reset! a/ansatz-env saved-env)
            (reset! a/ansatz-instance-index saved-idx)))))))

;; ============================================================
;; Grind: insertion sort preservation (Phase 1)
;; After induction, grind handles all 3 cases automatically:
;; nil (constructors), single (by_cases+simp+constructors),
;; cons_cons (nested by_cases+constructors+assumption+omega)
;; ============================================================

(deftest test-isort-preservation-grind
  (testing "Sorted(insertSorted x l) via induction + grind"
    (binding [a/*verbose* false]
      (let [saved-env @a/ansatz-env
            fresh-env (env/fork @init-env)
            saved-idx @a/ansatz-instance-index]
        (try
          (reset! a/ansatz-env fresh-env)
          (reset! a/ansatz-instance-index saved-idx)
          (reset! @(resolve 'ansatz.tactic.simp/fun-info-cache) {})
          (eval '(ansatz.core/defn ^{:- (List Nat)} ex-insertSorted [^Nat x ^{:- (List Nat)} l]
                   (match l (List Nat) (List Nat)
                          (nil (cons x nil)) (cons [hd tl] (match (<= x hd) Bool (List Nat)
                                                                  (true (cons x l)) (false (cons hd ih_tail)))))))
          (eval '(ansatz.core/inductive Sorted [] :in Prop :indices [l (List Nat)]
                                        (nil :where [(nil)])
                                        (single [a Nat] :where [(cons a nil)])
                                        (cons_cons [a Nat] [b Nat] [tl (List Nat)]
                                                   [hab (le a b)]
                                                   [hsorted (Sorted (cons b tl))]
                                                   :where [(cons a (cons b tl))])))
          (let [ctx (a/make-context @a/ansatz-env @a/ansatz-instance-index)]
            (a/prove-theorem 'ex-insert-preserves-grind
                             '[x :- Nat, l :- (List Nat), h :- (Sorted l)]
                             '(Sorted ((ex-insertSorted x) l))
                             '[(induction h)
                               (grind "ex-insertSorted")]
                             ctx)
            (is true "preservation proved by induction + grind"))
          (finally
            (reset! a/ansatz-env saved-env)
            (reset! a/ansatz-instance-index saved-idx)))))))

;; ============================================================
;; Indexed family infrastructure tests
;; Regression tests for: indexed motive construction, IH ordering,
;; equation theorem discriminant position, match l leak
;; ============================================================

(deftest test-indexed-family-induction
  (testing "Induction on indexed family over user-defined type"
    (binding [a/*verbose* false]
      ;; Define ValidRB : TRBTree Nat → Prop (indexed by user-defined type)
      (eval '(ansatz.core/inductive ValidRB [] :in Prop :indices [t (TRBTree Nat)]
                                    (vleaf :where [(TRBTree.leaf Nat)])
                                    (vnode [c TRBColor] [l (TRBTree Nat)] [k Nat] [r (TRBTree Nat)]
                                           [hl (ValidRB l)] [hr (ValidRB r)]
                                           :where [(TRBTree.node Nat c l k r)])))
      (is (some? (env/lookup (a/env) (name/from-string "ValidRB"))))
      (is (some? (env/lookup (a/env) (name/from-string "ValidRB.rec"))))
      ;; Verify Sorted.rec IH bvar lifting (Bug 3 fix)
      ;; and IH ordering (fields first, then IHs)
      (let [ctx (a/make-context @a/ansatz-env @a/ansatz-instance-index)]
        ;; Identity proof: induction with 2 recursive fields (hl, hr)
        (a/prove-theorem 'vrb-id
                         '[t :- (TRBTree Nat), h :- (ValidRB t)]
                         '(ValidRB t)
                         '[(induction h)
                           (apply ValidRB.vleaf)
                           (apply ValidRB.vnode) (assumption) (assumption)]
                         ctx)
        (is true "indexed family induction with multiple recursive fields"))
      ;; Cases on indexed family with COMPLEX index (constructor application)
      ;; Uses the generalizeIndices + noConfusion pipeline to eliminate the
      ;; impossible branch and recover the matching constructor fields.
      (let [ctx (a/make-context @a/ansatz-env @a/ansatz-instance-index)]
        ;; cases hl where hl : ValidRB(node c l k r) → ValidRB l
        (a/prove-theorem 'vrb-cases-l
                         '[c :- TRBColor, l :- (TRBTree Nat), k :- Nat, r :- (TRBTree Nat),
                           hl :- (ValidRB (TRBTree.node Nat c l k r))]
                         '(ValidRB l)
                         '[(cases hl) (assumption)]
                         ctx)
        (is true "cases on indexed family extracts ValidRB l"))
      ;; Same but extract ValidRB r (different component)
      (let [ctx (a/make-context @a/ansatz-env @a/ansatz-instance-index)]
        (a/prove-theorem 'vrb-cases-r
                         '[c :- TRBColor, l :- (TRBTree Nat), k :- Nat, r :- (TRBTree Nat),
                           hl :- (ValidRB (TRBTree.node Nat c l k r))]
                         '(ValidRB r)
                         '[(cases hl) (assumption)]
                         ctx)
        (is true "cases on indexed family extracts ValidRB r"))
      ;; cases on leaf index (opposite impossible branch)
      (let [ctx (a/make-context @a/ansatz-env @a/ansatz-instance-index)]
        (a/prove-theorem 'vrb-cases-leaf
                         '[hl :- (ValidRB (TRBTree.leaf Nat))]
                         '(Nat.le Nat.zero Nat.zero)
                         '[(cases hl) (apply Nat.le.refl)]
                         ctx)
        (is true "cases on ValidRB leaf — node branch impossible")))))

(deftest test-equation-theorem-discriminant-position
  (testing "Equation theorems for first-arg discriminant (balance1 matches on l, not r)"
    (binding [a/*verbose* false]
      ;; balance1 has eq_1 for leaf and eq_2 + splits for node
      ;; The leaf equation should be: balance1 leaf v r = node black leaf v r
      ;; NOT: balance1 v r leaf = ... (wrong discriminant position)
      (a/define-verified 'ex-balance1b
        '[^{:- (TRBTree Nat)} l ^Nat v ^{:- (TRBTree Nat)} r] '(TRBTree Nat)
        '(match l (TRBTree Nat) (TRBTree Nat)
                (leaf (TRBTree.node Nat (TRBColor.black) (TRBTree.leaf Nat) v r))
                (node [lc ll lk lr] (TRBTree.node Nat (TRBColor.black) l v r))))
      ;; Verify: eq_1 should have balance1 leaf v r on LHS
      (let [ci (env/lookup (a/env) (name/from-string "ex-balance1b.eq_1"))
            ^ansatz.kernel.TypeChecker tc (ansatz.kernel.TypeChecker. (a/env))]
        (.setFuel tc (int 50000000))
        (is (some? ci) "eq_1 exists")
        (is (.isDefEq tc (.inferType tc (.value ci)) (.type ci))
            "eq_1 type-checks (discriminant in first position)")))))

(deftest test-match-discriminant-substitution
  (testing "Match body referencing outer parameter uses ctor-applied form"
    (binding [a/*verbose* false]
      ;; insertSorted has (cons x l) in the true branch where l is the match param.
      ;; After the match compilation fix, l should be substituted with (cons hd tl).
      ;; The equation theorem eq_2 must be kernel-verifiable.
      (eval '(ansatz.core/defn ^{:- (List Nat)} ex-ins2 [^Nat x ^{:- (List Nat)} l]
               (match l (List Nat) (List Nat)
                      (nil (cons x nil)) (cons [hd tl] (match (<= x hd) Bool (List Nat)
                                                              (true (cons x l)) (false (cons hd ih_tail)))))))
      (let [^ansatz.kernel.TypeChecker tc (ansatz.kernel.TypeChecker. (a/env))]
        (.setFuel tc (int 50000000))
        (doseq [suffix ["1" "2"]]
          (let [ci (env/lookup (a/env) (name/from-string (str "ex-ins2.eq_" suffix)))]
            (is (some? ci) (str "eq_" suffix " exists"))
            (when ci
              (is (.isDefEq tc (.inferType tc (.value ci)) (.type ci))
                  (str "eq_" suffix " is kernel-verifiable")))))))))

(deftest test-balance1-leaf-preservation
  (testing "balance1 preserves ValidRB for leaf case"
    (binding [a/*verbose* false]
      ;; Uses the ValidRB from test-indexed-family-induction (already defined in fixture env)
      (when (env/lookup (a/env) (name/from-string "ValidRB"))
        (a/define-verified 'ex-bal1c
          '[^{:- (TRBTree Nat)} l ^Nat v ^{:- (TRBTree Nat)} r] '(TRBTree Nat)
          '(match l (TRBTree Nat) (TRBTree Nat)
                  (leaf (TRBTree.node Nat (TRBColor.black) (TRBTree.leaf Nat) v r))
                  (node [lc ll lk lr]
                        (match lc TRBColor (TRBTree Nat)
                               (black (TRBTree.node Nat (TRBColor.black) l v r))
                               (red
                                (match ll (TRBTree Nat) (TRBTree Nat)
                                       (leaf (TRBTree.node Nat (TRBColor.black) l v r))
                                       (node [llc lll llk llr]
                                             (match llc TRBColor (TRBTree Nat)
                                                    (black (TRBTree.node Nat (TRBColor.black) l v r))
                                                    (red (TRBTree.node Nat (TRBColor.red)
                                                                       (TRBTree.node Nat (TRBColor.black) lll llk llr)
                                                                       lk
                                                                       (TRBTree.node Nat (TRBColor.black) lr v r)))))))))))
        (let [ctx (a/make-context @a/ansatz-env @a/ansatz-instance-index)]
          ;; Leaf case: balance1 leaf v r = node black leaf v r → ValidRB
          (a/prove-theorem 'bal1-leaf-valid
                           '[v :- Nat, r :- (TRBTree Nat), hr :- (ValidRB r)]
                           '(ValidRB (((ex-bal1c (TRBTree.leaf Nat)) v) r))
                           '[(simp "ex-bal1c")
                             (apply ValidRB.vnode) (apply ValidRB.vleaf) (assumption)]
                           ctx)
          (is true "balance1 leaf case preserves ValidRB")
          ;; LL rotation case: balance1 (node red (node red a x b) y c) v r → ValidRB
          (a/prove-theorem 'bal1-ll-valid
                           '[a :- (TRBTree Nat), x :- Nat, b :- (TRBTree Nat),
                             y :- Nat, c :- (TRBTree Nat), v :- Nat, r :- (TRBTree Nat),
                             ha :- (ValidRB a), hb :- (ValidRB b),
                             hc :- (ValidRB c), hr :- (ValidRB r)]
                           '(ValidRB (((ex-bal1c
                                        (TRBTree.node Nat (TRBColor.red)
                                                      (TRBTree.node Nat (TRBColor.red) a x b) y c)) v) r))
                           '[(simp "ex-bal1c")
                             (apply ValidRB.vnode)
                             (apply ValidRB.vnode) (assumption) (assumption)
                             (apply ValidRB.vnode) (assumption) (assumption)]
                           ctx)
          (is true "balance1 LL rotation preserves ValidRB"))))))

(deftest test-cases-indexed-goal-preservation
  (testing "cases on indexed family preserves original fvars in goal (Path C)"
    (binding [a/*verbose* false]
      ;; This test verifies the core capability: after `cases hl` where
      ;; hl : ValidRB(node c l k r) and the goal references l and r
      ;; in other positions, the goal type correctly keeps l and r via
      ;; the generalizeIndices + unifyCasesEqs + noConfusion pipeline.
      (when (env/lookup (a/env) (name/from-string "ValidRB"))
        ;; Test: given hl : ValidRB(node c l k r), hr : ValidRB r
        ;; prove: ValidRB l ∧ ValidRB r (both components accessible)
        (let [ctx (a/make-context @a/ansatz-env @a/ansatz-instance-index)]
          ;; cases hl decomposes ValidRB(node c l k r) into fields with
          ;; proper substitution: hl_l : ValidRB l, hl_r : ValidRB r
          (a/prove-theorem 'vrb-decompose-both
                           '[c :- TRBColor, l :- (TRBTree Nat), k :- Nat, r :- (TRBTree Nat),
                             hl :- (ValidRB (TRBTree.node Nat c l k r)),
                             hr :- (ValidRB r)]
                           '(ValidRB r)
                           '[(cases hl) (assumption)]
                           ctx)
          (is true "cases decomposes indexed family, goal preserves fvars"))))))

(deftest test-balance1-invariant-full
  (testing "balance1 preserves ValidRB for ALL cases (full kernel-verified proof)"
    (binding [a/*verbose* false]
      ;; Define ValidRB if needed
      (when-not (env/lookup (a/env) (name/from-string "ValidRB"))
        (eval '(ansatz.core/inductive ValidRB [] :in Prop :indices [t (TRBTree Nat)]
                                      (vleaf :where [(TRBTree.leaf Nat)])
                                      (vnode [c TRBColor] [l (TRBTree Nat)] [k Nat] [r (TRBTree Nat)]
                                             [hl (ValidRB l)] [hr (ValidRB r)]
                                             :where [(TRBTree.node Nat c l k r)]))))
      (when (env/lookup (a/env) (name/from-string "ValidRB"))
        ;; Define balance1 if needed
        (when-not (env/lookup (a/env) (name/from-string "ex-bal1full"))
          (a/define-verified 'ex-bal1full
            '[^{:- (TRBTree Nat)} l ^Nat v ^{:- (TRBTree Nat)} r] '(TRBTree Nat)
            '(match l (TRBTree Nat) (TRBTree Nat)
                    (leaf (TRBTree.node Nat (TRBColor.black) (TRBTree.leaf Nat) v r))
                    (node [lc ll lk lr]
                          (match lc TRBColor (TRBTree Nat)
                                 (black (TRBTree.node Nat (TRBColor.black) l v r))
                                 (red
                                  (match ll (TRBTree Nat) (TRBTree Nat)
                                         (leaf (TRBTree.node Nat (TRBColor.black) l v r))
                                         (node [llc lll llk llr]
                                               (match llc TRBColor (TRBTree Nat)
                                                      (black (TRBTree.node Nat (TRBColor.black) l v r))
                                                      (red (TRBTree.node Nat (TRBColor.red)
                                                                         (TRBTree.node Nat (TRBColor.black) lll llk llr)
                                                                         lk
                                                                         (TRBTree.node Nat (TRBColor.black) lr v r))))))))))))
        ;; Prove: ∀ l v r, ValidRB l → ValidRB r → ValidRB(balance1 l v r)
        ;;
        ;; This is the full balance invariant for the left-left rotation case of
        ;; red-black tree insertion. The proof exercises the complete Lean 4 cases
        ;; pipeline:
        ;;
        ;; 1. cases hl (indexed family decomposition via generalizeIndices + noConfusion)
        ;;    Decomposes ValidRB(l) into vleaf (l=leaf) and vnode (l=node c ll lk lr)
        ;;    with field hypotheses hl_l : ValidRB ll, hr_l : ValidRB lr
        ;;
        ;; 2. cases c (structural with dependent hl, uses Lean 4 revert pattern)
        ;;    Splits on the color. The motive includes reverted hl so its type
        ;;    updates from ValidRB(node c ...) to ValidRB(node red/black ...)
        ;;
        ;; 3. cases l (structural on inner left subtree)
        ;;    Further decomposes for the equation theorem matching
        ;;
        ;; 4. cases color (inner color split for LL rotation detection)
        ;;
        ;; 5. cases hl (SECOND indexed decomposition for LL rotation)
        ;;    Decomposes ValidRB(node red lll llk llr) to get ValidRB lll, ValidRB llr
        ;;
        ;; 6. simp "ex-bal1full" (equation theorem simplification in each branch)
        ;;
        ;; 7. apply ValidRB.vnode + assumption (close each branch)
        ;;
        ;; Total: 7 branches, all kernel-verified via the Java TypeChecker.
        (let [ctx (a/make-context @a/ansatz-env @a/ansatz-instance-index)]
          (a/prove-theorem 'bal1-full-invariant
                           '[l :- (TRBTree Nat), v :- Nat, r :- (TRBTree Nat),
                             hl :- (ValidRB l), hr :- (ValidRB r)]
                           '(ValidRB (((ex-bal1full l) v) r))
                           '[(cases hl)
                             ;; vleaf: balance1 leaf v r = node black leaf v r
                             (simp "ex-bal1full")
                             (apply ValidRB.vnode) (apply ValidRB.vleaf) (assumption)
                             ;; vnode: cases on color (structural, hl reverted in motive)
                             (cases c)
                             ;; red: cases on inner left subtree
                             (cases l)
                             ;; red-leaf: eq_2s1
                             (simp "ex-bal1full")
                             (apply ValidRB.vnode)
                             (apply ValidRB.vnode) (apply ValidRB.vleaf) (assumption)
                             (assumption)
                             ;; red-node: cases on inner color
                             (cases color)
                             ;; LL rotation (red-red): decompose inner ValidRB
                             (cases hl)
                             (simp "ex-bal1full")
                             (apply ValidRB.vnode)
                             (apply ValidRB.vnode) (assumption) (assumption)
                             (apply ValidRB.vnode) (assumption) (assumption)
                             ;; red-black: no rotation
                             (simp "ex-bal1full")
                             (apply ValidRB.vnode)
                             (apply ValidRB.vnode) (assumption) (assumption)
                             (assumption)
                             ;; black: no rotation
                             (simp "ex-bal1full")
                             (apply ValidRB.vnode)
                             (apply ValidRB.vnode) (assumption) (assumption)
                             (assumption)]
                           ctx)
          (is true "balance1 preserves ValidRB for all cases (kernel-verified)"))))))

;; ============================================================
;; GD convergence examples (requires Mathlib)
;; ============================================================

(def ^:private mathlib-available?
  (delay
    (try
      (let [store-path "/var/tmp/ansatz-mathlib"]
        (.exists (java.io.File. store-path)))
      (catch Exception _ false))))

(defmacro ^:private when-mathlib [& body]
  `(if @mathlib-available?
     (let [saved-env# @a/ansatz-env
           saved-idx# @a/ansatz-instance-index]
       (try
         (binding [a/*verbose* false]
           (a/init! "/var/tmp/ansatz-mathlib" "mathlib")
           ~@body)
         (finally
           (reset! a/ansatz-env saved-env#)
           (reset! a/ansatz-instance-index saved-idx#))))
     (is true "skipped: Mathlib store not available")))

(deftest test-gd-defn
  (when-mathlib
   (testing "Define verified GD step function"
     (let [f (a/define-verified 'ex-gd-step
               '[x :- Real, grad :- Real, eta :- Real] 'Real
               '(sub Real x (mul Real eta grad)))]
       (is (fn? f))
       (is (= 8.2 (double (((f 10.0) 6.0) 0.3))))))))

(deftest test-gd-convergence
  (when-mathlib
   (testing "Prove GD convergence rate"
     (a/prove-theorem 'ex-convergence
                      '[κ :- Real, ε₀ :- Real, n :- Nat,
                        hκ₀ :- (<= Real 0 κ), hκ₁ :- (<= Real κ 1), hε₀ :- (<= Real 0 ε₀)]
                      '(<= Real (mul Real (pow Real κ n) ε₀) ε₀)
                      '[(apply mul_le_of_le_one_left) (assumption)
                        (apply pow_le_one₀) (all_goals (assumption))])
     (is true))))

(deftest test-gd-full
  (when-mathlib
   (testing "Prove full GD convergence with step size"
     (a/prove-theorem 'ex-full
                      '[η :- Real, L :- Real, ε₀ :- Real, n :- Nat,
                        hη :- (<= Real 0 η), hL :- (<= Real 0 L),
                        hbound :- (<= Real (mul Real η L) 1), hε₀ :- (<= Real 0 ε₀)]
                      '(<= Real (mul Real (pow Real (sub Real 1 (mul Real η L)) n) ε₀) ε₀)
                      '[(apply mul_le_of_le_one_left) (assumption)
                        (apply pow_le_one₀)
                        (apply sub_nonneg_of_le) (assumption)
                        (apply sub_le_self) (apply mul_nonneg) (assumption) (assumption)])
     (is true))))
