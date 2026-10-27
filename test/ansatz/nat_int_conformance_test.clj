(ns ansatz.nat-int-conformance-test
  "Direct translations of test/lean/nat_int_conformance.lean.
  Uses list-conformance-test translation rules; explicit type arguments spell Lean @ applications.
  Constructor branches use ansatz field names. No alternative proof scripts for gaps."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.name :as name]
            [ansatz.conformance-support :as cs]))

;; Lean reference: src/Lean/Elab/Tactic/{Induction,Simp,Decide}.lean,
;; evalInductionCore/evalCasesCore, evalSimp, evalDecideCore.
;; Surface if uses Bool.rec/Nat.ble for Lean's propositional comparison.
;; Int.ofNat spells the typed zero in the match base case explicitly.
;; Lean 4.33 rejects deprecated simp_arith; n19 uses Lean simp +arith.
(def ^:private defs
  '[(ansatz.core/defn tally [xs :- (List Nat)] Nat (match xs [nil 0] [(cons h t) (+ (tally t) 1)]))
    (ansatz.core/defn total [xs :- (List Nat)] Nat (match xs [nil 0] [(cons h t) (+ h (total t))]))
    (ansatz.core/defn zeros [n :- Nat] Nat (match n [zero 0] [(succ k) (+ (zeros k) 0)]))
    (ansatz.core/defn power [a :- Nat, n :- Nat] Nat (match n [zero 1] [(succ k) (* (power a k) a)]))
    (ansatz.core/defn factorial [n :- Nat] Nat (match n [zero 1] [(succ k) (* (+ k 1) (factorial k))]))
    (ansatz.core/defn peak [xs :- (List Nat)] Nat (match xs [nil 0] [(cons h t) (if (Nat.ble h (peak t)) (peak t) h)]))
    (ansatz.core/defn itotal [xs :- (List Int)] Int (match xs [nil (Int.ofNat 0)] [(cons h t) (+ h (itotal t))]))])

(def ^:private theorems
  '[[n01_zeros [n :- Nat]
     (= (zeros n) 0)
     [(and_then (induction n) (simp [zeros *]))]]
    [n02_tally_nonneg [xs :- (List Nat)]
     (<= Nat 0 (tally xs))
     [(omega)]]
    [n03_tally_cons [x :- Nat, xs :- (List Nat)]
     (> (tally (List.cons Nat x xs)) (tally xs))
     [(simp [tally])]]
    [n04_total_cons [x :- Nat, xs :- (List Nat)]
     (<= (total xs) (total (List.cons Nat x xs)))
     [(and_then (simp [total]) (omega))]]
    [n05_total_zero [xs :- (List Nat), h :- (= (total xs) 0), x :- Nat]
     (= (total (List.cons Nat x xs)) x)
     [(simp [total h])]]
    [n06_sub_self [xs :- (List Nat)]
     (= (- (total xs) (total xs)) 0)
     [(omega)]]
    [n07_sub_truncate [xs :- (List Nat), n :- Nat, h :- (<= (total xs) n)]
     (= (- (total xs) n) 0)
     [(omega)]]
    [n08_sub_cancel [xs :- (List Nat), n :- Nat]
     (= (- (+ (total xs) n) n) (total xs))
     [(omega)]]
    [n09_le_trans [xs :- (List Nat), a :- Nat, b :- Nat, h :- (<= (total xs) a), k :- (<= a b)]
     (<= (total xs) b)
     [(exact (Nat.le_trans h k))]]
    [n10_peak_head [x :- Nat, xs :- (List Nat)]
     (<= x (peak (List.cons Nat x xs)))
     [(simp only [peak]) (and_then (split) (omega))]]
    [n11_peak_tail [x :- Nat, xs :- (List Nat)]
     (<= (peak xs) (peak (List.cons Nat x xs)))
     [(simp only [peak]) (and_then (split) (omega))]]
    [n12_power_one [n :- Nat]
     (= (power 1 n) 1)
     [(and_then (induction n) (simp [power *]))]]
    [n13_power_zero [a :- Nat]
     (= (power a 0) 1)
     [(rfl)]]
    [n14_factorial_four []
     (= (factorial 4) 24)
     [(decide)]]
    [n15_power_closed []
     (= (power 2 5) 32)
     [(decide)]]
    [n16_itotal_cons [x :- Int, xs :- (List Int)]
     (= Int (- (itotal (List.cons Int x xs)) x) (itotal xs))
     [(and_then (simp [itotal]) (omega))]]
    [n17_int_cancel [xs :- (List Int), n :- Int]
     (= Int (- (+ (itotal xs) n) n) (itotal xs))
     [(omega)]]
    [n18_int_bound [xs :- (List Int), n :- Int, h :- (<= (itotal xs) n)]
     (<= Int (- (itotal xs) n) 0)
     [(omega)]]
    [n19_simp_arith [xs :- (List Nat)]
     (Not (= (+ (total xs) 1) 0))
     [(simp +arith)]]
    [n20_total_closed []
     (And (= (total (List.cons Nat 2 (List.cons Nat 3 (List.cons Nat 4 (List.nil Nat))))) 9) (= Nat (- 3 5) 0))
     [(decide)]]])

(def ^:private known-gaps
  {'n19_simp_arith "simp +arith: arithmetic simprocs are not ported; omega is a solver, not a simp normalizer."})

(deftest nat-int-conformance
  (cs/check-suite "nat/int"
                  (cs/run-suite 'ansatz.nat-int-conformance-test defs theorems)
                  known-gaps))

(deftest peak-equation-generation
  (cs/run-suite 'ansatz.nat-int-conformance-test [(nth defs 5)] [])
  (doseq [lemma ["peak.eq_1" "peak.eq_2"]]
    (is (some? (env/lookup (a/env) (name/from-string lemma)))))
  (is (= {:errors []}
         (:equation-generation
          (meta (var-get (ns-resolve 'ansatz.nat-int-conformance-test 'peak)))))))

(deftest computed-discriminant-equation-generation
  (a/load-init!)
  (doseq [[nm ret branch] [['eqNat 'Nat 'x] ['eqBool 'Bool true]]]
    (let [result (binding [a/*verbose* false]
                   (a/define-verified nm '[x :- Nat, y :- Nat] ret
                                      (list 'if '(Nat.ble x y) branch branch)))]
      (is (= {:errors []} (:equation-generation (meta result))))
      (is (some? (env/lookup (a/env) (name/from-string (str nm ".eq_1")))))
      (is (nil? (env/lookup (a/env) (name/from-string (str nm ".eq_2"))))))))

(deftest equation-generation-failure-is-reported
  (a/load-init!)
  (doseq [[nm params body suffix]
          [['warnPeak '[xs :- (List Nat)] '(match xs [nil 0] [(cons h t) h]) ".eq_2"]
           ['warnApply '[b :- Bool, x :- Nat]
            '((match b [false (fn [z :- Nat] z)]
                       [true (fn [z :- Nat] (+ z 1))]) x) ".eq_1"]]]
    (let [check env/check-constant
          lemma (str nm suffix)
          result (atom nil)
          warning (java.io.StringWriter.)]
      (binding [a/*verbose* false *err* warning]
        (with-redefs [env/check-constant
                      (fn [env ci]
                        (if (= lemma (str (.name ci)))
                          (throw (ex-info "injected equation rejection" {:test true}))
                          (check env ci)))]
          (reset! result (a/define-verified nm params 'Nat body))))
      (let [errors (:errors (:equation-generation (meta @result)))]
        (is (= 1 (count errors)))
        (is (instance? clojure.lang.ExceptionInfo (first errors)))
        (is (= lemma (:lemma (ex-data (first errors)))))
        (is (= "injected equation rejection" (some-> (first errors) ex-cause ex-message))))
      (is (.contains (str warning) lemma))
      (is (.contains (str warning) "injected equation rejection")))))

(defn- checked-equation [lemma]
  (let [ci (env/lookup (a/env) (name/from-string lemma))]
    (is (some? ci) (str lemma " installed"))
    (when ci
      (let [tc (ansatz.kernel.TypeChecker. (a/env))]
        (is (.isDefEq tc (.inferType tc (.value ci)) (.type ci))
            (str lemma " kernel-checks")))
      (loop [ty (.type ci)]
        (if (e/forall? ty) (recur (e/forall-body ty)) ty)))))

(deftest regression-function-valued-unfold-equation
  (a/load-init!)
  (let [result (binding [a/*verbose* false]
                 (a/define-verified 'regrFn '[x :- Nat, y :- Nat] '(=> Nat Nat)
                                    '(if (Nat.ble x y) (fn [z :- Nat] x) (fn [z :- Nat] y))))
        equality (checked-equation "regrFn.eq_1")]
    (is (= {:errors []} (:equation-generation (meta result))))
    (when equality
      ;; Eq's domain is the function type, rather than an invented extra binder.
      (is (e/forall? (red/whnf (a/env) (first (e/get-app-args equality)) {}))))))

(deftest regression-nested-matcher-result-type
  (a/load-init!)
  (let [result (binding [a/*verbose* false]
                 (a/define-verified 'regrNested '[b :- Bool, xs :- (List Nat)] 'Nat
                                    '(match xs [nil 0]
                                       [(cons h t) (if (if b true false) h (regrNested b t))])))]
    (is (= {:errors []} (:equation-generation (meta result))))
    (doseq [lemma ["regrNested._match_1.eq_1" "regrNested._match_1.eq_2"]]
      (when-let [equality (checked-equation lemma)]
        (is (= "Bool" (str (e/const-name (first (e/get-app-args equality))))))))
    (doseq [lemma ["regrNested.eq_1" "regrNested.eq_2s1" "regrNested.eq_2s2"]]
      (checked-equation lemma))))

(deftest regression-overapplied-recursor-equation
  (a/load-init!)
  (let [result (binding [a/*verbose* false]
                 (a/define-verified 'regrApply '[b :- Bool, x :- Nat] 'Nat
                                    '((match b [false (fn [z :- Nat] z)]
                                               [true (fn [z :- Nat] (+ z 1))]) x)))
        equality (checked-equation "regrApply.eq_1")]
    (is (= {:errors []} (:equation-generation (meta result))))
    (when equality
      (is (= "Nat" (str (e/const-name (first (e/get-app-args equality)))))))))

(deftest recursive-inner-recursors-remain-terms
  (a/load-init!)
  (doseq [[nm params body]
          [['regrRec '[xs :- (List Nat), n :- Nat]
            '(match xs [nil 0]
               [(cons h t)
                (Nat.rec (fn [k :- Nat] Nat) 0
                         (fn [k :- Nat, ih :- Nat] (+ ih 1)) n)])]
           ['regrListRec '[xs :- (List Nat), ys :- (List Nat), b :- Bool]
            '(match xs [nil 0]
               [(cons h t)
                (List.rec Nat (fn [ys :- (List Nat)] Nat) 0
                          (fn [head :- Nat, tail :- (List Nat), ih :- Nat] (+ ih 1))
                          (if b ys t))])]]]
    (let [result (binding [a/*verbose* false] (a/define-verified nm params 'Nat body))]
      (is (= {:errors []} (:equation-generation (meta result))))
      (checked-equation (str nm ".eq_1"))
      (checked-equation (str nm ".eq_2"))
      (is (not-any? #(.startsWith (str (.name ^ansatz.kernel.ConstantInfo %)) (str nm "._match_"))
                    (env/all-constants (a/env)))
          "recursive implementations must not spawn matcher auxiliaries"))))
