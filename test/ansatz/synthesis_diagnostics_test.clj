(ns ansatz.synthesis-diagnostics-test
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.surface.elaborate :as elab]
            [ansatz.surface.ingest :as ingest]
            [ansatz.test-env :as test-env]))

(use-fixtures :each
  (fn [f]
    (let [saved @a/ansatz-env]
      (try (reset! a/ansatz-env @test-env/checked-bundled-init-env)
           (binding [a/*verbose* false] (f))
           (finally (reset! a/ansatz-env saved))))))

(defn- failure [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo ex ex)))

(defn- check-missing-order [f]
  (let [error (failure f)]
    (is (re-find #"failed to synthesize\n  \(LE\.\{0\} A\)" (or (ex-message error) "")))
    (is (= (name/from-string "LE") (:class (ex-data error))))
    (is (= :synthetic (:mvar-kind (ex-data error))))
    (is (= :failed-instance (:problem (ex-data error))))
    (is (re-find #"Additional diagnostic information" (or (ex-message error) "")))))

;; Lean pairs: test/lean/synthesis_diagnostics.lean.
(deftest declarations-report-the-missing-class
  (check-missing-order #(a/inductive MissingOrder [A Type] (mk [x A] [h (<= x x)])))
  (check-missing-order #(a/structure MissingOrderRecord [A Type] (x A) (h (<= x x))))
  (check-missing-order #(a/defn missing-order [A :- Type x :- A] Prop (<= x x)))
  (check-missing-order #(a/theorem missing-order-thm [A :- Type x :- A] (<= x x) (assumption))))

(deftest strict-elaboration-distinguishes-stuck-instances-and-holes
  (let [stuck (failure #(elab/elaborate (a/env) '(LE.le _ _)))
        implicit (failure #(elab/elaborate (a/env) '(List.length List.nil)))
        hole (failure #(elab/elaborate (a/env) '_ (e/const' (name/from-string "Nat") [])))]
    (is (re-find #"typeclass instance problem is stuck" (or (ex-message stuck) "")))
    (is (= :stuck-instance (:problem (ex-data stuck))))
    (is (= (name/from-string "LE") (:class (ex-data stuck))))
    (is (re-find #"don't know how to synthesize implicit argument" (or (ex-message implicit) "")))
    (is (= :implicit-argument (:problem (ex-data implicit))))
    (is (re-find #"don't know how to synthesize placeholder" (or (ex-message hole) "")))
    (is (= :placeholder (:problem (ex-data hole))))))

(deftest tactic-terms-report-the-missing-class
  (doseq [tactic ['(exact (<= x x)) '(refine (<= x x)) '(apply (LE.le x x))
                  '(have h Prop (<= x x)) '(have h := (LE.le x x))]]
    (let [error (failure #(a/prove-law '[A :- Type x :- A] 'Prop [tactic]))]
      (is (re-find #"failed to synthesize\n  \(LE\.\{0\} A\)" (or (ex-message error) "")) (str tactic))
      (is (= :failed-instance (:problem (ex-data error))))
      (is (= (name/from-string "LE") (:class (ex-data error)))))))

(deftest tactic-terms-distinguish-stuck-instances
  (doseq [tactic ['(exact (LE.le _ _)) '(refine (LE.le _ _))
                  '(apply (LE.le _ _)) '(have h Prop (LE.le _ _)) '(have h := (LE.le _ _))]]
    (let [error (failure #(a/prove-law [] 'Prop [tactic]))]
      (is (re-find #"typeclass instance problem is stuck" (or (ex-message error) "")) (str tactic))
      (is (= :stuck-instance (:problem (ex-data error)))))))

(deftest failed-instances-precede-stuck-problems
  (let [error (failure #(elab/elaborate (a/env)
                                        '(forall [A Type x A]
                                                 (arrow (LE.le _ _) (< x x)))))]
    (is (= :failed-instance (:problem (ex-data error))))
    (is (= (name/from-string "LT") (:class (ex-data error))))
    (is (re-find #"\(LT\.\{0\} A\)" (or (ex-message error) "")))))

(deftest instance-diagnostics-retain-source-order
  (let [error (failure #(elab/elaborate (a/env)
                                        '(forall [A Type x A]
                                                 (arrow (<= x x) (< x x)))))]
    (is (= (name/from-string "LE") (:class (ex-data error))))))

(deftest output-metavariables-do-not-make-synthesis-stuck
  (let [error (failure #(elab/elaborate (a/env) '(HAdd.hAdd Bool.false Bool.false)))]
    (is (re-find #"failed to synthesize" (or (ex-message error) "")))
    (is (= :failed-instance (:problem (ex-data error))))
    (is (= (name/from-string "HAdd") (:class (ex-data error)))))
  (a/defn diagnostic-consume [A :- Type :implicit x :- A q :- Prop] Nat 0)
  (let [error (failure #(elab/elaborate (a/env)
                                        '(forall [A Type x A]
                                                 (= (diagnostic-consume (HAdd.hAdd Bool.false Bool.false)
                                                                        (LE.le x x)) 0))))]
    (is (= :failed-instance (:problem (ex-data error))))
    (is (= (name/from-string "HAdd") (:class (ex-data error))))))

(deftest direct-apply-reports-synthesis-failure-for-unknown-inputs
  ;; Meta.synthInstance reports failure even when its inputs are stuck; compound
  ;; apply terms instead use Elab.reportStuckSyntheticMVar (covered above).
  (let [error (failure #(a/prove-law [] 'Prop '[(apply LE.le)]))]
    (is (re-find #"apply: failed to synthesize" (or (ex-message error) "")))
    (is (= :failed-instance (:problem (ex-data error))))
    (is (= (name/from-string "LE") (:class (ex-data error))))
    (is (= :synthetic (:mvar-kind (ex-data error))))))

(deftest stuck-problems-prefer-the-smallest-syntax-range
  (a/defn diagnostic-f [p :- Prop :implicit inst :- (Decidable p) :inst q :- Prop] Nat 0)
  (let [error (failure #(elab/elaborate (a/env) '(diagnostic-f (LE.le _ _))))]
    (is (= :stuck-instance (:problem (ex-data error))))
    (is (= (name/from-string "LE") (:class (ex-data error))))))

(deftest stuck-problems-use-source-position-then-pending-order
  (a/defn diagnostic-two [p :- Prop q :- Prop] Nat 0)
  (let [error (failure #(elab/elaborate (a/env) '(diagnostic-two (LE.le _ _) (LT.lt _ _))))]
    (is (= :stuck-instance (:problem (ex-data error))))
    (is (= (name/from-string "LE") (:class (ex-data error)))))
  (a/defn diagnostic-g [p :- Prop :implicit A :- Type :implicit
                        instP :- (Decidable p) :inst instA :- (LE A) :inst q :- Prop] Nat 0)
  (let [error (failure #(elab/elaborate (a/env) '(diagnostic-g True)))]
    (is (= :stuck-instance (:problem (ex-data error))))
    (is (= (name/from-string "LE") (:class (ex-data error))))))

(deftest semi-output-metavariables-do-not-make-synthesis-stuck
  (a/class DiagnosticSemi [A (semiOutParam Type)] (witness A))
  (a/defn diagnostic-semi [A :- Type :implicit inst :- (DiagnosticSemi A) :inst] Nat 0)
  (let [error (failure #(elab/elaborate (a/env) '(diagnostic-semi)))]
    (is (= :failed-instance (:problem (ex-data error))))
    (is (= (name/from-string "DiagnosticSemi") (:class (ex-data error))))))

(deftest diagnostic-ranges-preserve-deep-kernel-term-passthrough
  (let [succ (e/const' (name/from-string "Nat.succ") [])
        term (nth (iterate #(e/app succ %) (e/lit-nat 0)) 8000)]
    (is (identical? term (elab/elaborate (a/env) term)))))

(defn- with-discard-payload [f]
  (let [saved @ingest/term-elaborator-registry]
    (try
      (swap! ingest/term-elaborator-registry assoc 'discard-payload (fn [_ _] (e/lit-nat 0)))
      (f)
      (finally (reset! ingest/term-elaborator-registry saved)))))

(deftest diagnostic-ranges-do-not-inspect-discarded-extension-payloads
  (with-discard-payload
    (fn []
      (let [deep (nth (iterate vector 'unused) 8000)
            opaque (proxy [Object] [] (toString [] (throw (ex-info "payload was printed" {}))))
            deferred (lazy-seq (throw (ex-info "payload was realized" {})))
            opaque-vector (subvec (proxy [clojure.lang.APersistentVector] []
                                    (count [] 2)
                                    (nth [i] (throw (ex-info "payload was indexed" {})))) 0 1)]
        (doseq [payload [deep opaque deferred opaque-vector]]
          (is (= (e/lit-nat 0)
                 (elab/elaborate (a/env) (list 'discard-payload payload)))))))))

(deftest deep-or-opaque-syntax-falls-back-when-reporting-stuck-instances
  (a/defn diagnostic-payload-use [n :- Nat p :- Prop] Nat 0)
  (with-discard-payload
    (fn []
      (let [deep (nth (iterate vector 'unused) 40000)
            opaque (proxy [Object] [] (toString [] (throw (ex-info "payload was printed" {}))))
            deferred (lazy-seq (throw (ex-info "payload was realized" {})))
            opaque-vector (subvec (proxy [clojure.lang.APersistentVector] []
                                    (count [] 2)
                                    (nth [i] (throw (ex-info "payload was indexed" {})))) 0 1)]
        (doseq [payload [deep opaque deferred opaque-vector]]
          (let [form (list 'diagnostic-payload-use (list 'discard-payload payload) '(LE.le _ _))
                error (failure #(elab/elaborate (a/env) form))]
            (is (= :stuck-instance (:problem (ex-data error))))
            (is (= (name/from-string "LE") (:class (ex-data error))))))))))

;; Lean's Meta/Check.lean throwAppTypeMismatch, as Elab/App.lean ensureArgType reports it: the
;; argument, its type, the expected type and the application (Klara's report: the bare
;; "Type mismatch in application" named none of them).
(deftest application-mismatch-names-the-argument-and-both-types
  (a/theorem diagReach [P :- (=> Int Prop), lo :- Int, hi :- Int, hlo :- (P lo), hle :- (<= lo hi)]
             (P lo) (exact hlo))
  (testing "a hypothesis whose type is not defeq to the parameter"
    (let [error (failure #(a/theorem diagReachWrong [P :- (=> Int Prop), hgd :- (P -4)] (P -3)
                                     (apply (diagReach P -3 3 hgd _)) (decide)))
          message (str (ex-message error))]
      (is (re-find #"Application type mismatch: The argument\n  hgd\nhas type\n  P \(Neg\.neg Int Int\.instNegInt \(OfNat\.ofNat Int 4 " message))
      (is (re-find #"but is expected to have type\n  P \(Neg\.neg Int Int\.instNegInt \(OfNat\.ofNat Int 3 " message))
      (is (re-find #"in the application\n  diagReach P " message))))
  (testing "Int.negSucc and Neg.neg spellings of the same literal are defeq"
    (is (nil? (failure #(a/theorem diagReachSucc [P :- (=> Int Prop), hgd :- (P (Int.negSucc 1454082))]
                                   (P -1454083)
                                   (apply (diagReach P -1454083 1454083 hgd _)) (decide)))))))
