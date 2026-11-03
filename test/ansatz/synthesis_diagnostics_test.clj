(ns ansatz.synthesis-diagnostics-test
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.surface.elaborate :as elab]
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
