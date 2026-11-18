(ns ansatz.surface.clj-refusals-test
  "Clojure forms Ansatz cannot give clojure.core's meaning are refused with a structured reason
   (ansatz.surface.ingest/refusal-reasons), instead of being dropped, misread or rejected late
   by the kernel. `^:lean` opts a definition out of Clojure surface mode."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.surface.ingest :as ingest]))

(defn- init-once [f]
  (binding [a/*verbose* false]
    (a/load-init!)
    (f)))

(use-fixtures :once fixtures/isolated-session init-once)

(defn- define! [form]
  (binding [*ns* (the-ns 'ansatz.surface.clj-refusals-test) a/*verbose* false]
    (eval form)))

(defn- refusal
  "The refusal ex-data of evaluating `form`, or :accepted."
  [form]
  (try (define! form) :accepted
       (catch Throwable t
         (or (some #(let [d (ex-data %)] (when (= :clj/refused (:kind d)) d))
                   (take-while some? (iterate #(.getCause ^Throwable %) t)))
             (throw t)))))

(defn- reason [form] (let [r (refusal form)] (if (map? r) (:reason r) r)))

(deftest every-reason-is-documented
  (doseq [[r text] ingest/refusal-reasons]
    (is (keyword? r))
    (is (seq text))))

(deftest bodies-with-several-forms
  (is (= :multi-form-body (reason '(ansatz.core/defn ^Nat rf-do [^Nat a] (do 1 a)))))
  (is (= :empty-do (reason '(ansatz.core/defn ^Nat rf-do0 [^Nat a] (do)))))
  (is (= :multi-form-body (reason '(ansatz.core/defn ^Nat rf-let [^Nat a] (let [x a] x x)))))
  (is (= :multi-form-body (reason '(ansatz.core/defn ^Nat rf-loop [^Nat a] (loop [i a] i i)))))
  (testing "an a/defn with several body forms is refused when the macro expands"
    (is (= :multi-form-body (reason '(ansatz.core/defn ^Nat rf-two [^Nat a] 1 a)))))
  (testing "one form in do is its value"
    (define! '(ansatz.core/defn ^Nat rf-do1 [^Nat a] (do (+ a a))))
    (is (= 6 ((resolve 'ansatz.surface.clj-refusals-test/rf-do1) 3)))))

(deftest tests-must-be-bool
  (is (= :non-bool-test (reason '(ansatz.core/defn ^Nat rf-if [^Nat a] (if a 1 2)))))
  (is (= :non-bool-test (reason '(ansatz.core/defn ^Nat rf-cond [^Nat a] (cond a 1 :else 2)))))
  (is (= :non-bool-test (reason '(ansatz.core/defn ^Bool rf-and [^Nat a ^Bool p] (and a p)))))
  (let [d (refusal '(ansatz.core/defn ^Nat rf-if2 [^{:- (Option Nat)} o] (if o 1 2)))]
    (is (= 'o (:form d)) "the refusal names the offending test")
    (is (string? (:hint d)))))

(deftest nil-branches
  (is (= :nil-at-type (reason '(ansatz.core/defn ^Nat rf-if1 [^Bool p ^Nat a] (if p a)))))
  (is (= :nil-at-type (reason '(ansatz.core/defn ^Nat rf-when [^Bool p ^Nat a] (when p a)))))
  (is (= :nil-at-type (reason '(ansatz.core/defn ^Nat rf-cond0 [^Nat a] (cond (< a 1) 1)))))
  (testing "at a List type the missing branch is the empty list"
    (define! '(ansatz.core/defn ^{:- (List Nat)} rf-when-list [^Bool p ^{:- (List Nat)} xs] (when p xs)))
    (is (= [[1] nil] [((resolve 'ansatz.surface.clj-refusals-test/rf-when-list) true [1])
                      ((resolve 'ansatz.surface.clj-refusals-test/rf-when-list) false [1])]))))

(deftest arithmetic-arities
  (is (= :nat-negation (reason '(ansatz.core/defn ^Nat rf-neg [^Nat a] (- a)))))
  (define! '(ansatz.core/defn ^Nat rf-sum0 [^Nat a] (+ (+) (* a) (*))))
  (is (= 4 ((resolve 'ansatz.surface.clj-refusals-test/rf-sum0) 3))))

(deftest comparisons-that-are-not-binary-chain
  (define! '(ansatz.core/defn ^Bool rf-chain [^Nat a ^Nat b ^Nat c] (< a b c)))
  (is (= [true false] [((resolve 'ansatz.surface.clj-refusals-test/rf-chain) 1 2 3)
                       ((resolve 'ansatz.surface.clj-refusals-test/rf-chain) 1 3 2)]))
  (define! '(ansatz.core/defn ^Bool rf-one [^Nat a] (= a)))
  (is (true? ((resolve 'ansatz.surface.clj-refusals-test/rf-one) 3))))

(deftest equality-with-nil
  (is (= :nil-vs-empty (reason '(ansatz.core/defn ^Bool rf-nil [^{:- (List Nat)} xs] (= xs nil))))))

(deftest get-and-keyword-defaults
  (define! '(ansatz.core/structure RfPoint [] (x Nat) (y Nat)))
  (testing "a structure field is always present, so the default is unreachable"
    (define! '(ansatz.core/defn ^Nat rf-getd [^{:- RfPoint} p] (get p :x 9)))
    (is (= 3 ((resolve 'ansatz.surface.clj-refusals-test/rf-getd)
              ((resolve 'ansatz.surface.clj-refusals-test/->RfPoint) 3 4)))))
  (is (= :get-non-keyword (reason '(ansatz.core/defn ^Nat rf-get [^{:- (List Nat)} xs] (get xs 0)))))
  (is (= :get-default (reason '(ansatz.core/defn ^Nat rf-kwd [^{:- (Option Nat)} o] (:x o 7))))))

(deftest case-needs-a-default
  (is (= :case-no-default (reason '(ansatz.core/defn ^Nat rf-case [^Nat a] (case a 0 1 2 3))))))

(deftest lean-opt-out
  (testing "^:lean elaborates the body without Clojure surface mode: a 4-element comparison is
            the typed Prop form again, which is not a Bool"
    (is (= :accepted (refusal '(ansatz.core/defn ^Bool rf-chain-clj [^Nat a ^Nat b ^Nat c] (< a b c)))))
    (is (thrown? Exception (define! '(ansatz.core/defn ^:lean ^Bool rf-chain-lean [^Nat a ^Nat b ^Nat c]
                                       (< a b c)))))))

(deftest partial-bodies-are-type-checked
  (testing "a ^:partial body is kernel-checked at its type before it is compiled"
    (is (thrown? Exception
                 (define! '(ansatz.core/defn ^:lean ^:partial ^Nat rf-partial [^Nat n]
                             (if n 0 (rf-partial n))))))))
