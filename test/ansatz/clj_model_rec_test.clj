(ns ansatz.clj-model-rec-test
  "PR G3: recursion (self-calls, loop/recur, letfn, mutually recursive a/defmodel functions) as
   fuel-indexed models, calls into DSL functions, and opaque calls of unmodelled functions."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.clj-check :as cc]
            [ansatz.clj-model :as m]
            [ansatz.clj-model.translate :as tr]
            [ansatz.clj-model.boundary :as b]
            [ansatz.surface.data :as data]
            [clojure.set]))

;; loop/recur over a vector
(a/defmodel sum-loop [xs]
  (loop [s (seq xs) acc 0]
    (if s (recur (next s) (+ acc (first s))) acc)))

;; self-recursion over nested maps and vectors (an EDN tree)
(a/defmodel leaf-sum [t]
  (cond (map? t) (reduce + 0 (map leaf-sum (vals t)))
        (vector? t) (reduce + 0 (map leaf-sum t))
        (int? t) t
        :else 0))

;; mutual recursion between two a/defmodel functions
(declare od?)
(a/defmodel ev? [n] (if (zero? n) true (od? (dec n))))
(a/defmodel od? [n] (if (zero? n) false (ev? (dec n))))

;; multi-arity, calling its own other arity
(a/defmodel cnt
  ([xs] (cnt xs 0))
  ([xs acc] (if (seq xs) (recur (next xs) (inc acc)) acc)))

;; a modelled function calling a DSL function and an unmodelled Clojure function
(defn ext-width
  "Not an a/defmodel: calls of it are opaque."
  [m] (count (str m)))

(declare dbl vdsl)                      ;; a/defns, defined once the fixture has an env
(a/defmodel quad [x] (dbl (dbl x)))
(a/defmodel widths [m] (+ 1 (ext-width m)))

;; a modelled function passed to a higher-order function
(a/defmodel sq [x] (* x x))
(a/defmodel sum-sq [xs] (reduce + 0 (map sq xs)))

;; the default fuel cuts this one short (its argument grows), a user :fuel does not
(a/defmodel sq-down [x] (cond (neg? x) (sq-down (* x x)) (zero? x) :done :else (sq-down (dec x))))
(a/defmodel ^{:fuel (+ (* x x) 2)} sq-down-fueled [x]
  (cond (neg? x) (sq-down-fueled (* x x)) (zero? x) :done :else (sq-down-fueled (dec x))))

(defn- define-models! []
  (a/defn dbl [x :- Int] Int (* 2 x))
  (a/defn vdsl [v :- Value] Int 0)
  (a/foreign ^:model sum-sq-of [xs :- (List Int)] Int sum-sq)
  (a/foreign ^:model sqd [x :- Int] Value sq-down)
  (a/foreign ^:model sqd-fueled [x :- Int] Value sq-down-fueled)
  (a/foreign ^:model capped [xs :- (List Int)] Nat
             (fn [xs] (loop ^{:fuel 3} [s (seq xs) n 0] (if s (recur (next s) (inc n)) n))))
  (a/foreign ^:model sum-of [xs :- (List Int)] Int sum-loop)
  (a/foreign ^:model leaves [t :- Value] Int leaf-sum)
  (a/foreign ^:model even-nat [n :- Nat] Bool ev?)
  (a/foreign ^:model count-of [xs :- (List Int)] Nat cnt)
  (a/foreign ^:model quad-of [x :- Int] Int quad)
  (a/foreign ^:model width-of [m :- Value] Int widths))

(defn- setup [f]
  (binding [a/*verbose* false]
    (a/load-init!)
    (data/install-value-type!)
    (b/install-codecs!)
    (define-models!)
    (f)))

(use-fixtures :once fixtures/isolated-session setup)

(defn- proves? [prop tactics]
  (try (binding [a/*verbose* false] (a/prove-theorem (gensym "clj-model-rec-fact") '[] prop tactics)) true
       (catch Throwable _ false)))

(defn- faithful? [f]
  (let [r (cc/check-model! f :runs 40)]
    (and (zero? (get-in r [:faithful :model-bug])) (pos? (get-in r [:faithful :agree])))))

(deftest loop-recur
  (is (= 6 (sum-of [1 2 3])))
  (is (proves? '(= Int (sum-of (List.cons 1 (List.cons 2 (List.cons 3 List.nil)))) 6) '[(rfl)])
      "the kernel evaluates the fuel-indexed model")
  (is (faithful? 'sum-of)))

(deftest tree-walk
  (is (= 10 (leaves (data/edn->value {:a 1 :b [2 {:c 3}] :d 4}))))
  (is (faithful? 'leaves)))

(deftest mutual-recursion
  (testing "two a/defmodel functions form one group"
    (is (true? (even-nat 10)))
    (is (proves? '(= Bool (even-nat 7) false) '[(rfl)]))
    (is (faithful? 'even-nat))))

(deftest multi-arity
  (is (= 3 (count-of [5 6 7])))
  (is (proves? '(= Nat (count-of (List.cons 5 (List.cons 6 List.nil))) 2) '[(rfl)]))
  (is (faithful? 'count-of)))

(deftest dsl-callee
  (is (= 12 (quad-of 3)))
  (is (proves? '(= Int (quad-of 3) 12) '[(rfl)]))
  (is (faithful? 'quad-of))
  (is (empty? (:opaque (b/info 'quad-of)))))

(deftest opaque-callee
  (is (= ["ansatz.clj-model-rec-test/ext-width"] (:opaque (b/info 'width-of))))
  (is (= 2 (width-of (data/edn->value 7))))
  (is (= ["ansatz.clj-model-rec-test/ext-width"] (:opaque (a/trust-report width-of))))
  (is (faithful? 'width-of) "the compiled model calls the real ext-width"))

(deftest modelled-callee-as-a-function-argument
  (is (= 14 (sum-sq-of [1 2 3])))
  (is (proves? '(= Int (sum-sq-of (List.cons 1 (List.cons 2 (List.cons 3 List.nil)))) 14) '[(rfl)]))
  (is (faithful? 'sum-sq-of)))

(deftest fuel
  (testing "out of fuel is no claim: the kernel's sqd is the default where the model has none"
    (is (proves? '(= Value (sqd 2) (Value.vkw "done")) '[(rfl)]) "counting down: within the default fuel")
    (is (proves? '(= Value (sqd -5) Value.vnil) '[(rfl)]) "25 levels from a weight of 7: cut short")
    (is (= (data/edn->value :done) (sqd -5)) "the runtime is the impl")
    (is (proves? '(= Value (sqd-fueled -5) (Value.vkw "done")) '[(rfl)]) "^{:fuel (+ (* x x) 2)}"))
  (testing "a loop's :fuel"
    (is (proves? '(= Nat (capped (List.cons 1 (List.cons 2 List.nil))) 2) '[(rfl)]))
    (is (proves? '(= Nat (capped (List.cons 1 (List.cons 2 (List.cons 3 List.nil)))) 0) '[(rfl)])
        "3 levels: a list of 3 needs 4")
    (is (= 3 (capped [1 2 3])))
    (is (faithful? 'capped) "no claim is never a model bug")))

(deftest conformance-proofs
  (testing "a model calling a DSL function: the default script unfolds the callee's model"
    (binding [a/*verbose* false] (a/conforms quad-of))
    (is (= :proved (b/status 'quad-of))))
  (testing "a recursive model is not proved by the default script (it needs an induction)"
    (is (thrown? Throwable (binding [a/*verbose* false] (b/prove-conforms! 'even-nat []))))
    (is (= :tested (b/status 'even-nat)))))

(deftest refusals
  (doseq [[form reason] '[[(fn [x] (vdsl x)) :unmodelled-fn]
                          [(fn [x] (clojure.set/union x x)) :unmodelled-fn]
                          [(fn f [a b c d e g h i j] (f a b c d e g h i j)) :recursion]]]
    (is (= reason (:reason (try (tr/translate form 'ansatz.clj-model-rec-test nil) nil
                                (catch clojure.lang.ExceptionInfo ex (ex-data ex)))))
        (pr-str form))))
