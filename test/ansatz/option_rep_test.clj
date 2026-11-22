(ns ansatz.option-rep-test
  "`Option` runs as Clojure passes it: `none` is nil, `some x` is x, and only an x that would read
   as `none` (nil, or already a box) is boxed in a `SomeBox`. The box is chosen at run time, so a
   definition polymorphic in α computes the same values as one specialised to α."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [malli.core :as m]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.codegen :as cg]
            [ansatz.codegen.lean-runtime :as rt]
            [ansatz.clj-check :as cc]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.malli :as am]
            [ansatz.surface.elaborate :as elab])
  (:import [ansatz.kernel TypeChecker]
           [ansatz.codegen.lean_runtime SomeBox]))

(defn- init-once [f]
  (binding [a/*verbose* false]
    (a/load-init!)
    (f)))

(use-fixtures :once fixtures/isolated-session init-once)

(defn- run [term]
  (let [t (if (instance? ansatz.kernel.Expr term) term (elab/elaborate (a/env) term))]
    (eval (cg/ansatz->clj (a/env) t []))))

(defn- head-name [x]
  (let [[h _] (e/get-app-fn-args x)]
    (when (e/const? h) (name/->string (e/const-name h)))))

(defn- kernel->runtime
  "The runtime value a closed kernel value of descriptor `d` must compile to, read off the
   kernel's own reduction: `none` → nil, `some x` → (some-of x), List → a seq or nil."
  [whnf d x]
  (let [x (whnf x)
        [_ as] (e/get-app-fn-args x)
        h (head-name x)]
    (case (first d)
      :nat (long (e/lit-nat-val x))
      :bool (case h "Bool.true" true "Bool.false" false)
      :string (e/lit-str-val x)
      :unit nil
      :option (case h
                "Option.none" nil
                "Option.some" (rt/some-of (kernel->runtime whnf (second d) (nth as 1))))
      :list (case h
              "List.nil" nil
              "List.cons" (cons (kernel->runtime whnf (second d) (nth as 1))
                                (kernel->runtime whnf d (nth as 2)))))))

(defn- agrees-with-kernel! [application d]
  (let [term (elab/elaborate (a/env) application)
        tc (doto (TypeChecker. (a/env)) (.setFuel 200000000))
        whnf #(.whnf (.getReducer tc) %)
        kernel (kernel->runtime whnf d term)
        runtime (run term)]
    (is (= kernel runtime) (pr-str application))
    runtime))

(def ^:private none-box (rt/some-of nil))

(deftest runtime-helpers
  (testing "some-of boxes only what would read as none"
    (is (= 5 (rt/some-of 5)))
    (is (false? (rt/some-of false)))
    (is (instance? SomeBox (rt/some-of nil)))
    (is (instance? SomeBox (rt/some-of (rt/some-of nil))))
    (is (not= (rt/some-of nil) (rt/some-of (rt/some-of nil)))))
  (testing "some-val inverts some-of"
    (doseq [x [5 false "a" [] {:a 1} nil none-box]]
      (is (= x (rt/some-val (rt/some-of x))) (pr-str x))))
  (testing "boxes compare and hash by value"
    (is (= (rt/some-of nil) (rt/some-of nil)))
    (is (= (hash (rt/some-of nil)) (hash (rt/some-of nil))))
    (is (= #{none-box} #{(rt/some-of nil)}))
    (is (= "#ansatz/some nil" (pr-str none-box)))
    (is (= "#ansatz/some #ansatz/some nil" (pr-str (rt/some-of none-box))))))

(deftest constructions-round-trip
  (testing "the table of PR H"
    (is (nil? (agrees-with-kernel! '(Option.none Nat) [:option [:nat]])))
    (is (= 5 (agrees-with-kernel! '(Option.some Nat 5) [:option [:nat]])))
    (is (false? (agrees-with-kernel! '(Option.some Bool false) [:option [:bool]])))
    (is (= "a" (agrees-with-kernel! '(Option.some String "a") [:option [:string]])))
    (is (= none-box (agrees-with-kernel! '(Option.some (Option Nat) (Option.none Nat))
                                         [:option [:option [:nat]]])))
    (is (= 5 (agrees-with-kernel! '(Option.some (Option Nat) (Option.some Nat 5))
                                  [:option [:option [:nat]]])))
    (is (= (rt/some-of none-box)
           (agrees-with-kernel! '(Option.some (Option (Option Nat))
                                              (Option.some (Option Nat) (Option.none Nat)))
                                [:option [:option [:option [:nat]]]])))
    (is (= none-box (agrees-with-kernel! '(Option.some (List Nat) (List.nil Nat))
                                         [:option [:list [:nat]]])))
    (is (= [1 2] (agrees-with-kernel! '(Option.some (List Nat) (List.cons Nat 1 (List.cons Nat 2 (List.nil Nat))))
                                      [:option [:list [:nat]]])))
    (is (= none-box (agrees-with-kernel! '(Option.some Unit Unit.unit) [:option [:unit]])))))

(defn- nat-list [xs]
  (reduce (fn [tail x] (list 'List.cons 'Nat x tail)) '(List.nil Nat) (reverse xs)))

(deftest store-bodies-agree-with-kernel
  (doseq [xs [[] [5] [1 2 3] [0 2]]]
    (testing (str "xs = " xs)
      (agrees-with-kernel! (list 'List.head? (nat-list xs)) [:option [:nat]])
      (agrees-with-kernel! (list 'List.filterMap
                                 '(fn [x :- Nat] (if (Nat.beq x 2) (Option.none Nat) (Option.some Nat x)))
                                 (nat-list xs))
                           [:list [:nat]])
      ;; the constructor as a function value
      (agrees-with-kernel! (list 'List.map 'Option.some (nat-list xs)) [:list [:option [:nat]]])
      (agrees-with-kernel! (list 'List.map 'Option.some
                                 (list 'List.map '(fn [x :- Nat] (if (Nat.beq x 0) (Option.none Nat) (Option.some Nat x)))
                                       (nat-list xs)))
                           [:list [:option [:option [:nat]]]])
      (agrees-with-kernel! (list 'List.map '(fn [x :- Nat] (Option.none Nat)) (nat-list xs))
                           [:list [:option [:nat]]])
      ;; head? of a list of options: none, some none and some (some x) all differ
      (agrees-with-kernel! (list 'List.head?
                                 (list 'List.map '(fn [x :- Nat] (if (Nat.beq x 0) (Option.none Nat) (Option.some Nat x)))
                                       (nat-list xs)))
                           [:option [:option [:nat]]])))
  (doseq [o ['(Option.none Nat) '(Option.some Nat 0) '(Option.some Nat 7)]]
    (testing (pr-str o)
      (agrees-with-kernel! (list 'Option.getD o 9) [:nat])
      (agrees-with-kernel! (list 'Option.map '(fn [x :- Nat] (+ x 1)) o) [:option [:nat]])
      (agrees-with-kernel! (list 'Option.map '(fn [x :- Nat] (Option.none Nat)) o) [:option [:option [:nat]]])
      (agrees-with-kernel! (list 'Option.bind o '(fn [x :- Nat] (if (Nat.beq x 0) (Option.none Nat) (Option.some Nat x))))
                           [:option [:nat]])
      (agrees-with-kernel! (list 'Option.elim o 3 '(fn [x :- Nat] (+ x 10))) [:nat])
      (agrees-with-kernel! (list 'Option.isSome o) [:bool])
      (agrees-with-kernel! (list 'Option.isNone o) [:bool])))
  (doseq [o ['(Option.none (Option Nat)) '(Option.some (Option Nat) (Option.none Nat))
             '(Option.some (Option Nat) (Option.some Nat 4))]]
    (testing (pr-str o)
      (agrees-with-kernel! (list 'Option.getD o '(Option.some Nat 1)) [:option [:nat]])
      (agrees-with-kernel! (list 'Option.isSome o) [:bool])
      (agrees-with-kernel! (list 'Option.map '(fn [x :- (Option Nat)] (Option.isSome x)) o) [:option [:bool]]))))

(deftest polymorphic-and-monomorphic-agree
  (binding [*ns* (the-ns 'ansatz.option-rep-test)]
    (eval '(ansatz.core/defn optrep-wrap [A :- Type, x :- A] (Option A) (Option.some A x)))
    (eval '(ansatz.core/defn optrep-get [A :- Type, o :- (Option A), d :- A] A
             (match o none d (some x) x)))
    (eval '(ansatz.core/defn optrep-wrap-nat [x :- Nat] (Option Nat) (Option.some Nat x)))
    (eval '(ansatz.core/defn optrep-wrap-opt [x :- (Option Nat)] (Option (Option Nat))
             (Option.some (Option Nat) x)))
    (eval '(ansatz.core/defn optrep-poly-nat [x :- Nat] (Option Nat) (optrep-wrap Nat x)))
    (eval '(ansatz.core/defn optrep-poly-opt [x :- (Option Nat)] (Option (Option Nat))
             (optrep-wrap (Option Nat) x)))
    (eval '(ansatz.core/defn optrep-get-opt [o :- (Option (Option Nat))] (Option Nat)
             (optrep-get (Option Nat) o (Option.some Nat 42))))
    (eval '(ansatz.core/defn optrep-get-opt-mono [o :- (Option (Option Nat))] (Option Nat)
             (match o none (Option.some Nat 42) (some x) x))))
  (let [f #(deref (ns-resolve 'ansatz.option-rep-test %))]
    (doseq [x [0 5]]
      (is (= ((f 'optrep-wrap-nat) x) ((f 'optrep-poly-nat) x) x)))
    (doseq [x [nil 5 none-box]]
      (is (= ((f 'optrep-wrap-opt) x) ((f 'optrep-poly-opt) x) (rt/some-of x)) (pr-str x)))
    (doseq [o [nil none-box 5]]
      (is (= ((f 'optrep-get-opt) o) ((f 'optrep-get-opt-mono) o)) (pr-str o)))
    (is (= 42 ((f 'optrep-get-opt) nil)))
    (is (nil? ((f 'optrep-get-opt) none-box)) "some none projects to none, not to the default")
    (is (= 5 ((f 'optrep-get-opt) 5)))))

;; A Clojure caller passes nil or the value for [:maybe T]; the compiled function takes it as is.
(m/=> optrep-maybe-inc [:=> [:cat [:maybe :int]] :int])

(deftest malli-maybe-crosses-unchanged
  (binding [*ns* (the-ns 'ansatz.option-rep-test)]
    (eval '(ansatz.core/defn optrep-maybe-inc [o] (match o none 0 (some x) (+ x 1)))))
  (let [f @(ns-resolve 'ansatz.option-rep-test 'optrep-maybe-inc)
        clj (fn [o] (if (nil? o) 0 (+ o 1)))]
    (doseq [o [nil 5 -3 0]]
      (is (= (clj o) (f o)) (pr-str o))))
  (is (= 20 (:ok (am/check-verified! 'ansatz.option-rep-test 'optrep-maybe-inc :runs 20)))
      "kernel and runtime agree on generated [:maybe :int] arguments"))

(deftest clj-check-takes-option-without-conversion
  (is (= :nil-punning cc/*option-rep*))
  (doseq [d [[:option [:int]] [:option [:option [:int]]]]]
    (is (nil? (cc/clj->runtime d nil)))
    (is (= 5 (cc/clj->runtime d 5)))
    (is (= 5 (cc/runtime->clj d 5))))
  (let [row {:id :option-rep/identity :group :data :form 'o :params '[[o (Option Int)]]
             :ret '(Option Int) :expect :agree}
        result (cc/run-row row)]
    (is (:ok? (cc/row-verdict row result)) (pr-str result))
    (let [f (:fn (cc/define-row! row))]
      (is (nil? (f nil)))
      (is (= 5 (f 5))))))
