(ns ansatz.clj-ingest-test
  "Clojure ingestion: the elaborator macroexpands whitelisted pure-structural clojure.core macros on
   the way in and elaborates the resulting core forms (let* / application / …) to kernel terms, so
   idiomatic functional Clojure can be copied into a/defn with few/no adjustments. Grows phase by
   phase (Phase A: let + threading; later: fn, destructuring, recursion ladder)."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]))

(defn- with-init [f]
  (a/load-init!)
  (binding [a/*verbose* false] (f)))
(use-fixtures :once with-init)

(deftest let-elaborates-and-runs
  (eval '(ansatz.core/defn ^Nat ci-let1 [^Nat n] (let [x (Nat.add n n)] (Nat.add x x))))
  (eval '(ansatz.core/defn ^Nat ci-let2 [^Nat n] (let [x (Nat.add n 1) y (Nat.add x x)] (Nat.add x y))))
  (eval '(ansatz.core/defn ^Nat ci-let3 [^Nat n] (let [x (Nat.add n n)] (let [y (Nat.add x 1)] y))))
  (is (= 24 ((resolve 'ci-let1) 6)) "single binding")
  (is (= 21 ((resolve 'ci-let2) 6)) "multiple bindings, later refers to earlier")
  (is (= 13 ((resolve 'ci-let3) 6)) "nested let"))

(deftest thread-last-elaborates
  (eval '(ansatz.core/defn ^Nat ci-thread [^Nat n] (->> n (Nat.add 1) (Nat.add 10))))
  (is (= 17 ((resolve 'ci-thread) 6)) "->> threads as the last argument"))

(deftest fn-lambda-elaborates
  ;; (fn [^T x] …) macroexpands to fn*; metadata survives, so annotated lambdas elaborate to kernel
  ;; lambdas — as beta-redexes and as arguments to higher-order functions.
  (eval '(ansatz.core/defn ^Nat ci-beta [^Nat n] ((fn [^Nat x] (Nat.add x x)) n)))
  (eval '(ansatz.core/defn ^Nat ci-apply1 [^{:- (=> Nat Nat)} f ^Nat n] (f n)))
  (eval '(ansatz.core/defn ^Nat ci-ho [^Nat n] (ci-apply1 (fn [^Nat x] (Nat.add x x)) n)))
  (is (= 10 ((resolve 'ci-beta) 5)) "beta-redex lambda")
  (is (= 10 ((resolve 'ci-ho) 5)) "lambda passed to a higher-order function"))

(deftest arrow-glyph-no-ambivalence
  ;; => is THE function-type arrow (any position); -> is ALWAYS Clojure threading, never the arrow.
  (eval '(ansatz.core/defn ^Nat ci-thread1 [^Nat n] (-> n (Nat.add 1) (Nat.add 2))))   ; -> threads
  (eval '(ansatz.core/defn ^Nat ci-ho-eq [^{:- (=> Nat Nat)} f ^Nat n] (f n)))          ; => arrow
  (is (= 9 ((resolve 'ci-thread1) 6)) "-> threads in term position")
  (is (= 9 ((resolve 'ci-ho-eq) (resolve 'ci-thread1) 6)) "=> is the function-type arrow"))

(deftest partial-recursion-runs
  ;; The recursion ladder's lenient fallback: a free self-call recursion we don't prove total, marked
  ;; ^:partial, loads as a TRUSTED axiom at its type (not verified, not usable in proofs) and RUNS via
  ;; the original recursive Clojure body. So any recursive fn can be copied over and executed.
  (binding [a/*verbose* false]
    (eval '(ansatz.core/defn ^:partial ^Nat ci-countdown [^Nat n] (if (<= n 0) 0 (ci-countdown (- n 1)))))
    (eval '(ansatz.core/defn ^:partial ^Nat ci-sumto [^Nat n] (if (<= n 0) 0 (+ n (ci-sumto (- n 1))))))
    (is (= [0 0 0] (mapv (resolve 'ci-countdown) [0 5 100])) "free self-call recursion runs")
    (is (= [0 15 55] (mapv (resolve 'ci-sumto) [0 5 10])) "accumulating recursion runs")))

(deftest structural-self-call-auto-ih
  ;; A NATURAL recursive call (ci-suml tl) on a bare recursive match field is auto-mapped to the
  ;; recursor's induction hypothesis — no manual ih_<field> (Lean's structural-recursion
  ;; affordance). It's kernel-verified (not partial) and runs.
  (eval '(ansatz.core/defn ^Nat ci-suml [^{:- (List Nat)} l]
           (match l (List Nat) Nat (nil 0) (cons [hd tl] (+ hd (ci-suml tl))))))
  (is (= [6 30 0] (mapv (resolve 'ci-suml) ['(1 2 3) '(10 20) '()]))
      "natural recursive call auto-maps to the IH — verified + runs")
  ;; multi-parameter: (ci-add2 k n) — recursive field k at the matched position, n carried unchanged.
  (eval '(ansatz.core/defn ^Nat ci-add2 [^Nat m ^Nat n]
           (match m Nat Nat (zero n) (succ [k] (Nat.succ (ci-add2 k n))))))
  (is (= [5 5 7] (mapv (fn [[a b]] ((resolve 'ci-add2) a b)) [[2 3] [0 5] [4 3]]))
      "multi-arg structural self-call (other params unchanged) auto-maps to the IH"))

(deftest loop-recur-counts-to-nat-rec
  ;; The common counting-loop shape (loop [i n acc 0] (if (== i 0) acc (recur (dec i) …)))
  ;; compiles to Nat.rec on the decreasing counter — kernel-verified (not partial) and runs.
  (eval '(ansatz.core/defn ^Nat ci-lsum [^Nat n]
           (loop [i n acc 0] (if (== i 0) acc (recur (dec i) (+ acc i))))))
  (is (= [0 1 15 55] (mapv (resolve 'ci-lsum) [0 1 5 10]))
      "loop/recur counting accumulator → Nat.rec, verified + runs (sum 1..n)"))

(deftest get-record-accessor
  ;; (get rec :field) → keyword projection (a sound record accessor). Full {:keys […]} destructuring
  ;; needs a custom typed desugar (Clojure's injects a dynamic seq-normalization preamble) — follow-on.
  (eval '(ansatz.core/structure CiPoint [] (x Nat) (y Nat)))
  (eval '(ansatz.core/defn ^Nat ci-getx [^{:- CiPoint} p] (get p :x)))
  (is (= 3 ((resolve 'ci-getx) ((resolve '->CiPoint) 3 4))) "(get rec :field) projects"))

(deftest and-or-over-bool-elaborate
  ;; expand-by-default: and/or macroexpand to let*+if, which now typecheck because the if case
  ;; infers its branch type properly (no Nat guessing). Pure structural — no special handler.
  (eval '(ansatz.core/defn ^Bool ci-and [^Bool p ^Bool q] (and p q)))
  (eval '(ansatz.core/defn ^Bool ci-or  [^Bool p ^Bool q] (or p q)))
  (is (= [true false] [((resolve 'ci-and) true true) ((resolve 'ci-and) true false)]) "and over Bool")
  (is (= [true false] [((resolve 'ci-or) false true) ((resolve 'ci-or) false false)]) "or over Bool"))
