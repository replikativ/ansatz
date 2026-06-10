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

(deftest and-or-over-bool-elaborate
  ;; expand-by-default: and/or macroexpand to let*+if, which now typecheck because the if case
  ;; infers its branch type properly (no Nat guessing). Pure structural — no special handler.
  (eval '(ansatz.core/defn ^Bool ci-and [^Bool p ^Bool q] (and p q)))
  (eval '(ansatz.core/defn ^Bool ci-or  [^Bool p ^Bool q] (or p q)))
  (is (= [true false] [((resolve 'ci-and) true true) ((resolve 'ci-and) true false)]) "and over Bool")
  (is (= [true false] [((resolve 'ci-or) false true) ((resolve 'ci-or) false false)]) "or over Bool"))
