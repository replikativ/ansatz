(ns ansatz.seams-test
  "The runtime SEAMS ansatz.core exposes so an additive runtime layer (wandler) can plug in a
   certified optimizer and collection/relational codegen WITHOUT ansatz depending on it, and with
   ansatz-alone a/defn staying fully runnable:
     - optimize-hook    : (fn [env term] → term') run on the elaborated body just before codegen
     - codegen-registry : Name-string → (fn [env expr names] → clj-form), consulted by ansatz->clj
                          for application heads it doesn't lower natively
   Also checks the metadata + :- type-annotation surfaces."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]))

(defn- with-init [f]
  (a/load-init!)                       ; bundled Init — enough for Nat / +
  (binding [a/*verbose* false] (f)))
(use-fixtures :once with-init)

(deftest optimize-hook-fires-and-base-still-runs
  (let [called (atom 0)]
    (reset! a/optimize-hook (fn [_env term] (swap! called inc) term))
    (try
      (eval '(ansatz.core/defn ^Nat sh-dbl [^Nat n] (+ n n)))
      (is (pos? @called) "define-verified ran the optimize hook on the elaborated body")
      (is (= 42 ((resolve 'sh-dbl) 21)) "and the function still runs (hook returned the term unchanged)")
      (finally (reset! a/optimize-hook nil)))))

(deftest optimize-hook-unset-is-a-noop
  (reset! a/optimize-hook nil)
  (eval '(ansatz.core/defn ^Nat sh-id [^Nat n] n))
  (is (= 7 ((resolve 'sh-id) 7)) "no hook → base codegen, runs"))

(deftest codegen-registry-fires
  (eval '(ansatz.core/defn ^Nat sh-base [^Nat n] (+ n n)))
  (swap! a/codegen-registry assoc "sh-base" (fn [_env _expr _names] 777))
  (try
    (eval '(ansatz.core/defn ^Nat sh-caller [^Nat n] (sh-base n)))
    (is (= 777 ((resolve 'sh-caller) 5))
        "ansatz->clj consulted the codegen-registry for the sh-base head (not the user-fn fallback)")
    (finally (reset! a/codegen-registry {}))))

(deftest type-annotation-surfaces
  (eval '(ansatz.core/defn ^Nat md-add [^Nat a ^Nat b] (+ a b)))          ; metadata ^Type
  (eval '(ansatz.core/defn ^{:- Nat} md-add2 [^{:- Nat} a ^{:- Nat} b] (+ a b))) ; metadata ^{:- T}
  (eval '(ansatz.core/defn sep-add [a :- Nat b :- Nat] Nat (+ a b)))      ; :- separator
  (is (= 5 (((resolve 'md-add) 2) 3))  "metadata ^Type")
  (is (= 5 (((resolve 'md-add2) 2) 3)) "metadata ^{:- T}")
  (is (= 5 (((resolve 'sep-add) 2) 3)) ":- separator"))
