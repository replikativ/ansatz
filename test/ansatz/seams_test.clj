(ns ansatz.seams-test
  "The runtime SEAMS ansatz.core exposes so an additive runtime layer (wandler) can plug in a
   certified optimizer and collection/relational codegen WITHOUT ansatz depending on it, and with
   ansatz-alone a/defn staying fully runnable:
     - optimize-hook    : (fn [env term] → term') run on the elaborated body just before codegen
     - codegen-registry : Name-string → (fn [env expr names] → clj-form), consulted by ansatz->clj
                          for application heads it doesn't lower natively
   Also checks the metadata + :- type-annotation surfaces."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr]
            [ansatz.kernel.name :as name]))

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

(deftest clojure-fragment-cond-and-do
  (eval '(ansatz.core/defn ^Nat sh-cond [^Nat n] (cond (Nat.ble n 5) 0 (Nat.ble n 10) 1 :else 2)))
  (eval '(ansatz.core/defn ^Nat sh-do   [^Nat n] (do (Nat.add n n))))
  (is (= [0 1 2] (mapv (resolve 'sh-cond) [3 7 20])) "cond → nested if")
  (is (= 42 ((resolve 'sh-do) 21)) "do → last form"))

(deftest type-annotation-surfaces
  (eval '(ansatz.core/defn ^Nat md-add [^Nat a ^Nat b] (+ a b)))          ; metadata ^Type
  (eval '(ansatz.core/defn ^{:- Nat} md-add2 [^{:- Nat} a ^{:- Nat} b] (+ a b))) ; metadata ^{:- T}
  (eval '(ansatz.core/defn sep-add [a :- Nat b :- Nat] Nat (+ a b)))      ; :- separator
  (is (= 5 (((resolve 'md-add) 2) 3))  "metadata ^Type")
  (is (= 5 (((resolve 'md-add2) 2) 3)) "metadata ^{:- T}")
  (is (= 5 (((resolve 'sep-add) 2) 3)) ":- separator"))

(deftest term-elaborator-registry-type-directed
  (testing "lean4 elab_rules seam: a term elaborator sees the live est and dispatches on the
            INFERRED type of its argument — inexpressible with the form→form macro registry"
    (binding [ansatz.core/*verbose* false]
      ((requiring-resolve 'ansatz.surface.api/register-term-elaborator!)
       'tcount
       (fn [est args]
         (let [api-elab (requiring-resolve 'ansatz.surface.api/elab)
               api-type (requiring-resolve 'ansatz.surface.api/arg-type)
               e (requiring-resolve 'ansatz.kernel.expr/app)
               coll (api-elab est (first args))
               ty ((requiring-resolve 'ansatz.surface.api/arg-type) est coll)
               [th targs] (ansatz.kernel.expr/get-app-fn-args ty)
               tnm (when (ansatz.kernel.expr/const? th)
                     (ansatz.kernel.name/->string (ansatz.kernel.expr/const-name th)))]
           (case tnm
             "List" (ansatz.kernel.expr/app*
                     (ansatz.kernel.expr/const' (ansatz.kernel.name/from-string "List.length")
                                                (vec (ansatz.kernel.expr/const-levels th)))
                     (first targs) coll)
             ;; anything else: its sizeOf-free fallback — just 0 (enough for the seam test)
             (ansatz.kernel.expr/lit-nat 0)))))
      (try
        (eval '(ansatz.core/defn seam-tcount [xs :- (List Nat)] Nat (tcount xs)))
        (is (some? (env/lookup (a/env) (name/from-string "seam-tcount")))
            "type-directed term elaborator verified through the seam")
        (is (= 3 (clojure.core/long ((deref (resolve 'seam-tcount)) '(7 8 9))))
            "and the lowered fn runs")
        (finally
          (swap! @(requiring-resolve 'ansatz.surface.ingest/term-elaborator-registry)
                 dissoc 'tcount))))))
