(ns ansatz.structural-runtime-test
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.codegen :as cg]
            [ansatz.codegen.storedef :as sd]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.surface.elaborate :as elab]))

(use-fixtures :once
  (fn [f]
    (let [saved-env @a/ansatz-env
          saved-arity @a/arity-registry
          saved-codegen @a/codegen-registry
          saved-structures @a/structure-registry
          saved-instances @a/ansatz-instance-index]
      (try
        (binding [*ns* (the-ns 'ansatz.structural-runtime-test) a/*verbose* false]
          (a/load-init!)
          (f))
        (finally
          (reset! a/ansatz-env saved-env)
          (reset! a/arity-registry saved-arity)
          (reset! a/codegen-registry saved-codegen)
          (reset! a/structure-registry saved-structures)
          (reset! a/ansatz-instance-index saved-instances))))))

(defn- install! [form] (eval form))
(defn- runtime [sym] @(ns-resolve *ns* sym))

(deftest structural-predefinitions-use-direct-calls
  (let [emit sd/emit-direct-recursion
        emitted (atom {})]
    (with-redefs [sd/emit-direct-recursion
                  (fn [env cname term convention]
                    (let [result (emit env cname term convention)]
                      (swap! emitted assoc cname (:fn-form result))
                      result))]
      (run! install!
            '[(ansatz.core/defn runtime-countdown [fuel :- Nat, n :- Nat] Nat
                (match fuel [zero n]
                       [(succ k) (if (Nat.beq n 0) 0 (runtime-countdown k (- n 1)))]))
              (ansatz.core/defn runtime-factorial [n :- Nat] Nat
                (match n [zero 1] [(succ k) (* (+ k 1) (runtime-factorial k))]))
              (ansatz.core/defn runtime-nested [fuel :- Nat, n :- Nat] Nat
                (let [x n]
                  (match fuel [zero x]
                         [(succ k) (match x [zero 0] [(succ j) (runtime-nested k j)])])))
              (ansatz.core/defn runtime-list [xs :- (List Nat), n :- Nat] Nat
                (match xs [nil n]
                       [(cons h t) (if (Nat.beq n 0) 0 (runtime-list t (- n 1)))]))
              (ansatz.core/inductive RuntimeFuel [] (zero) (succ [n RuntimeFuel]))
              (ansatz.core/defn runtime-custom [fuel :- RuntimeFuel, n :- Nat] Nat
                (match fuel [zero n]
                       [(succ k) (if (Nat.beq n 0) 0 (runtime-custom k (- n 1)))]))]))
    (is (= 0 ((runtime 'runtime-countdown) 10000 14)))
    (is (= 10000 ((runtime 'runtime-countdown) 0 10000)))
    (is (= 0 ((runtime 'runtime-countdown) 10000 10000)))
    (is (= 3628800 ((runtime 'runtime-factorial) 10)))
    (is (= 0 ((runtime 'runtime-nested) 10000 10000)))
    (is (= 0 ((runtime 'runtime-list) (range 10000) 10000)))
    (is (= 0 ((runtime 'runtime-custom) (nth (iterate vector nil) 10000) 14)))
    (doseq [cname ["runtime-countdown" "runtime-nested" "runtime-list" "runtime-custom"]]
      (let [form (get @emitted cname)
            nodes (tree-seq coll? seq form)]
        (is (some #{'recur} nodes) cname)
        (is (not-any? #{'letfn 'clojure.core/delay} nodes) cname)))))

(deftest native-recursors-keep-unused-ih-lazy
  ;; A compiler replacement must not hijack the native lazy-IH lowering.
  ;; Unlike Lean ToImpure.toImpure, ansatz supports direct recursors; this
  ;; existing extension deliberately uses lazy, shared IHs rather than recCompiled.
  (let [saved @a/codegen-registry
        env (env/with-extension (a/env) :csimp {"Nat.rec" "Nat.recCompiled"})]
    (try
      (swap! a/codegen-registry assoc "Nat.recCompiled"
             (fn [& _] (throw (ex-info "strict compiler replacement selected" {}))))
      (let [term (elab/elaborate env
                                 (list (symbol "@Nat.rec.{1}") '(fn [_ :- Nat] Nat) 0
                                       '(fn [k :- Nat, ih :- Nat] (if true 7 (+ ih ih))) 10000))
            form (cg/ansatz->clj env term [])]
        (is (= 7 (eval form)))
        (is (not-any? #{'Nat.recCompiled} (tree-seq coll? seq form))))
      (finally (reset! a/codegen-registry saved)))))

(deftest well-founded-and-hoisted-loops-use-direct-calls
  (run! install!
        '[(ansatz.core/defn runtime-list-loop [n :- Nat] (List Nat)
            (loop [fuel n, xs (List.nil Nat)]
              (if (== fuel 0) xs (recur (dec fuel) (List.cons Nat fuel xs)))))
          (ansatz.core/defn runtime-wf [fuel :- Nat, n :- Nat] Nat
            :termination-by fuel
            (if (<= fuel 0) n
                (if (<= n 0) 0 (runtime-wf (- fuel 1) (- n 1)))))
          (ansatz.core/defn runtime-loop [n :- Nat] Nat
            (loop [acc 0, fuel n]
              (if (== fuel 0) acc (recur (+ acc 1) (- fuel 1)))))])
  (is (= '(1 2 3 4 5) ((runtime 'runtime-list-loop) 5)))
  (is (= 0 ((runtime 'runtime-wf) 10000 14)))
  (is (= 0 ((runtime 'runtime-wf) 10000 10000)))
  (is (= 10000 ((runtime 'runtime-loop) 10000))))

(deftest direct-emission-errors-do-not-execute-kernel-encodings
  (doseq [[cname define!]
          [['runtime-declined
            #(a/define-verified 'runtime-declined '[n :- Nat] 'Nat
               '(match n [zero 0] [(succ k) (runtime-declined k)]))]
           ['runtime-wf-declined
            #(a/define-verified-wf 'runtime-wf-declined '[n :- Nat] 'Nat
               '(if (<= n 0) 0 (runtime-wf-declined (- n 1))) 'n)]]]
    (testing (str cname)
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cannot emit direct recursion"
                            (with-redefs [sd/emit-direct-recursion (fn [& _] nil)] (define!))))
      (is (nil? (env/lookup (a/env) (name/from-string (str cname)))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"emitter bug"
                            (with-redefs [sd/emit-direct-recursion
                                          (fn [& _] (throw (ex-info "emitter bug" {})))]
                              (define!))))
      (is (nil? (get @a/arity-registry (str cname))))
      (is (= 0 ((define!) 5))))))

(deftest hoisted-loop-emitter-errors-propagate
  (is (thrown-with-msg?
       clojure.lang.ExceptionInfo #"emitter bug"
       (with-redefs [sd/emit-direct-recursion
                     (fn [& _] (throw (ex-info "emitter bug" {:kind :codegen-error})))]
         (a/define-verified 'runtime-loop-error '[n :- Nat] 'Nat
           '(loop [acc 0, fuel n]
              (if (== fuel 0) acc (recur (+ acc 1) (- fuel 1)))))))))

(deftest recursive-runtime-implicit-prefix-is-retained
  (let [f (a/define-verified 'runtime-offset '[offset :- Nat :implicit, n :- Nat] 'Nat
            (list 'match 'n ['zero 'offset]
                  ['(succ k) (list '+ 'offset (list (symbol "@runtime-offset") 'offset 'k))]))
        convention (get @a/arity-registry "runtime-offset")]
    (is (= 0 (:erased convention)))
    (is (= 2 (:arity convention)))
    (is (= 8 (f 2 3)))))
