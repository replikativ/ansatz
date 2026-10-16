(ns ansatz.codegen-numeric-test
  "Runtime regressions through the real Expr→Clojure compiler, without a downloaded store."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.codegen :as cg]
            [ansatz.codegen.numeric :as numeric]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as level]))

(defn- c [n] (e/const' (name/from-string n) []))
(defn- lit [n]
  (if (neg? n)
    (e/app (c "Int.neg") (e/lit-nat (biginteger (-' n))))
    (e/lit-nat (biginteger n))))
;; Minimal class/constructor metadata exercises real projection selection without
;; loading a proof corpus. These are codegen unit fixtures, not kernel admissions.
(def ^:private numeric-env
  (reduce (fn [en cls]
            (let [nm (name/from-string cls) ctor (name/from-string (str cls ".mk"))
                  ty (e/sort' (level/succ level/zero))]
              (-> en
                  (env/add-constant (env/mk-induct nm [] ty :num-params 3 :ctors [ctor]))
                  (env/add-constant (env/mk-ctor ctor [] ty nm 0 3 1)))))
          (env/empty-env) ["HAdd" "HMul" "HSub" "HDiv" "HMod" "HPow"]))
(def ^:dynamic *runtime-env* numeric-env)
(defn- run [expr] (eval (cg/ansatz->clj *runtime-env* expr [])))
(defn- applied [op x y] (run (e/app* (c op) (lit x) (lit y))))
(defn- instance-expr [op carrier impl]
  (let [cls (subs op 0 (.indexOf ^String op "."))
        beta (if (= op "HPow.hPow") "Nat" carrier)]
    (e/app* (c (str cls ".mk")) (c carrier) (c beta) (c carrier) impl)))
(defn- heterogeneous-with [op carrier instance operands]
  (let [beta (if (= op "HPow.hPow") "Nat" carrier)]
    (reduce e/app (c op) (concat [(c carrier) (c beta) (c carrier) instance] operands))))
(defn- heterogeneous [op carrier operands]
  (let [primitive (str carrier "." (case op "HAdd.hAdd" "add" "HMul.hMul" "mul"
                                                  "HSub.hSub" "sub" "HPow.hPow" "pow"
                                                  "HDiv.hDiv" (if (= carrier "Nat") "div" "ediv")
                                                  "HMod.hMod" (if (= carrier "Nat") "mod" "emod")))]
    (heterogeneous-with op carrier (instance-expr op carrier (c primitive)) operands)))

(deftest exact-integer-powers
  (doseq [op ["Nat.pow" "Int.pow"]
          [x n expected] [[3 34 16677181699666569N]
                          [2 100 1267650600228229401496703205376N]
                          [0 0 1] [0 5 0] [123 0 1]
                          [1 18446744073709551616N 1]]]
    (is (= expected (applied op x n)) [op x n]))
  (doseq [[x n expected] [[-3 35 -50031545098999707N]
                          [-2 100 1267650600228229401496703205376N]
                          [-1 18446744073709551617N -1]]]
    (is (= expected (applied "Int.pow" x n))))
  (is (thrown? IllegalArgumentException (numeric/pow 2 -1)))
  (is (thrown? IllegalArgumentException (numeric/pow 2 0.5))))

(deftest exact-total-division
  (doseq [[x y eq er tq tr fq fr]
          [[-5 2 -3 1 -2 -1 -3 1]
           [-5 -2 3 1 2 -1 2 -1]
           [5 -2 -2 1 -2 1 -3 -1]
           [5 2 2 1 2 1 2 1]
           [-6 2 -3 0 -3 0 -3 0]
           [-6 -2 3 0 3 0 3 0]
           [0 -2 0 0 0 0 0 0]
           [-5 0 0 -5 0 -5 0 -5]
           [5 0 0 5 0 5 0 5]
           [Long/MIN_VALUE -1 9223372036854775808N 0
            9223372036854775808N 0 9223372036854775808N 0]]
          [op expected] [["Int.ediv" eq] ["Int.emod" er]
                         ["Int.tdiv" tq] ["Int.tmod" tr]
                         ["Int.fdiv" fq] ["Int.fmod" fr]]]
    (is (= expected (applied op x y)) [op x y]))
  (doseq [x [0 5 Long/MAX_VALUE 18446744073709551616N]]
    (is (= 0 (applied "Nat.div" x 0)))
    (is (= x (applied "Nat.mod" x 0))))
  (is (= 6148914691236517205N (applied "Nat.div" 18446744073709551616N 3)))
  (is (= 1 (applied "Nat.mod" 18446744073709551616N 3))))

(deftest overflow-promoting-unary-and-subtraction
  (is (= 9223372036854775808N (run (e/app (c "Int.neg") (lit Long/MIN_VALUE)))))
  (is (= 9223372036854775808N (run (e/app (c "Int.natAbs") (lit Long/MIN_VALUE)))))
  (is (= 18446744073709551615N (applied "Int.sub" Long/MAX_VALUE Long/MIN_VALUE)))
  (is (= 0 (applied "Nat.sub" 0 18446744073709551616N))))

(deftest heterogeneous-integer-contracts
  (doseq [[op carrier x y expected]
          [["HPow.hPow" "Nat" 3 34 16677181699666569N]
           ["HPow.hPow" "Int" -3 35 -50031545098999707N]
           ["HDiv.hDiv" "Nat" 5 0 0]
           ["HDiv.hDiv" "Int" -5 2 -3]
           ["HDiv.hDiv" "Int" -5 -2 3]
           ["HDiv.hDiv" "Int" 5 0 0]
           ["HMod.hMod" "Nat" 5 0 5]
           ["HMod.hMod" "Int" -5 -2 1]
           ["HSub.hSub" "Int" Long/MAX_VALUE Long/MIN_VALUE 18446744073709551615N]
           ["HSub.hSub" "Nat" 0 18446744073709551616N 0]
           ["HAdd.hAdd" "Int" Long/MAX_VALUE 1 9223372036854775808N]
           ["HMul.hMul" "Nat" Long/MAX_VALUE 2 18446744073709551614N]]]
    (let [full (heterogeneous op carrier [(lit x) (lit y)])
          value (run (heterogeneous op carrier []))
          partial (run (heterogeneous op carrier [(lit x)]))]
      (is (= expected (run full)) [op carrier])
      (is (= expected (value x y)) [op :flat])
      (is (= expected ((value x) y)) [op :curried])
      (is (= expected (partial y)) [op :partial]))))

(deftest primitive-values-support-flat-and-curried-calls
  (doseq [[op x y expected]
          [["Nat.pow" 3 34 16677181699666569N]
           ["Int.pow" -3 35 -50031545098999707N]
           ["Nat.div" 5 0 0] ["Nat.mod" 5 0 5]
           ["Int.ediv" -5 2 -3] ["Int.emod" -5 -2 1]
           ["Int.tdiv" Long/MIN_VALUE -1 9223372036854775808N]
           ["Int.tmod" -5 0 -5] ["Int.fdiv" 5 -2 -3] ["Int.fmod" 5 -2 -1]
           ["Nat.sub" 0 18446744073709551616N 0]
           ["Nat.add" Long/MAX_VALUE 1 9223372036854775808N]
           ["Int.sub" Long/MAX_VALUE Long/MIN_VALUE 18446744073709551615N]]]
    (let [f (run (c op))
          partial (run (e/app (c op) (lit x)))
          ;; A lambda-bound head uses codegen's unknown-head CURRIED application path.
          caller (run (e/lam "f" (c "Nat")
                              (e/app* (e/bvar 0) (lit x) (lit y)) :default))]
      (is (= expected (f x y)) [op :flat])
      (is (= expected ((f x) y)) [op :curried])
      (is (= expected (partial y)) [op :partial])
      (is (= expected (caller f)) [op :higher-order]))))

(deftest heterogeneous-dispatch-honors-the-instance
  (doseq [op ["HAdd.hAdd" "HMul.hMul" "HSub.hSub" "HDiv.hDiv" "HMod.hMod" "HPow.hPow"]
          carrier ["Nat" "Real"]]
    (let [impl (e/lam "x" (c "Nat") (e/lam "y" (c "Nat") (lit 42) :default) :default)
          inst (instance-expr op carrier impl)
          call #(heterogeneous-with op carrier % [(lit 5) (lit 2)])
          named-env (env/add-constant numeric-env
                                     (env/mk-def (name/from-string "customInstance") []
                                                 (c "Nat") inst))]
      (is (= 42 (run (call inst))) [op :inline])
      (binding [*runtime-env* named-env]
        (is (= 42 (run (call (c "customInstance"))))) [op :named])
      (let [f (run (e/lam "inst" (c "Nat") (call (e/bvar 0)) :default))]
        (is (= 42 (f [(fn [_] (fn [_] 42))])) [op :dynamic]))))
  (testing "unresolved concrete instances fail explicitly instead of selecting by carrier"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Cannot resolve concrete runtime instance"
                         (run (heterogeneous-with "HDiv.hDiv" "Nat" (lit 0) [(lit 5) (lit 2)])))))
  (testing "instance aliases cannot make compilation unfold forever"
    (let [cyclic-env (env/add-constant numeric-env
                                     (env/mk-def (name/from-string "cycleInstance") []
                                                 (c "Nat") (c "cycleInstance")))]
      (binding [*runtime-env* cyclic-env]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unfolding budget"
                             (run (heterogeneous-with "HDiv.hDiv" "Nat" (c "cycleInstance")
                                                      [(lit 5) (lit 2)]))))))))


(deftest float-power-retains-the-existing-floating-profile
  (let [f (run (c "Float.pow"))
        ft (c "Float")
        instance (e/app* (c "HPow.mk") ft ft ft (c "Float.pow"))
        expr (e/app* (c "HPow.hPow") ft ft ft instance (lit 2) (lit 3))]
    (is (= 8.0 (applied "Float.pow" 2 3)))
    (is (= 8.0 (f 2.0 3.0)))
    (is (= 8.0 ((f 2.0) 3.0)))
    (is (= 8.0 (run expr)))))
