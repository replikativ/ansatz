(ns ansatz.surface.nat-sub-obligation-test
  "A Clojure `-` at Nat is accepted only where it cannot go below 0: the obligation `b ≤ a` is
   proved by omega from the guards in scope, else the definition is refused
   (:nat-sub-may-be-negative). Explicit Lean spellings and ^:lean bodies keep truncation."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]))

(defn- init-once [f]
  (binding [a/*verbose* false] (a/load-init!) (f)))

(use-fixtures :once fixtures/isolated-session init-once)

(defn- outcome [form]
  (try (binding [*ns* (the-ns 'ansatz.surface.nat-sub-obligation-test) a/*verbose* false]
         (eval form))
       :accepted
       (catch Throwable t
         (or (some #(:reason (ex-data %)) (take-while some? (iterate #(.getCause ^Throwable %) t)))
             (throw t)))))

(defn- run [sym & args]
  (apply (ns-resolve 'ansatz.surface.nat-sub-obligation-test sym) args))

(deftest accepted-under-guards
  (is (= :accepted (outcome '(ansatz.core/defn ^Nat ns-le [^Nat a ^Nat b] (if (<= b a) (- a b) 0)))))
  (is (= [2 0] [(run 'ns-le 5 3) (run 'ns-le 3 5)]))
  (is (= :accepted (outcome '(ansatz.core/defn ^Nat ns-lt [^Nat a ^Nat b] (if (< a b) 0 (- a b))))))
  (is (= :accepted (outcome '(ansatz.core/defn ^Nat ns-eq [^Nat n] (if (== n 0) 0 (- n 1))))))
  (is (= :accepted (outcome '(ansatz.core/defn ^Nat ns-fact [^Nat n] (if (== n 0) 1 (* n (ns-fact (- n 1))))))))
  (is (= 120 (run 'ns-fact 5)))
  (testing "a Bool guard (Nat.beq) is read as the proposition it decides"
    (is (= :accepted (outcome '(ansatz.core/defn ^Nat ns-beq [^Nat n] (if (Nat.beq n 0) 0 (- n 1)))))))
  (testing "a let binding is a fact"
    (is (= :accepted (outcome '(ansatz.core/defn ^Nat ns-let [^Nat a ^Nat b] (let [m (+ a b)] (- m a))))))
    (is (= 4 (run 'ns-let 3 4))))
  (testing "n-ary subtraction, every step"
    (is (= :accepted (outcome '(ansatz.core/defn ^Nat ns-nary [^Nat a ^Nat b ^Nat c]
                                 (if (<= (+ b c) a) (- a b c) 0)))))))

(deftest refused-where-it-may-go-negative
  (is (= :nat-sub-may-be-negative (outcome '(ansatz.core/defn ^Nat ns-bad [^Nat a ^Nat b] (- a b)))))
  (is (= :nat-sub-may-be-negative (outcome '(ansatz.core/defn ^Nat ns-bad1 [^Nat a] (- a 1)))))
  (testing "a guard that does not imply b ≤ a: n ≠ 0 does not give 2 ≤ n"
    (is (= :nat-sub-may-be-negative
           (outcome '(ansatz.core/defn ^Nat ns-two [^Nat n] (if (== n 0) 0 (ns-two (- n 2))))))))
  (testing "the refusal names the form and how to resolve it"
    (let [d (try (binding [*ns* (the-ns 'ansatz.surface.nat-sub-obligation-test) a/*verbose* false]
                   (eval '(ansatz.core/defn ^Nat ns-bad2 [^Nat a ^Nat b] (+ 1 (- a b)))))
                 nil
                 (catch Throwable t
                   (some #(when (:reason (ex-data %)) (ex-data %))
                         (take-while some? (iterate #(.getCause ^Throwable %) t)))))]
      (is (= '(- a b) (:form d)))
      (is (re-find #"Int" (:hint d))))))

(deftest lean-spellings-keep-truncation
  (is (= :accepted (outcome '(ansatz.core/defn ^Nat ns-natsub [^Nat a ^Nat b] (Nat.sub a b)))))
  (is (= 0 (run 'ns-natsub 3 5)))
  (is (= :accepted (outcome '(ansatz.core/defn ^:lean ^Nat ns-lean [^Nat a ^Nat b] (- a b)))))
  (is (= 0 (run 'ns-lean 3 5)))
  (testing "Int subtraction has no obligation"
    (is (= :accepted (outcome '(ansatz.core/defn ^Int ns-int [^Int a ^Int b] (- a b)))))
    (is (= -2 (run 'ns-int 3 5)))))

(deftest theorem-statements-are-unaffected
  (is (= :accepted (outcome '(ansatz.core/theorem ns-thm [n :- Nat] (= Nat (- n n) 0) (omega))))))

(deftest partial-bodies-are-covered
  (is (= :nat-sub-may-be-negative
         (outcome '(ansatz.core/defn ^:partial ^Nat ns-part [^Nat n] (if (== n 3) 0 (ns-part (- n 1)))))))
  (is (= :accepted
         (outcome '(ansatz.core/defn ^:partial ^Nat ns-part2 [^Nat n] (if (<= n 0) 0 (ns-part2 (- n 1))))))))
