(ns ansatz.clj-check-test
  "check-clojure!: a verified function against its Clojure reading (the same body run by
   clojure.core), on inputs generated from its kernel parameter types."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.clj-check :as cc]))

(defn- define!
  "Evaluate a definition in this namespace (fixtures and tests run with another *ns*)."
  [form]
  (binding [*ns* (the-ns 'ansatz.clj-check-test)] (eval form)))

(defn- init-once [f]
  (binding [a/*verbose* false]
    (a/load-init!)
    (define! '(do (ansatz.core/defn ^Nat cc-fact [^Nat n] (if (== n 0) 1 (* n (cc-fact (- n 1)))))
                  (ansatz.core/defn ^Int cc-clamp [^Bool neg ^Int x] (if neg (if (< x 0) (- x) x) (+ x 1)))
                  (ansatz.core/defn ^Nat cc-len [^{:- (List Nat)} xs]
                    (match xs (List Nat) Nat (nil 0) (cons [h t] (+ 1 (cc-len t)))))))
    (f)))

(use-fixtures :once fixtures/isolated-session init-once)

(defn- defined [sym] (ns-resolve 'ansatz.clj-check-test sym))

(defn- ex-data-in-chain [^Throwable t]
  (some #(when (instance? clojure.lang.ExceptionInfo %) (ex-data %))
        (take-while some? (iterate #(.getCause ^Throwable %) t))))

(deftest guarded-recursion-agrees
  (let [r (cc/check-clojure! (defined 'cc-fact))]
    (is (= :agree (:status r)))
    (is (pos? (:agree r)))))

(deftest bool-and-int-agree
  (is (= :agree (:status (cc/check-clojure! (defined 'cc-clamp))))))

(deftest a-match-body-has-no-clojure-reading
  (is (= :no-clojure-reading (:status (cc/check-clojure! (defined 'cc-len))))))

(deftest a-non-terminating-reading-is-a-divergence
  (testing "Nat subtraction truncates, so (- n 2) reaches 0 from every n in the kernel; the
            Clojure reading never terminates for odd n"
    (define! '(ansatz.core/defn ^Nat cc-nonstruct [^Nat n] (if (== n 0) 0 (cc-nonstruct (- n 2)))))
    (let [data (try (cc/check-clojure! (defined 'cc-nonstruct)) nil
                    (catch clojure.lang.ExceptionInfo e (ex-data e)))]
      (is (some? data) "divergence reported")
      (is (odd? (first (:args data))))
      (is (contains? #{:out-of-fuel :stack-overflow :timeout} (:clojure data)))
      (is (= 0 (:ansatz data))))))

(deftest a-value-divergence-names-the-inputs
  (define! '(ansatz.core/defn ^Nat cc-diff [^Nat a ^Nat b] (- a b)))
  (let [data (try (cc/check-clojure! (defined 'cc-diff)) nil
                  (catch clojure.lang.ExceptionInfo e (ex-data e)))]
    (is (< (first (:args data)) (second (:args data))))
    (is (neg? (:clojure data)))))

(deftest check-metadata-runs-at-definition-time
  (testing "^:check on the name runs check-clojure! after the definition"
    (let [data (try (define! '(ansatz.core/defn ^:check ^Nat cc-checked-diff [^Nat a ^Nat b] (- a b)))
                    nil
                    (catch Throwable t (ex-data-in-chain t)))]
      (is (neg? (:clojure data)) "the divergence is reported when the definition is made"))
    (define! '(ansatz.core/defn ^:check ^Nat cc-checked-sum [^Nat a ^Nat b] (+ a b)))
    (is (= 5 ((defined 'cc-checked-sum) 2 3)))))

(cc/deftest-clojure fact-matches-its-clojure-reading cc-fact)
