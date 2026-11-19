(ns ansatz.surface.lean-namespace-test
  "A namespace with :ansatz/lean metadata writes its a/defn bodies in Lean style, as if every name
   had ^:lean; ^{:lean false} opts one definition back into Clojure surface mode. The setting is
   read from *ns* when a/defn expands, so it is lexical: other namespaces keep Clojure mode."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.config :as config]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]))

(def ^:private lean-ns 'ansatz.lnsopt.lean-model)
(def ^:private attr-ns 'ansatz.lnsopt.attr-model)
(def ^:private plain-ns 'ansatz.lnsopt.plain)

(defn- init-once [f]
  (binding [a/*verbose* false]
    (a/load-init!)
    (try (f)
         (finally (run! remove-ns [lean-ns attr-ns plain-ns])))))

(use-fixtures :once fixtures/isolated-session init-once)

(defn- load-source!
  "Load `source` as a file would be loaded: its `ns` form, then each form in that namespace."
  [source]
  (binding [*ns* (the-ns 'ansatz.surface.lean-namespace-test) a/*verbose* false]
    (load-string source)))

(defn- outcome
  "Evaluate `form` in namespace `ns-sym` (a REPL with that namespace current): :accepted, or the
   refusal reason."
  [ns-sym form]
  (try (binding [*ns* (the-ns ns-sym) a/*verbose* false] (eval form))
       :accepted
       (catch Throwable t
         (or (some #(let [d (ex-data %)] (when (= :clj/refused (:kind d)) (:reason d)))
                   (take-while some? (iterate #(.getCause ^Throwable %) t)))
             (throw t)))))

(defn- run [ns-sym f & args] (apply @(ns-resolve ns-sym f) args))

(deftest lean-namespace-accepts-lean-style-bodies
  (load-source! "(ns ^:ansatz/lean ansatz.lnsopt.lean-model (:require [ansatz.core :as a]))
                 (a/defn ^Nat lnsopt-sub [^Nat a ^Nat b] (- a b))")
  (is (config/lean-namespace? lean-ns))
  (testing "Nat `-` with no guard is accepted and keeps Lean's truncation"
    (is (= 0 (run lean-ns 'lnsopt-sub 3 5)))
    (is (= 2 (run lean-ns 'lnsopt-sub 5 3))))
  (testing "forms evaluated with the namespace current (a REPL) see the same setting"
    (is (= :accepted (outcome lean-ns '(ansatz.core/defn ^Nat lnsopt-sub-repl [^Nat a] (- a 1)))))
    (is (= 0 (run lean-ns 'lnsopt-sub-repl 0))))
  (testing "^{:lean false} on a name opts that definition back into Clojure surface mode"
    (is (= :nat-sub-may-be-negative
           (outcome lean-ns '(ansatz.core/defn ^{:lean false} ^Nat lnsopt-sub-clj [^Nat a ^Nat b]
                               (- a b)))))
    (is (= :accepted
           (outcome lean-ns '(ansatz.core/defn ^{:lean false} ^Nat lnsopt-sub-guarded [^Nat a ^Nat b]
                               (if (<= b a) (- a b) 0)))))
    (is (= 2 (run lean-ns 'lnsopt-sub-guarded 5 3))))
  (testing "^:lean in a lean namespace is still Lean style"
    (is (= :accepted (outcome lean-ns '(ansatz.core/defn ^:lean ^Nat lnsopt-sub-explicit [^Nat a ^Nat b]
                                         (- a b)))))))

(deftest attribute-map-spelling
  (load-source! "(ns ansatz.lnsopt.attr-model {:ansatz/lean true} (:require [ansatz.core :as a]))
                 (a/defn ^Nat lnsopt-attr-sub [^Nat a ^Nat b] (- a b))")
  (is (config/lean-namespace? attr-ns))
  (is (= 0 (run attr-ns 'lnsopt-attr-sub 3 5))))

(deftest other-namespaces-are-unaffected
  (load-source! "(ns ^:ansatz/lean ansatz.lnsopt.lean-model (:require [ansatz.core :as a]))")
  (load-source! "(ns ansatz.lnsopt.plain (:require [ansatz.core :as a]))")
  (is (not (config/lean-namespace? plain-ns)))
  (is (= :nat-sub-may-be-negative
         (outcome plain-ns '(ansatz.core/defn ^Nat lnsopt-plain-sub [^Nat a ^Nat b] (- a b)))))
  (is (= :nat-sub-may-be-negative
         (outcome 'ansatz.surface.lean-namespace-test
                  '(ansatz.core/defn ^Nat lnsopt-test-ns-sub [^Nat a ^Nat b] (- a b)))))
  (testing "^:lean still opts a single definition out in a Clojure namespace"
    (is (= :accepted (outcome plain-ns '(ansatz.core/defn ^:lean ^Nat lnsopt-plain-lean [^Nat a ^Nat b]
                                          (- a b)))))))
