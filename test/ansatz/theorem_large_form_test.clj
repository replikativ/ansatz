(ns ansatz.theorem-large-form-test
  "a/theorem with a large statement or proof script: the forms are emitted as strings read at
   load time, so the class initializer stays below the JVM's 64 KB method limit."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]))

(use-fixtures :once fixtures/isolated-session
  (fn [f] (binding [a/*verbose* false] (a/load-init!) (f))))

(deftest long-proof-script-compiles
  ;; 3000 tactics: "Method code too large!" as a quoted constant
  (let [nm (gensym "large_script_")]
    (eval (concat (list 'ansatz.core/theorem nm '[n :- Nat] '(= Nat n n))
                  (repeat 3000 '(try (exact (Eq.refl Nat 0))))
                  ['(rfl)]))
    (is (some? (env/lookup (a/env) (name/from-string (str nm)))))))

(deftest large-literal-round-trips-with-metadata
  (let [form (vec (concat [(with-meta 'x {:- 'Nat})] (repeat 5000 '(f "s" 1N :k))))
        code (#'a/large-form-literal form)
        back (eval code)]
    (is (= `a/read-form-literal (first code)) "large forms are read, not quoted")
    (is (= form back))
    (is (= {:- 'Nat} (select-keys (meta (first back)) [:-])))
    (is (= '(quote [1 2]) (#'a/large-form-literal [1 2])) "small forms stay quoted")))
