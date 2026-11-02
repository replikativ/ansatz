(ns ansatz.kernel.name-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.kernel.name :as name]))

(defn- scoped [base]
  (name/mk-num (name/mk-str (name/mk-str (name/mk-str base "_@") "X") "_hyg") 42))

(deftest structural-append-preserves-components
  (let [parent (name/mk-str (name/anonymous) "main")]
    (doseq [component ["001" "9223372036854775808" "a.b"]]
      (let [suffix (name/mk-str (name/anonymous) component)]
        (is (= (name/mk-str parent component) (name/append parent suffix)))))
    (is (= (name/mk-num parent 1)
           (name/append parent (name/mk-num (name/anonymous) 1))))))

(deftest macro-scope-views-preserve-parent-components
  (let [base (name/mk-str (name/anonymous) "main")
        suffix (name/mk-str (name/anonymous) "h")
        parent (scoped base)
        ;; Imported scopes and the main context must survive independently.
        imported-parent (name/mk-num
                         (name/mk-str
                          (name/mk-str
                           (name/mk-num (name/mk-str (name/mk-str base "_@") "Imported") 7)
                           "X") "_hyg") 42)]
    (doseq [n [parent imported-parent]]
      (is (= n (name/macro-scopes-view-review (name/extract-macro-scopes n))))
      (is (= {:name base :ctx (name/mk-str (name/anonymous) "X")
              :imported (name/mk-num (name/mk-str (name/anonymous) "Imported") 7)
              :scopes '(42)}
             (name/extract-macro-scopes imported-parent)))
      (is (= base (name/erase-macro-scopes parent)))
      (is (= (scoped (name/mk-str base "h")) (name/append parent suffix)))
      (is (= (scoped (name/mk-str base "h")) (name/append base (scoped suffix))))
      (is (= (name/mk-str (name/anonymous) "main.h")
             (name/erase-macro-scopes (scoped (name/mk-str (name/anonymous) "main.h"))))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"both arguments have macro scopes"
                          (name/append parent (scoped suffix))))))
