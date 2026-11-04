(ns ansatz.catalogue-scalars-test
  "Catalogue artifact conversion without the optional Datahike runtime."
  (:require [clojure.test :refer [deftest is]]
            [clojure.edn :as edn]
            [ansatz.catalogue.scalars :as scalars]
            [ansatz.simp-index :as si]))

(deftest versioned-simp-artifacts-produce-declaration-entities
  (let [entries [["f.eq_1" "KEY1"] ["f.eq_1" "KEY2"] ["f.eq_2" "KEY3"]]
        artifact (edn/read-string (pr-str (si/key-entries-artifact entries)))
        expected [{:decl/name "f.eq_1" :decl/simp-key #{"KEY1" "KEY2"}}
                  {:decl/name "f.eq_2" :decl/simp-key #{"KEY3"}}]]
    (is (= entries (si/key-entries artifact)))
    (is (= expected (scalars/scalar-entities {:simp-keys artifact})))
    (is (= expected (scalars/scalar-entities {:simp-keys entries})))
    (is (= [] (scalars/scalar-entities {})))))

(deftest invalid-simp-artifacts-fail-before-catalogue-conversion
  (doseq [artifact [{:key-encoding 999 :entries [["f" "KEY"]]}
                    {:key-encoding 2}
                    {:entries [["f" "KEY"]]}
                    {:key-encoding 2 :entries [[:entries 2]]}
                    {:key-encoding 2 :entries [["f" "KEY" "extra"]]}]]
    (is (thrown? clojure.lang.ExceptionInfo (scalars/scalar-entities {:simp-keys artifact})))
    (is (thrown? clojure.lang.ExceptionInfo (si/build-simp-trie artifact)))))
