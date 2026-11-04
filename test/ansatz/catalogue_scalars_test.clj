(ns ansatz.catalogue-scalars-test
  "Catalogue artifact conversion without the optional Datahike runtime."
  (:require [clojure.test :refer [deftest is]]
            [clojure.edn :as edn]
            [ansatz.catalogue.scalars :as scalars]
            [ansatz.simp-index :as si]
            [ansatz.discr-key-encoding :as ke]))

(deftest versioned-simp-artifacts-produce-declaration-entities
  (let [entries [["f.eq_1" "[{:tag :star}]"] ["f.eq_1" "[{:tag :lit :val 2}]"] ["f.eq_2" "[{:tag :lit :val 3}]"]]]
    (doseq [version [1 2]]
      (let [artifact (if (= version 1) entries (edn/read-string (pr-str (si/key-entries-artifact entries))))
            [a b c] (map #(ke/stored-path version (second %)) entries)
            expected [{:decl/name "f.eq_1" :decl/simp-key #{a b}}
                      {:decl/name "f.eq_2" :decl/simp-key #{c}}]]
        (is (= entries (si/key-entries artifact)))
        (is (= expected (scalars/scalar-entities {:simp-keys artifact}))))))
  (is (= [] (scalars/scalar-entities {}))))

(deftest invalid-simp-artifacts-fail-before-catalogue-conversion
  (doseq [artifact [{:key-encoding 999 :entries [["f" "KEY"]]}
                    {:key-encoding 2}
                    {:entries [["f" "KEY"]]}
                    {:key-encoding 2 :entries [[:entries 2]]}
                    {:key-encoding 2 :entries [["f" "KEY" "extra"]]}]]
    (is (thrown? clojure.lang.ExceptionInfo (scalars/scalar-entities {:simp-keys artifact})))
    (is (thrown? clojure.lang.ExceptionInfo (si/build-simp-trie artifact)))))
