(ns ansatz.persisted-discr-keys-test
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [clojure.edn :as edn]
            [clojure.walk :as walk]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.discr-key-encoding :as ke]
            [ansatz.recall :as recall]
            [ansatz.simp-index :as si]
            [ansatz.state :as state]
            [ansatz.export.storage :as storage]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.instance :as inst]
            [ansatz.tactic.discr-tree :as dt]
            [ansatz.catalogue.scalars :as scalars]))

(def frozen (edn/read-string (slurp "test/fixtures/discr-keys-legacy.edn")))
(defn c [n] (e/const' (name/from-string n) []))
(defn succ [x] (e/app (c "Nat.succ") x))
(defn goal [x] (e/app* (c "Nat.lt") (e/lit-nat 0) x))
(def numeral (succ (succ (succ (c "Nat.zero")))))

(use-fixtures :once fixtures/isolated-session (fn [f] (a/load-init!) (binding [a/*verbose* false] (f))))

(deftest frozen-recall-artifact-survives-current-defaults
  (let [old @state/ansatz-discr-trie old-store @state/ansatz-store]
    (try
      (reset! state/ansatz-discr-trie nil)
      (reset! state/ansatz-store {:store-map {:store ::frozen} :branch "legacy"})
      (with-redefs [recall/catalogue-db (constantly nil)
                    storage/read-derived (fn [store branch artifact]
                                           (is (= [::frozen "legacy" :recall-keys] [store branch artifact]))
                                           (:recall-keys frozen))]
        (is (some #{"Legacy.succ"} (recall/recall-names (goal (succ (e/fvar 100))))))
        (is (some #{"Legacy.three"} (recall/recall-names (goal numeral)))))
      (let [trie @state/ansatz-discr-trie]
        (is (= 1 (ke/encoding trie)))
        (is (thrown? clojure.lang.ExceptionInfo
                     (dt/trie-match trie (recall/query-key (goal numeral) 2))))
        (is (not (some #{"Legacy.three"}
                       (dt/trie-match trie (:keys (recall/query-key (goal numeral) 2)))))))
      (finally
        (reset! state/ansatz-discr-trie old)
        (reset! state/ansatz-store old-store)))))

(deftest frozen-simp-entries-and-materialized-trie-share-the-policy
  (let [st (tc/mk-tc-state-with-locals (a/env) {100 {:tag :local :type (c "Nat")}}) expr (e/app (c "Nat.pred") (succ (e/fvar 100)))]
    (doseq [trie [(si/build-simp-trie (:simp-keys frozen)) (si/read-simp-trie (:simp-trie frozen))]]
      (is (= ["Nat.pred_succ"] (vec (si/candidate-names trie st (a/env) expr)))))))

(deftest versioned-recall-and-catalogue-rows-retain-source-encoding
  (let [row ["new" (pr-str (recall/decl-key (goal (succ (e/mvar 100)))))]
        artifact (ke/entries-artifact [row])
        trie (recall/build-discr-trie (edn/read-string (pr-str artifact)))
        entities (scalars/scalar-entities {:recall-keys (:recall-keys frozen)
                                           :simp-keys (si/key-entries-artifact (:simp-keys frozen))})]
    (is (= 2 (ke/encoding trie)))
    (is (= ["new"] (vec (dt/trie-match trie (recall/query-key (goal (succ (e/fvar 100))) 2)))))
    (is (= 1 (:key-encoding (ke/read-path (:decl/dt-key (first entities))))))
    (is (= 2 (:key-encoding (ke/read-path (first (:decl/simp-key (last entities))))))))
  (doseq [artifact [{:entries []} {:key-encoding 999 :entries []} {:key-encoding 2}]]
    (is (thrown? clojure.lang.ExceptionInfo (recall/build-discr-trie artifact)))
    (is (thrown? clojure.lang.ExceptionInfo (scalars/scalar-entities {:recall-keys artifact}))))
  (is (thrown? clojure.lang.ExceptionInfo
               (ke/checked-query 1 (ke/path-artifact 2 [])))))

(deftest frozen-generic-trie-supports-streaming-and-scored-lookups
  (let [tree (walk/postwalk (fn [x]
                              (if (and (map? x) (= :const (:tag x)) (string? (:name x)))
                                (update x :name name/from-string) x))
                            (:catalogue-chunk frozen))
        query (goal numeral)]
    (is (some #{11} (dt/lookup-simp-tree tree query)))
    (is (some #{11} (map first (dt/trie-match-scored tree
                                                     (ke/path-artifact 1 (dt/expr->keys nil nil query {:key-encoding 1 :pattern? false}))))))
    (is (= 2 (ke/encoding (dt/build-tree []))))
    (is (= 2 (ke/encoding (dt/make-simp-tree []))))))

(deftest frozen-independent-instance-registry-keeps-its-own-encoder
  (let [entry (-> (:instance-entry frozen)
                  (update :name name/from-string)
                  (update :keys #(mapv (fn [[tag n arity]] [tag (name/from-string n) arity]) %)))
        registry {(name/from-string "Inhabited") [entry]}
        st (tc/mk-tc-state (a/env))
        query (e/app (e/const' (name/from-string "Inhabited") [(lvl/succ lvl/zero)]) (c "Nat"))]
    (is (= (c "instInhabitedNat") (inst/synthesize* st (a/env) registry query 0)))
    ;; Stale persisted keys are never compared with the current instance encoder:
    ;; the existing :dt-version reader recomputes from the declaration instead.
    (is (= (c "instInhabitedNat")
           (inst/synthesize* st (a/env)
                             {(name/from-string "Inhabited") [(assoc entry :dt-version 1 :keys [[:other]])]}
                             query 0)))))
