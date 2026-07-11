;; The relational search draws its candidates from the datahike library
;; (disc-tree recall + kernel defeq confirm), per goal — inhabito/expro at
;; library scale. Runs under :datahike:test -d test-datahike.
(ns ansatz.datalog-recall-test
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.datalog.recall :as recall]
            [ansatz.rel :as r]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.level :as lvl]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

(def ^:private env*
  (delay (:env (replay/replay (:decls (parser/parse-ndjson-file "test-data/init-medium.ndjson"))))))

(def ^:dynamic *env* nil)
(def ^:dynamic *trie* nil)

(use-fixtures :once
  (fn [f]
    (let [env (or @env* (throw (ex-info "init-medium not found" {})))
          trie (recall/build-recall-trie env)]      ; index Init for recall
      (binding [*env* env, *trie* trie] (f)))))

(def ^:private le0 (e/const' (nm/from-string "LE.le") [lvl/zero]))
(def ^:private inst (e/const' (nm/from-string "instLENat") []))
(def ^:private nat (e/const' (nm/from-string "Nat") []))
(def ^:private ofnat (e/const' (nm/from-string "OfNat.ofNat") [lvl/zero]))
(defn- nle [a b] (reduce e/app le0 [nat inst a b]))
(defn- onat [n] (reduce e/app ofnat [nat (e/lit-nat n)
                                     (reduce e/app (e/const' (nm/from-string "instOfNatNat") [])
                                             [(e/lit-nat n)])]))

(deftest recall+confirm-narrows-to-applicable-lemmas
  (testing "recall+confirm returns the library lemmas that ACTUALLY apply to
            0 ≤ 5 (incl. Nat.zero_le) — disc-tree over-approximation refined by
            kernel defeq"
    (let [provider (recall/recall+confirm-provider *trie* *env*)
          cands (atom nil)
          _ (r/run 1 (r/state *env*)
                   (r/fresh (nle (onat 0) (onat 5))
                            (fn [g] (fn [s] (reset! cands (map second (provider s g)))
                                      (r/unit s)))))]
      (is (some #{"Nat.zero_le"} @cands)
          "Nat.zero_le is recalled+confirmed for a 0 ≤ _ goal")
      (is (not-any? #{"HShiftLeft.hShiftLeft" "Sub.sub" "Add.add"} @cands)
          "structural catch-alls that don't unify are filtered out by confirm"))))

(deftest search-scales-via-datahike-recall
  (testing "prove 0 ≤ 5 where candidates come from the datahike RECALL+CONFIRM
            query (not a hand-list) — inhabito/expro at library scale, certified"
    (let [provider (recall/recall+confirm-provider *trie* *env*)
          res (r/run 1 (r/state *env*)
                     (r/fresh (nle (onat 0) (onat 5))
                              (fn [g] (r/all (r/expro g provider 2)
                                             (fn [s] (r/unit (assoc s ::g g)))))))
          s (first res)
          c (when s (r/certify s (::g s)))]
      (is (some? s) "proved 0 ≤ 5 from datahike-recalled candidates")
      (is (:ok? c) "kernel-certified")
      (is (= [] (:assumed c)) "no assumptions — a real library proof"))))
