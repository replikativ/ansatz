(ns prototype.klara-branch-model-test
  "Finite differential checks against native Lean output, not a refinement proof."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.string :as str]
            [prototype.branch-lab :as lab]
            [prototype.branch-lab-test :refer [rejected?]]
            [prototype.host-cells-lab :as cells]
            [prototype.host-cells-lab-test :as host]
            [prototype.machine :as m]))

(defn model-rows []
  (mapv #(json/read-str % :key-fn keyword)
        (str/split-lines (slurp "research/klara-branch-model/sample-results.jsonl"))))

(deftest host-cell-adapters-match-the-lean-store-observations
  (let [rows (filter #(= "store" (:kind %)) (model-rows))]
    (is (= 27 (count rows)))
    (doseq [{:keys [base left right observations]} rows
            backend [:persistent :mutable :compiled]
            scoped? [false true]]
      (let [{:keys [store cell] :as f} (host/fixture)
            store (cells/write store cell base)
            [store other] (cells/allocate store base)
            capture (fn [packet] (cells/read (:host-store packet) cell))
            [l r] (host/run-pair (assoc f :store store) backend scoped? left right)]
        (is (= observations
               [(cells/read store cell)
                (cells/read (:host-store l) cell) (capture l)
                (cells/read (:host-store r) cell) (capture r)
                (cells/read (:host-store l) other) (cells/read (:host-store r) other)])
            (str [base left right backend scoped?]))))))

(defn authority-trial [outcomes]
  (let [body (reduce (fn [body n] [:host :lab/emit [[:imm n]] 1 body])
                     [:return [:imm 0]] (reverse (range (count outcomes))))
        functions {:entry {:params [] :body [:suspend 0 body]}}
        world (m/run (m/start (m/world functions) :entry []))
        s (lab/session world {})
        [a b] (lab/fork! s (:initial s))
        run (lab/scoped-runner :compiled functions)
        a (lab/advance-scoped! s a run 0)
        b (lab/advance-scoped! s b run 0)
        attempts (atom 0) second-choice (atom false)
        failed? (rejected?
                 #(lab/adopt! s a
                              (fn [n]
                                (reset! second-choice (rejected? (fn [] (lab/adopt! s b identity))))
                                (swap! attempts inc)
                                (when-not (nth outcomes n)
                                  (throw (ex-info "Synthetic failure" {})))
                                :receipt)))]
    {:attempts @attempts :receipts (count (:completed @(:ledger s)))
     :second-choice-rejected @second-choice
     :replay-rejected (rejected? #(lab/adopt! s a identity))
     :choice-rejected (rejected? #(lab/adopt! s b identity))
     :failed? failed? :phase (:family @(:ledger s))}))

(deftest registry-observations-match-the-lean-authority-example
  (let [rows (filter #(= "authority" (:kind %)) (model-rows))
        _ (is (= 1 (count rows)))
        complete (authority-trial [true true])
        incomplete (authority-trial [true false true])]
    (is (= :adopted (:phase complete)))
    (is (false? (:failed? complete)))
    (is (= :incomplete (:phase incomplete)))
    (is (true? (:failed? incomplete)))
    (is (= (first rows)
           {:kind "authority"
            :secondChoiceRejected (:second-choice-rejected complete)
            :completeAttempts (:attempts complete)
            :completeReceipts (:receipts complete)
            :completeReplayRejected (:replay-rejected complete)
            :incompleteAttempts (:attempts incomplete)
            :incompleteReceipts (:receipts incomplete)
            :incompleteReplayRejected (:replay-rejected incomplete)
            :incompleteChoiceRejected (:choice-rejected incomplete)}))))
