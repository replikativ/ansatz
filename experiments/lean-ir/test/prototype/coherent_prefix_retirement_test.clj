(ns prototype.coherent-prefix-retirement-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.coherent-owner-ledger :as owners]))

(deftest new-branch-retirement-respects-original-wrapper-disposition
  (doseq [close-original? [false true]]
    (let [ledger (atom {}) events (atom []) receipt {:status :closed :receipt :model}
          invoke #(owners/retire-prefix! ledger :role {:context :original :prefix :prefix}
                    (fn [c p] (is (= [:original :prefix] [c p])) (swap! events conj :retire) receipt)
                    (fn [c] (is (= :original c)) (swap! events conj :close)) close-original?)]
      (is (identical? receipt (invoke)))
      (is (identical? receipt (invoke)))
      (is (= (if close-original? [:retire :close] [:retire]) @events))
      (is (false? (:unsafe-partial? @ledger))))))

(deftest destructive-failures-are-terminal-and-preserve-the-closed-branch-receipt
  (doseq [failure-at [:retire :close :result-validation]]
    (let [ledger (atom {}) calls (atom []) receipt {:status :closed}
          failure (ex-info "partial disposition" {:checkpoint :actual})
          invoke #(owners/retire-prefix! ledger :role {:context :original :prefix :prefix}
                    (fn [& _] (swap! calls conj :retire)
                      (if (= :retire failure-at) (throw failure)
                          (if (= :result-validation failure-at) {:status :unknown} receipt)))
                    (fn [& _] (swap! calls conj :close) (throw failure)) true)]
      (is (thrown? clojure.lang.ExceptionInfo (invoke)))
      (let [before @calls]
        (is (thrown? clojure.lang.ExceptionInfo (invoke)))
        (is (= before @calls)))
      (is (:unsafe-partial? @ledger))
      (is (= :failed (:disposal-phase @ledger)))
      (when (= :close failure-at)
        (is (identical? receipt (get-in @ledger [:cleanup-operations [:role :release-and-close] :result])))))))
