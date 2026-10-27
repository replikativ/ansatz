(ns ansatz.conformance-support
  "Shared runner for the Lean-conformance suites. A suite is a
  Lean reference file under test/lean/ (every theorem accepted by Lean, with Lean's own proof) and
  an ansatz test that states the same theorems with the line-by-line translation of those scripts.

  Theorems that Lean proves but ansatz does not (yet) are listed as KNOWN GAPS with a one-line
  diagnosis: the suite stays green while it prints the score, fails when a passing theorem
  regresses, and fails when a known gap starts passing (so the list is kept honest)."
  (:require [clojure.test :refer [is testing]]
            [ansatz.core :as a]))

(defn attempt
  "Prove one `[name params statement tactics]` within `timeout-ms`: :ok, or the failure message."
  [[nm params stmt tactics] timeout-ms]
  (let [f (future (try (a/prove-theorem nm params stmt tactics) :ok
                       (catch Throwable t (or (.getMessage t) (str (class t))))))
        r (deref f timeout-ms ::timeout)]
    (when (= ::timeout r) (future-cancel f))
    (if (= ::timeout r) (str "timeout after " timeout-ms " ms") r)))

(defn run-suite
  "On a fresh Init env: eval `defs` (in namespace `ns-sym`), then attempt every theorem in order.
   Returns [[name result] …]."
  [ns-sym defs theorems & {:keys [timeout-ms] :or {timeout-ms 60000}}]
  (a/load-init!)
  (binding [a/*verbose* false
            *ns* (the-ns ns-sym)]
    (run! eval defs)
    (mapv (fn [t] [(first t) (attempt t timeout-ms)]) theorems)))

(defn check-suite
  "clojure.test assertions for a suite run. `known-gaps` maps theorem name → diagnosis."
  [suite-name results known-gaps]
  (let [passed (count (filter #(= :ok (second %)) results))]
    (println (str suite-name " conformance: " passed "/" (count results) " Lean scripts go through"
                  (when (seq known-gaps) (str " (" (count known-gaps) " known gaps)"))))
    (doseq [[nm r] results]
      (let [gap (get known-gaps nm)]
        (when (and (not= :ok r) (not gap))
          (println " " nm "-" (subs r 0 (min 300 (count r)))))
        (testing (str nm)
          (if gap
            (is (not= :ok r) (str nm " now passes: remove it from the known gaps (" gap ")"))
            (is (= :ok r))))))))
