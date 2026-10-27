(ns resident-cost-probe
  "REPL controls only: captured identity IR, synthetic code-image size, no Init.
   Instrumented spans are inclusive and add overhead; compare uninstrumented
   samples for baseline performance, not parent/child sums."
  (:require [prototype.coherent-jvm-slice :as slice]
            [prototype.resident-frontend :as resident]
            [prototype.resident-code-validation :as code]
            [prototype.resident-frontend-test :as fixture]
            [prototype.hosted-file-test :as hosted]
            [prototype.module-import :as imports]
            [prototype.raw-interop :as raw]))

(def measure (ns-resolve 'prototype.coherent-jvm-slice 'measurement))
(defn median [xs] (nth (vec (sort xs)) (quot (count xs) 2)))
(defn summarize [samples]
  (into {:count (count samples)}
        (for [k [:wall-ns :cpu-ns :allocated-bytes]] [k (median (map k samples))])))

(defn image [n protected?]
  (let [prepared (fixture/prepared :jvm true @hosted/captured)
        extras (into {} (for [i (range n)]
                          [["str" ["anonymous"] (str "CostPadding" i)]
                           {:params [] :body [:return [:imm 0]]}]))
        functions (merge (get-in prepared [:world :functions]) extras)
        functions (if protected?
                    (update functions (:root imports/helpers) assoc :runtime-dependencies (vec (keys extras)))
                    functions)]
    (resident/adopt-prepared
      (-> prepared (assoc-in [:world :functions] functions)
          (assoc :session (raw/open-functions functions {} {:backend :jvm :compile-threshold 1})))
      {:trusted-functions functions :trusted-bindings {}})))

(def operations
  {:context-validation ['prototype.resident-frontend 'valid-context!]
   :target ['prototype.resident-frontend 'target!]
   :closure ['prototype.eval-const 'check-function-closure!]
   :dependencies ['prototype.eval-const 'executable-dependencies]
   :raw-call ['prototype.raw-interop 'call]
   :thaw ['prototype.mutable 'thaw]
   :freeze ['prototype.mutable 'freeze]
   :new-context ['prototype.resident-frontend 'make-context]})

(defn run-case
  "Return counters only; each sampled call closes its returned child Context."
  [n protected? samples instrument?]
  (let [base (image n protected?) loaded (fixture/load-identity base)
        context (:context loaded) spans (atom {})
        data @(.-state ^prototype.resident_frontend.Context context)
        [_ issuance] (measure #(code/validate! (get-in data [:prepared :world :functions])
                                              (get-in data [:prepared :session :bindings])
                                              (:protected-functions data) (:protected-bindings data) nil))
        call #(resident/call context (:file loaded) hosted/answer-name [nil 42] fixture/identity-signature)
        invoke (fn []
                 (let [[result metrics] (measure call)]
                   (assert (= 42 (:value result)))
                   (resident/close! (:context result))
                   metrics))]
    (try
      (dotimes [_ 50] (invoke))
      (let [redefinitions
            (when instrument?
              (into {} (for [[label [ns f]] operations
                             :let [v (ns-resolve ns f) original @v]]
                         [v (fn [& args]
                              (let [[result metrics] (measure #(apply original args))]
                                (swap! spans update label (fnil conj []) metrics)
                                result))])))
            measured (with-redefs-fn (or redefinitions {}) #(mapv (fn [_] (invoke)) (range samples)))]
        {:padding n :protected? protected? :instrumented? instrument?
         :protected-count (count (:protected-functions @(.-state ^prototype.resident_frontend.Context context)))
         :code-proof-issuance issuance
         :public-call (summarize measured)
         :spans (into {} (map (fn [[label rows]] [label (summarize rows)])) @spans)})
      (finally (resident/close! context) (resident/close! base)))))

(defn prototype-case
  "Experimental memoization ONLY for this controlled synthetic fixture. Its keys
   are known immutable names. Not a general runtime cache or authority boundary."
  [n samples]
  (let [v (ns-resolve 'prototype.resident-frontend 'valid-context!)
        matching (ns-resolve 'prototype.resident-frontend 'matching!)
        original @v stamp (volatile! nil)]
    (with-redefs-fn
      {v (fn [data]
           (let [maps [(get-in data [:prepared :world :functions])
                       (get-in data [:prepared :session :bindings])
                       (:protected-functions data) (:protected-bindings data)]]
             (if (and @stamp (every? true? (map identical? maps @stamp)))
               (do (matching (:prepared data)) data)
               (let [checked (original data)] (vreset! stamp maps) checked))))}
      #(run-case n true samples false))))
