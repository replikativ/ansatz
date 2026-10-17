(ns prototype.hosted-file-output-test
  "Execution regression for IR actually produced by the hosted file experiment.
   Source elaboration evidence lives in measurements/hosted-prelude-file.json;
   these small-world tests do not rerun the full frontend or certify its kernel."
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m] [prototype.program-install :as install]
            [prototype.raw-interop :as raw]))
(def answer ["str" ["anonymous"] "answer"])
(defn installed []
  (install/install (m/world {}) (slurp "fixtures/hosted/PreludeIdentity.ir.jsonl")))
(deftest actual-hosted-output-executes-in-each-backend
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [world boxed-entrypoints pending-local-initializers]} (installed)
          session (raw/open-functions (:functions world) {} {:backend backend})
          result (raw/call session world (get boxed-entrypoints answer) [m/erased 42])]
      (is (= 42 (:value result)))
      (is (empty? pending-local-initializers)))))
(deftest polymorphic-identity-transfers-the-same-owned-object-in-independent-forks
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [world boxed-entrypoints]} (installed)
          [world child] (m/allocate world :ctor 0 [])
          [world payload] (m/allocate world :ctor 1 [child])
          session (raw/open-functions (:functions world) {} {:backend backend})
          a (raw/call session world (get boxed-entrypoints answer) [m/erased payload])
          b (raw/call session world (get boxed-entrypoints answer) [m/erased payload])]
      (is (= payload (:value a) (:value b)))
      (is (= 1 (:rc (m/node (:state a) payload))))
      (is (= 1 (:rc (m/node world payload))))
      (is (= (:state a) (:state b)))
      (is (empty? (:heap (m/release (:state a) (:value a) 1))))) ))

(deftest actual-hosted-interop-output-transfers-owned-values-through-clojure
  (doseq [backend [:reference :mutable :jvm]]
    (let [calls (atom 0)
          bindings {"ansatz_host_identity"
                    {:signature {:params [{:ty "erased" :borrow false} {:ty "tobject" :borrow false}]
                                 :return-type "tobject"}
                     :handler (fn [_ world [_ value]] (swap! calls inc) [world value])}}
          installed (install/install (m/world {}) (slurp "fixtures/hosted/PreludeInterop.ir.jsonl")
                      {:lower-extern #(raw/lower bindings %)})
          world (:world installed)
          target (get (:boxed-entrypoints installed) ["str" ["anonymous"] "interopAnswer"])
          [world child] (m/allocate world :ctor 0 [])
          [world payload] (m/allocate world :ctor 7 [child])
          session (raw/open-functions (:functions world) bindings {:backend backend})
          scalar (raw/call session world target [m/erased 42])
          a (raw/call session world target [m/erased payload])
          b (raw/call session world target [m/erased payload])]
      (is (= 42 (:value scalar)))
      (is (= 3 @calls))
      (is (= payload (:value a) (:value b)))
      (is (= 1 (:rc (m/node world payload))))
      (is (= (:state a) (:state b)))
      (is (empty? (:heap (m/release (:state a) payload 1)))))))
