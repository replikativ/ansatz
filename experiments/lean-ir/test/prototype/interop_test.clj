(ns prototype.interop-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.import-ir :as ir]
            [prototype.interop :as interop]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.lazy-runtime :as lazy]))

(def catalogue (delay (ir/index-bundles ["fixtures/interop.jsonl"])))
(def bindings
  {"ansatz_host_transform" {:arguments [:nat] :result :nat :fn (fn [_ x] (inc x))}
   "ansatz_host_apply" {:arguments [:closure :nat] :result :nat
                       :fn (fn [{:keys [invoke]} f x] (+ (invoke f [x]) (invoke f [x])))}})
(defn session [backend]
  (interop/open-session @catalogue (keys (:declarations @catalogue)) bindings backend))

(deftest real-lean-host-and-reentrant-callbacks
  (let [results (for [backend [:reference :mutable :jvm]]
                  (let [s (session backend)
                        direct (interop/call s "InteropProbe.callHost" [42])
                        nested (interop/call s "InteropProbe.roundTrip" [42])
                        callback (interop/call s "InteropProbe.applyCallback"
                                               [(interop/function-ref "InteropProbe.hostTransform") 42])]
                    (is (= 43 (:value direct)))
                    (is (= 84 (:value nested)))
                    (is (= 43 (:value callback)))
                    (is (empty? (get-in nested [:state :heap])))
                    (is (empty? (get-in callback [:state :heap])))
                    [direct nested callback]))]
    (is (apply = results))))

(deftest host-boundary-fuel-and-snapshot-equivalence
  (let [functions (:functions (session :reference))
        root (interop/resolve (session :reference) "InteropProbe.roundTrip")
        initial (m/start (m/world functions) root [42])
        boundary (m/run initial)
        program (lazy/open-program functions)]
    (is (= :host-call (:status boundary)))
    (doseq [fuel (range (+ 2 (get-in boundary [:stats :steps])))]
      (is (= (m/run initial fuel) (u/freeze (lazy/run! program (u/thaw initial) fuel)))))
    (is (= boundary (u/freeze (u/thaw boundary))))
    (let [left (m/run (m/resume boundary 84))
          right (u/freeze (lazy/run! program (u/resume! (u/thaw boundary) 84)))]
      (is (= left right))
      (is (= 84 (:result left))))))

(deftest binding-validation-and-budget
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"host binding"
                        (interop/open-session @catalogue (keys (:declarations @catalogue)) {})))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"small Nat"
                        (interop/call (session :jvm) "InteropProbe.callHost" [-1])))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"budget"
                        (interop/call (assoc (session :jvm) :fuel 0) "InteropProbe.callHost" [42]))))

(deftest bindings-are-session-local-and-callbacks-cannot-escape
  (let [old (session :jvm)
        child (assoc-in old [:bindings "ansatz_host_transform" :fn] (fn [_ _] 99))
        escaped (atom nil)
        callback-session (assoc-in old [:bindings "ansatz_host_apply" :fn]
                                   (fn [{:keys [invoke]} f x]
                                     (reset! escaped #(invoke f [x])) (invoke f [x])))]
    (is (= 43 (:value (interop/call old "InteropProbe.callHost" [42]))))
    (is (= 99 (:value (interop/call child "InteropProbe.callHost" [42]))))
    (is (= 43 (:value (interop/call old "InteropProbe.callHost" [42]))))
    (is (= 42 (:value (interop/call callback-session "InteropProbe.roundTrip" [42]))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"synchronous host invocation" (@escaped)))))

(deftest shared-code-cache-does-not-capture-host-implementations
  (let [cache (lazy/code-cache)
        roots (keys (:declarations @catalogue))
        old (interop/open-session @catalogue roots bindings :jvm cache)
        child (interop/open-session @catalogue roots
                                    (assoc-in bindings ["ansatz_host_transform" :fn] (fn [_ _] 99)) :jvm cache)]
    (is (= 43 (:value (interop/call old "InteropProbe.callHost" [42]))))
    (is (= 99 (:value (interop/call child "InteropProbe.callHost" [42]))))
    (is (zero? (:compiled (lazy/summary (:program child)))))
    (is (pos? (:cache-hits (lazy/summary (:program child)))))))
