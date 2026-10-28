(ns bulk-calls
  "REPL experiment only: direct-entry routing without application maps.
   Load runtime-feasibility.clj first. No native Source or production defaults."
  (:require [prototype.machine :as m]
            [prototype.mutable :as u])
  (:import [java.util Arrays HashMap]))

(defn candidate [ordinary]
  (let [ctl (ns-resolve 'prototype.mutable 'ctl)
        put! (ns-resolve 'prototype.mutable 'put!)
        push-frame! (ns-resolve 'prototype.mutable 'push-frame!)
        callee-slots (ns-resolve 'prototype.mutable 'callee-slots)
        registers (ns-resolve 'prototype.mutable 'registers)
        bind! (ns-resolve 'prototype.mutable 'bind-params!)
        unbound @(ns-resolve 'prototype.mutable 'unbound)]
    (fn [machine target arguments destination continuation]
      (let [name (second target)]
        (if (or (not= :direct (first target))
                (instance? prototype.machine.Builtin name))
          (ordinary machine target arguments destination continuation)
          (do
            ;; Preserve the original failure checkpoint: caller push precedes
            ;; unresolved-function and arity validation.
            (when continuation
              (push-frame! machine continuation destination (ctl machine 1) (ctl machine 2)))
            (let [{:keys [params body] :as function} (get (:functions machine) name)]
              (when-not function (m/fail "Unresolved function" {:target name}))
              (when-not (= (count params) (count arguments))
                (m/fail "Guest arity mismatch" {:target name :expected (count params) :actual (count arguments)}))
              (let [width (callee-slots machine name function)]
                (put! machine 0 body)
                (if continuation
                  (do (put! machine 1 (bind! (registers width nil) params arguments))
                      (put! machine 2 (HashMap.)))
                  (let [old ^objects (ctl machine 1)
                        locals (if (= (alength old) width)
                                 (do (Arrays/fill old unbound) old)
                                 (registers width nil))]
                    (bind! locals params arguments)
                    (put! machine 1 locals)
                    (.clear ^HashMap (ctl machine 2))))))))))))

(defn benchmark [context n]
  (let [ordinary u/call-values! fast (candidate ordinary)
        run (get-in context [:workloads :jvm-private])
        expected ((get-in context [:workloads :reference]) n)]
    (doseq [_ (range 6)] (run n) (with-redefs [u/call-values! fast] (run n)))
    {:n n :trials 7
     :scope "One program, private build/fold, direct-entry variant only; full World parity outside timing; wrapper guard changes mean this is an experiment, not production uptake."
     :runs (vec (for [trial (range 7)
                      mode (if (even? trial) [:ordinary :direct] [:direct :ordinary])]
                  (let [[actual metrics]
                        (prototype.unchanged-program-benchmark/measure
                         #(if (= :direct mode)
                            (with-redefs [u/call-values! fast] (run n))
                            (run n)))]
                    (assert (= expected actual))
                    (assoc metrics :trial trial :mode mode))))}))
