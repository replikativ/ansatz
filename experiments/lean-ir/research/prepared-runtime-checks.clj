(ns prepared-runtime-checks
  "Bounded local validation of prepared runtime fusion; no Source/Init jobs."
  (:require [prepared-runtime :as r]
            [prepared-native-ops :as native]
            [prepared-interpreter-checks :as checks]
            [prototype.mutable :as u]
            [prototype.machine :as m]))

(def ^:private new-machine (ns-resolve 'prepared-interpreter-checks 'machine))
(def ^:private value-var (ns-resolve 'prototype.mutable 'value))
(def ^:private evaluate-var (ns-resolve 'prototype.runtime-prim 'evaluate))
(def ^:private numeric-var (ns-resolve 'prototype.runtime-prim 'numeric))
(def ^:private supported-var (ns-resolve 'prototype.runtime-prim 'supported-symbols))
(def ^:private operations-var (ns-resolve 'prototype.runtime-prim 'scalar-operations))

(defn- ensure! [ok label data]
  (when-not ok (throw (ex-info (str "Prepared runtime check failed: " label) data))))

(defn- outcome [f]
  (try (f) {:kind :ok}
       (catch Throwable error
         {:kind :error :class (class error) :message (ex-message error) :data (ex-data error)})))

(defn- capture [s]
  (let [world (u/freeze s)]
    ;; Numeric = alone would conceal Long/BigInt carrier changes.
    {:world world :local-classes (update-vals (:locals world) class)
     :result-class (class (:result world))}))

(defn- ordinary-scope [thunk _] (thunk))

(defn compare-runtime-step!
  "Prepare under stock definitions, then compare a scoped ordinary/prepared
  step including errors, counters, body, locals, numeric carriers and hook log."
  ([symbol operands locals] (compare-runtime-step! symbol operands locals ordinary-scope))
  ([symbol operands locals scope]
   (let [body [:let 3 [:runtime symbol operands] [:return [:var 3]]]
         functions {:main {:params [] :body body}}
         program (r/prepare-program functions)
         execute (fn [step]
                   (let [s (@new-machine functions body locals)
                         log (atom [])
                         result (scope #(outcome (fn [] (step s))) log)]
                     {:outcome result :calls @log :state (capture s)}))
         expected (execute #(u/step! %))
         actual (execute #(r/step! program %))]
     (ensure! (= expected actual) :step
              {:symbol symbol :operands operands :expected expected :actual actual})
     {:native-sites (:prepared-native-sites program)
      :outcome (:outcome actual) :calls (:calls actual)
      :value (get-in actual [:state :world :locals 3])
      :value-class (get-in actual [:state :local-classes 3])})))

(defn boundary-checks! []
  (let [cases
        [[:add "lean_nat_add" [[:imm 20] [:imm 22]]]
         [:sub "lean_nat_sub" [[:imm 20] [:imm 22]]]
         [:eq "lean_nat_dec_eq" [[:imm 22] [:imm 22]]]
         [:lt "lean_nat_dec_lt" [[:imm 20] [:imm 22]]]
         [:mod "lean_nat_mod" [[:imm 23] [:imm 5]]]
         [:mod-zero "lean_nat_mod" [[:imm 23] [:imm 0]]]
         [:overflow "lean_nat_add" [[:imm Long/MAX_VALUE] [:imm 1]]]
         [:bigint "lean_nat_add" [[:imm 20N] [:imm 22N]]]
         [:negative "lean_nat_add" [[:imm -1] [:imm 22]]]
         [:invalid "lean_nat_add" [[:imm :invalid] [:imm 22]]]
         [:extra-args "lean_nat_add" [[:imm 1] [:imm 2] [:imm 3]]]
         [:missing-arg "lean_nat_add" [[:imm 1]]]]]
    (mapv (fn [[label symbol operands]]
            (let [result (compare-runtime-step! symbol operands {})]
              (ensure! (= (if (contains? #{:extra-args :missing-arg} label) 0 1)
                          (:native-sites result))
                       :site-coverage {:case label :result result})
              [label result])) cases)))

(defn invalidation-checks! []
  (let [symbol "lean_nat_add"
        descriptor (native/prepare-op symbol)
        original-supported @supported-var
        original-operations @operations-var
        invalidations
        [[:signature supported-var (assoc original-supported symbol {:arity 3})]
         [:operation operations-var (assoc original-operations symbol :nat-sub)]]]
    (ensure! (some? descriptor) :descriptor-present {})
    (doseq [[label variable replacement] invalidations]
      (with-redefs-fn {variable replacement}
        #(do
           (ensure! (native/decline? (native/try-op descriptor 20 22)) :registry-invalidates {:case label})
           (ensure! (nil? (native/prepare-op symbol)) :no-learning-changed-registry {:case label}))))
    (let [registry-results
          (mapv (fn [[label variable replacement]]
                  [label
                   (compare-runtime-step!
                    symbol [[:imm 20] [:imm 22]] {}
                    (fn [thunk _] (with-redefs-fn {variable replacement} thunk)))])
                invalidations)
          function-results
          (mapv
           (fn [variable]
             (let [original @variable
                   result
                   (compare-runtime-step!
                    symbol [[:imm 20] [:imm 22]] {}
                    (fn [thunk log]
                      (with-redefs-fn
                        {variable (fn [& arguments]
                                    (swap! log conj :changed-function)
                                    (apply original arguments))}
                        #(do
                           (ensure! (native/decline? (native/try-op descriptor 20 22))
                                    :function-invalidates {:function (str variable)})
                           (ensure! (nil? (native/prepare-op symbol))
                                    :no-learning-changed-function {:function (str variable)})
                           (thunk)))))]
               (ensure! (= [:changed-function] (:calls result))
                        :function-fallback-observed {:function (str variable) :result result})
               [(str variable) result]))
           [evaluate-var numeric-var])]
      {:registry registry-results :functions function-results})))

(defn argument-and-fallback-checks! []
  (let [runtime-original u/runtime-value!
        read-original u/read-local
        value-original @value-var
        operands [[:var 0] [:var 1]]
        captured-custom
        (compare-runtime-step!
         "lean_nat_add" operands {0 20 1 22}
         (fn [thunk log]
           (with-redefs
             [u/runtime-value! (fn [_ symbol args]
                                 (swap! log conj [:selected-custom symbol args]) 777)
              u/read-local (fn [array slot]
                             (swap! log conj [:read slot])
                             (alter-var-root #'u/runtime-value! (constantly runtime-original))
                             (read-original array slot))]
             (thunk))))
        captured-stock
        (compare-runtime-step!
         "lean_nat_add" operands {0 20 1 22}
         (fn [thunk log]
           (with-redefs
             [u/runtime-value! runtime-original
              u/read-local (fn [array slot]
                             (swap! log conj [:read slot])
                             (alter-var-root #'u/runtime-value!
                                             (constantly (fn [& _]
                                                           (swap! log conj :wrong-custom) 777)))
                             (read-original array slot))]
             (thunk))))
        mid-value-change
        (compare-runtime-step!
         "lean_nat_add" operands {0 20 1 22}
         (fn [thunk log]
           (with-redefs-fn
             {value-var value-original
              #'u/read-local
              (fn [array slot]
                (swap! log conj [:read slot])
                (alter-var-root value-var
                                (constantly (fn [_ operand]
                                              (swap! log conj [:changed-value operand]) 100)))
                (read-original array slot))}
             thunk)))
        invalid-first
        (compare-runtime-step!
         "lean_nat_add" operands {0 :invalid 1 22}
         (fn [thunk log]
           (with-redefs [u/read-local (fn [array slot]
                                       (swap! log conj [:read slot])
                                       (read-original array slot))]
             (thunk))))]
    (ensure! (= 777 (:value captured-custom)) :captured-custom {})
    (ensure! (= 42 (:value captured-stock)) :captured-stock {})
    (ensure! (= 120 (:value mid-value-change)) :second-operand-current-value {})
    (ensure! (= [[:read 0] [:read 1]] (:calls invalid-first)) :all-reads-before-validation {})
    {:captured-custom captured-custom :captured-stock captured-stock
     :mid-value-change mid-value-change :invalid-first invalid-first}))

(defn fuel-checks! []
  (let [body [:let 0 [:runtime "lean_nat_add" [[:imm 20] [:imm 22]]]
              [:let 3 [:runtime "lean_nat_sub" [[:var 0] [:imm 1]]]
               [:return [:var 3]]]]
        functions {:main {:params [] :body body}}
        program (r/prepare-program functions)]
    (mapv
     (fn [fuel]
       (let [ordinary (@new-machine functions body {})
             candidate (@new-machine functions body {})
             expected (outcome #(u/run! ordinary fuel))
             actual (outcome #(r/run! program candidate fuel))]
         (ensure! (= expected actual) :fuel-outcome {:fuel fuel :expected expected :actual actual})
         (ensure! (= (capture ordinary) (capture candidate)) :fuel-prefix {:fuel fuel})
         {:fuel fuel :status (u/status candidate) :steps (u/steps candidate)}))
     [-1 0 1 2 3 4 20 0N 1N 4N 1.5 nil])))

(defn native-fork-check! []
  (let [functions
        {:entry {:params [7]
                 :body [:join 42 [9]
                        [:let 13 [:runtime "lean_nat_add" [[:var 7] [:var 9]]]
                         [:return [:var 13]]]
                        [:let 7 [:literal 100]
                         [:call 14 [:direct :worker] [] [:jump 42 [[:var 14]]]]]]}
         :worker {:params [] :body [:suspend 11 [:return [:var 11]]]}}
        program (r/prepare-program functions)
        initial (m/start (m/world functions) :entry [3])
        parent (r/run! program (u/thaw initial) 100)
        saved (u/freeze parent)]
    (ensure! (= 1 (:prepared-native-sites program)) :fork-native-site {})
    (ensure! (= saved (u/freeze (u/run! (u/thaw initial) 100))) :fork-saved-world {})
    (ensure! (= 3 (get-in saved [:frames 0 :joins 42 :locals 7])) :fork-captured-value {})
    (doseq [answer [10 20]]
      (let [ordinary (u/resume! (u/thaw saved) answer)
            candidate (u/resume! (u/thaw saved) answer)]
        (loop [n 0]
          (ensure! (= (capture ordinary) (capture candidate)) :fork-prefix {:answer answer :step n})
          (when (= :running (u/status ordinary))
            (ensure! (< n 100) :fork-bound {})
            (u/step! ordinary)
            (r/step! program candidate)
            (recur (inc n))))
        (ensure! (= (+ 3 answer) (:result (u/freeze candidate))) :fork-result {:answer answer})
        (ensure! (= saved (u/freeze parent)) :fork-parent-unchanged {})))
    {:forks 2 :native-sites (:prepared-native-sites program)}))

(defn check! []
  {:shared (checks/check! {:prepare-program r/prepare-program :step! r/step! :run! r/run!})
   :boundaries (boundary-checks!)
   :invalidation (invalidation-checks!)
   :argument-and-fallback (argument-and-fallback-checks!)
   :fuel (fuel-checks!)
   :native-fork (native-fork-check!)})
