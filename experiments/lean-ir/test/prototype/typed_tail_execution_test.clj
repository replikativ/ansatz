(ns prototype.typed-tail-execution-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.java.io :as io]
            [clojure.data.json :as json]
            [prototype.typed-tail-execution :as execution]
            [prototype.typed-tail-test :as fixture]
            [prototype.scalar-wrapper-test :as scalar-fixture]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.block-compile :as b]
            [prototype.lazy-runtime :as lazy]
            [prototype.typed-tail :as prep]
            [prototype.runtime-prim :as runtime]
            [prototype.scalar :as scalar]
            [prototype.slot-count :as slots]
            [prototype.walk :as walk]))

(defn config [input]
  {:typed-functions (:typed input) :roots (vec (keys (:typed input))) :descriptors (:descriptors input)
   :profile scalar-fixture/profile :budgets fixture/budgets})
(defn options [input] {:typed-tail (config input)})
(defn context [input] (execution/prepare-context (:runtime input) (config input) {}))
(defn start [input label args]
  (m/start (m/world (:runtime input)) (fixture/target (:typed input) label) args))
(defn run [backend program initial fuel]
  (case backend
    :reference (m/run initial fuel)
    :mutable (u/freeze (u/run! (u/thaw initial) fuel))
    :lazy (u/freeze (lazy/run! program (u/thaw initial) fuel))
    :eager (u/freeze (b/run! program (u/thaw initial) fuel))))
(defn cases [input file]
  (mapv (fn [{:keys [function args result]}]
          {:label function :args (mapv scalar-fixture/carrier args) :result (bigint result)})
        (:cases (json/read-str (slurp (io/file fixture/fixture-dir file)) :key-fn keyword))))
(defn carrier-shape [state]
  {:locals (update-vals (:locals state) class) :result (class (:result state))
   :frames (mapv #(update-vals (:locals %) class) (:frames state))
   :joins (update-vals (:joins state) #(update-vals (:locals %) class))})
(defn check-prefixes [input examples]
  (let [fs (:runtime input) opts (options input)
        programs [[:lazy (lazy/open-program fs opts)] [:eager (b/compile-program fs nil opts)] [:mutable nil]]]
    (doseq [{:keys [label args result]} examples]
      (let [initial (start input label args) terminal (m/run initial) steps (get-in terminal [:stats :steps])]
        (is (= result (:result terminal)))
        (doseq [fuel (range (+ steps 2)) [backend program] programs]
          (let [actual (run backend program initial fuel) prefix (m/run initial fuel)]
            (is (= prefix actual))
            (is (= (carrier-shape prefix) (carrier-shape actual)))
            (when (= :paused (:status actual))
              (let [saved actual left (run backend program (m/resume saved nil) 10000)
                    right (run backend program (m/resume saved nil) 10000)]
                (is (= terminal left right))
                (is (= saved actual))))))))))

(deftest actual-sums-every-fuel-and-native-wrap-results
  (let [input (fixture/bundle "scalar-wrapper-programs.jsonl")]
    (check-prefixes input (cases input "scalar-wrapper-program-values.json"))))

(deftest actual-mutual-arity-branches-identity-constants-and-terminal-intrinsics
  (let [input (fixture/bundle "typed-tail-programs.jsonl")]
    (check-prefixes input (cases input "typed-tail-program-values.json"))))

(deftest executor-route-carriers-and-historical-frame-peak
  (let [input (fixture/bundle "typed-tail-programs.jsonl") ctx (context input)]
    (doseq [{:keys [label args]} (cases input "typed-tail-program-values.json")]
      (let [initial (assoc-in (start input label args) [:stats :max-frames] 7)
            name (fixture/target (:typed input) label)
            plan (execution/compile-entry ctx (get-in input [:runtime name :body]))
            machine (execution/bind-context (u/thaw initial) ctx)
            route ((:execute-budget! plan) machine 10000)
            actual (u/freeze machine) expected (m/run initial)]
        (is (= :specialized route))
        (is (= expected actual))
        (is (= 7 (get-in actual [:stats :max-frames])))
        (is (= (class (:result expected)) (class (:result actual))))
        (is (= (update-vals (:locals expected) class) (update-vals (:locals actual) class)))))))

(defn attempt [f machine]
  (try (let [route (f machine)] {:route route :state (u/freeze machine)})
       (catch Throwable t {:error [(class t) (.getMessage t) (ex-data t)] :state (u/freeze machine)})))
(defn execute-plan [input label initial fuel]
  (let [ctx (context input) name (fixture/target (:typed input) label)
        plan (execution/compile-entry ctx (get-in input [:runtime name :body]))
        machine (execution/bind-context (u/thaw initial) ctx)]
    (assoc (attempt #((:execute-budget! plan) % fuel) machine) :factory-realized? (realized? (:factory ctx)))))

(deftest carrier-local-join-frame-and-counter-declines-progress-exactly
  (let [input (fixture/small-bundle (fixture/row "identity" (fixture/return-node 0)))
        base (start input "identity" [7])
        variants [(start input "identity" [(biginteger 7)])
                  (assoc-in base [:locals 99] 4)
                  (assoc base :joins {9 {:params [] :locals {} :body [:return [:imm 0]]}})
                  (assoc-in base [:stats :max-frames] -7)
                  (assoc-in base [:stats :steps] -1)]]
    (doseq [initial variants]
      (let [actual (execute-plan input "identity" initial 10)
            expected (u/freeze (u/run! (u/thaw initial) 10))]
        (is (= :interpreted (:route actual)))
        (is (= expected (:state actual)))
        (is (false? (:factory-realized? actual)))))
    (let [name (fixture/target (:typed input) "identity") caller (fixture/name-of "caller")
          fs (assoc (:runtime input) caller {:params [0] :body [:call 1 [:direct name] [[:var 0]] [:return [:var 1]]]})
          chosen (assoc input :runtime fs)
          paused (m/run (m/start (m/world fs) caller [7]) 1)
          initial (m/resume paused nil)
          actual (execute-plan chosen "identity" initial 10)]
      (is (= :interpreted (:route actual)))
      (is (= (m/run initial 10) (:state actual))))))

(deftest failed-intrinsic-and-missing-case-retain-committed-mutable-prefix
  (let [input (fixture/bundle "scalar-wrapper-programs.jsonl")]
    (doseq [args [["invalid" 0] [nil 0] [-1 0] [18446744073709551616N 0]]]
      (let [initial (start input "sum64" args)
            expected (dissoc (attempt #(u/run! % 100) (u/thaw initial)) :route)
            actual (execute-plan input "sum64" initial 100)]
        (is (= expected (dissoc actual :route :factory-realized?)))
        (is (false? (:factory-realized? actual))))))
  (let [r {:name (fixture/name-of "missing")
           :ir {:fdecl {:f (fixture/name-of "missing") :xs [(fixture/parameter 0 "uint8")]
                        :type "uint8" :info {}
                        :body ["vdecl" {:idx 1} "uint8" {:lit {:v {:num {:v 9}}}}
                               ["case" (fixture/name-of "UInt8") {:idx 0} "uint8"
                                [["ctor" {:cidx 0} ["ret" (fixture/var-arg 1)]]]]]}}}
        input (fixture/small-bundle r) initial (start input "missing" [2])
        expected (dissoc (attempt #(u/run! % 10) (u/thaw initial)) :route)
        actual (execute-plan input "missing" initial 10)]
    (is (= expected (dissoc actual :route :factory-realized?)))
    (is (= 2 (get-in actual [:state :stats :steps])))
    (is (= 9 (get-in actual [:state :locals 1])))))

(deftest checked-counter-overflow-prefix-and-bigint-fuel
  (let [body ["vdecl" {:idx 1} "uint64" {:lit {:v {:num {:v 7}}}} (fixture/return-node 1)]
        input (fixture/small-bundle (fixture/row "constant" body))]
    (doseq [steps [(dec Long/MAX_VALUE) Long/MAX_VALUE]]
      (let [initial (assoc-in (start input "constant" [3]) [:stats :steps] steps)
            expected (dissoc (attempt #(u/run! % 2) (u/thaw initial)) :route)
            actual (execute-plan input "constant" initial 2)
            ref-error (try (m/run initial 2) nil (catch Throwable t [(class t) (.getMessage t)]))]
        (is (= expected (dissoc actual :route :factory-realized?)))
        (is (= ref-error (take 2 (:error actual)))))))
  (let [input (fixture/bundle "scalar-wrapper-programs.jsonl") initial (start input "sum64" [10 0])
        fuel 18446744073709551616N actual (execute-plan input "sum64" initial fuel)]
    (is (= :specialized (:route actual)))
    (is (= (m/run initial fuel) (:state actual)))))

(deftest long-loop-quantum-boundaries-preserve-snapshots-and-carriers
  (let [input (fixture/bundle "scalar-wrapper-programs.jsonl") fs (:runtime input)
        program (lazy/open-program fs (options input)) initial (start input "sum64" [10000 0])]
    (doseq [fuel [53247 53248 53249 106496 130006 130007]]
      (let [expected (m/run initial fuel) actual (run :lazy program initial fuel)]
        (is (= expected actual))
        (is (= (update-vals (:locals expected) class) (update-vals (:locals actual) class)))))))

(deftest missing-case-after-a-completed-tail-chunk-replays-only-current-entry
  (let [name (fixture/name-of "missing-after-tail")
        r {:name name :ir {:fdecl {:f name :xs [(fixture/parameter 0 "uint8")] :type "uint8" :info {}
                                  :body ["case" (fixture/name-of "UInt8") {:idx 0} "uint8"
                                         [["ctor" {:cidx 0}
                                           ["vdecl" {:idx 1} "uint8" {:lit {:v {:num {:v 1}}}}
                                            ["vdecl" {:idx 2} "uint8" {:fap {:c name :ys [(fixture/var-arg 1)]}} ["ret" (fixture/var-arg 2)]]]]
                                          ["ctor" {:cidx 1}
                                           ["vdecl" {:idx 3} "uint8" {:lit {:v {:num {:v 9}}}}
                                            ["case" (fixture/name-of "UInt8") {:idx 0} "uint8"
                                             [["ctor" {:cidx 0} ["ret" (fixture/var-arg 3)]]]]]]]]}}}
        input (fixture/small-bundle r) initial (start input "missing-after-tail" [0])
        expected (dissoc (attempt #(u/run! % 10) (u/thaw initial)) :route)
        fallback (atom []) original u/run!
        actual (with-redefs [u/run! (fn [machine fuel]
                                     (swap! fallback conj {:steps (u/steps machine) :locals (:locals (u/freeze machine)) :fuel fuel})
                                     (original machine fuel))]
                 (execute-plan input "missing-after-tail" initial 10))]
    (is (= expected (dissoc actual :route :factory-realized?)))
    (is (= [{:steps 3 :locals {0 1} :fuel 7}] @fallback))
    (is (= 6 (get-in actual [:state :stats :steps])))
    (is (= {0 1, 3 9} (get-in actual [:state :locals])))))

(deftest normalization-once-public-validation-cache-reuse-and-context-lifetime
  (let [input (fixture/bundle "scalar-wrapper-programs.jsonl") fs (:runtime input) opts (options input)
        calls (atom 0) original prep/prepare-region cache (lazy/code-cache)
        [a b] (with-redefs [prep/prepare-region (fn [& args] (swap! calls inc) (apply original args))]
                (let [a (lazy/open-program fs opts cache) b (lazy/open-program fs opts cache)
                      initial (start input "sum64" [10 0])]
                  (lazy/run! a (u/thaw initial) 1000)
                  (lazy/run! b (u/thaw initial) 1000)
                  [a b]))]
    (is (= 2 @calls))
    (is (= 1 (count @cache)))
    (is (= 1 (:cache-hits (lazy/summary b))))
    (let [ctx-a (get-in a [:options :prototype.block-compile/tail-provider])
          ctx-b (get-in b [:options :prototype.block-compile/tail-provider])]
      (is (= (:key ctx-a) (:key ctx-b))))
    (let [owned (context input)]
      (is (thrown? ClassCastException (assoc owned :factory (delay {:code (constantly :forged)})))))
    (let [used (atom 0) malicious {:bind (fn [machine] (swap! used inc) machine) :compile (fn [_] (swap! used inc))}
          forged (assoc opts :prototype.block-compile/tail-provider malicious :unused-world (Object.))
          program (lazy/open-program fs forged cache)]
      (is (not (contains? (:options program) :typed-tail)))
      (is (not (contains? (:options program) :unused-world)))
      (is (nil? (meta (:options program))))
      (is (= 55N (:result (u/freeze (lazy/run! program (u/thaw (start input "sum64" [10 0])) 1000)))))
      (is (zero? @used)))
    (let [body (get-in fs [(fixture/target (:typed input) "sum64") :body])
          bad (assoc-in opts [:typed-tail :profile :schema] "invalid")]
      (is (thrown? clojure.lang.ExceptionInfo
                   (b/compile-runtime-block fs body (assoc bad :prototype.block-compile/tail-provider (get-in a [:options :prototype.block-compile/tail-provider]))))))))

(deftest runtime-helper-redefinitions-before-and-after-compilation-decline
  (let [input (fixture/bundle "scalar-wrapper-programs.jsonl") initial (start input "sum64" [2 0])
        ctx (context input) name (fixture/target (:typed input) "sum64") old (execution/compile-entry ctx (get-in input [:runtime name :body]))
        changes [{#'runtime/evaluate (fn [_ world _ _] [world 1N])}
                 {#'scalar/integer! (fn [_ _] 0N)}
                 {#'u/function-slots (fn [_] 1)}
                 {#'slots/function-slots (fn [_] 1)}
                 {#'walk/forms (fn [_] [])}]]
    (doseq [change changes]
      (with-redefs-fn change
        (fn []
          (let [expected (dissoc (attempt #(u/run! % 8) (u/thaw initial)) :route)]
            (doseq [[chosen plan] [[ctx old] (let [new (context input)] [new (execution/compile-entry new (get-in input [:runtime name :body]))])]]
              (let [machine (execution/bind-context (u/thaw initial) chosen)
                    actual (attempt #((:execute-budget! plan) % 8) machine)]
                (is (= expected (dissoc actual :route)))
                (when-not (:error actual) (is (= :interpreted (:route actual))))))))))))

(deftest missing-case-after-cross-function-tail-restores-new-register-layout
  (let [a (fixture/name-of "A") g (fixture/name-of "G")
        ra {:name a :ir {:fdecl {:f a :xs [(fixture/parameter 0 "uint8")] :type "uint8" :info {}
                                :body ["vdecl" {:idx 1} "uint8" {:lit {:v {:num {:v 2}}}}
                                       ["vdecl" {:idx 2} "uint8" {:fap {:c g :ys [(fixture/var-arg 1)]}}
                                        ["ret" (fixture/var-arg 2)]]]}}}
        rg {:name g :ir {:fdecl {:f g :xs [(fixture/parameter 7 "uint8")] :type "uint8" :info {}
                                :body ["vdecl" {:idx 8} "uint8" {:lit {:v {:num {:v 9}}}}
                                       ["case" (fixture/name-of "UInt8") {:idx 7} "uint8"
                                        [["ctor" {:cidx 0} ["ret" (fixture/var-arg 8)]]]]]}}}
        input {:runtime (into {} (map prototype.import-ir/lower-declaration) [ra rg])
               :typed (into {} (map prototype.import-ir/lower-typed-declaration) [ra rg]) :descriptors {}}
        initial (start input "A" [0]) expected (dissoc (attempt #(u/run! % 10) (u/thaw initial)) :route)
        actual (execute-plan input "A" initial 10)]
    (is (= expected (dissoc actual :route :factory-realized?)))
    (is (= 4 (get-in actual [:state :stats :steps])))
    (is (= {7 2, 8 9} (get-in actual [:state :locals])))))

(deftest unrelated-persistent-heap-globals-events-and-context-survive
  (let [input (fixture/bundle "scalar-wrapper-programs.jsonl") owner (Object.)
        initial (-> (start input "sum64" [10 0])
                    (assoc :heap {0 {:kind :ctor :tag 0 :fields [] :rc 1}} :next-id 1
                           :globals {:g {:status :ready :value 7}} :events [{:existing true}]
                           :environment owner)
                    (assoc-in [:stats :allocations] 1))
        actual (execute-plan input "sum64" initial 1000)]
    (is (= :specialized (:route actual)))
    (is (= (m/run initial 1000) (:state actual)))
    (is (identical? owner (get-in actual [:state :environment])))))

(deftest stale-compiler-and-abi-generations-decline-before-delayed-emission
  (let [input (fixture/small-bundle (fixture/row "identity" (fixture/return-node 0)))
        initial (start input "identity" [7])]
    (doseq [v [#'prototype.typed-tail-emit/generation-token #'prototype.runtime-abi/scalar-description-token]]
      (let [ctx (context input) plan (execution/compile-entry ctx (:body initial)) token (Object.)
            machine (execution/bind-context (u/thaw initial) ctx)
            actual (with-redefs-fn {v (constantly token)} (fn [] (attempt #((:execute-budget! plan) % 10) machine)))]
        (is (= :interpreted (:route actual)))
        (is (= (m/run initial 10) (:state actual)))
        (is (false? (realized? (:factory ctx))))))))

(deftest unsupported-actual-attributes-and-ambiguous-entry-bodies-remain-ordinary-code
  (let [input (fixture/small-bundle (fixture/row "identity" (fixture/return-node 0)))
        name (fixture/target (:typed input) "identity") owner (Object.)]
    (doseq [changed [(assoc-in input [:runtime name :typed-ir] (get-in input [:typed name :typed-ir]))
                     (update-in input [:runtime name :body] with-meta {:owner owner})]]
      (is (= {:status :fallback :reason :unsupported-actual-code-attributes} (context changed)))
      (let [initial (start changed "identity" [7]) program (lazy/open-program (:runtime changed) (options changed))]
        (is (= (m/run initial 10) (run :lazy program initial 10)))))
    (let [other (fixture/small-bundle (fixture/row "other" (fixture/return-node 0)))
          both (merge-with merge input other) ctx (context both)]
      (is (nil? (execution/compile-entry ctx (get-in both [:runtime name :body])))))))

(deftest bounded-emission-refusals-remember-fallback-without-guest-effects
  (let [deep (reduce (fn [body id] ["vdecl" {:idx id} "uint64" {:lit {:v {:num {:v 7}}}} body])
                     (fixture/return-node 1000) (range 1000 0 -1))
        shared (nth (iterate (fn [body]
                               ["case" (fixture/name-of "UInt8") {:idx 0} "uint8"
                                [["ctor" {:cidx 0} body] ["ctor" {:cidx 1} body]]])
                             (fixture/return-node 128)) 8)
        wide (reduce (fn [body id] ["vdecl" {:idx id} "uint8" {:lit {:v {:num {:v 7}}}} body])
                     shared (range 128 0 -1))
        wide-row (-> (fixture/row "wide" wide)
                     (assoc-in [:ir :fdecl :xs] [(fixture/parameter 0 "uint8")])
                     (assoc-in [:ir :fdecl :type] "uint8"))]
    (doseq [[label row reason] [["deep" (fixture/row "deep" deep) :method-depth-budget]
                                ["wide" wide-row :construction-budget]]]
      (let [input (fixture/small-bundle row) ctx (context input) initial (start input label [0])
            plan (execution/compile-entry ctx (:body initial))
            actual (attempt #((:execute-budget! plan) % 5000) (execution/bind-context (u/thaw initial) ctx))]
        (is (= :interpreted (:route actual)))
        (is (= (m/run initial 5000) (:state actual)))
        (is (= reason (:fallback @(:factory ctx))))
        (is (identical? @(:factory ctx) @(:factory ctx)))))))
