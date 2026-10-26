(ns prototype.tail-caller-frames-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.typed-tail-test :as fixture]
            [prototype.typed-tail-execution-test :as execution-test]
            [prototype.typed-tail-execution :as execution]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.import-ir :as ir]
            [prototype.interop-codec :as codec]
            [prototype.lazy-runtime :as lazy]
            [prototype.block-compile :as block]))

(defn wrapped
  "Canonical control-flow fixture, not a native producer or source ABI oracle."
  [input label depth]
  (let [target (fixture/target (:typed input) label)
        params (get-in input [:runtime target :params])]
    (loop [input input target target n depth]
      (if (zero? n) (assoc input :entry target :depth depth :scalar-label label)
          (let [name (fixture/name-of (str "caller-" n))
                body [:let 90 [:literal 77N]
                      [:join 91 [] [:return [:var 90]]
                       [:call 92 [:direct target] (mapv #(vector :var %) params)
                        [:let 93 [:literal 8] [:return [:var 92]]]]]]]
            (recur (assoc-in input [:runtime name] {:params params :body body}) name (dec n)))))))

(defn start [input args]
  (m/start (m/world (:runtime input)) (:entry input) args))

(defn entry [input args]
  ;; Each canonical caller executes let/join/call before the callee entry.
  (nth (iterate m/step (start input args)) (* 3 (:depth input))))

(deftest every-fuel-prefix-restores-saved-callers-and-joins
  (let [input (fixture/bundle "typed-tail-programs.jsonl")]
    (doseq [depth [1 2]
            {:keys [label args]} (execution-test/cases input "typed-tail-program-values.json")]
      (let [input (wrapped input label depth) initial (start input args)
            expected (m/run initial) saved initial
            opts (execution-test/options input)
            programs [[:lazy (lazy/open-program (:runtime input) opts)]
                      [:eager (block/compile-program (:runtime input) nil opts)] [:mutable nil]]]
        (doseq [fuel (range (+ 2 (get-in expected [:stats :steps])))
                [backend program] programs]
          (let [actual (execution-test/run backend program initial fuel)
                prefix (m/run initial fuel)]
            (is (= prefix actual))
            (is (= (execution-test/carrier-shape prefix) (execution-test/carrier-shape actual)))
            (when (= :paused (:status actual))
              (is (= expected (execution-test/run backend program (m/resume actual nil) 10000))))))
        (is (= saved initial))))))

(deftest region-return-exits-before-running-the-restored-caller
  (let [source (fixture/bundle "typed-tail-programs.jsonl")]
    (doseq [depth [1 2] peak [nil 7]
            {:keys [label args]} (execution-test/cases source "typed-tail-program-values.json")]
      (let [input (wrapped source label depth)
            initial (cond-> (entry input args) peak (assoc-in [:stats :max-frames] peak))
            scalar-steps (get-in (m/run (execution-test/start source label args)) [:stats :steps])
            expected (nth (iterate m/step initial) scalar-steps)
            ctx (execution-test/context input)
            target (fixture/target (:typed input) label)
            plan (execution/compile-entry ctx (get-in input [:runtime target :body]))
            machine (execution/bind-context (u/thaw initial) ctx)]
        (is (= :typed-tail (get-in plan [:specialization :kind])))
        (is (= :specialized ((:execute-budget! plan) machine 10000)))
        (let [actual (u/freeze machine)]
          (is (= :running (:status actual)))
          (is (= (dec depth) (count (:frames actual))))
          (is (seq (:joins actual)))
          (is (= expected actual))
          (is (= (execution-test/carrier-shape expected) (execution-test/carrier-shape actual))))))))

(deftest quantum-and-cache-reuse-read-this-invocations-caller-depth
  (let [source (fixture/bundle "scalar-wrapper-programs.jsonl") cache (lazy/code-cache)
        first-artifact (atom nil)]
    (doseq [depth [1 2 1]]
      (let [input (wrapped source "sum64" depth) initial (start input [5000 0])
            program (lazy/open-program (:runtime input) (execution-test/options input) cache)]
        (doseq [fuel [3 53247 53248 53249 65009 65020]]
          (let [expected (m/run initial fuel)
                actual (execution-test/run :lazy program initial fuel)]
            (is (= expected actual))
            (is (= (execution-test/carrier-shape expected) (execution-test/carrier-shape actual)))))
        (let [body (get-in source [:runtime (fixture/target (:typed source) "sum64") :body])
              artifact (.get ^java.util.IdentityHashMap (:identity-dispatch program) body)]
          (is (= :typed-tail (get-in artifact [:specialization :kind])))
          (if-let [prior @first-artifact]
            (do (is (identical? prior artifact))
                (is (pos? (:cache-hits (lazy/summary program)))))
            (reset! first-artifact artifact)))
        (is (= initial (start input [5000 0])))))))

(deftest caller-depth-helper-redefinition-declines-before-emission
  (let [input (wrapped (fixture/bundle "typed-tail-programs.jsonl") "identity" 2)
        initial (entry input [7]) ctx (execution-test/context input)
        target (fixture/target (:typed input) "identity")
        plan (execution/compile-entry ctx (get-in input [:runtime target :body]))
        machine (execution/bind-context (u/thaw initial) ctx)
        expected (u/freeze (u/run! (u/thaw initial) 10))]
    (with-redefs [u/tail-frame-depth (constantly 0)]
      (is (= :interpreted ((:execute-budget! plan) machine 10))))
    (is (= expected (u/freeze machine)))
    (is (false? (realized? (:factory ctx))))))

(deftest missing-case-after-a-committed-tail-keeps-the-real-callers
  (let [a (fixture/name-of "A") g (fixture/name-of "G")
        rows [{:name a :ir {:fdecl {:f a :xs [(fixture/parameter 0 "uint8")] :type "uint8" :info {}
                                   :body ["vdecl" {:idx 1} "uint8" {:lit {:v {:num {:v 2}}}}
                                          ["vdecl" {:idx 2} "uint8" {:fap {:c g :ys [(fixture/var-arg 1)]}}
                                           ["ret" (fixture/var-arg 2)]]]}}}
              {:name g :ir {:fdecl {:f g :xs [(fixture/parameter 7 "uint8")] :type "uint8" :info {}
                                   :body ["vdecl" {:idx 8} "uint8" {:lit {:v {:num {:v 9}}}}
                                          ["case" (fixture/name-of "UInt8") {:idx 7} "uint8"
                                           [["ctor" {:cidx 0} ["ret" (fixture/var-arg 8)]]]]]}}}]
        source {:runtime (into {} (map ir/lower-declaration) rows)
                :typed (into {} (map ir/lower-typed-declaration) rows) :descriptors {}}
        input (wrapped source "A" 2) initial (entry input [0])
        expected (dissoc (execution-test/attempt #(u/run! % 10) (u/thaw initial)) :route)
        seen (atom []) run! u/run!
        actual (with-redefs [u/run! (fn [machine fuel]
                                     (swap! seen conj [(u/steps machine) (u/tail-frame-depth machine) fuel])
                                     (run! machine fuel))]
                 (execution-test/execute-plan input "A" initial 10))]
    (is (= [[8 2 8]] @seen))
    (is (= expected (dissoc actual :route :factory-realized?)))
    (is (= (:frames initial) (get-in actual [:state :frames])))
    (is (= {7 2, 8 9} (get-in actual [:state :locals])))))

(deftest authentic-boxed-wrappers-run-a-specialized-callee-and-box-its-result
  (let [all (fixture/bundle "boxed-scalar-wrapper-programs.jsonl")
        input (update all :typed #(into {} (remove (fn [[name _]] (= "_boxed" (last name)))) %))
        fs (:runtime input) opts (execution-test/options input)
        observed (atom []) original block/compile-runtime-block-prepared]
    (with-redefs [block/compile-runtime-block-prepared
                  (fn [functions body options]
                    (let [plan (original functions body options)]
                      (if (= :typed-tail (get-in plan [:specialization :kind]))
                        (update plan :execute-budget!
                                (fn [execute]
                                  (fn [machine fuel]
                                    (let [route (execute machine fuel)]
                                      (swap! observed conj [(get-in plan [:specialization :kind]) route])
                                      route))))
                        plan)))]
      (doseq [{:keys [label args result]} (execution-test/cases input "scalar-wrapper-program-values.json")]
        (let [descriptor (if (= "sum64" label) :uint64 :usize)
              target ["str" (fixture/target (:typed input) label) "_boxed"]
              [world boxed] (reduce (fn [[world values] value]
                                     (let [[world encoded] (codec/encode-boxed world descriptor value)]
                                       [world (conj values encoded)])) [(m/world fs) []] args)
              initial (m/start world target boxed) saved initial
              terminal (m/run initial) program (lazy/open-program fs opts)
              programs [[:lazy program] [:eager (block/compile-program fs nil opts)] [:mutable nil]]]
          (is (= result (codec/decode-boxed terminal descriptor (:result terminal))))
          (doseq [fuel (range (+ 2 (get-in terminal [:stats :steps]))) [backend chosen] programs]
            (let [expected (m/run initial fuel)
                  actual (execution-test/run backend chosen initial fuel)]
              (is (= expected actual))
              (is (= (execution-test/carrier-shape expected) (execution-test/carrier-shape actual)))))
          (is (= saved initial)))))
    (is (some #{[:typed-tail :specialized]} @observed))))
