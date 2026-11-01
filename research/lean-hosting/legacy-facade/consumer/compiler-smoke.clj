(load-file "compiler-fixture.clj")
(require '[consumer.compiler-fixture :as fixture] '[prototype.raw-interop :as raw]
         '[prototype.machine :as m] '[prototype.mutable :as u]
         '[prototype.block-compile :as block] '[prototype.interop-codec :as codec]
         '[prototype.lazy-runtime :as lazy])
(import 'CompilerSmoke)
(assert (nil? (find-ns 'pattern.llvm)))
(defn verify-compiled []
  (let [{:keys [functions options targets]} (fixture/input)
        events (atom []) compile block/compile-runtime-block-prepared cache (lazy/code-cache)]
    (with-redefs [block/compile-runtime-block-prepared
                  (fn [& args]
                    (let [artifact (apply compile args)]
                      (reduce (fn [out key]
                                (if-let [execute (get out key)]
                                  (assoc out key (fn [& xs]
                                                   (let [route (apply execute xs)]
                                                     (swap! events conj [(get-in artifact [:specialization :kind]) route]) route)))
                                  out)) artifact [:execute! :execute-budget!])))]
      (doseq [[label type] [["sum64" :uint64] ["sumSize" :usize]]]
        (let [seen (count @events) target (get targets label) boxed ["str" target "_boxed"]
              session (raw/open-functions functions {} {:cache cache :compiler-options options})
              [world args] (reduce (fn [[world args] n]
                                     (let [[world v] (codec/encode-boxed world type n)] [world (conj args v)]))
                                   [(m/world functions) []] [10 0])
              initial (m/start world boxed args) expected (m/run initial)
              actual (:state (raw/call session world boxed args))]
          (assert (= 55N (codec/decode-boxed actual type (:result actual))))
          (assert (= expected actual))
          (assert (= (fixture/shape expected) (fixture/shape actual)))
          (doseq [fuel (range (+ 2 (get-in expected [:stats :steps])))]
            (let [prefix (:state (raw/advance-to-boundary (assoc session :fuel fuel) initial))
                  oracle (m/run initial fuel)]
              (assert (= oracle prefix))
              (assert (= (fixture/shape oracle) (fixture/shape prefix)))))
          (let [reopened (raw/open-functions functions {} {:cache cache :compiler-options options})]
            (assert (= 55N (:value (raw/call reopened (m/world functions) target [10 0]))))
            (assert (pos? (:cache-hits (lazy/summary (:program reopened))))))
          (assert (some #{[:typed-tail :specialized]} (subvec @events seen))))))
    (assert (some #{[:typed-tail :specialized]} @events))
    55N))
(assert (= 55N (verify-compiled)))
;; The Java provider forwards options and runs selected raw code; its deliberately
;; invalid prepared packet is rejected. No checked Java Context is fabricated.
(CompilerSmoke/verify (fn [options]
                        (assert (= "typed-compiler" (get (.values options) "profile")))
                        (verify-compiled)))
(println :optional-compiler-jar-smoke-passed)
