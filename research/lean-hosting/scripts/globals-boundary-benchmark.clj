(require '[prototype.machine :as m] '[prototype.mutable :as u] '[clojure.data.json :as json])
(import '[java.util Map])
(def functions {:entry {:params [] :body (reduce (fn [body id] [:let id [:literal id] body]) [:return [:imm 42]] (range 7))}})
(defn globals [n] (into {} (map (fn [i] [["str" ["anonymous"] (str "g" i)] {:status :ready :value 42}]) (range n))))
(defn trial [base kind]
  (let [machine (u/thaw (if (= kind :eight-step-call) (m/start base :entry []) base))]
    (case kind
      :eight-step-call (u/run! machine)
      :one-write (.put ^Map (:globals machine) ["str" ["anonymous"] "changed"] {:status :ready :value 43})
      :thousand-writes (dotimes [i 1000] (.put ^Map (:globals machine) ["str" ["anonymous"] (str "g" i)] {:status :ready :value 43}))
      nil)
    (let [result (u/freeze machine)]
      (when (seq (:globals base)) (assert (= 42 (get-in base [:globals ["str" ["anonymous"] "g0"] :value]))))
      (assert (= (+ (count (:globals base)) (case kind :one-write 1 :thousand-writes (max 0 (- 1000 (count (:globals base)))) 0)) (count (:globals result))))
      (when (= kind :eight-step-call) (assert (= 42 (:result result))) (assert (= 8 (get-in result [:stats :steps]))))
      (count (:globals result)))))
(def result
  (vec (for [n [0 56125 100000]
             :let [base (assoc (m/world functions) :globals (globals n))]
             kind [:unchanged :eight-step-call :one-write :thousand-writes]]
         (do
           (dotimes [_ 10] (trial base kind))
           (let [samples (vec (for [_ (range 5)]
                                (let [before (System/nanoTime)]
                                  (dotimes [_ 5] (trial base kind))
                                  (/ (- (System/nanoTime) before) 5000000.0))))]
             {:global-count n :case kind :samples-ms-per-operation samples
              :median-ms (nth (vec (sort samples)) 2)})))))
(println (json/write-str {:scope "synthetic-globals-boundary-benchmark/2" :warmups 10 :samples 5 :operations-per-sample 5 :jvm (System/getProperty "java.version") :rows result
                          :limits ["Synthetic immutable globals; no hosted frontend or checkpoint restore." "Write cases exercise Map storage directly, excluding guest initializer/RC semantics; regression tests must cover those separately." "Independent thaw/freeze per operation; output remains persistent."]}))
(System/exit 0)
