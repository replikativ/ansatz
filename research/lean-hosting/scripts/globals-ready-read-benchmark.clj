(require '[prototype.machine :as m] '[prototype.mutable :as u] '[clojure.data.json :as json])
(import '[java.util Map HashMap] '[ansatz.runtime GlobalsOverlay])

(defn table [n]
  (into {} (map (fn [i] [["str" ["anonymous"] (str "g" i)] {:status :ready :value 42}]) (range n))))
(def query ["str" ["anonymous"] "g0"])
(defn reads [state n]
  (loop [i (long 0) checksum (long 0)]
    (if (< i n)
      (recur (inc i) (+ checksum (long (u/initialized-value state query))))
      checksum)))
(def rows
  (vec (for [n [1 56125 100000]
             :let [base (table n)]
             mode [:eager-map :borrowed-overlay :materialized-overlay]]
         (let [state (u/thaw (assoc (m/world {}) :globals base))
               state (if (= mode :eager-map) (assoc state :globals (HashMap. ^Map base)) state)
               _ (when (= mode :materialized-overlay) (.entrySet ^Map (:globals state)))
               _ (case mode
                   :eager-map (assert (instance? HashMap (:globals state)))
                   :borrowed-overlay (do (assert (instance? GlobalsOverlay (:globals state)))
                                         (assert (identical? base (GlobalsOverlay/unchangedBase (:globals state)))))
                   :materialized-overlay (do (assert (instance? GlobalsOverlay (:globals state)))
                                             (assert (nil? (GlobalsOverlay/unchangedBase (:globals state))))))
               _ (dotimes [_ 10] (assert (= (* 42 200000) (reads state 200000))))
               samples (vec (for [_ (range 5)]
                              (let [before (System/nanoTime) checksum (reads state 200000) after (System/nanoTime)]
                                (assert (= (* 42 200000) checksum))
                                (/ (- after before) 200000.0))))]
           {:global-count n :mode mode :samples-ns-per-read samples
            :median-ns (nth (vec (sort samples)) 2)}))))
(println (json/write-str {:scope "synthetic-ready-global-read/1" :jvm (System/getProperty "java.version")
                         :warmups 10 :warmup-reads 200000 :samples 5 :reads-per-sample 200000 :rows rows
                         :limits ["All modes use the optimized interpreter's initialized-value helper in one JVM; eager-map is its HashMap representation, not a separately compiled old interpreter."
                                  "Construction and cold key validation excluded; fixed order, small samples and JVM optimization can affect results."
                                  "This measures repeated ready-global lookup only, excluding hosted frontend, bytecode compilation, boundary conversion and initialization effects."]}))
(System/exit 0)
