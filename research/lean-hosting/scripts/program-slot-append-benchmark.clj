;; Run the identical script under baseline and candidate source trees:
;; clojure -J-Xmx512m -M scripts/program-slot-append-benchmark.clj baseline 56125
;; clojure -J-Xmx512m -M scripts/program-slot-append-benchmark.clj candidate 56125
;; Each process measures one size; run larger sizes under an external RSS guard.
(require '[prototype.slot-count :as slots]
         '[clojure.data.json :as json])

(let [[mode size-text] *command-line-args*
      size (Long/parseLong (or size-text "56125"))
      _ (when-not (and (contains? #{"baseline" "candidate"} mode) (<= 1 size 400000))
          (throw (ex-info "Expected baseline|candidate and size 1..400000" {})))
      append (if (= mode "baseline")
               (fn [base additions] (merge base additions))
               (requiring-resolve 'prototype.slot-count/append-functions))
      base (persistent!
             (reduce (fn [out i]
                       (assoc! out (str "entry-" i)
                               {:params [7] :body [:return [:var 7]] :probe-index i}))
                     (transient {}) (range size)))
      cold-start (System/nanoTime)
      width (slots/program-slots base)
      cold-ms (/ (- (System/nanoTime) cold-start) 1000000.0)
      _ (when-not (= 8 width) (throw (ex-info "Unexpected base width" {})))
      samples
      (mapv (fn [i]
              (let [register (+ 31 i)
                    additions {(str "new-" i) {:params [register] :body [:return [:var register]]}}
                    start (System/nanoTime)
                    extended (append base additions)
                    width (slots/program-slots extended)
                    elapsed (/ (- (System/nanoTime) start) 1000000.0)
                    hit-start (System/nanoTime)
                    again (slots/program-slots extended)
                    hit-ms (/ (- (System/nanoTime) hit-start) 1000000.0)]
                (when-not (and (= (inc register) width again) (= (inc size) (count extended))
                               (identical? (get base "entry-0") (get extended "entry-0"))
                               (= size (count base)))
                  (throw (ex-info "Append benchmark changed code or width" {})))
                {:kind (if (< i 2) :warmup :measured) :index i
                 :append-and-size-ms elapsed :repeat-size-ms hit-ms :slots width}))
            (range 7))]
  (println (json/write-str
             {:scope "synthetic-validated-program-append/1" :mode mode :program-size size
              :base-cold-validation-ms cold-ms :base-slots width :samples samples
              :warmups 2 :measured 5 :guest-invocations 0 :phase :passed
              :limits "Synthetic host sizing/append only; excludes code admission and interpreter/frontend execution."}))
  (shutdown-agents))
