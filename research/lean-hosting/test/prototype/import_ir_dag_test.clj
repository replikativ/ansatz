(ns prototype.import-ir-dag-test
  "Dependency scans only; no guest execution, Source or declaration admission."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.data.json :as json] [clojure.java.io :as io]
            [prototype.import-ir :as ir] [prototype.eval-const :as eval]))
(defn- oracle [body] ((ns-resolve 'prototype.import-ir 'static-targets-tree) body))
(defn- probe [body] ((ns-resolve 'prototype.import-ir 'static-targets-canonical) body))
(def a ["str" ["anonymous"] "a"])
(def b ["str" ["anonymous"] "b"])
(def done [:return [:var 0]])
(def ta [:tail [:direct a] []])
(def tb [:tail [:direct b] []])
(defn- outcome [scan body]
  (try {:targets (scan body)}
       (catch Exception e {:class (class e) :message (.getMessage e) :data (ex-data e)})))

(deftest every-static-edge-position-preserves-the-tree-oracle
  (doseq [body [[:let 0 [:closure a []] done] [:let 0 [:literal [:direct b]] done]
                [:call 0 [:direct a] [] done] ta [:tail [:var 0] []]
                [:join 0 [] ta tb] [:case [:var 0] [[0 ta] [:default tb]]]
                [:inc [:var 0] 1 ta] [:dec [:var 0] 1 ta] [:set-tag [:var 0] 1 ta]
                [:del [:var 0] ta] [:suspend 0 ta]
                [:set [:var 0] 0 [:var 1] ta] [:scalar-set [:var 0] {} [:var 1] ta]
                [:host "host" [] 0 ta] [:global 0 a] [:begin-init 0 a]
                done [:jump 0 []] [:publish-global 0 a] [:unreachable]
                [:read-global a] [:publish-io-global a] [:trap "ignored"]]]
    (is (= (oracle body) (ir/static-targets body)) (str (first body)))))

(deftest shared-instructions-are-visited-once-by-identity
  (let [shared (loop [n 16 node ta] (if (zero? n) node (recur (dec n) [:join 0 [] node node])))
        equal-tail (mapv identity ta)
        target-check (ns-resolve 'prototype.import-ir 'frozen-target?)
        original @target-check calls (atom 0)
        scan #(with-redefs-fn {target-check (fn [x] (swap! calls inc) (original x))}
                (fn [] (ir/static-targets %)))]
    (is (= #{a} (oracle shared) (scan shared)))
    (is (= 1 @calls))
    (reset! calls 0)
    (is (and (= ta equal-tail) (not (identical? ta equal-tail))))
    (is (= #{a} (scan [:join 0 [] ta equal-tail])))
    (is (zero? @calls))))

(defn- changing-arms [calls]
  (reify clojure.lang.Seqable
    (seq [_] (let [target (if (= 1 (swap! calls inc)) a b)]
               (seq [[0 [:tail [:direct target] []]]])))))
(deftest exotic-shared-arms-use-original-sequencing
  (doseq [scan [oracle ir/static-targets]]
    (let [calls (atom 0) shared [:case [:var 0] (changing-arms calls)]]
      (is (= #{a b} (scan [:join 0 [] shared shared])))
      (is (= 2 @calls)))))

(deftest failed-probe-does-not-replay-earlier-exotic-reads
  (doseq [scan [oracle ir/static-targets]]
    (let [early-calls (atom 0) late-calls (atom 0)
          earlier [:case [:var 0] (changing-arms early-calls)]
          shared [:case [:var 0] (changing-arms late-calls)]
          body [:join 0 [] earlier [:join 0 [] shared shared]]]
      (is (= #{a b} (scan body)))
      (is (= 1 @early-calls))
      (is (= 2 @late-calls)))))

(deftest literal-data-is-never-inspected
  (let [calls (atom 0) payload (changing-arms calls)
        literal [:let 0 [:literal [[:direct b] [:closure b] payload]] done]
        body [:join 0 [] literal literal]]
    (is (= #{} (oracle body) (ir/static-targets body)))
    (is (zero? @calls))))

(deftest mutable-targets-are-not-memoized
  (let [array (object-array [:direct a]) target (clojure.lang.ArraySeq/create array)
        body [:join 0 [] [:tail target []] [:tail target []]]]
    (is (= #{a} (oracle body) (ir/static-targets body)))
    (aset array 1 b)
    (is (= #{b} (oracle body) (ir/static-targets body)))
    (is (= :prototype.import-ir/fallback (probe body)))))

(deftest malformed-input-and-exotic-op-hashing-stay-unchanged
  (doseq [body [[:tail [:direct nil] []] [:let 0 [:closure nil] done]
                [:global 0 nil] [:case [:var 0] [[0 nil]]] [:unknown] nil]]
    (is (= (outcome oracle body) (outcome ir/static-targets body))))
  (let [counts (mapv (fn [scan]
                       (let [calls (atom 0)
                             op (reify Object (hashCode [_] (swap! calls inc)) (toString [_] "exotic-op"))]
                         (outcome scan [op]) @calls)) [oracle ir/static-targets])]
    (is (= (first counts) (second counts)))))

(def fixture-paths
  ["fixtures/raw-cases-on/probe-ir.jsonl"
   "fixtures/raw-cases-on/imported-ir.jsonl"
   "fixtures/raw-cases-on/constructor-ir.jsonl"])
(defn authentic-functions []
  (vec (mapcat (fn [path]
                 (with-open [reader (io/reader (or (io/resource path)
                                           (io/file "experiments/lean-ir/test" path)))]
                   (doall (keep (fn [line]
                                  (let [row (json/read-str line :key-fn keyword)]
                                    (when (get-in row [:ir :fdecl]) (ir/lower-declaration row))))
                                (line-seq reader))))) fixture-paths)))
(deftest authentic-normalized-functions-and-runtime-edges
  (let [functions (authentic-functions)]
    (is (seq functions))
    (doseq [[name f] functions]
      (is (vector? name))
      (is (= (oracle (:body f)) (ir/static-targets (:body f))))
      (is (not= :prototype.import-ir/fallback (probe (:body f))))
      (is (= (conj (oracle (:body f)) a)
             (eval/executable-dependencies (assoc f :runtime-dependencies [a])))))))

(defn- chunked-arms [calls]
  (reify clojure.lang.IChunkedSeq
    (seq [this] this)
    (first [_] [0 ta]) (next [_] nil) (more [_] '())
    (cons [_ x] (cons x (list [0 ta]))) (count [_] 1)
    (empty [_] '()) (equiv [_ _] false)
    (chunkedFirst [_] (clojure.lang.ArrayChunk. (object-array [[0 ta]])))
    (chunkedNext [_] (swap! calls conj :chunk-next) nil)
    (chunkedMore [_] (swap! calls conj :chunk-rest) '())))
(deftest exotic-chunked-arms-retain-map-chunk-rest-behavior
  (let [results (mapv (fn [scan]
                        (let [calls (atom []) body [:case [:var 0] (chunked-arms calls)]]
                          {:targets (scan body) :calls @calls})) [oracle ir/static-targets])]
    (is (= (first results) (second results)))
    (is (= [:chunk-rest] (:calls (first results))))))
