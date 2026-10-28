(ns java-ir-baseline
  (:require [clojure.java.io :as io]
            [clojure.data.json :as json]
            [prototype.machine :as m]
            [prototype.unchanged-program-benchmark :as benchmark])
  (:import [java.net URL URLClassLoader]
           [java.lang.reflect Method Constructor Field]))

(defn rows [path]
  (with-open [reader (io/reader path)]
    (mapv json/read-str (line-seq reader))))

(defn class-basis [directory]
  (let [loader (URLClassLoader. (into-array URL [(.toURL (.toURI (io/file directory)))])
                               (clojure.lang.RT/baseLoader))
        cls (Class/forName "ansatz.research.ir.Interpreter" true loader)
        program (Class/forName "ansatz.research.ir.Interpreter$Program" true loader)
        node (Class/forName "ansatz.research.ir.Interpreter$Node" true loader)]
    {:loader loader :class cls :node-class node
     :prepare (.getMethod cls "prepare" (into-array Class [java.util.List]))
     :constructor (.getConstructor cls (into-array Class [program]))
     :function-id (.getMethod program "functionId" (into-array Class [String]))
     :invoke (.getMethod cls "invoke" (into-array Class [Integer/TYPE (class (object-array 0))]))
     :rbmap (.getMethod cls "rbmap" (into-array Class (repeat 4 Integer/TYPE)))
     :batch (.getMethod cls "rbmapBatch" (into-array Class (repeat 5 Integer/TYPE)))
     :inc (.getMethod cls "inc" (into-array Class [Object Integer/TYPE]))
     :dec (.getMethod cls "dec" (into-array Class [Object Integer/TYPE]))
     :close (.getMethod cls "close" (make-array Class 0))
     :tag (.getField node "tag") :rc (.getField node "rc")
     :fields (.getField node "fields") :scalars (.getField node "scalars")}))

(defn invoke-static [^Method method args] (.invoke method nil (object-array args)))
(defn open-program [basis path]
  (assoc basis :program (invoke-static (:prepare basis) [(rows path)])))
(defn machine [basis]
  (.newInstance ^Constructor (:constructor basis) (object-array [(:program basis)])))
(defn function-id [basis label]
  (.invoke ^Method (:function-id basis) (:program basis) (object-array [label])))
(defn call [basis engine label args]
  (.invoke ^Method (:invoke basis) engine
           (object-array [(int (function-id basis label)) (object-array args)])))
(defn close! [basis engine] (.invoke ^Method (:close basis) engine (object-array 0)))
(defn release! [basis engine value] (.invoke ^Method (:dec basis) engine (object-array [value (int 1)])))
(defn retain! [basis engine value] (.invoke ^Method (:inc basis) engine (object-array [value (int 1)])))

(defn rbmap-runner [basis engine]
  (let [ids (mapv #(int (function-id basis %)) ["mkMap" "fold._redArg" "main._closed_0"])]
    (fn [n]
      (.invoke ^Method (:rbmap basis) engine (object-array (conj ids (int n)))))))

(defn java-value [basis value]
  (if (.isInstance ^Class (:node-class basis) value)
    {:tag (.getInt ^Field (:tag basis) value)
     :fields (mapv #(java-value basis %) (.get ^Field (:fields basis) value))
     :scalar-bytes (mapv #(bit-and 255 %) (.get ^Field (:scalars basis) value))}
    value))

(defn reference-value [world value]
  (cond
    (m/ref? value)
    (let [n (m/node world value) layout (:layout n)
          count (+ (* 8 (or (:usize layout) 0)) (or (:ssize layout) 0))]
      {:tag (:tag n) :fields (mapv #(reference-value world %) (:fields n))
       :scalar-bytes (mapv #(get (:scalar-bytes n) (+ (* 8 (or (:objects layout) 0)) %) 0) (range count))})
    (instance? prototype.machine.Tag value) (:tag value)
    :else value))

(defn measure-rbmap [basis sizes]
  (let [engine (machine basis) run (rbmap-runner basis engine)]
    (try
      (doseq [n [0 1 11 100 300 1000]] (assert (= (quot (+ n 9) 10) (run n))))
      (doseq [_ (range 100)] (run 300))
      (doseq [_ (range 30)] (run 1000))
      {:scope "Original typed exported RBMap on recursive Java IR port. One retained engine, reusable stacks, final result only; no World materialization, no fork/hosted frontend."
       :runs (vec (for [n sizes trial (range 7)]
                    (let [[answer metrics] (benchmark/measure #(run n))]
                      (assert (= (quot (+ n 9) 10) answer))
                      (assoc metrics :n n :trial trial))))}
      (finally (close! basis engine)))))

(defn measure-batch [basis sizes repetitions]
  (let [engine (machine basis)
        ids (mapv #(int (function-id basis %)) ["mkMap" "fold._redArg" "main._closed_0"])
        run (fn [n]
              (.invoke ^Method (:batch basis) engine (object-array (into ids [(int n) (int repetitions)]))))]
    (try
      (doseq [_ (range 5)] (run 300) (run 1000))
      {:scope "Original raw typed IR; adjacent n/n+1 batch matching Lean harness. One engine with warm constants, recursive interpreter, no final World. Preparation excluded."
       :repetitions repetitions
       :runs (vec (for [n sizes trial (range 7)]
                    (let [[checksum metrics] (benchmark/measure #(run n))
                          expected (* (quot repetitions 2)
                                      (+ (quot (+ n 9) 10) (quot (+ (inc n) 9) 10)))]
                      (assert (= expected checksum))
                      (assoc metrics :n n :trial trial :checksum checksum))))}
      (finally (close! basis engine)))))
