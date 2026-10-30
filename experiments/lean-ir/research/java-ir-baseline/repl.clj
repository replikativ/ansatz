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
     :constructor-explicit (.getConstructor cls (into-array Class [program Boolean/TYPE]))
     :function-id (.getMethod program "functionId" (into-array Class [String]))
     :invoke (.getMethod cls "invoke" (into-array Class [Integer/TYPE (class (object-array 0))]))
     :rbmap (.getMethod cls "rbmap" (into-array Class (repeat 4 Integer/TYPE)))
     :batch (.getMethod cls "rbmapBatch" (into-array Class (repeat 5 Integer/TYPE)))
     :inc (.getMethod cls "inc" (into-array Class [Object Integer/TYPE]))
     :dec (.getMethod cls "dec" (into-array Class [Object Integer/TYPE]))
     :close (.getMethod cls "close" (make-array Class 0))
     :start (.getMethod cls "start" (into-array Class [Integer/TYPE (class (object-array 0))]))
     :advance (.getMethod cls "advance" (into-array Class [Long/TYPE]))
     :take-result (.getMethod cls "takeResult" (make-array Class 0))
     :phase (.getMethod cls "phase" (make-array Class 0))
     :depth (.getMethod cls "continuationDepth" (make-array Class 0))
     :instructions (.getMethod cls "instructionCount" (make-array Class 0))
     :active (.getMethod cls "activeFunction" (make-array Class 0))
     :tag (.getField node "tag") :rc (.getField node "rc")
     :fields (.getField node "fields") :scalars (.getField node "scalars")}))

(defn invoke-static [^Method method args] (.invoke method nil (object-array args)))
(defn open-program [basis path]
  (assoc basis :program (invoke-static (:prepare basis) [(rows path)])))
(defn machine [basis]
  (if (:explicit basis)
    (.newInstance ^Constructor (:constructor-explicit basis) (object-array [(:program basis) true]))
    (.newInstance ^Constructor (:constructor basis) (object-array [(:program basis)]))))
(defn function-id [basis label]
  (.invoke ^Method (:function-id basis) (:program basis) (object-array [label])))
(defn call [basis engine label args]
  (.invoke ^Method (:invoke basis) engine
           (object-array [(int (function-id basis label)) (object-array args)])))
(defn close! [basis engine] (.invoke ^Method (:close basis) engine (object-array 0)))
(defn release! [basis engine value] (.invoke ^Method (:dec basis) engine (object-array [value (int 1)])))
(defn retain! [basis engine value] (.invoke ^Method (:inc basis) engine (object-array [value (int 1)])))
(defn start! [basis engine label args]
  (.invoke ^Method (:start basis) engine (object-array [(int (function-id basis label)) (object-array args)])))
(defn advance! [basis engine budget] (.invoke ^Method (:advance basis) engine (object-array [(long budget)])))
(defn take-result! [basis engine] (.invoke ^Method (:take-result basis) engine (object-array 0)))
(defn phase [basis engine] (.invoke ^Method (:phase basis) engine (object-array 0)))
(defn depth [basis engine] (.invoke ^Method (:depth basis) engine (object-array 0)))
(defn instructions [basis engine] (.invoke ^Method (:instructions basis) engine (object-array 0)))
(defn active [basis engine] (.invoke ^Method (:active basis) engine (object-array 0)))

(defn host-basis
  "Attach the opt-in host-boundary API from this exact isolated engine artifact.
   Old computational-control artifacts remain usable through class-basis."
  [basis]
  (let [loader (:loader basis)
        host (Class/forName "ansatz.research.ir.Interpreter$HostExtern" true loader)
        request (Class/forName "ansatz.research.ir.Interpreter$HostRequest" true loader)
        host-array (class (java.lang.reflect.Array/newInstance host 0))
        string-array (class (make-array String 0)) bool-array (class (boolean-array 0))
        cls ^Class (:class basis)]
    (assoc basis :host-class host
           :host-constructor (.getConstructor host (into-array Class [String string-array bool-array String]))
           :prepare-host (.getMethod cls "prepare" (into-array Class [java.util.List host-array]))
           :host-request (.getMethod cls "pendingHostRequest" (make-array Class 0))
           :resume-host (.getMethod cls "resumeHost" (into-array Class [request Object]))
           :fail-host (.getMethod cls "failHost" (into-array Class [request Throwable]))
           :host-failure (.getMethod cls "hostFailure" (make-array Class 0)))))

(defn prepare-host-program
  "Prepare in-memory original IR rows with exact opt-in host ABI descriptors.
   This registers no callback or effect; only explicit execution can request one."
  [basis rows specifications]
  (let [basis (host-basis basis)
        descriptors (mapv (fn [{:keys [symbol parameters borrowed result]}]
                            (.newInstance ^Constructor (:host-constructor basis)
                              (object-array [symbol (into-array String parameters)
                                             (boolean-array borrowed) result]))) specifications)
        array (java.lang.reflect.Array/newInstance ^Class (:host-class basis) (count descriptors))]
    (doseq [[index descriptor] (map-indexed vector descriptors)]
      (java.lang.reflect.Array/set array index descriptor))
    (assoc basis :explicit true :program (invoke-static (:prepare-host basis) [rows array]))))

(defn host-request [basis engine]
  (.invoke ^Method (:host-request basis) engine (object-array 0)))
(defn request-value
  "Borrow a request accessor; arguments acquire no new guest ownership."
  [request accessor]
  (.invoke (.getMethod ^Class (class request) accessor (make-array Class 0)) request (object-array 0)))
(defn resume-host! [basis engine request value]
  (.invoke ^Method (:resume-host basis) engine (object-array [request value])))
(defn fail-host! [basis engine request cause]
  (.invoke ^Method (:fail-host basis) engine (object-array [request cause])))
(defn host-failure [basis engine]
  (.invoke ^Method (:host-failure basis) engine (object-array 0)))
(defn fork!
  "On-demand capture. ROOTS must account for the external owner/alias contract."
  [basis engine roots]
  (let [packet (.invoke (.getMethod ^Class (:class basis) "eagerFork"
                                  (into-array Class [(class (object-array 0))]))
                        engine (object-array [(object-array roots)]))
        cls ^Class (class packet)]
    {:engine (.get (.getField cls "engine") packet)
     :roots (vec (.get (.getField cls "roots") packet))}))

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

(defn measure-modes [basis sizes repetitions]
  (let [contexts {:recursive (dissoc basis :explicit) :explicit (assoc basis :explicit true)}
        engines (into {} (map (fn [[mode ctx]] [mode (machine ctx)])) contexts)
        ids (mapv #(int (function-id basis %)) ["mkMap" "fold._redArg" "main._closed_0"])
        run (fn [mode n]
              (.invoke ^Method (:batch basis) (engines mode)
                       (object-array (into ids [(int n) (int repetitions)]))))]
    (try
      (doseq [_ (range 5) n [300 1000] mode [:recursive :explicit]] (run mode n))
      {:scope "Paired recursive and explicit drivers, same prepared Program/heap semantics; adjacent inputs and reusable engine per mode; preparation/capture excluded."
       :repetitions repetitions
       :runs (vec (for [n sizes trial (range 7)
                        mode (if (even? trial) [:recursive :explicit] [:explicit :recursive])]
                    (let [[checksum metrics] (benchmark/measure #(run mode n))]
                      (assert (= checksum (* (quot repetitions 2)
                                             (+ (quot (+ n 9) 10) (quot (+ (inc n) 9) 10)))))
                      (assoc metrics :mode mode :n n :trial trial :checksum checksum))))}
      (finally (doseq [[mode engine] engines] (close! (contexts mode) engine))))))
