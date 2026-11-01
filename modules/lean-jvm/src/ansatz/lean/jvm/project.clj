(ns ansatz.lean.jvm.project
  "Private issued Project leases behind the Java facade. No raw guest values,
   native producer receipts or mutable engine aliases cross that facade."
  (:require [ansatz.lean.jvm.ir :as ir] [ansatz.lean.jvm.artifact :as artifact]
            [ansatz.lean.jvm.publisher :as publisher] [ansatz.lean.jvm.startup :as startup]
            [clojure.java.io :as io] [clojure.string :as str])
  (:import [java.math BigInteger] [java.nio.charset StandardCharsets]
           [java.util WeakHashMap] [ansatz.lean.jvm MainResult]))
(deftype Services [basis capability])
(deftype Project [])
(deftype Handle [owner name signature])
(defonce ^:private projects (WeakHashMap.))
;; Only an actual lifetime invariant refusal enters quarantine. It never counts
;; as successful cleanup; keep actual private custody instead of losing owners.
(defonce ^:private quarantine (atom []))
(def ^:private duration-nanos 5000000000)
(def ^:private instruction-limit 2000000)
(defn- need [ok code message]
  (when-not ok (throw (ex-info message {:code code}))))
(defn- cell! [project]
  (need (= Project (class project)) "RuntimeBoundary" "Actual Project issuer required")
  (locking projects (or (.get projects project) (throw (ex-info "Expired Project" {:code "RuntimeBoundary"})))))
(defn- live! [cell]
  (need (= :ready (:status @cell)) "RuntimeBoundary" "Project is closed or its branch failed"))
(defn- typed-name [value]
  (need (and (string? value) (<= 1 (count value) 16384)) "EntryRejected" "Bounded dotted entry name required")
  (let [parts (str/split value #"\." -1)]
    (need (and (<= (count parts) 128) (every? #(<= 1 (count %) 4096) parts)) "EntryRejected" "Empty or excessive name segment")
    (reduce (fn [parent part] ["str" parent part]) ["anonymous"] parts)))
(defn- label [name]
  (loop [name name parts ()]
    (if (= name ["anonymous"]) (str/join "." parts)
        (recur (second name) (conj parts (nth name 2))))))
(defn- nat! [value]
  (need (and (= BigInteger (class value)) (not (neg? (.signum ^BigInteger value)))
             (<= (.bitLength ^BigInteger value) 4096)) "ResourceLimit" "Nat requires a nonnegative BigInteger of at most 4096 bits") value)
(defn- result-nat! [value]
  (nat! (if (= Long (class value)) (BigInteger/valueOf (long value)) value)))
(defn- string! [value]
  (need (and (= String (class value)) (<= (.length ^String value) 65536)
             (= value (String. (.getBytes ^String value StandardCharsets/UTF_8) StandardCharsets/UTF_8)))
        "ResourceLimit" "String requires valid Unicode and at most 65536 UTF-16 units") value)
(defn- invoke-zero [engine name]
  (.invoke (.getMethod (class engine) name (make-array Class 0)) engine (object-array 0)))
(defn- deadline! [engine]
  (.invoke (.getMethod (class engine) "configureAtomicDeadlineAfterNanos" (into-array Class [Long/TYPE]))
           engine (object-array [(long duration-nanos)])))
(defn- drain! [engine] (vec (invoke-zero engine "drainCapturedOutput")))
(defn- codec-bytes []
  (let [resource (io/resource "META-INF/ansatz-lean-jvm/user-error.json")]
    (need resource "RuntimeBoundary" "SDK codec resource is absent")
    (with-open [input (io/input-stream resource)]
      (let [bytes (.readNBytes input 16385)]
        (need (<= (alength bytes) 16384) "RuntimeBoundary" "SDK codec resource exceeds bound") bytes))))
(defn- entropy [basis]
  (let [cls (Class/forName "ansatz.research.ir.Interpreter$EntropyCapability" true (:loader basis))]
    (ir/invoke-static (.getMethod cls "secureRandom" (into-array Class [String String Integer/TYPE]))
                      ["DRBG" "" (int 1048576)])))
(defn runtime-service!
  "One shared JDK DRBG service per Java Lean scope, initialized lazily."
  []
  (let [basis (ir/linked-basis)] (Services. basis (entropy basis))))
(defn- startup-from-failure [failure]
  (loop [failure failure left 8]
    (when (and failure (pos? left))
      (or (when (instance? clojure.lang.IExceptionInfo failure) (:startup (ex-data failure)))
          (recur (.getCause ^Throwable failure) (dec left))))))
(defn- retire! [cell]
  (let [{:keys [run slot]} @cell
        failure
        (when run
          (try
            (let [status (:status (startup/status run))]
              (cond
                (#{:closed :abandoned} status) nil
                (#{:host-failed :close-started} status) (startup/abandon! run)
                (= :running status) (do (startup/cancel! run) (startup/abandon! run))
                (= :io-error status) (do (startup/release-error! run) (startup/close! run))
                :else (startup/close! run)))
            nil
            (catch Throwable failure
              (try (startup/abandon! run)
                   (catch Throwable refused
                     (swap! quarantine conj cell)
                     (throw failure)))
              ;; Preserve an actual normal-close failure even when the separately
              ;; certified host-reference abandonment subsequently succeeds.
              failure)))]
    (when slot (dotimes [i (alength ^objects slot)] (aset ^objects slot i nil)))
    (reset! cell {:status :closed})
    (when failure (throw failure))))
(defn- open-prepared! [services prepared]
  (let [cell (atom {:status :opening :slot (object-array 3)}) token (Project.)]
    (try
      (let [run (startup/open! prepared (.-capability ^Services services))]
        (swap! cell assoc :run run)
        (deadline! (:engine (startup/owner-packet run)))
        (let [deadline (+ (System/nanoTime) duration-nanos)]
          (loop [left instruction-limit]
            (when (.isInterrupted (Thread/currentThread))
              (throw (ex-info "Project startup interrupted" {:code "Cancelled"})))
            (need (and (pos? left) (< (System/nanoTime) deadline)) "ResourceLimit" "Project startup cooperative budget exhausted")
            (case (:status (startup/status run))
              :ready nil
              :running (do (startup/poll! run (min 128 left)) (recur (- left (min 128 left))))
              :io-error (throw (ex-info "Project initialization returned an IO error" {:code "InitializationFailed"}))
              (throw (ex-info "Project initialization stopped" {:code "InitializationFailed"})))))
        (let [output (startup/with-ready-engine! run
                       (fn [{:keys [engine]}]
                         (invoke-zero engine "clearAtomicDeadline") (drain! engine)))]
          (swap! cell assoc :status :ready :prefix output))
        (locking projects (.put projects token cell)) token)
      (catch Throwable failure
        (when-not (:run @cell)
          (when-let [run (startup-from-failure failure)] (swap! cell assoc :run run)))
        (try (retire! cell) (catch Throwable _ nil))
        (throw failure)))))
(defn open-artifact! [services input expected-manifest-sha]
  (let [receipt (artifact/load! input expected-manifest-sha) basis (.-basis ^Services services)]
    (open-prepared! services (publisher/prepare-artifact! basis receipt (codec-bytes)))))
(defn open-project! [services source-root options]
  ;; Resolve and retire native services before any runtime Project is opened.
  (let [bundle-open (requiring-resolve 'ansatz.lean.jvm.compiler.bundle/open!)
        build (requiring-resolve 'ansatz.lean.jvm.compiler.evidence/build!)
        compiler-close (requiring-resolve 'ansatz.lean.jvm.compiler.transport/close!)
        {:keys [compiler project-options evidence-options]} (bundle-open (.compiler options))
        receipt
        (try
          (let [roots [(typed-name (.rootModule options))]
                entries (mapv (fn [entry] {:root (first roots) :name (typed-name (.name entry))
                                          :signature (.signature entry)}) (.entries options))]
            (build compiler (assoc project-options :project source-root
                             :source-root (.sourceRoot options) :roots roots)
                   evidence-options entries (atom {})))
          (finally (compiler-close compiler)))
        basis (.-basis ^Services services)]
    (open-prepared! services (publisher/prepare-build-bytes! basis receipt (codec-bytes)))))
(defn lookup-function! [project name signature]
  (let [cell (cell! project) name (typed-name name)]
    (locking cell
      (live! cell)
      (let [matched (startup/with-ready-engine! (:run @cell)
                      (fn [{:keys [entries headers]}]
                        (let [entry (first (filter #(= name (get % "name")) entries))]
                          (and entry (= signature (get-in entry ["typeCheck" "signature"]))
                               (some? (get headers (get-in entry ["callable" "name"])))))))]
        ;; Ordinary requested-name/type rejection is outside the runtime callback.
        (need matched "EntryRejected" "No checked entry matches this name and requested signature")
        (Handle. project name signature)))))
(defn- entry! [entries headers name signature]
  (let [entry (first (filter #(= name (get % "name")) entries))]
    (need (= signature (get-in entry ["typeCheck" "signature"])) "EntryRejected" "Checked entry signature changed")
    [(get headers (get-in entry ["callable" "name"])) (label (get-in entry ["callable" "name"]))]))
(defn- drive! [ctx engine callable args slot]
  (deadline! engine)
  (let [deadline (+ (System/nanoTime) duration-nanos)]
    (aset ^objects slot 1 :start-pending)
    (ir/start! ctx engine callable args)
    (aset ^objects slot 1 :running)
    (loop []
      (when (.isInterrupted (Thread/currentThread)) (throw (ex-info "Project call interrupted" {:code "Cancelled"})))
      (need (< (System/nanoTime) deadline) "ResourceLimit" "Project call cooperative deadline exhausted")
      (case (ir/phase ctx engine)
        "complete" nil
        "running" (let [left (- instruction-limit (ir/instructions ctx engine))]
                    (need (pos? left) "ResourceLimit" "Project call instruction budget exhausted")
                    (ir/advance! ctx engine (min 128 left)) (recur))
        (throw (ex-info "Unsupported runtime boundary" {:code "CapabilityMissing"}))))
    (need (identical? (aget ^objects slot 2)
                     (#'startup/engine-field (#'startup/engine-field engine "entry") "header"))
          "RuntimeBoundary" "Actual root callable Header changed")
    (aset ^objects slot 1 :take-pending)
    (let [value (ir/take-result! ctx engine)]
      (aset ^objects slot 0 value) (aset ^objects slot 1 :owned) value)))
(defn- finish-result! [ctx engine value slot]
  (aset ^objects slot 1 :release-started)
  (ir/release! ctx engine value)
  (aset ^objects slot 0 nil) (aset ^objects slot 1 :released) (aset ^objects slot 2 nil)
  (invoke-zero engine "clearAtomicDeadline")
  (drain! engine))
(defn invoke-function! [project handle input]
  (let [cell (cell! project)]
    (locking cell
      (live! cell)
      (need (and (= Handle (class handle)) (identical? project (.-owner ^Handle handle)))
            "EntryRejected" "Function handle belongs to another Project lease")
      (let [signature (.-signature ^Handle handle)
            _ ((if (= signature "nat-to-nat") nat! string!) input)
            slot (:slot @cell)]
        (try
          (startup/with-ready-engine! (:run @cell)
            (fn [{:keys [ctx engine entries headers]}]
              (let [[header callable] (entry! entries headers (.-name ^Handle handle) signature)
                    _ (aset ^objects slot 2 header)
                    value (drive! ctx engine callable [input] slot)
                    answer ((if (= signature "nat-to-nat") result-nat! string!) value)
                    output (finish-result! ctx engine value slot)]
                (need (= ["" ""] output) "RuntimeBoundary" "Pure checked entry unexpectedly produced captured output")
                answer)))
          (catch Throwable failure (swap! cell assoc :status :failed) (throw failure)))))))
(defn- io-result! [ctx value]
  (need (= (:node-class ctx) (class value)) "RuntimeBoundary" "IO entry returned another carrier")
  (let [tag (.get ^java.lang.reflect.Field (:tag ctx) value)
        fields (.get ^java.lang.reflect.Field (:fields ctx) value)
        scalars (.get ^java.lang.reflect.Field (:scalars ctx) value)
        kind-method (.getDeclaredMethod ^Class (:class ctx) "kindMetadata" (into-array Class [(:node-class ctx)]))
        _ (.setAccessible kind-method true)]
    (need (and (= 1 (alength ^objects fields)) (zero? (alength ^bytes scalars)) (#{0 1} tag)
               (not (neg? (.get ^java.lang.reflect.Field (:rc ctx) value)))
               (every? #(false? (#'startup/engine-field value %)) ["dead" "array" "ref" "readyTask"])
               (nil? (#'startup/engine-field value "closure"))
               (nil? (.invoke kind-method nil (object-array [value]))))
          "RuntimeBoundary" "IO entry returned an unsupported result envelope")
    (if (= 0 tag)
      (do (need (and (= Long (class (aget ^objects fields 0))) (zero? (long (aget ^objects fields 0))))
                "RuntimeBoundary" "IO Unit entry returned another payload") :ok)
      :io-error)))
(defn run-main! [project]
  (let [cell (cell! project)]
    (locking cell
      (live! cell)
      (let [slot (:slot @cell)
            mains (startup/with-ready-engine! (:run @cell)
                    (fn [{:keys [entries]}]
                      (filterv #(= "io-unit" (get-in % ["typeCheck" "signature"])) entries)))]
        (need (= 1 (count mains)) "EntryRejected" "Exactly one checked IO Unit entry is required")
        (try
          (let [result (startup/with-ready-engine! (:run @cell)
                         (fn [{:keys [ctx engine entries headers]}]
                           (let [mains (filterv #(= "io-unit" (get-in % ["typeCheck" "signature"])) entries)]
                             (need (= 1 (count mains)) "EntryRejected" "Exactly one checked IO Unit entry is required")
                             (let [entry (first mains) [header callable] (entry! entries headers (get entry "name") "io-unit")
                                   _ (aset ^objects slot 2 header)
                                   value (drive! ctx engine callable [(long 0)] slot)
                                   kind (io-result! ctx value)
                                   output (finish-result! ctx engine value slot)]
                               {:kind kind :output output}))))]
            (if (= :ok (:kind result))
              (let [[out err] (:output result) [prefix-out prefix-err] (:prefix @cell)]
                (swap! cell assoc :prefix ["" ""])
                (MainResult. (str prefix-out out) (str prefix-err err)))
              (throw (ex-info "IO Unit entry returned an IO error" {:code "GuestIOError"}))))
          (catch Throwable failure (swap! cell assoc :status :failed) (throw failure)))))))
(defn close! [project]
  (let [cell (cell! project)]
    (locking cell
      (when-not (= :closed (:status @cell))
        (swap! cell assoc :status :closing)
        (retire! cell))) nil))
