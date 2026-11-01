(ns java-ir-entropy-capability-checks
  "Opt-in portable JDK entropy, actual codec rows, and explicit failure custody."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.java.io :as io]
            [clojure.data.json :as json] [java-ir-baseline :as j]
            [java-ir-baseline-checks :as c] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as host] [java-ir-byte-array-checks :as bytes]
            [lean-compatibility-corpus :as corpus])
  (:import [java.nio.file Files] [java.math BigInteger] [java.security MessageDigest]))
(def ^:dynamic *basis* nil)
(def ^:dynamic *directory* "test/fixtures/java-entropy-runtime")
(defonce ^:private packets (atom []))
(defn owner-packets [] (mapv deref @packets))
(defn file [name] (io/file (str *directory*) name))
(defn row [name] (json/read-str (slurp (file name))))
(defn read-bytes [name] (Files/readAllBytes (.toPath (file name))))
(defn cap-class [] (Class/forName "ansatz.research.ir.Interpreter$EntropyCapability" true (:loader *basis*)))
(defn cap [method types args] (j/invoke-static (.getMethod ^Class (cap-class) method (into-array Class types)) args))
(defn pattern-cap [pattern] (cap "deterministicForTesting" [(class (byte-array 0)) Integer/TYPE] [pattern (int 8)]))
(defn failing-cap [kind] (cap "failureForTesting" [String String Integer/TYPE] [kind "expected test source failure" (int 8)]))
(defn draws [capability] (.invoke (.getMethod (class capability) "draws" (make-array Class 0)) capability (object-array 0)))
(defn row-sha [r]
  (apply str (map #(format "%02x" (bit-and 255 %))
                 (.digest (MessageDigest/getInstance "SHA-256") (.getBytes (json/write-str r) "UTF-8")))))
(defn context
  ([] (context identity identity))
  ([error-transform] (context error-transform identity))
  ([error-transform row-transform]
   (let [names ["entropy-raw.json" "entropy-boxed.json" "user-error.json" "uint64-to-nat.json"
                "usize-of-nat.json" "usize-of-nat-boxed.json"]
         provenance (row "provenance.json") originals (mapv row names) rs (mapv row-transform originals)
         pins (into {} (map (fn [f original r] [(get r "name")
                            (if (= original r) (get-in provenance ["files" f "sha256"]) (row-sha r))]) names originals rs))
         base (j/prepare-host-program *basis* [] []) source (j/source-binding base {"entropy-fixtures" provenance "current-row-hashes" pins})
         headers (into {} (map (fn [r] [(get r "name") (j/declaration-header source r (pins (get r "name")))]) rs))
         registered (j/register-headers base (vec (vals headers)))
         prepared (reduce (fn [ctx r]
                            (if (get-in r ["ir" "fdecl"])
                              (let [actual (if (= (get r "name") (get (row "user-error.json") "name")) (error-transform r) r)]
                                (j/materialize-body ctx (headers (get r "name")) actual (mapv headers (get r "dependencies")))) ctx)) registered rs)]
     (-> prepared (dissoc :task-runtime :profiling-policy)
         (assoc :explicit true :initializing true :headers headers :source source)))))
(defn engine [ctx]
  (when (>= (count @packets) 128) (throw (ex-info "Test owner-packet bound" {})))
  (let [e (j/machine ctx) packet (atom {:ctx ctx :engine e :status :open})]
    (swap! packets conj packet)
    {:ctx ctx :engine e :packet packet}))
(defn close! [{:keys [ctx engine packet]}]
  (j/close! ctx engine) (reset! packet {:status :closed}))
(defn status [{:keys [ctx engine]}]
  (.invoke (.getMethod ^Class (:class ctx) "entropyStatus" (make-array Class 0)) engine (object-array 0)))
(defn install!
  ([state capability] (install! state capability (get-in state [:ctx :headers (get (row "user-error.json") "name")]) (read-bytes "user-error.json")))
  ([{:keys [ctx engine]} capability error-header raw]
   (let [entropy (get-in ctx [:headers (get (row "entropy-raw.json") "name")])]
     (.invoke (.getMethod ^Class (:class ctx) "installEntropy"
                          (into-array Class [(cap-class) (class entropy) (class error-header) (class raw)]))
              engine (object-array [capability entropy error-header raw])))))
(defn start! [{:keys [ctx engine]} n] (j/start! ctx engine "IO.getRandomBytes" [n 0]))
(defn drain! [{:keys [ctx engine]}]
  (loop [left 64]
    (case (j/phase ctx engine)
      "complete" nil
      "running" (do (when (zero? left) (throw (ex-info "Entropy model budget exhausted" {})))
                     (j/advance! ctx engine 1) (recur (dec left)))
      (throw (ex-info "Unexpected entropy phase" {:phase (j/phase ctx engine)})))))
(defn take! [{:keys [ctx engine] :as state}] (drain! state) (j/take-result! ctx engine))
(defn fields [ctx node] (vec (.get ^java.lang.reflect.Field (:fields ctx) node)))
(defn tag [ctx node] (.getInt ^java.lang.reflect.Field (:tag ctx) node))
(defn counters [{:keys [engine]}] (mapv #(host/private-value engine %) ["allocations" "stores" "retains" "releases"]))
(defn private-method [state method types args]
  (let [m (doto (.getDeclaredMethod ^Class (get-in state [:ctx :class]) method (into-array Class types)) (.setAccessible true))]
    (.invoke m (:engine state) (object-array args))))
(defn set-field! [o name value]
  (let [f (doto (.getDeclaredField (class o) name) (.setAccessible true))] (.set f o value)))

(deftest exact-original-rows-and-native-abi
  (let [p (row "provenance.json") raw (row "entropy-raw.json")]
    (doseq [[name pin] (get p "files")] (is (= (get pin "sha256") (corpus/sha256 (file name)))))
    (is (= ["usize" "void"] (mapv #(get % "ty") (get-in raw ["ir" "extern" "xs"]))))
    (is (= [false false] (mapv #(get % "borrow") (get-in raw ["ir" "extern" "xs"]))))
    (let [method (.getMethod ^Class (:class *basis*) "validateExternAbi" (into-array Class [java.util.Map]))]
      (is (= "lean_io_get_random_bytes" (j/invoke-static method [raw])))
      (doseq [r [(assoc-in raw ["ir" "extern" "xs" 0 "borrow"] true)
                (assoc-in raw ["ir" "extern" "xs" 0 "ty"] "tobject")
                (assoc-in raw ["ir" "extern" "type"] "tobject")]]
        (is (g/bad? #(j/invoke-static method [r])))))))

(deftest install-requires-authentic-body-not-merely-header-metadata
  (doseq [change [#(assoc-in % ["ir" "fdecl" "body" 3 "ctor" "i" "cidx"] 17)
                  #(assoc-in % ["ir" "fdecl" "body" 4 1 "var" "id" "idx"] 1)]]
    (let [s (engine (context change)) capability (pattern-cap (byte-array 8))]
      (is (g/bad? #(install! s capability))) (is (= 0 (draws capability))) (close! s)))
  (let [s (engine (context)) capability (pattern-cap (byte-array 8))
        header (get-in s [:ctx :headers (get (row "user-error.json") "name")])
        fresh (j/declaration-header (get-in s [:ctx :source]) (row "user-error.json")
                                    (get-in (row "provenance.json") ["files" "user-error.json" "sha256"]))]
    (is (g/bad? #(install! s capability header (byte-array [1]))))
    (is (g/bad? #(install! s capability fresh (read-bytes "user-error.json"))))
    (install! s capability) (is (g/bad? #(install! s capability)))
    (close! s)))

(deftest current-row-provenance-hashes-are-independent-of-frozen-codec-witness
  (let [metadata #(-> % (dissoc "pretty") (assoc "sourceLocal" false)
                        (assoc-in ["runtime" "initializationAction"] nil))
        s (engine (context identity metadata)) capability (pattern-cap (byte-array 8))
        entropy (get-in s [:ctx :headers (get (row "entropy-raw.json") "name")])
        error (get-in s [:ctx :headers (get (row "user-error.json") "name")])]
    (is (not= (get-in (row "provenance.json") ["files" "entropy-raw.json" "sha256"])
              (j/request-value entropy "originalSha256")))
    (is (not= (get-in (row "provenance.json") ["files" "user-error.json" "sha256"])
              (j/request-value error "originalSha256")))
    (install! s capability)
    (is (true? (get (status s) "configured"))) (is (= 0 (draws capability)))
    (close! s)))

(deftest current-canonical-rows-must-still-be-ordinary-uninitialized-and-correct-kind
  (doseq [target [(get (row "entropy-raw.json") "name") (get (row "user-error.json") "name")]
          change [#(assoc-in % ["runtime" "role"] "value")
                  #(assoc-in % ["runtime" "initializer"] (get (row "user-error.json") "name"))
                  #(assoc-in % ["runtime" "initializationAction"] "io")
                  #(assoc % "redirect" {})]]
    (let [transform #(if (= target (get % "name")) (change %) %)
          s (engine (context identity transform)) capability (pattern-cap (byte-array 8))]
      (is (g/bad? #(install! s capability))) (is (= 0 (draws capability))) (close! s)))
  (let [entropy-name (get (row "entropy-raw.json") "name")
        error-name (get (row "user-error.json") "name")]
    (doseq [transform [(fn [r] (if (= entropy-name (get r "name"))
                                (assoc r "ir" {"fdecl" (-> (get-in r ["ir" "extern"])
                                                           (dissoc "ext") (assoc "body" ["unreachable"] "info" {}))}) r))
                      (fn [r] (if (= error-name (get r "name"))
                                (assoc r "ir" {"extern" (-> (get-in r ["ir" "fdecl"])
                                                           (dissoc "body" "info")
                                                           (assoc "ext" {"entries" [{"standard" {"backend" ["str" ["anonymous"] "all"]
                                                                                                  "fn" "unavailable_entropy_test_codec"}}]}))}) r))]]
      (let [s (engine (context identity transform)) capability (pattern-cap (byte-array 8))]
        (is (g/bad? #(install! s capability))) (is (= 0 (draws capability))) (close! s)))))

(deftest freshness-is-monotonic-even-after-zero-instruction-native-call
  (let [s (engine (context)) {:keys [ctx engine]} s capability (pattern-cap (byte-array 8))]
    (j/start! ctx engine "UInt64.toNat" [0])
    (is (= 0 (j/instructions ctx engine)))
    (is (= 0 (j/take-result! ctx engine)))
    (is (g/bad? #(install! s capability)))
    (is (= 0 (draws capability))) (close! s)))

(deftest preflight-rejects-before-allocation-effect-or-start-claim
  (let [s (engine (context)) {:keys [ctx engine]} s capability (pattern-cap (byte-array 8))]
    (is (g/bad? #(start! s 8)))
    (is (false? (host/private-value engine "everStarted")))
    (install! s capability)
    (doseq [args [[-1 0] [9 0] [8 1] [(.shiftLeft BigInteger/ONE 80) 0]]]
      (let [before (counters s)]
        (is (g/bad? #(j/start! ctx engine "IO.getRandomBytes" args)))
        (is (= before (counters s))) (is (= 0 (draws capability)))
        (is (= "idle" (j/phase ctx engine)))))
    (close! s)))

(deftest preallocated-private-bytes-zero-no-source-and-defensive-copy
  (let [s (engine (context)) {:keys [ctx engine]} s pattern (byte-array (range 8)) capability (pattern-cap pattern)]
    (install! s capability) (aset-byte pattern 0 (byte 99))
    (start! s 0)
    (let [result (take! s) payload (first (fields ctx result))]
      (is (= 0 (tag ctx result))) (is (= [] (bytes/payload ctx payload)))
      (is (= 0 (draws capability))) (j/release! ctx engine result))
    (start! s 8) (j/advance! ctx engine 1)
    (is (= 0 (draws capability))) (is (true? (get (status s) "successOwned")))
    (let [attempt (host/private-value engine "pendingEntropy") host-buffer (host/private-value attempt "host")]
      (j/advance! ctx engine 1) (aset-byte ^bytes host-buffer 0 (byte 77))
      (let [result (take! s) payload (first (fields ctx result))]
        (is (= (vec (range 8)) (bytes/payload ctx payload)))
        (is (= 8 (alength ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) payload))))
        (is (= 1 (draws capability))) (j/release! ctx engine result)))
    (is (nil? (host/private-value engine "pendingEntropy"))) (close! s)))

(deftest expected-provider-error-is-the-actual-original-user-error-shape
  (let [s (engine (context)) {:keys [ctx engine]} s capability (failing-cap "provider")]
    (install! s capability) (start! s 8)
    (let [result (take! s) error (first (fields ctx result)) message (first (fields ctx error))]
      (is (= 1 (tag ctx result))) (is (= 18 (tag ctx error)))
      (is (= "JDK entropy source failed: expected test source failure" message))
      (j/start! ctx engine "IO.userError" [message])
      (let [original (take! s)]
        (is (= (tag ctx original) (tag ctx error)))
        (is (= (fields ctx original) (fields ctx error))) (j/release! ctx engine original))
      (j/release! ctx engine result))
    (is (= 1 (draws capability))) (is (nil? (host/private-value engine "pendingEntropy"))) (close! s)))

(deftest genuine-original-boxed-wrapper-uses-source-boxed-usize-input
  (let [s (engine (context)) {:keys [ctx engine]} s capability (pattern-cap (byte-array (range 8)))]
    (install! s capability)
    (j/start! ctx engine "USize.ofNat._boxed" [8])
    (let [boxed-size (take! s)]
      (is (= 1 (c/rc ctx boxed-size)))
      (j/start! ctx engine "IO.getRandomBytes._boxed" [boxed-size 0])
      (let [result (take! s)]
        (is (= (vec (range 8)) (bytes/payload ctx (first (fields ctx result)))))
        (is (true? (host/private-value boxed-size "dead")))
        (j/release! ctx engine result)))
    (is (= 1 (draws capability))) (close! s)))

(deftest bounded-error-message-formatting-does-not-concatenate-unbounded-input
  (let [method (doto (.getDeclaredMethod ^Class (:class *basis*) "entropyMessage"
                                        (into-array Class [java.security.ProviderException])) (.setAccessible true))
        message (.invoke method nil (object-array [(java.security.ProviderException. (apply str (repeat 5000 "λ")))]))]
    (is (= 4096 (count message))) (is (.startsWith ^String message "JDK entropy source failed: "))))

(deftest unexpected-provider-vm-and-interrupt-failures-retain-owned-custody
  (doseq [kind ["runtime" "vm" "interrupt"]]
    (let [s (engine (context)) {:keys [ctx engine]} s capability (failing-cap kind)]
      (install! s capability) (start! s 8)
      (let [failed (g/bad? #(drain! s)) interrupted (.isInterrupted (Thread/currentThread))]
        ;; Capture and clear before clojure.test reporting can consume the flag.
        (Thread/interrupted)
        (is failed) (is (= (= kind "interrupt") interrupted)))
      (is (= "failed" (j/phase ctx engine))) (is (= 1 (draws capability)))
      (is (true? (get (status s) "successOwned")))
      (is (g/bad? #(j/advance! ctx engine 1))) (is (= 1 (draws capability)))
      (is (g/bad? #(close! s))))))

(deftest injected-prepare-after-effect-and-delivery-failures-never-retry
  (doseq [[fault expected-draws] [[1 0] [2 1] [3 1] [4 0]]]
    (let [s (engine (context)) {:keys [ctx engine]} s capability (pattern-cap (byte-array 8))]
      (install! s capability) (set-field! engine "entropyTestFault" (int fault)) (start! s 8)
      (is (g/bad? #(drain! s))) (is (= expected-draws (draws capability)))
      (is (true? (get (status s) (if (= fault 4) "bytesOwned" "successOwned"))))
      (is (g/bad? #(j/advance! ctx engine 1))) (is (= expected-draws (draws capability)))
      (is (g/bad? #(close! s))))))

(deftest idle-fork-shares-external-service-not-guest-buffer-or-inflight-effect
  (let [s (engine (context)) {:keys [ctx engine]} s capability (pattern-cap (byte-array (range 8)))]
    (install! s capability) (start! s 8)
    (is (g/bad? #(j/fork! ctx engine []))) (is (= 0 (draws capability)))
    (drain! s) (is (g/bad? #(j/fork! ctx engine [])))
    (let [result (j/take-result! ctx engine) fork (j/fork! ctx engine [result])
          child (:engine fork) cloned (first (:roots fork))
          child-packet (atom {:ctx ctx :engine child :status :open}) child-state {:ctx ctx :engine child :packet child-packet}]
      (swap! packets conj child-packet)
      (is (identical? (host/private-value engine "entropyCapability") (host/private-value child "entropyCapability")))
      (is (not (identical? result cloned)))
      (is (not (identical? (first (fields ctx result)) (first (fields ctx cloned)))))
      (start! child-state 8)
      (let [again (take! child-state)] (is (= (vec (range 8)) (bytes/payload ctx (first (fields ctx again)))))
        (j/release! ctx child again))
      (is (= 1 (get (status s) "calls"))) (is (= 2 (get (status child-state) "calls")))
      (is (= 2 (draws capability)))
      (j/release! ctx child cloned) (j/release! ctx engine result)
      (close! child-state))
    (set-field! engine "initializerFailed" true)
    (is (g/bad? #(j/fork! ctx engine [])))
    (set-field! engine "initializerFailed" false) (close! s)))

(deftest saturated-entropy-ap-rejects-surplus-before-any-owner-change
  (doseq [shared? [false true]]
    (let [s (engine (context)) {:keys [ctx engine]} s capability (pattern-cap (byte-array 8))]
      (install! s capability)
      (j/start! ctx engine "IO.userError" ["surplus owner"])
      (let [surplus (take! s) closure (j/make-closure! ctx engine "IO.getRandomBytes._boxed" [])
            functions ^objects (host/private-value (:program ctx) "functions")
            raw (aget functions (int (j/function-id ctx "IO.getRandomBytes")))]
        ;; Controlled internal guard fixture: public closure factories correctly
        ;; reject raw unboxed targets. Preserve the real generation/owner while
        ;; selecting the actual native Function solely to test this preflight.
        (set-field! closure "closure" raw)
        (when shared? (j/retain! ctx engine closure))
        (let [rc (c/rc ctx closure) before (counters s)
              rejected (g/bad? #(private-method s "prepareExplicitApply" [Object (class (object-array 0))]
                                                [closure (object-array [8 0 surplus])]))]
          (is rejected) (is (= rc (c/rc ctx closure))) (is (= 1 (c/rc ctx surplus)))
          (is (= before (counters s))) (is (= 0 (draws capability)))
          (when rejected
            (dotimes [_ rc] (j/release! ctx engine closure)) (j/release! ctx engine surplus) (close! s)))))))

(deftest thread-fence-belongs-to-active-attempt-not-idle-configuration
  (let [s (engine (context)) {:keys [ctx engine]} s capability (pattern-cap (byte-array 8))
        outcome (promise)]
    (install! s capability)
    (let [thread (Thread. ^Runnable (reify Runnable
                                    (run [_] (try (start! s 8)
                                                  (let [result (take! s)] (j/release! ctx engine result))
                                                  (deliver outcome :idle)
                                                  (catch Throwable _ (deliver outcome :failed))))))]
      (.start thread) (.join thread 5000)
      (is (not (.isAlive thread)))
      (is (= :idle (deref outcome 0 :unfinished)))
      (when (= :idle (deref outcome 0 :unfinished)) (close! s))))
  (let [s (engine (context)) {:keys [ctx engine]} s capability (pattern-cap (byte-array 8))
        outcome (promise)]
    (install! s capability) (start! s 8)
    (let [thread (Thread. ^Runnable (reify Runnable
                                    (run [_] (deliver outcome (g/bad? #(j/advance! ctx engine 1))))))]
      (.start thread) (.join thread 5000)
      (is (not (.isAlive thread))) (is (true? (deref outcome 0 false)))
      (is (= "failed" (j/phase ctx engine))) (is (= 0 (draws capability)))
      (is (g/bad? #(close! s))))))

(deftest genuine-jdk-provider-success-has-only-portable-shape-claims
  (let [s (engine (context)) {:keys [ctx engine]} s
        capability (cap "secureRandom" [String String Integer/TYPE] ["DRBG" "" (int 8)])]
    (install! s capability) (start! s 8)
    (let [result (take! s) payload (first (fields ctx result))]
      (is (= 0 (tag ctx result))) (is (= 8 (count (bytes/payload ctx payload))))
      (is (= "portable-jdk-entropy/1" (get (status s) "profile")))
      (is (seq (get (status s) "provider"))) (j/release! ctx engine result))
    (close! s)))

(defn check!
  ([] (run-tests 'java-ir-entropy-capability-checks))
  ([basis fixture-directory] (binding [*basis* basis *directory* fixture-directory] (check!))))
