(ns prototype.coherent-jvm-selection
  "Bounded demanded facts for one admitted worker; no execution or readiness receipt."
  (:refer-clojure :exclude [select])
  (:require [prototype.import-ir :as ir]
            [prototype.runtime-abi :as abi]
            [prototype.session-compiler-options :as options]
            [prototype.typed-ir :as typed]
            [prototype.typed-tail :as tail]))

(def profile
  {:schema "lean-block-profile/1" :producer-commit "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
   :phase :expanded-rc :word-bits 64 :layout :lean-64
   :abi-generation "ansatz-runtime/1" :target :jvm})
(def limits {:max-functions 16 :max-descriptors 64 :max-work 100000 :max-source-bytes 16384})
(def budgets
  {:max-functions 16 :max-instructions 4096 :max-blocks 4096 :max-work 100000
   :max-registers 65536 :max-params 16 :max-emission 8192 :max-constants 8192 :max-chunk-cost 2048})

(defn- refuse! [reason details]
  (throw (ex-info "Finite compiler selection refused" {::refusal reason :details details})))
(defn- require! [condition message]
  (when-not condition (throw (ex-info message {}))))

(defn- copy-data [root spend! & [unsupported-reason]]
  ;; Only demanded rows are copied. Depth and every traversed edge are charged;
  ;; ordinary containers discard metadata and cannot retain Context/World owners.
  (letfn [(copy [x depth]
            (spend! 1)
            (when (> depth 256) (refuse! :nesting-budget {}))
            (cond
              (contains? #{clojure.lang.PersistentArrayMap clojure.lang.PersistentHashMap} (class x))
              (into {} (map (fn [[k v]] [(copy k (inc depth)) (copy v (inc depth))])) x)
              (= clojure.lang.PersistentVector (class x)) (mapv #(copy % (inc depth)) x)
              (or (nil? x) (boolean? x)) x
              (keyword? x) (do (spend! (+ (count (name x)) (count (namespace x)))) x)
              (string? x) (do (spend! (count x)) x)
              (contains? #{Long Integer Short Byte clojure.lang.BigInt java.math.BigInteger} (class x))
              (do (require! (<= (.bitLength (biginteger x)) 4096) "Oversized compiler selection integer") x)
              :else (if unsupported-reason (refuse! unsupported-reason {})
                        (throw (ex-info "Compiler selection requires plain immutable producer data" {})))))]
    (copy root 0)))

(defn- digest! [[digest opaque]]
  (when (seq opaque) (refuse! :opaque-source-key {}))
  (require! (and (string? digest) (re-matches #"[a-f0-9]{64}" digest)) "Invalid compiler key")
  digest)

(defn select
  "Build facts from actual admitted rows and the ORIGINAL independent catalogue.
   Keyed reads only. Facts copying and installed-image preflight share 100k work;
   tail preparation has its existing independent 100k budget. Unsupported shapes
   return fallback; malformed facts throw.
   The caller must still use the public session setter and its live owner checks."
  [prepared independent worker policy-limits]
  (require! (= limits policy-limits) "Unapproved finite compiler selection limits")
  (try
    (let [work (volatile! 0)
          spend! (fn [n] (when (> (vswap! work + n) (:max-work policy-limits))
                           (refuse! :work-budget {})))
          worker (copy-data worker spend!)
          admitted (get-in prepared [:world :eval-const-authorizations :declarations])
          actual-functions (get-in prepared [:world :functions])
          _ (require! (map? actual-functions) "Missing actual installed executable image")
          _ (require! (get admitted worker) "Worker is not an admitted loaded declaration")
          catalogue (:catalogue independent)
          row-for (fn [name]
                    (or (get admitted name)
                        (if-let [read-row (:read-declaration catalogue)] (read-row name)
                            (get-in catalogue [:declarations name]))))
          selected
          (loop [pending [worker] seen #{} functions {} descriptors {}]
            (if (empty? pending) {:functions functions :descriptors descriptors}
              (let [name (peek pending) pending (pop pending)]
                (spend! 1)
                (if (contains? seen name) (recur pending seen functions descriptors)
                  (let [row (or (row-for name) (refuse! :missing-demanded-row {:name name}))
                        row (copy-data (select-keys row [:name :ir :runtime :redirect]) spend!)
                        _ (require! (= name (:name row)) "Demanded declaration name mismatch")]
                    (cond
                      (get-in row [:ir :fdecl])
                      (do
                        (when (>= (count functions) (:max-functions policy-limits)) (refuse! :function-budget {}))
                        (let [[actual function] (ir/lower-typed-declaration row)]
                          (require! (= actual name) "Typed declaration name mismatch")
                          (recur (into pending (ir/static-targets (:body function)))
                                 (conj seen name) (assoc functions name function) descriptors)))
                      (get-in row [:ir :extern])
                      (do
                        (when (>= (count descriptors) (:max-descriptors policy-limits)) (refuse! :descriptor-budget {}))
                        (when (:redirect row) (refuse! :redirected-extern {:name name}))
                        (let [symbol (abi/symbol-for (get-in row [:ir :extern]))]
                          (when-not (abi/scalar-operation symbol) (refuse! :unsupported-extern {:name name}))
                          (let [descriptor (or (abi/describe-scalar row profile)
                                               (refuse! :unsupported-extern {:name name}))]
                            (recur pending (conj seen name) functions (assoc descriptors name descriptor)))))
                      :else (refuse! :unsupported-declaration {:name name})))))))
          raw {:typed-tail {:typed-functions (:functions selected) :roots [worker]
                            :descriptors (:descriptors selected) :profile profile :budgets budgets}}
          _ (doseq [name (concat (keys (:functions selected)) (keys (:descriptors selected)))]
              ;; Charge only demanded installed definitions. The disposable copy
              ;; is not authority: public validators inspect ORIGINAL definitions
              ;; and metadata in the actual image through selected keyed reads.
              (copy-data (get actual-functions name) spend! :unsupported-installed-data))
          validated (options/validate actual-functions raw)
          config (:typed-tail validated)
          represented (tail/prepare-region actual-functions (:typed-functions config) (:roots config)
                                           (:descriptors config) (:profile config) (:budgets config))]
      (if-not (= :ready (:status represented)) represented
        {:compiler-options validated
         :region-key (digest! (get-in represented [:region :key]))
         :source-key (digest! (typed/typed-code-key (get-in config [:typed-functions worker]) profile))}))
    (catch clojure.lang.ExceptionInfo failure
      (if-let [reason (::refusal (ex-data failure))]
        {:status :fallback :reason reason :details (:details (ex-data failure))}
        (throw failure)))))
