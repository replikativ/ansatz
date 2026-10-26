(ns prototype.typed-tail-execution
  "Optional JVM emission for validated represented tail graphs."
  (:require [prototype.typed-tail :as prep]
            [prototype.typed-tail-emit :as emit]
            [prototype.mutable :as u]
            [prototype.runtime-abi :as abi]
            [prototype.fingerprint :as fingerprint]
            [prototype.machine :as m]))

(def ^:private generation (Object.))
(def ^:private maximum 18446744073709551615N)
(def ^:private modulus 18446744073709551616N)
(def ^:private context-slot ::context)
(deftype ^:private Context [region key names entry-info dependencies literals literal-tags tokens abi-token emit-token owner factory]
  clojure.lang.ILookup
  (valAt [this k] (.valAt this k nil))
  (valAt [_ k not-found]
    (case k :region region :key key :names names :entry-info entry-info
          :dependencies dependencies :literals literals :literal-tags literal-tags
          :tokens tokens :abi-token abi-token :emit-token emit-token :owner owner :factory factory not-found)))

(defn- owner-free-body? [body]
  (let [pending (java.util.ArrayDeque.) seen (java.util.IdentityHashMap.)]
    (.addLast pending body)
    (loop []
      (if (.isEmpty pending) true
          (let [x (.removeLast pending)]
            (cond
              (.containsKey seen x) (recur)
              (= clojure.lang.PersistentVector (class x))
              (if (meta x) false
                  (do (.put seen x true) (doseq [child x] (when (some? child) (.addLast pending child))) (recur)))
              (or (nil? x) (string? x) (keyword? x) (boolean? x)
                  (contains? #{Long Integer Short Byte clojure.lang.BigInt java.math.BigInteger} (class x))) (recur)
              :else false))))))

(defn- carrier? [type value]
  (and (or (= Long (class value)) (= clojure.lang.BigInt (class value)))
       (<= 0 value)
       (<= value (case type "uint8" 255 "uint16" 65535 "uint32" 4294967295 maximum))))

(defn- scalar-value [context bits tag]
  (case (long tag)
    0 (Long/valueOf (long bits))
    1 (if (neg? (long bits)) (+' (bigint bits) modulus) (bigint bits))
    (nth (:literals context) (- (long tag) 2))))

(defn- context-valid? [context machine]
  (and (instance? Context context) (identical? generation (:owner context))
       (identical? (abi/scalar-description-token) (:abi-token context))
       (identical? (emit/generation-token) (:emit-token context))
       (u/current-tail-region? (:tokens context)
                               (mapv (juxt :extern :operation) (vals (get-in context [:region :descriptors]))))
       (every? (fn [[name expected]]
                 (let [actual (get (:functions machine) name)
                       cached (when-let [cache (:function-slot-cache machine)] (.get ^java.util.IdentityHashMap cache actual))]
                   (and (identical? (:body expected) (:body actual))
                        (= (:params expected) (:params actual))
                        (= (:runtime-extern expected) (:runtime-extern actual))
                        (= (:keys expected) (set (keys actual)))
                        (or (nil? cached) (= cached (:slots expected)))
                        (= (:slots expected) (u/function-slots actual))))) (:dependencies context))))

(defn- entry-valid? [context machine name]
  (let [params (get-in context [:region :functions name :params])
        ^objects locals (u/locals-array machine)]
    (and (identical? (get-in context [:entry-info name :body]) (u/body-of machine))
         (<= (get-in context [:dependencies name :slots]) (alength locals))
         (u/tail-entry-state? machine (mapv :id params))
         (every? #(carrier? (:type %) (aget locals (int (:id %)))) params))))

(defn- factory-plan [region names literal-tags options]
  (try (emit/emit-factory region names literal-tags options)
       (catch Throwable t
         (cond
           (:typed-tail-emission-fallback (ex-data t)) {:fallback (:typed-tail-emission-fallback (ex-data t))}
           (some (fn [cause]
                   (or (contains? #{"clojure.asm.MethodTooLargeException" "clojure.asm.ClassTooLargeException"} (.getName (class cause)))
                       (and (instance? IndexOutOfBoundsException cause)
                            (contains? #{"Method code too large!" "Class file too large!"} (.getMessage ^Throwable cause)))))
                 (take-while some? (iterate ex-cause t))) {:fallback :jvm-size-limit}
           :else (throw t)))))

(defn prepare-context [functions config options]
 (try
  (when-not (and (map? config) (= #{:typed-functions :roots :descriptors :profile :budgets} (set (keys config))))
    (m/fail "Invalid typed-tail compiler configuration" {}))
  (let [prepared (prep/prepare-region functions (:typed-functions config) (:roots config)
                                       (:descriptors config) (:profile config) (:budgets config))]
    (if-not (= :ready (:status prepared)) {:status :fallback :reason (:reason prepared)}
      (let [region (:region prepared) names (vec (sort-by pr-str (keys (:functions region))))
            dependencies (into {} (for [[name expected] (:dependencies region)
                                        :let [actual (get functions name)]]
                                    (do
                                      (when-not (and (owner-free-body? (:body actual))
                                                     (= (set (keys actual)) (if (= :extern (:kind expected))
                                                                             #{:params :body :runtime-extern} #{:params :body})))
                                        (throw (ex-info "Unsupported actual typed-tail code attributes" {::fallback :unsupported-actual-code-attributes})))
                                      [name (assoc (into {} expected) :body (:body actual) :keys (set (keys actual))
                                                   :slots (if (= :extern (:kind expected))
                                                            (+ 2 (reduce max 0 (:params expected)))
                                                            (inc (reduce max 0
                                                                         (concat (:params expected)
                                                                                 (keep (fn [b] (when (contains? #{:literal :intrinsic} (first (:operation b)))
                                                                                                 (nth (:operation b) 2)))
                                                                                       (get-in region [:functions name :blocks])))))))])))
            entry-keys (frequencies (map #(fingerprint/key (get-in dependencies [% :body])) names))
            entry-info (into {} (map-indexed (fn [tag name]
                                              (let [body (get-in dependencies [name :body])]
                                                [name {:tag tag :body body :ambiguous? (> (get entry-keys (fingerprint/key body)) 1)}])) names))
            literals (vec (for [name names block (get-in region [:functions name :blocks])
                               :when (= :literal (first (:operation block)))]
                           {:site [name (:id block)] :value (get-in block [:carrier :value])}))
            literal-tags (into {} (map-indexed (fn [i literal] [(:site literal) (+ i 2)]) literals))
            key [::region-v1 generation (emit/generation-token) (abi/scalar-description-token) (u/tail-region-tokens)
                 (:key region) names (mapv #(select-keys % [:site :value]) literals)
                 (boolean (:direct-linking options))]
            emission-options {:direct-linking (boolean (:direct-linking options))}
            factory (delay (factory-plan region names literal-tags emission-options))]
        (->Context region key names entry-info dependencies (mapv :value literals) literal-tags
                   (u/tail-region-tokens) (abi/scalar-description-token) (emit/generation-token) generation factory))))
  (catch clojure.lang.ExceptionInfo e
    (if-let [reason (::fallback (ex-data e))] {:status :fallback :reason reason} (throw e)))))

(defn bind-context [machine context] (assoc machine context-slot context))

(defn- return-body [context name pc]
  (get-in context [:region :functions name :canonical-instructions pc :form]))

(defn- fallback! [machine fuel one?]
  (if one? (u/step! machine) (u/run! machine fuel))
  :interpreted)

(defn- run-entry [expected-key tag factory machine fuel one?]
  (let [context (get machine context-slot)]
    (if-not (and (context-valid? context machine) (= expected-key (:key context)))
      (fallback! machine fuel one?)
      (let [name (nth (:names context) tag) max-cost (get-in context [:region :functions name :max-cost])
            steps (u/steps machine)
            headroom (if (neg? steps) 0 (- Long/MAX_VALUE steps))]
        (if-not (and (entry-valid? context machine name) (<= 0 (u/steps machine))
                     (<= max-cost headroom) (<= max-cost fuel))
          (fallback! machine fuel one?)
          (if-let [code (:code @factory)]
           (code machine context tag
           (long (min fuel headroom (* 4096 (reduce max 1 (map :max-cost (vals (get-in context [:region :functions])))))))
           fuel (if one? 1 4096) one?)
           (fallback! machine fuel one?)))))))

(defn extension-key [context body]
  (when (instance? Context context)
    (let [matches (filter (fn [[_ info]] (and (not (:ambiguous? info)) (identical? body (:body info)))) (:entry-info context))]
      (when (= 1 (count matches)) [(:key context) (get-in (first matches) [1 :tag])]))))

(defn compile-entry [context body]
  (when-let [[key tag] (extension-key context body)]
    (let [name (nth (:names context) tag) cost (get-in context [:region :functions name :max-cost]) factory (:factory context)]
      {:max-cost cost :tail-extension (extension-key context body) :specialization {:kind :typed-tail :name name}
       :execute! (fn [machine] (run-entry key tag factory machine cost true))
       :execute-budget! (fn [machine fuel] (run-entry key tag factory machine fuel false))})))

(defn force-compilation!
  "Internal preparation/emission measurement hook; performs no guest execution."
  [context]
  (if (and (instance? Context context) (identical? generation (:owner context))
           (identical? (emit/generation-token) (:emit-token context))
           (identical? (abi/scalar-description-token) (:abi-token context)))
    @(:factory context)
    {:fallback :stale-or-unsupported-context}))
