;; Environment replay — verify imported declarations.

(ns ansatz.export.replay
  "Replays imported declarations through the Ansatz kernel type checker."
  (:require [ansatz.kernel.env :as env]
            [ansatz.export.parser :as parser])
  (:import [ansatz.kernel ConstantInfo InductiveBundle TypeChecker Env ExprStore Name]))

(def ^:private default-fuel
  "Default fuel per declaration for legacy in-memory replay. Lean 4 has no
  fuel limit; this 20M bound keeps small replay jobs responsive. Full Mathlib
  store verification should use ansatz.export.storage with its higher verifier
  default or an explicit :fuel."
  20000000)

(def ^:private default-stack-size
  "64MB stack for deep type-checker recursion on large proofs."
  (* 64 1024 1024))

(defn- run-with-large-stack
  "Run f on a thread with a large stack (default 64MB).
   Blocks until completion. Re-throws any exception from f."
  ([f] (run-with-large-stack f default-stack-size))
  ([f stack-size]
   (let [result (promise)
         error (promise)
         t (Thread. nil
                    (fn []
                      (try
                        (deliver result (f))
                        (catch Throwable e
                          (deliver error e))))
                    "ansatz-large-stack"
                    (long stack-size))]
     (.start t)
     (.join t)
     (when (realized? error)
       (throw @error))
     @result)))

(defn replay-one
  "Type-check and add one declaration to the environment.
   Returns [env result-map]."
  [^Env env ^ConstantInfo ci]
  (let [tag (.tag ci)
        name-str (.toString (.name ci))]
    (try
      (cond
        ;; Quotient primitives.
        (= 4 (int tag))
        (let [env (.addConstant env ci)
              env (.enableQuot env)]
          [env {:status :ok :name name-str :tag (env/ci-tag ci)}])

        ;; Inductives, constructors, recursors must be replayed as a bundle.
        (#{5 6 7} (int tag))
        [env {:status :error :name name-str :tag (env/ci-tag ci)
              :error "inductive declarations must be admitted as a bundle"}]

        :else
        (let [env (TypeChecker/checkConstant env ci default-fuel)]
          ;; Note: do NOT strip theorem values — downstream isDefEq may need them.
          [env {:status :ok :name name-str :tag (env/ci-tag ci)}]))

      (catch Exception ex
        [env {:status :error :name name-str :tag (env/ci-tag ci)
              :error (.getMessage ex)}]))))

(defn- bundle-member?
  [^objects all-names ^ConstantInfo ci]
  (let [tag (.tag ci)]
    (case tag
      5 (some #(= ^Object % (.name ci)) all-names)
      6 (some #(= ^Object % (.inductName ci)) all-names)
      7 (let [rec-all (.all ci)]
          (and rec-all
               (= (alength all-names) (alength rec-all))
               (every? true?
                       (map (fn [a b] (= a b))
                            all-names rec-all))))
      false)))

(defn- collect-inductive-bundle
  "Collect one contiguous inductive bundle starting at decls/head.
   Returns {:bundle ... :members [...] :rest remaining-decls}."
  [decls]
  (let [^ConstantInfo first-ci (first decls)
        all-names (or (.all first-ci) (into-array Object [(.name first-ci)]))]
    (loop [remaining (seq decls)
           members []]
      (if-let [^ConstantInfo ci (first remaining)]
        (if (bundle-member? all-names ci)
          (recur (next remaining) (conj members ci))
          {:members members :rest remaining})
        {:members members :rest nil}))))

(defn- build-inductive-bundle
  [members]
  (let [inductives (filterv #(.isInduct ^ConstantInfo %) members)
        ctors (filterv #(.isCtor ^ConstantInfo %) members)
        recursors (filterv #(.isRecursor ^ConstantInfo %) members)
        ^ConstantInfo first-ind (first inductives)]
    (env/mk-inductive-bundle
     (vec (.levelParams first-ind))
     (.numParams first-ind)
     (.isUnsafe first-ind)
     inductives
     ctors
     recursors)))

(defn- replay-inductive-bundle
  [^Env env members]
  (let [bundle (build-inductive-bundle members)]
    (try
      (let [env' (env/check-inductive-bundle env bundle default-fuel)
            results (mapv (fn [^ConstantInfo ci]
                            {:status :ok :name (.toString (.name ci)) :tag (env/ci-tag ci)})
                          members)]
        [env' results])
      (catch Exception ex
        (let [msg (.getMessage ex)
              results (mapv (fn [^ConstantInfo ci]
                              {:status :error :name (.toString (.name ci)) :tag (env/ci-tag ci)
                               :error msg})
                            members)]
          [env results])))))

(defn replay
  "Replay all declarations through the type checker.
   Runs on a thread with a 64MB stack to handle deep recursion."
  [decls & {:keys [verbose? stop-on-error?]
            :or {verbose? false stop-on-error? false}}]
  (run-with-large-stack
   (fn []
     (let [start-time (System/currentTimeMillis)
           env (env/empty-env)]
       (loop [decls (seq decls)
              env env
              results (transient [])
              ok-count 0
              err-count 0]
         (if-let [ci (first decls)]
           (if (.isInduct ^ConstantInfo ci)
             (let [{:keys [members rest]} (collect-inductive-bundle decls)
                   [env' bundle-results] (replay-inductive-bundle env members)
                   results' (reduce conj! results bundle-results)
                   ok+ (count (filter #(= :ok (:status %)) bundle-results))
                   err+ (count (filter #(= :error (:status %)) bundle-results))]
               (when verbose?
                 (doseq [result bundle-results]
                   (case (:status result)
                     :ok (print ".")
                     :error (do (println)
                                (println "ERROR:" (:name result) "-" (:error result))))))
               (when (and stop-on-error? (pos? err+))
                 (throw (ex-info "Replay stopped on error"
                                 {:result (first (filter #(= :error (:status %)) bundle-results))
                                  :env env
                                  :results (persistent! results')})))
               (recur rest
                      env'
                      results'
                      (+ ok-count ok+)
                      (+ err-count err+)))
             (let [[env' result] (replay-one env ci)]
               (when verbose?
                 (case (:status result)
                   :ok (print ".")
                   :error (do (println)
                              (println "ERROR:" (:name result) "-" (:error result)))))
               (when (and stop-on-error? (= :error (:status result)))
                 (throw (ex-info "Replay stopped on error"
                                 {:result result :env env
                                  :results (persistent! (conj! results result))})))
               (recur (next decls)
                      env'
                      (conj! results result)
                      (if (= :ok (:status result)) (inc ok-count) ok-count)
                      (if (= :error (:status result)) (inc err-count) err-count))))
           (do
             (when verbose? (println))
             {:env env
              :results (persistent! results)
              :stats {:ok ok-count
                      :errors err-count
                      :total (+ ok-count err-count)
                      :elapsed-ms (- (System/currentTimeMillis) start-time)}})))))))

(defn replay-file
  "Parse an NDJSON file and replay all declarations."
  [path & {:as opts}]
  (let [_ (println "Parsing" path "...")
        st (parser/parse-ndjson-file path)
        decls (:decls st)
        meta (:meta st)
        _ (println "Parsed:" (count decls) "declarations,"
                   (.size ^java.util.ArrayList (:names st)) "names,"
                   (.size ^ExprStore (:exprs st)) "expressions")
        _ (println "Replaying declarations...")
        result (replay decls opts)]
    (println "Done:" (:stats result))
    (assoc result :meta meta)))

(defn- record-stream-result
  [state result]
  (-> state
      (update (if (= :ok (:status result)) :ok :errors) inc)
      (assoc :last-result result)
      (cond-> (= :error (:status result))
        (update :error-names conj (:name result)))))

(defn- record-stream-results
  [state results]
  (reduce record-stream-result state results))

(defn- flush-stream-bundle
  [state]
  (if-let [members (:pending-inductive-members state)]
    (let [[env' results] (replay-inductive-bundle (:env state) members)]
      (-> state
          (assoc :env env')
          (dissoc :pending-inductive-members :pending-all-names)
          (record-stream-results results)))
    state))

(declare process-stream-decl)

(defn- process-stream-decl
  [state ^ConstantInfo ci]
  (if-let [^objects pending-all (:pending-all-names state)]
    (if (bundle-member? pending-all ci)
      (update state :pending-inductive-members conj ci)
      (process-stream-decl (flush-stream-bundle state) ci))
    (cond
      (.isInduct ci)
      (assoc state
             :pending-inductive-members [ci]
             :pending-all-names (or (.all ci) (into-array Object [(.name ci)])))

      (or (.isCtor ci) (.isRecursor ci))
      (record-stream-result
       state
       {:status :error
        :name (.toString (.name ci))
        :tag (env/ci-tag ci)
        :error "inductive bundle member encountered outside bundle head"})

      :else
      (let [[env' result] (replay-one (:env state) ci)]
        (record-stream-result (assoc state :env env') result)))))

(defn replay-file-streaming
  "Parse and replay declarations in streaming mode.
   Runs on a thread with a 64MB stack to handle deep recursion."
  [path & {:keys [verbose?] :or {verbose? false}}]
  (run-with-large-stack
   (fn []
     (println "Streaming replay of" path "...")
     (let [start-time (System/currentTimeMillis)
           env (env/empty-env)
           result (parser/parse-ndjson-file-streaming
                   path
                   {:env env :ok 0 :errors 0 :error-names []}
                   (fn [state ci]
                     (let [state' (process-stream-decl state ci)
                           result (:last-result state')]
                       (when verbose?
                         (case (:status result)
                           :ok (when (zero? (mod (+ (:ok state) (:errors state)) 1000))
                                 (let [rt (Runtime/getRuntime)
                                       used (quot (- (.totalMemory rt) (.freeMemory rt)) 1048576)]
                                   (println (str "  [" (+ (:ok state) (:errors state)) "] ok=" (:ok state) " err=" (:errors state) " mem=" used "MB"))))
                           :error (println "ERROR:" (:name result) "-" (:error result))
                           nil))
                       state')))]
       (let [st (flush-stream-bundle (:final-state result))
             elapsed (- (System/currentTimeMillis) start-time)]
         (println "Done: ok=" (:ok st) "errors=" (:errors st) "elapsed=" elapsed "ms")
         (when (seq (:error-names st))
           (println "Failed:" (count (:error-names st)) "declarations"))
         {:env (:env st)
          :stats {:ok (:ok st) :errors (:errors st)
                  :total (+ (:ok st) (:errors st))
                  :elapsed-ms elapsed}
          :error-names (:error-names st)
          :meta (:parser-meta result)})))))

(defn summarize-errors
  "Print a summary of replay errors grouped by error message pattern."
  [results]
  (let [errors (filter #(= :error (:status %)) results)
        truncate (fn [s] (if (and s (> (count s) 80)) (subs s 0 80) s))
        by-msg (group-by (comp truncate :error) errors)]
    (println (count errors) "errors out of" (count results) "declarations")
    (println)
    (doseq [[msg decls] (sort-by (comp - count val) by-msg)]
      (println (count decls) "x" msg)
      (when (<= (count decls) 5)
        (doseq [d decls]
          (println "  " (:name d) "(" (clojure.core/name (:tag d)) ")"))))))
