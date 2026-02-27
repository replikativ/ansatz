;; Copyright (c) 2026 Simmis GmbH. All rights reserved.
;; Environment replay — verify imported declarations.

(ns cic.export.replay
  "Replays imported declarations through the CIC kernel type checker."
  (:require [cic.kernel.env :as env]
            [cic.kernel.name :as name]
            [cic.export.parser :as parser])
  (:import [cic.kernel ConstantInfo TypeChecker Env ExprStore Name]))

(def ^:private default-fuel
  "Default fuel per declaration. 10M steps handles all known proofs."
  10000000)

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
                    "cic-large-stack"
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
      (case tag
        ;; Quotient primitives
        4 ;; QUOT
        (do (.addConstant env ci)
            (.enableQuot env)
            [env {:status :ok :name name-str :tag (env/ci-tag ci)}])

        ;; Inductives, constructors, recursors: check type only
        (5 6 7) ;; INDUCT, CTOR, RECURSOR
        (do (TypeChecker/checkType env ci default-fuel)
            (.addConstant env ci)
            [env {:status :ok :name name-str :tag (env/ci-tag ci)}])

        ;; Everything else: full type check via Java TypeChecker
        ;; checkConstant adds to env internally
        (do (TypeChecker/checkConstant env ci default-fuel)
            ;; Strip values from thm/opaque to save memory
            (when (or (.isThm ci) (.isOpaq ci))
              (set! (.value ci) nil))
            [env {:status :ok :name name-str :tag (env/ci-tag ci)}]))

      (catch Exception ex
        (when (or (.isThm ci) (.isOpaq ci))
          (set! (.value ci) nil))
        ;; Try to add to env anyway (for subsequent declarations that depend on this one)
        (try (.addConstantIfAbsent env ci) (catch Exception _))
        [env {:status :error :name name-str :tag (env/ci-tag ci)
              :error (.getMessage ex)}]))))

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
              results (transient [])
              ok-count 0
              err-count 0]
         (if-let [ci (first decls)]
           (let [[_ result] (replay-one env ci)]
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
                    (conj! results result)
                    (if (= :ok (:status result)) (inc ok-count) ok-count)
                    (if (= :error (:status result)) (inc err-count) err-count)))
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
                     (let [[_ result] (replay-one (:env state) ci)]
                       (when verbose?
                         (case (:status result)
                           :ok (when (zero? (mod (+ (:ok state) (:errors state)) 1000))
                                 (let [rt (Runtime/getRuntime)
                                       used (quot (- (.totalMemory rt) (.freeMemory rt)) 1048576)]
                                   (println (str "  [" (+ (:ok state) (:errors state)) "] ok=" (:ok state) " err=" (:errors state) " mem=" used "MB"))))
                           :error (println "ERROR:" (:name result) "-" (:error result))))
                       (-> state
                           (update (if (= :ok (:status result)) :ok :errors) inc)
                           (cond-> (= :error (:status result))
                             (update :error-names conj (:name result)))))))]
       (let [st (:final-state result)
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
