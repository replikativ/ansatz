;; Environment replay — verify imported declarations.

(ns ansatz.export.replay
  "Replays imported declarations through the Ansatz kernel type checker."
  (:require [ansatz.kernel.env :as env]
            [ansatz.export.non-safe :as non-safe]
            [ansatz.kernel.quotient :as quotient]
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
   Returns [env result-map].

   When `verify?` is false (trust mode), definitions/theorems/axioms are admitted
   via `addConstant` WITHOUT re-typechecking — appropriate for loading an export
   that was already verified at build time. This is much faster (the typecheck is
   the dominant cost). Inductive bundles always go through the kernel (they need
   recursor-rule generation), so they are unaffected."
  ([^Env env ^ConstantInfo ci] (replay-one env ci true))
  ([^Env env ^ConstantInfo ci verify?]
   (let [tag (.tag ci)
         name-str (.toString (.name ci))]
     (try
       (cond
         ;; Native Lean initializes these as one complete package. A single
         ;; primitive cannot establish that invariant in verified replay.
         (= 4 (int tag))
         (if verify?
           [env {:status :error :name name-str :tag :quot
                 :error "verified quotient admission requires the complete canonical package; use replay"}]
           [(.enableQuot (.addConstant env ci))
            {:status :ok :name name-str :tag :quot}])

         ;; Inductives, constructors, recursors must be replayed as a bundle.
         (#{5 6 7} (int tag))
         [env {:status :error :name name-str :tag (env/ci-tag ci)
               :error "inductive declarations must be admitted as a bundle"}]

         :else
         (let [env (if verify?
                     (if (non-safe/non-safe-definition? ci)
                       (TypeChecker/checkMutualDefinitions env [ci] (long default-fuel))
                       (TypeChecker/checkConstant env ci default-fuel))
                     (.addConstant env ci))]
           ;; Note: do NOT strip theorem values — downstream isDefEq may need them.
           [env {:status :ok :name name-str :tag (env/ci-tag ci)}]))

       (catch Exception ex
         [env {:status :error :name name-str :tag (env/ci-tag ci)
               :error (.getMessage ex)}])))))

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

(defn collect-inductive-bundle
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

(defn replay-inductive-bundle
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

(defn- replay-quotient-package
  [^Env current declarations ^ConstantInfo ci]
  (try
    (let [already? (every? (fn [^ConstantInfo member]
                             (identical? member (.lookup current (.name member)))) declarations)
          next-env (if already? current (quotient/admit-package! current declarations default-fuel))]
      [next-env {:status :ok :name (str (.name ci)) :tag :quot}])
    (catch Exception ex
      [current {:status :error :name (str (.name ci)) :tag :quot :error (.getMessage ex)}])))

(defn- replay-non-safe-group
  [^Env current {:keys [members external-dependencies]}]
  (try
    (let [missing (filterv #(nil? (.lookup current %)) external-dependencies)]
      (when (seq missing)
        (throw (ex-info "Non-safe definition group has missing or out-of-order external dependencies"
                        {:missing (mapv str (take 8 (sort-by str missing)))
                         :missing-count (count missing)})))
      [(TypeChecker/checkMutualDefinitions current members (long default-fuel))
       (mapv (fn [^ConstantInfo ci] {:status :ok :name (str (.name ci)) :tag :def}) members)])
    (catch Exception ex
      [current (mapv (fn [^ConstantInfo ci]
                       {:status :error :name (str (.name ci)) :tag :def :error (.getMessage ex)}) members)])))

(defn- replay-from-env*
  "Replay a finite declaration sequence against an existing checked Env.
   Strict non-safe DEFs are grouped by body-reference SCCs, never DefinitionVal.all.
   Earlier SCC members wait until the last input member; independent interleaved
   declarations retain input order. Native export DFS order is required: external
   group dependencies must already be admitted when the group closes. Headers are
   checked before any group member is visible. Results retain original input order.
   Quotient packages retain atomic preflight/admission. :verify? false explicitly
   TRUSTs definitions without regrouping; inductive bundles are still checked."
  [^Env initial-env declarations & {:keys [verbose? stop-on-error? verify? quotient-errors-as-results? quotient-package-seen?]
                                    :or {verbose? false stop-on-error? false verify? true}}]
  (when-not (instance? Env initial-env)
    (throw (ex-info "Replay requires an initial Env" {})))
  (run-with-large-stack
   (fn []
     (let [start-time (System/currentTimeMillis)
           declarations (vec declarations)
           quotient-package (when verify? (filterv #(.isQuot ^ConstantInfo %) declarations))
           _ (when (and (seq quotient-package) (not quotient-errors-as-results?))
               (quotient/validate-package! quotient-package))
           groups (when verify? (non-safe/plan declarations))
           results (object-array (count declarations))]
       (loop [index 0 current initial-env ok-count 0 err-count 0]
         (if (< index (count declarations))
           (let [^ConstantInfo ci (nth declarations index)
                 group (when (and verify? (non-safe/non-safe-definition? ci)) (get groups (.name ci)))
                 [next-env indices rows next-index]
                 (cond
                   (.isInduct ci)
                   (let [{:keys [members]} (collect-inductive-bundle (subvec declarations index))
                         [next-env rows] (replay-inductive-bundle current members)
                         next-index (+ index (count members))]
                     [next-env (range index next-index) rows next-index])

                   group
                   (if (= index (:last-index group))
                     (let [[next-env rows] (replay-non-safe-group current group)]
                       [next-env (:indices group) rows (inc index)])
                     [current [] [] (inc index)])

                   :else
                   (let [[next-env row] (if (and verify? (.isQuot ci))
                                          (if (or quotient-package-seen? (.isQuotEnabled initial-env))
                                            [current {:status :error :name (str (.name ci)) :tag :quot
                                                      :error "duplicate quotient primitive after an earlier quotient package"}]
                                            (replay-quotient-package current quotient-package ci))
                                          (replay-one current ci verify?))]
                     [next-env [index] [row] (inc index)]))
                 ok+ (count (filter #(= :ok (:status %)) rows))
                 err+ (- (count rows) ok+)]
             (doseq [[i row] (map vector indices rows)]
               (aset results i row)
               (when verbose?
                 (if (= :ok (:status row)) (print ".")
                     (do (println) (println "ERROR:" (:name row) "-" (:error row))))))
             (when (and stop-on-error? (pos? err+))
               (throw (ex-info "Replay stopped on error"
                               {:result (first (filter #(= :error (:status %)) rows))
                                :env current :results (into [] (keep identity) results)})))
             (recur next-index next-env (+ ok-count ok+) (+ err-count err+)))
           (do
             (when (some nil? results)
               (throw (ex-info "Replay failed to account for every input declaration" {})))
             (when verbose? (println))
             {:env current :results (vec results)
              :stats {:ok ok-count :errors err-count :total (+ ok-count err-count)
                      :elapsed-ms (- (System/currentTimeMillis) start-time)}})))))))

(defn replay-from-env
  "Replay declarations against a checked Env. Non-safe definitions are admitted
   by body-reference SCC at its last input member; .all is never group authority.
   Results retain input order. All group headers precede recursive body checking.
   External dependencies must respect native exporter DFS order. Options match
   replay; TRUST false skips non-safe grouping and retains unchecked admission."
  [initial-env declarations & options]
  (apply replay-from-env* initial-env declarations options))

(defn replay
  "Replay declarations from an empty Env. See replay-from-env for admission
   ordering, complete quotient packages, non-safe SCCs, and explicit TRUST mode."
  [declarations & options]
  (apply replay-from-env (env/empty-env) declarations options))

(defn replay-file
  "Parse an NDJSON file and replay all declarations."
  [path & {:as opts}]
  (println "Parsing" path "...")
  (parser/with-parser-state
    (parser/parse-ndjson-file path)
    (fn [st]
      (let [decls (:decls st)
            meta (:meta st)
            _ (println "Parsed:" (count decls) "declarations,"
                       (.size ^java.util.ArrayList (:names st)) "names,"
                       (.size ^ExprStore (:exprs st)) "expressions")
            _ (println "Replaying declarations...")
            result (replay decls opts)]
        (println "Done:" (:stats result))
        (assoc result :meta meta)))))

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

(defn- process-stream-decl-ordinary
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

(defn- flush-stream-quotients
  "Admit all buffered primitives atomically, then replay the buffered ordinary
   declarations in original order. Eq must have been admitted before the first
   primitive, matching native add_quot. No adjacency assumption is made."
  [state]
  (if-let [buffer (:pending-quotient-decls state)]
    (let [package (filterv #(.isQuot ^ConstantInfo %) buffer)
          base (assoc (dissoc state :pending-quotient-decls :pending-quotient-count) :quotient-package-seen? true)
          [next-env admission] (replay-quotient-package (:env base) package (first package))
          base (assoc base :env next-env)]
      (reduce (fn [st ^ConstantInfo ci]
                (if (.isQuot ci)
                  (record-stream-result st (assoc admission :name (str (.name ci))))
                  (process-stream-decl-ordinary st ci)))
              base buffer))
    state))

(defn- process-stream-decl
  [state ^ConstantInfo ci]
  (cond
    (:deferred-non-safe-tail state)
    (update state :deferred-non-safe-tail conj ci)

    (non-safe/non-safe-definition? ci)
    (let [state (flush-stream-bundle state)
          tail (conj (or (:pending-quotient-decls state) []) ci)]
      (-> state
          (dissoc :pending-quotient-decls :pending-quotient-count :last-result)
          (assoc :deferred-non-safe-tail tail)))

    (:pending-quotient-decls state)
    (let [state (cond-> (update state :pending-quotient-decls conj ci)
                  (.isQuot ci) (update :pending-quotient-count inc))]
      (if (= 4 (:pending-quotient-count state)) (flush-stream-quotients state) state))

    (.isQuot ci)
    (if (:quotient-package-seen? state)
      (record-stream-result state {:status :error :name (str (.name ci)) :tag :quot
                                   :error "duplicate quotient package primitive after initialization"})
      (assoc (flush-stream-bundle state) :pending-quotient-decls [ci] :pending-quotient-count 1))

    :else (process-stream-decl-ordinary state ci)))

(defn- flush-stream-tail
  [state]
  (if-let [tail (:deferred-non-safe-tail state)]
    (let [result (replay-from-env* (:env state) tail :quotient-errors-as-results? true
                                   :quotient-package-seen? (:quotient-package-seen? state))]
      (-> state
          (dissoc :deferred-non-safe-tail)
          (assoc :env (:env result))
          (record-stream-results (:results result))))
    (flush-stream-bundle (flush-stream-quotients state))))

(defn replay-file-streaming
  "Parse and replay declarations in streaming mode.
   Runs on a thread with a 64MB stack to handle deep recursion. Quotient
   initialization buffers from its first primitive through the fourth (including
   interleaved declarations); a truncated package is rejected at EOF. A malformed
   input with a missing primitive may therefore retain the remaining stream.
   From the first non-safe DEF, retain the remaining suffix until EOF and replay
   it through the same SCC engine as vector replay. Memory is proportional to
   that suffix; files containing only safe definitions remain streaming."
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
                           nil nil))
                       state')))]
       (let [st (flush-stream-tail (:final-state result))
             elapsed (- (System/currentTimeMillis) start-time)]
         (println "Done: ok=" (:ok st) "errors=" (:errors st) "elapsed=" elapsed "ms")
         (when (seq (:error-names st))
           (println "Failed:" (count (:error-names st)) "declarations"))
         {:env (:env st)
          :stats {:ok (:ok st) :errors (:errors st)
                  :total (+ (:ok st) (:errors st))
                  :elapsed-ms elapsed}
          :error-names (:error-names st)
          :incomplete-mutual []
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
