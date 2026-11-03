;; Lean checkout 55f80e10a3: Elab/SyntheticMVars.lean reportStuckSyntheticMVar,
;; Meta/SynthInstance.lean throwFailedToSynthesize, and
;; Elab/Term/TermElabM.lean MVarErrorInfo.logError.
(ns ansatz.surface.diagnostics
  (:require [clojure.string :as str]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.meta :as meta]
            [ansatz.tactic.instance-index :as instance-index]))

(defn mvar-diagnostic
  "Describe an unresolved metavariable without changing synthesis or assignments.
   Returns :message/:type-str strings, :type Expr, :mvar-id integer,
   :mvar-kind keyword, :class Name (nil for ordinary holes), and :problem:
   :failed-instance, :stuck-instance, :implicit-argument, or :placeholder.
   :synthesis-failure? selects Meta.synthInstance's error, including stuck inputs,
   rather than Elab.reportStuckSyntheticMVar's pending-obligation diagnostic."
  ([environment mctx id] (mvar-diagnostic environment mctx id {}))
  ([environment mctx id {:keys [synthesis-failure?]}]
   (let [decl (meta/expr-decl mctx id)
         type (meta/zonk-expr mctx (:type decl))
         ;; Keep the expression printer's surface syntax, resolving local names in
         ;; the saved context rather than exposing free-variable implementation ids.
         type-str (str/replace (e/->string type) #"\?fv[0-9]+"
                               (fn [s]
                                 (let [local (get (:lctx decl) (Long/parseLong (subs s 3)))]
                                   (str (or (:name local) s)))))
         instance? (:inst-implicit? decl)
         [head args] (e/get-app-fn-args type)
         info (when (and instance? (e/const? head))
                (instance-index/class-info environment (e/const-name head)))
         outputs (into (:out-params info #{}) (:semi-out-params info))
         ;; SyntheticMVars.explainStuckTypeclassProblem ignores both kinds of
         ;; output arguments; synthInstance must determine these, not its caller.
         stuck? (and instance? (not synthesis-failure?)
                     (some (fn [[i arg]]
                             (and (not (contains? outputs i))
                                  (seq (meta/collect-expr-mvars arg))))
                           (map-indexed vector args)))
         implicit? (and (= :natural (:kind decl)) (:user-name decl))
         message (cond
                   stuck? "typeclass instance problem is stuck, it is often due to metavariables"
                   instance? "failed to synthesize"
                   implicit? (str "don't know how to synthesize implicit argument `"
                                  (name/->string (:user-name decl)) "`")
                   :else "don't know how to synthesize placeholder")]
     {:message (str message
                    (if instance? "\n  " "\ncontext:\n⊢ ") type-str
                    (when (and instance? (not stuck?))
                      "\n\nHint: Additional diagnostic information may be available using the `set_option diagnostics true` command."))
      :mvar-id id :mvar-kind (:kind decl) :type type :type-str type-str
      :problem (cond stuck? :stuck-instance instance? :failed-instance
                     implicit? :implicit-argument :else :placeholder)
      :class (when (and instance? (e/const? head)) (e/const-name head))})))

(def ^:private range-node-budget 10000)

(defn- ref-range
  [{:keys [forms ranges] :as ref}]
  (if (:bsize ref)
    ref
    (when-let [table (when ranges @ranges)]
      (loop [forms forms remaining range-node-budget]
        (when (and (seq forms) (pos? remaining))
          (or (.get ^java.util.IdentityHashMap table @(first forms))
              (recur (next forms) (dec remaining))))))))

(defn first-instance-diagnostic
  "Failed synthesis precedes pending stuck problems. For stuck problems follow
   SyntheticMVars.reportStuckSyntheticMVars: smallest range, earliest start;
   equal ranges retain pendingMVars order (registerSyntheticMVar conses).
   Optional ranges are computed only here, when an error is being reported."
  [environment mctx ids]
  (let [ids (sort-by #(get-in mctx [:decls % :index])
                     (filter #(and (get-in mctx [:decls % :inst-implicit?])
                                   (not (meta/expr-assigned-or-delayed? mctx %))) ids))
        problems (mapv #(mvar-diagnostic environment mctx %) ids)
        priority (fn [problem]
                   (let [decl (meta/expr-decl mctx (:mvar-id problem))
                         ref (ref-range (:ref decl))]
                     (if ref
                       [0 (:bsize ref) (:start ref) (- (:index decl))]
                       [1 0 0 (:index decl)])))]
    (or (first (filter #(= :failed-instance (:problem %)) problems))
        (first (sort-by priority problems)))))

(defn- syntax-children?
  [x]
  ;; Inspect only concrete reader collections. In particular, do not realize
  ;; lazy extension payloads or invoke methods of user-defined collections.
  (contains? #{clojure.lang.PersistentList clojure.lang.PersistentList$EmptyList
               clojure.lang.PersistentVector}
             (class x)))

(defn- token-size
  [x]
  ;; No generic printing of extension payloads. Unsupported tokens make range
  ;; information unavailable; the original elaboration error still gets reported.
  (when (or (nil? x) (symbol? x) (keyword? x) (boolean? x)
            (contains? #{Long Integer Short Byte Double Float} (class x)))
    (when (or (not (or (symbol? x) (keyword? x)))
              (<= (+ (count (name x)) (count (namespace x)) 2) range-node-budget))
      (let [s (if (nil? x) "nil" (str x))]
        (alength (.getBytes s java.nio.charset.StandardCharsets/UTF_8))))))

(defn syntax-ranges
  "Optional canonical surface ranges for error reporting only. An iterative
   walk bounds work to range-node-budget nodes; unsupported or larger syntax
   returns nil, preserving the reporting fallback instead of failing a program.
   No arbitrary payload is printed or realized. Generated syntax inherits the
   nearest represented enclosing form's reference."
  [form]
  (let [ranges (java.util.IdentityHashMap.)]
    (loop [todo [[:visit form false]] offset 0 remaining range-node-budget]
      (if-let [[op x extra] (peek todo)]
        (let [todo (pop todo)]
          (case op
            :close
            (let [end (inc offset)]
              (.put ranges x {:start extra :bsize (- end extra)})
              (recur todo end remaining))

            :items
            ;; Consume one known reader collection cell at a time. Even an
            ;; unusual list tail must not start an unbounded/lazy sequence walk.
            (cond
              (or (nil? x) (= (class x) clojure.lang.PersistentList$EmptyList))
              (recur todo offset remaining)

              (= (class x) clojure.lang.PersistentList)
              (when (pos? remaining)
                (recur (conj todo [:items (.next ^clojure.lang.ISeq x) (inc extra)]
                             [:visit (.first ^clojure.lang.ISeq x) (pos? extra)])
                       offset remaining))

              (= (class x) clojure.lang.PersistentVector)
              (if (= extra (count x))
                (recur todo offset remaining)
                (when (pos? remaining)
                  (recur (conj todo [:items x (inc extra)] [:visit (nth x extra) (pos? extra)])
                         offset remaining))))

            :visit
            (when (pos? remaining)
              (let [start (+ offset (if extra 1 0))]
                (if (syntax-children? x)
                  (recur (conj todo [:close x start] [:items x 0])
                         (inc start) (dec remaining))
                  (when-let [size (token-size x)]
                    (.put ranges x {:start start :bsize size})
                    (recur todo (+ start size) (dec remaining))))))))
        ranges))))
