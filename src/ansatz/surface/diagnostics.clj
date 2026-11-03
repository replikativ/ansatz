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

(defn first-instance-diagnostic
  "Failed synthesis precedes pending stuck problems. For stuck problems follow
   SyntheticMVars.reportStuckSyntheticMVars: smallest range, earliest start;
   equal ranges retain pendingMVars order (registerSyntheticMVar conses)."
  [environment mctx ids]
  (let [ids (sort-by #(get-in mctx [:decls % :index])
                     (filter #(and (get-in mctx [:decls % :inst-implicit?])
                                   (not (meta/expr-assigned-or-delayed? mctx %))) ids))
        problems (mapv #(mvar-diagnostic environment mctx %) ids)
        priority (fn [problem]
                   (let [decl (meta/expr-decl mctx (:mvar-id problem))
                         ref (:ref decl)]
                     (if ref
                       [0 (:bsize ref) (:start ref) (- (:index decl))]
                       [1 0 0 (:index decl)])))]
    (or (first (filter #(= :failed-instance (:problem %)) problems))
        (first (sort-by priority problems)))))

(defn syntax-ranges
  "Ranges in the canonical printed surface form, for diagnostic ordering only.
   Preserve source nesting, byte sizes, and left-to-right offsets without
   depending on Clojure reader line metadata (runtime forms often have none).
   Macro-generated syntax inherits its enclosing form's range."
  [form]
  (let [ranges (java.util.IdentityHashMap.)
        ;; Kernel terms spliced by term elaborators have no surface syntax.
        ;; Do not render their recursive Java representation just to order errors.
        byte-size (fn [x] (if (instance? ansatz.kernel.Expr x)
                            0
                            (alength (.getBytes (pr-str x) java.nio.charset.StandardCharsets/UTF_8))))]
    (letfn [(visit [x start]
              (let [end (if (or (seq? x) (vector? x))
                          (let [children (seq x)]
                            (inc (reduce (fn [offset [i child]]
                                           (visit child (+ offset (if (zero? i) 0 1))))
                                         (inc start) (map-indexed vector children))))
                          (+ start (byte-size x)))]
                (.put ranges x {:start start :bsize (- end start)})
                end))]
      (visit form 0)
      ranges)))
