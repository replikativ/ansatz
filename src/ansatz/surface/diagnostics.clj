;; Lean checkout 55f80e10a3: Elab/SyntheticMVars.lean reportStuckSyntheticMVar,
;; Meta/SynthInstance.lean throwFailedToSynthesize, and
;; Elab/Term/TermElabM.lean MVarErrorInfo.logError.
(ns ansatz.surface.diagnostics
  (:require [clojure.string :as str]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.meta :as meta]))

(defn mvar-diagnostic
  "Describe an unresolved metavariable without changing synthesis or assignments."
  [mctx id]
  (let [decl (meta/expr-decl mctx id)
        type (meta/zonk-expr mctx (:type decl))
        ;; Keep the expression printer's surface syntax, resolving local names in
        ;; the saved context rather than exposing free-variable implementation ids.
        type-str (str/replace (e/->string type) #"\?fv[0-9]+"
                              (fn [s]
                                (let [local (get (:lctx decl) (Long/parseLong (subs s 3)))]
                                  (str (or (:name local) s)))))
        instance? (:inst-implicit? decl)
        stuck? (and instance? (seq (meta/collect-expr-mvars type)))
        implicit? (and (= :natural (:kind decl)) (:user-name decl))
        message (cond
                  stuck? "typeclass instance problem is stuck, it is often due to metavariables"
                  instance? "failed to synthesize"
                  implicit? (str "don't know how to synthesize implicit argument `"
                                 (name/->string (:user-name decl)) "`")
                  :else "don't know how to synthesize placeholder")
        [head _] (e/get-app-fn-args type)]
    {:message (str message
                   (if instance? "\n  " "\ncontext:\n⊢ ") type-str
                   (when (and instance? (not stuck?))
                     "\n\nHint: Additional diagnostic information may be available using the `set_option diagnostics true` command."))
     :mvar-id id :mvar-kind (:kind decl) :type type :type-str type-str
     :problem (cond stuck? :stuck-instance instance? :failed-instance
                    implicit? :implicit-argument :else :placeholder)
     :class (when (and instance? (e/const? head)) (e/const-name head))}))

(defn first-instance-diagnostic
  "Lean synthesizeSyntheticMVars reports failed synthesis before stuck problems.
   Surface forms have no source ranges; ties retain metavariable creation order."
  [mctx ids]
  (let [problems (mapv #(mvar-diagnostic mctx %)
                       (sort-by #(get-in mctx [:decls % :index])
                                (filter #(and (get-in mctx [:decls % :inst-implicit?])
                                              (not (meta/expr-assigned-or-delayed? mctx %)))
                                        ids)))]
    (or (first (filter #(= :failed-instance (:problem %)) problems))
        (first problems))))
