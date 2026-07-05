;; Tactic layer — proof term extraction and verification.

(ns ansatz.tactic.extract
  "Extract complete proof terms from solved proof states and verify them."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.meta :as meta]
            [ansatz.tactic.proof :as proof])
  (:import [ansatz.kernel TypeChecker]))

(defn replace-mvar
  "Replace all occurrences of (mvar mvar-id) with replacement in expr.
   Unlike abstract1+instantiate1, this works correctly even when the mvar
   is inside lambda bodies (no bvar shifting needed since mvars are opaque)."
  [expr mvar-id replacement]
  (letfn [(go [e]
              (cond
                (and (e/mvar? e) (= (e/mvar-id e) mvar-id)) replacement
                (e/app? e) (let [f (go (e/app-fn e)) a (go (e/app-arg e))]
                             (if (and (identical? f (e/app-fn e)) (identical? a (e/app-arg e))) e
                                 (e/app f a)))
                (e/lam? e) (let [t (go (e/lam-type e)) b (go (e/lam-body e))]
                             (if (and (identical? t (e/lam-type e)) (identical? b (e/lam-body e))) e
                                 (e/lam (e/lam-name e) t b (e/lam-info e))))
                (e/forall? e) (let [t (go (e/forall-type e)) b (go (e/forall-body e))]
                                (if (and (identical? t (e/forall-type e)) (identical? b (e/forall-body e))) e
                                    (e/forall' (e/forall-name e) t b (e/forall-info e))))
                :else e))]
    (go expr)))

(defn- contains-level-mvar? [l]
  (and l (lvl/has-mvar? l)))

(defn- contains-mvar?
  "True when `expr` contains expression or universe-level metavariables."
  [expr]
  (case (e/tag expr)
    :mvar true
    :sort (contains-level-mvar? (e/sort-level expr))
    :const (boolean (some contains-level-mvar? (e/const-levels expr)))
    :app (or (contains-mvar? (e/app-fn expr))
             (contains-mvar? (e/app-arg expr)))
    :lam (or (contains-mvar? (e/lam-type expr))
             (contains-mvar? (e/lam-body expr)))
    :forall (or (contains-mvar? (e/forall-type expr))
                (contains-mvar? (e/forall-body expr)))
    :let (or (contains-mvar? (e/let-type expr))
             (contains-mvar? (e/let-value expr))
             (contains-mvar? (e/let-body expr)))
    :mdata (contains-mvar? (e/mdata-expr expr))
    :proj (contains-mvar? (e/proj-struct expr))
    false))

(defn extract-meta
  "Extract by zonking the Lean-shaped `:meta-mctx` root mvar. Succeeds only
   when the metacontext assignment graph closes completely."
  [ps]
  (when-not (proof/solved? ps)
    (throw (ex-info "Cannot extract: proof has open goals"
                    {:open-goals (count (:goals ps))})))
  (let [mctx (:meta-mctx ps)
        root (:root-mvar ps)
        term (meta/zonk-expr mctx (e/mvar root))]
    (when-not (meta/closed-expr? mctx term)
      (throw (ex-info "Cannot extract: meta proof contains unassigned metavariables"
                      {:root-mvar root
                       :unassigned-expr-mvars (meta/unassigned-expr-mvars mctx term)
                       :unassigned-level-mvars (meta/unassigned-level-mvars mctx term)})))
    term))

(defn extract
  "Extract the complete proof term by zonking the root metavariable through
   the one metacontext."
  [ps]
  (extract-meta ps))

(defn verify
  "Extract the proof term and verify it AUTHORITATIVELY with the kernel's STRICT
   checker `TypeChecker.check` (= Lean's `check` / infer_type_core(e, false)), which
   re-checks every application argument against the function domain — NOT the lenient
   `TypeChecker.inferType` (infer_type_core(e, true)), which assumes well-typed input
   and silently accepts ill-typed proofs. `.check` is the same strictness that admits
   mathlib declarations (checkConstant wraps it), but it does NOT add to the env, so it
   is safe on PSS/fork environments. Returns the extracted term on success, throws on
   failure."
  [ps]
  (let [term (extract ps)
        env (:env ps)
        root-type (proof/mvar-type ps (:root-mvar ps))]
    (when (e/has-fvar-flag term)
      (throw (ex-info "Extracted term contains free variables" {:term term})))
    (when (contains-mvar? term)
      (throw (ex-info "Extracted term contains metavariables" {:term term})))
    (let [tc (doto (TypeChecker. env) (.setFuel 50000000))
          inferred (.check tc term)]                ; STRICT: re-checks every app arg
      (when-not (.isDefEq tc inferred root-type)
        (throw (ex-info "Extracted term type does not match goal"
                        {:expected root-type :inferred inferred}))))
    term))
