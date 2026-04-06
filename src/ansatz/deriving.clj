;; Extensible deriving framework for auto-generating typeclass instances.
;;
;; Lean 4's `deriving` mechanism auto-generates instances (DecidableEq, BEq,
;; Repr, Inhabited, etc.) for inductive types. This module provides the same
;; capability for Ansatz.
;;
;; Architecture:
;;   - A registry maps class names (symbols) to handler functions
;;   - Each handler: (env, type-name-str, ctor-specs) → env'
;;   - `a/inductive` calls `run-deriving!` after defining the type
;;   - New handlers can be registered via `register-handler!`

(ns ansatz.deriving
  "Extensible deriving framework. Register handlers for typeclass auto-derivation.

   Built-in handlers:
   - DecidableEq: decidable equality for simple enums (zero-field constructors)

   Usage:
     (a/inductive Color [] (red) (green) (blue) :deriving [DecidableEq])

   Extension:
     (deriving/register-handler! 'MyClass my-handler-fn)"
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]))

;; ============================================================
;; Handler registry
;; ============================================================

(defonce ^:private handler-registry (atom {}))

(defn register-handler!
  "Register a deriving handler for a typeclass.
   handler-fn: (fn [env type-name-str ctor-specs] env')
   where ctor-specs is the same format passed to define-inductive:
   [[\"ctor1\" []] [\"ctor2\" []] ...] for enums."
  [class-sym handler-fn]
  (swap! handler-registry assoc class-sym handler-fn)
  nil)

(defn run-deriving!
  "Run all requested deriving handlers for a type.
   classes: sequence of symbols, e.g. [DecidableEq BEq]
   Returns the updated env."
  [env type-name-str ctor-specs classes]
  (reduce (fn [env class-sym]
            (if-let [handler (get @handler-registry class-sym)]
              (handler env type-name-str ctor-specs)
              (throw (ex-info (str "No deriving handler registered for: " class-sym)
                              {:class class-sym
                               :available (keys @handler-registry)}))))
          env
          classes))

;; ============================================================
;; DecidableEq handler — for simple enums (zero-field constructors)
;; ============================================================
;;
;; For (a/inductive Color [] (red) (green) (blue)):
;;
;; Generates instDecidableEqColor : DecidableEq Color
;; which is ∀ (a b : Color), Decidable (Eq Color a b)
;;
;; Proof strategy:
;;   1. intro a, intro b
;;   2. cases a → n goals (one per constructor)
;;   3. for each goal: cases b → n sub-goals
;;   4. diagonal (same ctor): apply Decidable.isTrue, then rfl
;;   5. off-diagonal (different ctor): apply Decidable.isFalse, intro h,
;;      then apply Type.noConfusion to h
;;
;; The result is registered as a definition with :hints :abbrev so
;; the decide tactic can evaluate it.

(def ^:private decidable-eq-name (name/from-string "DecidableEq"))
(def ^:private decidable-name (name/from-string "Decidable"))
(def ^:private eq-name (name/from-string "Eq"))
(def ^:private decidable-isTrue-name (name/from-string "Decidable.isTrue"))
(def ^:private decidable-isFalse-name (name/from-string "Decidable.isFalse"))

(defn- find-fvar-by-name
  "Find the most recently allocated fvar with the given name in goal's lctx."
  [goal fvar-name]
  (reduce (fn [best [id d]]
            (if (and (= fvar-name (:name d))
                     (or (nil? best) (> (long id) (long best))))
              id best))
          nil
          (:lctx goal)))

(defn- close-diagonal-goal
  "Close a goal of form Decidable (Eq T ctor ctor) with isTrue + rfl."
  [ps]
  (let [;; apply Decidable.isTrue — no level params
        ps (basic/apply-tac ps (e/const' decidable-isTrue-name []))
        ;; rfl closes the Eq goal
        ps (basic/rfl ps)]
    ps))

(def ^:private false-name (name/from-string "False"))

(defn- close-off-diagonal-goal
  "Close a goal of form Decidable (Eq T ctor_i ctor_j) where i≠j
   with isFalse + intro h + noConfusion with explicit args."
  [ps type-name-str]
  (let [;; apply Decidable.isFalse — no level params
        ;; creates subgoal: Not (Eq T ctor_i ctor_j)
        ;; which is (Eq T ctor_i ctor_j) → False
        ps (basic/apply-tac ps (e/const' decidable-isFalse-name []))
        ;; intro h — introduces the equality hypothesis
        ps (basic/intro ps "h")
        ;; Now goal is False with h : Eq T ctor_i ctor_j in context
        ;; Extract ctor_i, ctor_j from h's type: Eq.{u} T ctor_i ctor_j
        goal (proof/current-goal ps)
        h-fvar-id (find-fvar-by-name goal "h")
        h-decl (get (:lctx goal) h-fvar-id)
        ;; h-type is (Eq.{u} T ctor_i ctor_j)
        [_eq-head eq-args] (e/get-app-fn-args (:type h-decl))
        ;; eq-args: [T, ctor_i, ctor_j]
        ctor-i (nth eq-args 1)
        ctor-j (nth eq-args 2)
        nc-name (name/from-string (str type-name-str ".noConfusion"))
        ;; noConfusion.{v} : {P : Sort v} → {v1 v2 : T} → v1 = v2 → noConfusionType P v1 v2
        ;; P = False : Prop = Sort 0, so v = 0
        ;; Supply all args explicitly: False, ctor_i, ctor_j, h
        nc-term (e/app* (e/const' nc-name [lvl/zero])
                        (e/const' false-name [])
                        ctor-i ctor-j
                        (e/fvar h-fvar-id))]
    (basic/apply-tac ps nc-term)))

(defn- try-close-goal
  "Try to close the current goal — first as diagonal (isTrue+rfl),
   falling back to off-diagonal (isFalse+noConfusion)."
  [ps type-name-str]
  (basic/first-tac
   ps
   (fn [ps'] (close-diagonal-goal ps'))
   (fn [ps'] (close-off-diagonal-goal ps' type-name-str))))

(defn derive-decidable-eq!
  "Derive a DecidableEq instance for a simple enum type.
   Adds instDecidableEq{Type} to the environment.

   Args:
     env           - kernel environment (must already contain the inductive)
     type-name-str - e.g. \"Color\"
     ctor-specs    - e.g. [[\"red\" []] [\"green\" []] [\"blue\" []]]

   Returns: updated env with the instance added."
  [env type-name-str ctor-specs]
  ;; Validate: all constructors must have zero fields (simple enum)
  (doseq [[ctor-name fields] ctor-specs]
    (when (seq fields)
      (throw (ex-info (str "derive DecidableEq: constructor " ctor-name
                           " has fields — only zero-field enums are supported")
                      {:constructor ctor-name :fields fields}))))

  (let [type-nm (name/from-string type-name-str)
        ;; Look up the inductive to determine its universe level
        ^ansatz.kernel.ConstantInfo ind-ci (env/lookup! env type-nm)
        ind-levels (vec (.levelParams ind-ci))
        type-const (e/const' type-nm (mapv lvl/param ind-levels))

        ;; Determine the universe level of the type.
        ;; For simple enums with no level params: Type = Sort 1, so eq-level = succ zero
        ;; For polymorphic types: need the actual level
        eq-level (if (empty? ind-levels)
                   (lvl/succ lvl/zero)  ;; simple enum: Type = Sort(succ 0)
                   (lvl/succ (lvl/param (first ind-levels))))

        ;; Build goal type: ∀ (a b : T), Decidable (Eq T a b)
        ;; Eq.{u} : Sort u → Sort u → Prop
        ;; Decidable : Prop → Type
        goal-type (e/forall'
                   "a" type-const
                   (e/forall'
                    "b" type-const
                    (e/app (e/const' decidable-name [])
                           (e/app* (e/const' eq-name [eq-level])
                                   type-const
                                   (e/bvar 1)   ;; a
                                   (e/bvar 0))) ;; b
                    :default)
                   :default)

        ;; Start proof
        [ps _root-id] (proof/start-proof env goal-type)

        ;; intro a, intro b
        ps (basic/intros ps ["a" "b"])

        ;; cases a → n goals
        goal (proof/current-goal ps)
        a-fvar-id (find-fvar-by-name goal "a")
        ps (basic/cases ps a-fvar-id)

        ;; for each goal: cases b → n² total goals
        ps (basic/all-goals ps (fn [ps']
                                 (let [g (proof/current-goal ps')
                                       b-id (find-fvar-by-name g "b")]
                                   (basic/cases ps' b-id))))

        ;; close all n² goals
        ps (basic/all-goals ps (fn [ps']
                                 (try-close-goal ps' type-name-str)))]

    ;; Verify proof is complete
    (when-not (proof/solved? ps)
      (throw (ex-info (str "derive DecidableEq: proof incomplete for " type-name-str
                           "\n" (proof/format-goals ps))
                      {:type type-name-str})))

    ;; Extract and kernel-verify the proof term
    (let [term (extract/verify ps)
          ;; Register as instDecidableEq{Type} with abbrev hints
          ;; so decide can evaluate it
          inst-name (name/from-string (str "instDecidableEq" type-name-str))
          ci (env/mk-def inst-name [] goal-type term :hints :abbrev)]
      (println "✓ deriving DecidableEq" type-name-str)
      (env/add-constant env ci))))

;; ============================================================
;; Register built-in handlers
;; ============================================================

(register-handler! 'DecidableEq derive-decidable-eq!)
