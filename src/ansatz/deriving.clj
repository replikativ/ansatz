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
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.instance :as instance]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta.app-builder :as app-builder]
            [ansatz.meta.constructions.util :as u]
            [ansatz.meta.constructions.ctor-elim :as ctor-elim]
            [clojure.string :as str]))

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
  (:id (red/find-from-user-name? (:lctx goal) fvar-name)))

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
  "Close a goal of form Decidable (Eq T ctor_i ctor_j) where i≠j with isFalse, intro h and
   AppBuilder.mkNoConfusion (ansatz.meta.app-builder), which handles parameters."
  [ps]
  (let [ps (basic/apply-tac ps (e/const' decidable-isFalse-name []))
        ps (basic/intro ps "h")
        goal (proof/current-goal ps)
        h-fvar-id (find-fvar-by-name goal "h")
        h-decl (get (:lctx goal) h-fvar-id)
        [_ [t ci cj]] (e/get-app-fn-args (:type h-decl))
        ctx (atom (tc/attach-lctx (tc/mk-tc-state (:env ps)) (:lctx goal)))
        _ (swap! (:next-id @ctx) max (:next-id ps 1))
        [th targs] (e/get-app-fn-args t)
        tn (e/const-name th)
        has? #(some? (env/lookup (:env ps) %))
        term (if (and (empty? targs) (not (and (has? (name/from-string "noConfusion_of_Nat")) (has? (name/mk-str tn "ctorIdx"))))
                      (has? (name/mk-str tn "noConfusion")))
               ;; a reduced environment without the tag: the type's own noConfusion, as before
               (e/app* (e/const' (name/mk-str tn "noConfusion") (into [lvl/zero] (e/const-levels th)))
                       (e/const' false-name []) ci cj (e/fvar h-fvar-id))
               (app-builder/mk-no-confusion ctx (e/const' false-name []) t ci cj (e/fvar h-fvar-id)))]
    (basic/exact (assoc ps :env (:env @ctx)) term)))

(defn- try-close-goal
  "Try to close the current goal — first as diagonal (isTrue+rfl),
   falling back to off-diagonal (isFalse+noConfusion)."
  [ps]
  (basic/first-tac
   ps
   (fn [ps'] (close-diagonal-goal ps'))
   (fn [ps'] (close-off-diagonal-goal ps'))))

(defn- instance-name
  "Lean's instance naming (Elab/DeclNameGen mkBaseNameWithSuffix, Util mkUnusedBaseName): in the
   type's namespace, `inst` + class + the type's last component with its first letter
   capitalized (`N.color` → `N.instDecidableEqColor`); an occupied name gets `_1`, `_2`, …"
  [env type-name-str cls]
  (let [n (name/from-string type-name-str)
        last-s (.str ^ansatz.kernel.Name n)
        base (str "inst" cls (str/upper-case (subs last-s 0 1)) (subs last-s 1))
        cand #(name/mk-str (.prefix ^ansatz.kernel.Name n) (if (zero? %) base (str base "_" %)))]
    (first (remove #(env/lookup env %) (map cand (range))))))

(defn- mk-enum-of-nat
  "DecEq.lean mkEnumOfNat / mkEnumOfNatThm for an enumeration type: `T.ofNat : Nat → T`
   (a balanced `bif n.ble i` lookup tree, Meta/NatTable.lean) and
   `T.ofNat_ctorIdx : ∀ x, T.ofNat x.ctorIdx = x` (by cases)."
  [env type-name-str]
  (let [tn (name/from-string type-name-str)
        ^ansatz.kernel.ConstantInfo info (env/lookup! env tn)
        lps (vec (.levelParams info)) us (mapv lvl/param lps)
        t (e/const' tn us)
        ctx (u/context env)
        level (u/get-level ctx t)
        nat (e/const' (name/from-string "Nat") [])
        ctors (mapv #(e/const' % us) (.ctors info))
        n (u/local-decl ctx "n" nat)
        ;; Meta/NatTable.lean mkNatLookupTable: a balanced `bif n.ble mid` tree
        body (ctor-elim/mk-nat-lookup-table ctx n t ctors)
        of-nat (name/mk-str tn "ofNat")
        env (env/check-constant env (env/mk-def of-nat lps (e/arrow nat t) (u/mk-lambda-fvars ctx [n] body)
                                                :hints :abbrev))
        x-ty t
        thm-type (e/forall' "x" x-ty
                            (e/app* (e/const' eq-name [level]) t
                                    (e/app (e/const' of-nat us)
                                           (e/app (e/const' (name/mk-str tn "ctorIdx") us) (e/bvar 0)))
                                    (e/bvar 0))
                            :default)
        [ps _] (proof/start-proof env thm-type)
        ps (basic/intros ps ["x"])
        ps (basic/cases ps (find-fvar-by-name (proof/current-goal ps) "x"))
        ps (basic/all-goals ps basic/rfl)]
    (env/check-constant env (env/mk-thm (name/mk-str tn "ofNat_ctorIdx") lps thm-type (extract/verify ps)))))

(defn derive-decidable-eq!
  "Derive a DecidableEq instance for a fieldless inductive type (Lean Elab/Deriving/DecEq.lean):
   `<ns>.instDecidableEq<T> : ∀ {params} [DecidableEq α]…, DecidableEq (T params)`, a type
   parameter getting a `[DecidableEq α]` binder as in Lean, at the type's universe parameters;
   for an enumeration also `T.ofNat` and `T.ofNat_ctorIdx`. Registered as an instance.

   Args:
     env           - kernel environment (must already contain the inductive)
     type-name-str - e.g. \"N.Color\"
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
        ^ansatz.kernel.ConstantInfo ind-ci (env/lookup! env type-nm)
        _ (when (pos? (.numIndices ind-ci))
            (throw (ex-info (str "derive DecidableEq: " type-name-str " is an indexed family — not supported")
                            {:type type-name-str})))
        ind-levels (vec (.levelParams ind-ci))
        ctx (u/context env)
        [params _] (u/forall-telescope ctx (.type ind-ci) (.numParams ind-ci))
        _ (u/implicit! ctx params)
        ;; Lean mkInstImplicitBinders: `[DecidableEq α]` for each type parameter
        insts (vec (keep (fn [p]
                           (when (e/sort? (u/whnf ctx (u/infer-type ctx p)))
                             (u/local-decl ctx "inst"
                                           (e/app (e/const' decidable-eq-name [(u/get-level ctx p)]) p)
                                           :inst-implicit)))
                         params))
        type-const (u/app (e/const' type-nm (mapv lvl/param ind-levels)) params)
        eq-level (u/get-level ctx type-const)
        a (u/local-decl ctx "a" type-const)
        b (u/local-decl ctx "b" type-const)
        goal-type (u/mk-forall-fvars
                   ctx (into params (concat insts [a b]))
                   (e/app (e/const' decidable-name [])
                          (e/app* (e/const' eq-name [eq-level]) type-const a b)))
        [ps _root-id] (proof/start-proof env goal-type)
        ps (basic/intros ps (into (mapv #(str (:name (u/decl ctx %))) (concat params insts)) ["a" "b"]))
        goal (proof/current-goal ps)
        ps (basic/cases ps (find-fvar-by-name goal "a"))
        ps (basic/all-goals ps (fn [ps']
                                 (basic/cases ps' (find-fvar-by-name (proof/current-goal ps') "b"))))
        ps (basic/all-goals ps try-close-goal)]
    (when-not (proof/solved? ps)
      (throw (ex-info (str "derive DecidableEq: proof incomplete for " type-name-str
                           "\n" (proof/format-goals ps))
                      {:type type-name-str})))
    (let [term (extract/verify ps)
          inst-name (instance-name (:env ps) type-name-str "DecidableEq")
          ;; Elab/Deriving/DecEq.lean:mkDecEqInstance uses the class application,
          ;; so the registry indexes this dictionary under DecidableEq.
          inst-type (u/mk-forall-fvars ctx (into params insts)
                                       (e/app (e/const' decidable-eq-name [eq-level]) type-const))
          ci (env/mk-def inst-name ind-levels inst-type term :hints :abbrev)
          env (-> (env/check-constant (:env ps) ci)
                  (instance/add-instance inst-name))]
      (println "✓ deriving DecidableEq" type-name-str)
      ;; Lean isEnumType (an empty type is not one); a singleton's ofNat needs no lookup table
      (if (and (u/is-enum-type? env ind-ci)
               (env/lookup env (name/mk-str type-nm "ctorIdx"))
               (or (= 1 (count (.ctors ind-ci)))
                   (and (env/lookup env (name/from-string "cond")) (env/lookup env (name/from-string "Nat.ble")))))
        (mk-enum-of-nat env type-name-str)
        env))))

;; ============================================================
;; Register built-in handlers
;; ============================================================

(register-handler! 'DecidableEq derive-decidable-eq!)
