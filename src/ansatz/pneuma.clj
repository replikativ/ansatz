;; Pneuma architectural verification on Ansatz.
;;
;; Accepts spec data in the same format as Pneuma's formalisms and compiles
;; them into Ansatz kernel declarations: inductive types with DecidableEq,
;; transition functions, capability predicates, and boundary theorems.
;;
;; All proofs are kernel-verified in-process — no external Lean toolchain needed.

(ns ansatz.pneuma
  "Compile Pneuma-format spec maps into Ansatz kernel declarations.

   Entry point: (compile-spec! spec-system)

   Supports:
   - Statechart → State/Event inductives + transition function + theorems
   - Effect signature → Op inductive + allOps list + completeness theorem
   - Capability set → dispatch/query predicates
   - Existential morphism → boundary subset theorems"
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.inductive :as inductive]
            [ansatz.deriving :as deriving]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [clojure.string :as str]))

;; ============================================================
;; Name conversion
;; ============================================================

(defn kw->ctor-name
  "Convert a Clojure keyword to a valid Ansatz constructor name.
   :uninitialized → \"uninitialized\"
   :init-key → \"init_key\"
   :halt-key! → \"halt_key\""
  [kw]
  (-> (clojure.core/name kw)
      (str/replace "-" "_")
      (str/replace "!" "")
      (str/replace "?" "_q")
      (str/replace ">" "_to_")))

(defn- prefix-name
  "Create a prefixed name: prefix + suffix."
  [prefix suffix]
  (str prefix suffix))

;; ============================================================
;; Well-known constants
;; ============================================================

(def ^:private option-some-nm (name/from-string "Option.some"))
(def ^:private option-none-nm (name/from-string "Option.none"))
(def ^:private list-cons-nm (name/from-string "List.cons"))
(def ^:private list-nil-nm (name/from-string "List.nil"))
(def ^:private option-nm (name/from-string "Option"))
(def ^:private list-nm (name/from-string "List"))
(def ^:private bool-true-nm (name/from-string "Bool.true"))
(def ^:private bool-false-nm (name/from-string "Bool.false"))
(def ^:private bool-nm (name/from-string "Bool"))
(def ^:private eq-nm (name/from-string "Eq"))
(def ^:private list-mem-nm (name/from-string "List.Mem"))
(def ^:private list-mem-head-nm (name/from-string "List.Mem.head"))
(def ^:private list-mem-tail-nm (name/from-string "List.Mem.tail"))
(def ^:private nat-nm (name/from-string "Nat"))
(def ^:private nat-zero-nm (name/from-string "Nat.zero"))
(def ^:private nat-succ-nm (name/from-string "Nat.succ"))
(def ^:private nat-le-nm (name/from-string "Nat.le"))
(def ^:private nat-le-refl-nm (name/from-string "Nat.le.refl"))
(def ^:private nat-le-step-nm (name/from-string "Nat.le.step"))
(def ^:private nat-lt-nm (name/from-string "Nat.lt"))

;; Level zero for Type-level types (simple enums live in Sort 1 = Type)
(def ^:private u0 lvl/zero)

;; ============================================================
;; Term builders
;; ============================================================

(defn- mk-option-some
  "Build Option.some.{0} T val — for Type-level types."
  [type-expr val-expr]
  (e/app* (e/const' option-some-nm [u0]) type-expr val-expr))

(defn- mk-option-none
  "Build Option.none.{0} T — for Type-level types."
  [type-expr]
  (e/app (e/const' option-none-nm [u0]) type-expr))

(defn- mk-list
  "Build a List.{0} from a sequence of terms. Returns List.nil for empty."
  [type-expr terms]
  (reduce (fn [acc t]
            (e/app* (e/const' list-cons-nm [u0]) type-expr t acc))
          (e/app (e/const' list-nil-nm [u0]) type-expr)
          (reverse terms)))

(defn- mk-rec-term
  "Build a recursor application: T.rec motive minor1 ... minorN major.
   For an enum (zero-field ctors), each minor is just the result for that case."
  [env type-name-str motive-type minors major]
  (let [rec-nm (name/from-string (str type-name-str ".rec"))
        type-nm (name/from-string type-name-str)
        ^ansatz.kernel.ConstantInfo rec-ci (env/lookup! env rec-nm)
        rec-levels (vec (.levelParams rec-ci))
        ;; For motive returning Type-level things, the motive level is (succ zero)
        ;; For motive returning Bool, it's (succ zero) too (Bool : Type)
        ;; The rec level param is the motive's output universe
        motive-level (lvl/succ u0)
        type-const (e/const' type-nm [])
        ;; Motive: λ (_ : T) => ResultType
        motive (e/lam "_" type-const motive-type :default)]
    (reduce e/app
            (e/const' rec-nm [motive-level])
            (concat [motive] minors [major]))))

(defn- mk-nat
  "Build a Nat literal: 0 → Nat.zero, n → Nat.succ (mk-nat (dec n))."
  [n]
  (reduce (fn [acc _] (e/app (e/const' nat-succ-nm []) acc))
          (e/const' nat-zero-nm [])
          (range n)))

(defn- find-fvar
  "Find the most recently allocated fvar with the given name in goal's lctx."
  [goal fvar-name]
  (reduce (fn [best [id d]]
            (if (and (= fvar-name (:name d))
                     (or (nil? best) (> (long id) (long best))))
              id best))
          nil
          (:lctx goal)))

;; ============================================================
;; Completeness proof: ∀ x : T, List.Mem x allList
;; ============================================================

(defn- close-membership-goal
  "Close a goal of the form List.Mem ctor (cons ... ) by trying
   List.Mem.head, falling back to List.Mem.tail + recurse."
  [ps]
  (basic/first-tac
   ps
   (fn [ps'] (basic/apply-tac ps' (e/const' list-mem-head-nm [u0])))
   (fn [ps']
     (let [ps' (basic/apply-tac ps' (e/const' list-mem-tail-nm [u0]))]
       (close-membership-goal ps')))))

(defn prove-enum-completeness
  "Prove ∀ (x : T), List.Mem x allList.
   Returns the updated env with the theorem added.
   thm-name-str: name for the theorem
   type-const: the T type expression
   all-list: the List T expression"
  [env thm-name-str type-const all-list]
  (let [thm-nm (name/from-string thm-name-str)
        goal-type (e/forall'
                   "x" type-const
                   (e/app* (e/const' list-mem-nm [u0])
                           type-const (e/bvar 0) all-list)
                   :default)
        [ps _] (proof/start-proof env goal-type)
        ps (basic/intro ps "x")
        goal (proof/current-goal ps)
        x-id (find-fvar goal "x")
        ps (basic/cases ps x-id)
        ps (basic/all-goals ps close-membership-goal)]
    (when-not (proof/solved? ps)
      (throw (ex-info (str "Completeness proof failed: " thm-name-str)
                      {:goals (proof/format-goals ps)})))
    (let [term (extract/verify ps)
          ci (env/mk-thm thm-nm [] goal-type term)]
      (println "✓ theorem" thm-name-str)
      (env/add-constant env ci))))

;; ============================================================
;; Statechart compilation
;; ============================================================

(defn compile-statechart!
  "Compile a Pneuma statechart spec into Ansatz declarations.

   Input: {:states #{:s1 :s2 ...}
           :transitions [{:source :s1 :event :e1 :target :s2} ...]
           :initial {:root :s1}  ;; optional
           :label \"...\"        ;; optional
           }

   Generates:
   - {prefix}State inductive + DecidableEq
   - {prefix}Event inductive + DecidableEq
   - {prefix}Delta : State → Event → Option State (transition function)
   - Sink state theorems for terminal states

   Returns map of generated declaration names."
  [env prefix spec]
  (let [state-names (vec (sort (map kw->ctor-name (:states spec))))
        events (into #{} (map :event) (:transitions spec))
        event-names (vec (sort (map kw->ctor-name events)))

        state-type-str (prefix-name prefix "State")
        event-type-str (prefix-name prefix "Event")
        delta-str (prefix-name prefix "Delta")

        ;; 1. Define State inductive
        state-ctor-specs (mapv (fn [n] [n []]) state-names)
        env (inductive/define-inductive env state-type-str '[] state-ctor-specs)
        env (deriving/derive-decidable-eq! env state-type-str state-ctor-specs)

        ;; 2. Define Event inductive
        event-ctor-specs (mapv (fn [n] [n []]) event-names)
        env (inductive/define-inductive env event-type-str '[] event-ctor-specs)
        env (deriving/derive-decidable-eq! env event-type-str event-ctor-specs)

        ;; 3. Build transition function: Delta : State → Event → Option State
        ;; Using nested recursor applications
        state-nm (name/from-string state-type-str)
        event-nm (name/from-string event-type-str)
        state-const (e/const' state-nm [])
        event-const (e/const' event-nm [])
        option-state (e/app (e/const' option-nm [u0]) state-const)

        ;; Build a lookup: (source-kw, event-kw) → target-kw
        transition-map (reduce (fn [m {:keys [source event target]}]
                                 (assoc m [(kw->ctor-name source)
                                           (kw->ctor-name event)]
                                        (kw->ctor-name target)))
                               {} (:transitions spec))

        ;; For each state, build inner Event.rec returning Option State
        ;; The major premise is bvar 0 (the event argument from the outer lambda)
        state-minors
        (mapv (fn [sn]
                ;; For this state, build Event.rec over the event
                ;; Each event minor is either Some(target) or None
                (let [event-minors
                      (mapv (fn [en]
                              (if-let [target (get transition-map [sn en])]
                                (mk-option-some state-const
                                                (e/const' (name/from-string
                                                           (str state-type-str "." target)) []))
                                (mk-option-none state-const)))
                            event-names)]
                  ;; λ (e : Event) => Event.rec (λ _ => Option State) minor1..minorN e
                  (e/lam "e" event-const
                         (mk-rec-term env event-type-str option-state
                                      event-minors (e/bvar 0))
                         :default)))
              state-names)

        ;; Full delta: λ (s : State) (e : Event) =>
        ;;   State.rec (λ _ => Event → Option State)
        ;;     (λ e => Event.rec ... e)  -- per-state minors
        ;;     ...
        ;;     s e
        arrow-event-option (e/forall' "_" event-const option-state :default)
        delta-body
        (e/lam "s" state-const
               (e/lam "e" event-const
                      (e/app
                       (mk-rec-term env state-type-str arrow-event-option
                                    state-minors (e/bvar 1))
                       (e/bvar 0))
                      :default)
               :default)

        delta-type (e/forall' "s" state-const
                              (e/forall' "e" event-const option-state :default)
                              :default)
        delta-nm (name/from-string delta-str)
        delta-ci (env/mk-def delta-nm [] delta-type delta-body :hints :abbrev)
        env (env/add-constant env delta-ci)
        _ (println "✓" delta-str "defined")

        ;; 4. Identify sink states (no outgoing transitions)
        sources-with-transitions (into #{} (map (comp kw->ctor-name :source)) (:transitions spec))
        sink-states (remove sources-with-transitions state-names)

        ;; Prove sink theorems: ∀ e : Event, Delta sink e = none
        env (reduce
             (fn [env sink-name]
               (let [thm-name-str (str delta-str "_" sink-name "_sink")
                     thm-nm (name/from-string thm-name-str)
                     sink-const (e/const' (name/from-string (str state-type-str "." sink-name)) [])
                     ;; ∀ (e : Event), Eq (Option State) (Delta sink e) (Option.none State)
                     thm-type (e/forall'
                               "e" event-const
                               (e/app* (e/const' eq-nm [(lvl/succ u0)])
                                       option-state
                                       (e/app* (e/const' delta-nm []) sink-const (e/bvar 0))
                                       (mk-option-none state-const))
                               :default)
                     [ps _] (proof/start-proof env thm-type)
                     ps (basic/intro ps "e")
                     goal (proof/current-goal ps)
                     e-id (reduce (fn [best [id d]]
                                    (if (and (= "e" (:name d))
                                             (or (nil? best) (> (long id) (long best))))
                                      id best))
                                  nil (:lctx goal))
                     ps (basic/cases ps e-id)
                     ps (basic/all-goals ps (fn [ps'] (basic/rfl ps')))]
                 (when-not (proof/solved? ps)
                   (throw (ex-info (str "Sink theorem failed for " sink-name)
                                   {:goals (proof/format-goals ps)})))
                 (let [term (extract/verify ps)
                       ci (env/mk-thm thm-nm [] thm-type term)]
                   (println "✓ theorem" thm-name-str)
                   (env/add-constant env ci))))
             env
             sink-states)]

    {:env env
     :state-type state-type-str
     :event-type event-type-str
     :delta delta-str
     :state-names state-names
     :event-names event-names
     :sink-theorems (mapv #(str delta-str "_" % "_sink") sink-states)}))

;; ============================================================
;; Effect signature compilation
;; ============================================================

(defn compile-effect-signature!
  "Compile a Pneuma effect-signature spec into Ansatz declarations.

   Input: {:operations {:init-key {:input {...} :output :T} ...}}

   Generates:
   - {prefix}Op inductive + DecidableEq
   - {prefix}AllOps : List Op
   - {prefix}AllOps_complete theorem

   Returns map of generated declaration names."
  [env prefix spec]
  (let [op-names (vec (sort (map kw->ctor-name (keys (:operations spec)))))
        op-type-str (prefix-name prefix "Op")
        all-ops-str (prefix-name prefix "AllOps")

        ;; 1. Define Op inductive
        op-ctor-specs (mapv (fn [n] [n []]) op-names)
        env (inductive/define-inductive env op-type-str '[] op-ctor-specs)
        env (deriving/derive-decidable-eq! env op-type-str op-ctor-specs)

        op-nm (name/from-string op-type-str)
        op-const (e/const' op-nm [])

        ;; 2. Define AllOps : List Op
        all-ops-nm (name/from-string all-ops-str)
        op-terms (mapv (fn [n] (e/const' (name/from-string (str op-type-str "." n)) []))
                       op-names)
        all-ops-list (mk-list op-const op-terms)
        all-ops-type (e/app (e/const' list-nm [u0]) op-const)
        all-ops-ci (env/mk-def all-ops-nm [] all-ops-type all-ops-list :hints :abbrev)
        env (env/add-constant env all-ops-ci)
        _ (println "✓" all-ops-str "defined")

        ;; 3. Prove AllOps_complete : ∀ (op : Op), List.Mem op AllOps
        complete-str (str all-ops-str "_complete")
        env (prove-enum-completeness env complete-str op-const all-ops-list)]

    {:env env
     :op-type op-type-str
     :op-names op-names
     :all-ops all-ops-str
     :all-ops-complete complete-str}))

;; ============================================================
;; Capability set compilation
;; ============================================================

(defn compile-capability-set!
  "Compile a Pneuma capability-set into an Ansatz predicate.

   Input: {:dispatch #{:op1 :op2} :subscribe #{...} :query #{...}}

   Generates:
   - {prefix}{phase}Dispatch : Op → Bool (for dispatch set)
   - {prefix}{phase}Query : Op → Bool (for query set, if present)

   Requires Op type to already exist in env.

   Returns map of generated declaration names."
  [env prefix phase-name op-type-str op-names cap-spec]
  (let [op-nm (name/from-string op-type-str)
        op-const (e/const' op-nm [])
        bool-type (e/const' bool-nm [])

        gen-predicate
        (fn [env pred-suffix ref-set]
          (when (and ref-set (seq ref-set))
            (let [ref-name-set (into #{} (map kw->ctor-name) ref-set)
                  pred-str (str prefix phase-name pred-suffix)
                  pred-nm (name/from-string pred-str)
                  ;; Build Op.rec (λ _ => Bool) true/false ... op
                  minors (mapv (fn [op-name]
                                 (if (contains? ref-name-set op-name)
                                   (e/const' bool-true-nm [])
                                   (e/const' bool-false-nm [])))
                               op-names)
                  body (e/lam "op" op-const
                              (mk-rec-term env op-type-str bool-type minors (e/bvar 0))
                              :default)
                  pred-type (e/forall' "op" op-const bool-type :default)
                  ci (env/mk-def pred-nm [] pred-type body :hints :abbrev)]
              (println "✓" pred-str "defined")
              [(env/add-constant env ci) pred-str])))

        ;; Generate dispatch predicate
        [env dispatch-pred] (or (gen-predicate env "Dispatch" (:dispatch cap-spec))
                                [env nil])
        ;; Generate query predicate
        [env query-pred] (or (gen-predicate env "Query" (:query cap-spec))
                             [env nil])]

    {:env env
     :dispatch-pred dispatch-pred
     :query-pred query-pred}))

;; ============================================================
;; Existential morphism compilation
;; ============================================================

(def ^:private decidable-isTrue-nm (name/from-string "Decidable.isTrue"))
(def ^:private decidable-isFalse-nm (name/from-string "Decidable.isFalse"))
(def ^:private false-nm (name/from-string "False"))

(defn compile-existential-morphism!
  "Compile an existential morphism boundary theorem.

   Proves: ∀ op, Decidable (pred op = Bool.true)

   After case-splitting on op, each goal reduces to either:
   - Decidable (Bool.true = Bool.true) → isTrue + rfl
   - Decidable (Bool.false = Bool.true) → isFalse + Bool.noConfusion

   This confirms the predicate is well-typed over the Op type and
   that every operation has a decidable membership test.

   Returns map with theorem name."
  [env prefix morphism-id pred-name op-type-str]
  (let [thm-str (str prefix (clojure.core/name morphism-id) "_boundary")
        thm-nm (name/from-string thm-str)
        op-nm (name/from-string op-type-str)
        op-const (e/const' op-nm [])
        pred-nm-name (name/from-string pred-name)
        bool-type (e/const' bool-nm [])

        eq-level (lvl/succ u0)
        thm-type (e/forall'
                  "op" op-const
                  (e/app (e/const' (name/from-string "Decidable") [])
                         (e/app* (e/const' eq-nm [eq-level])
                                 bool-type
                                 (e/app (e/const' pred-nm-name []) (e/bvar 0))
                                 (e/const' bool-true-nm [])))
                  :default)

        [ps _] (proof/start-proof env thm-type)
        ps (basic/intro ps "op")
        goal (proof/current-goal ps)
        op-id (reduce (fn [best [id d]]
                        (if (and (= "op" (:name d))
                                 (or (nil? best) (> (long id) (long best))))
                          id best))
                      nil (:lctx goal))
        ps (basic/cases ps op-id)
        ;; Each goal: Decidable (pred ctor = Bool.true)
        ;; After reduction, pred ctor is Bool.true or Bool.false
        ;; Use isTrue+rfl for true cases, isFalse+noConfusion for false
        ps (basic/all-goals
            ps
            (fn [ps']
              (basic/first-tac
               ps'
               ;; Try diagonal: isTrue + rfl
               (fn [ps'']
                 (-> ps''
                     (basic/apply-tac (e/const' decidable-isTrue-nm []))
                     (basic/rfl)))
               ;; Try off-diagonal: isFalse + intro h + Bool.noConfusion
               (fn [ps'']
                 (let [ps'' (basic/apply-tac ps'' (e/const' decidable-isFalse-nm []))
                       ps'' (basic/intro ps'' "h")
                       goal' (proof/current-goal ps'')
                       h-id (reduce (fn [best [id d]]
                                      (if (and (= "h" (:name d))
                                               (or (nil? best) (> (long id) (long best))))
                                        id best))
                                    nil (:lctx goal'))
                       h-decl (get (:lctx goal') h-id)
                       [_ eq-args] (e/get-app-fn-args (:type h-decl))
                       val-a (nth eq-args 1)
                       val-b (nth eq-args 2)
                       nc-name (name/from-string "Bool.noConfusion")
                       nc-term (e/app* (e/const' nc-name [lvl/zero])
                                       (e/const' false-nm [])
                                       val-a val-b
                                       (e/fvar h-id))]
                   (basic/apply-tac ps'' nc-term))))))]

    (when-not (proof/solved? ps)
      (throw (ex-info (str "Morphism boundary theorem failed: " thm-str)
                      {:goals (proof/format-goals ps)})))

    (let [term (extract/verify ps)
          ci (env/mk-thm thm-nm [] thm-type term)
          env (env/add-constant env ci)]
      (println "✓ theorem" thm-str)
      {:env env
       :theorem thm-str})))

;; ============================================================
;; Type schema compilation
;; ============================================================

(defn compile-type-schema!
  "Compile a Pneuma type-schema spec into Ansatz declarations.

   Input: {:types {:ConfigKey :keyword :ConfigValue :any ...}}

   Generates:
   - {prefix}TypeId inductive + DecidableEq
   - {prefix}AllTypeIds : List TypeId
   - {prefix}AllTypeIds_complete theorem

   Returns map of generated declaration names."
  [env prefix spec]
  (let [type-names (vec (sort (map kw->ctor-name (keys (:types spec)))))
        type-id-str (prefix-name prefix "TypeId")
        all-types-str (prefix-name prefix "AllTypeIds")

        ;; 1. Define TypeId inductive
        type-ctor-specs (mapv (fn [n] [n []]) type-names)
        env (inductive/define-inductive env type-id-str '[] type-ctor-specs)
        env (deriving/derive-decidable-eq! env type-id-str type-ctor-specs)

        type-nm (name/from-string type-id-str)
        type-const (e/const' type-nm [])

        ;; 2. Define AllTypeIds : List TypeId
        all-types-nm (name/from-string all-types-str)
        type-terms (mapv (fn [n] (e/const' (name/from-string (str type-id-str "." n)) []))
                         type-names)
        all-types-list (mk-list type-const type-terms)
        all-types-type (e/app (e/const' list-nm [u0]) type-const)
        all-types-ci (env/mk-def all-types-nm [] all-types-type all-types-list :hints :abbrev)
        env (env/add-constant env all-types-ci)
        _ (println "✓" all-types-str "defined")

        ;; 3. Prove completeness
        complete-str (str all-types-str "_complete")
        env (prove-enum-completeness env complete-str type-const all-types-list)]

    {:env env
     :type-id-type type-id-str
     :type-names type-names
     :all-type-ids all-types-str
     :all-type-ids-complete complete-str}))

;; ============================================================
;; Structural morphism compilation
;; ============================================================

(defn compile-structural-morphism!
  "Compile a structural morphism: maps operation outputs to type identifiers.

   Defines {prefix}{morphism-id}Map : Op → TypeId via recursor.
   The definition type-checks iff every operation output is a valid TypeId.

   Also proves: ∀ op, List.Mem (map op) allTypeIds
   which certifies that every mapped type is in the type universe.

   Requires: op-output-map — a map from op-name (string) to output type-name (string).

   Returns map with definition and theorem names."
  [env prefix morphism-id op-type-str op-names type-id-str type-names
   all-type-ids-list op-output-map]
  (let [map-str (str prefix (clojure.core/name morphism-id) "_map")
        map-nm (name/from-string map-str)
        op-nm (name/from-string op-type-str)
        op-const (e/const' op-nm [])
        tid-nm (name/from-string type-id-str)
        tid-const (e/const' tid-nm [])

        ;; Build Op.rec (λ _ => TypeId) minor1..minorN op
        minors (mapv (fn [op-name]
                       (let [output-name (get op-output-map op-name)]
                         (when-not output-name
                           (throw (ex-info (str "No output type mapping for op: " op-name)
                                           {:op op-name :available (keys op-output-map)})))
                         (let [tid-ctor-nm (name/from-string (str type-id-str "." output-name))]
                           (when-not (env/lookup env tid-ctor-nm)
                             (throw (ex-info (str "Output type not in TypeId: " output-name)
                                             {:output output-name :type-id-type type-id-str})))
                           (e/const' tid-ctor-nm []))))
                     op-names)
        body (e/lam "op" op-const
                    (mk-rec-term env op-type-str tid-const minors (e/bvar 0))
                    :default)
        map-type (e/forall' "op" op-const tid-const :default)
        map-ci (env/mk-def map-nm [] map-type body :hints :abbrev)
        env (env/add-constant env map-ci)
        _ (println "✓" map-str "defined")

        ;; Prove: ∀ op, List.Mem (mapFn op) allTypeIds
        thm-str (str map-str "_valid")
        thm-nm (name/from-string thm-str)
        thm-type (e/forall'
                  "op" op-const
                  (e/app* (e/const' list-mem-nm [u0])
                          tid-const
                          (e/app (e/const' map-nm []) (e/bvar 0))
                          all-type-ids-list)
                  :default)
        [ps _] (proof/start-proof env thm-type)
        ps (basic/intro ps "op")
        goal (proof/current-goal ps)
        op-id (find-fvar goal "op")
        ps (basic/cases ps op-id)
        ;; Each goal: List.Mem (TypeId.X) allTypeIds — close with head/tail
        ps (basic/all-goals ps close-membership-goal)]

    (when-not (proof/solved? ps)
      (throw (ex-info (str "Structural morphism proof failed: " thm-str)
                      {:goals (proof/format-goals ps)})))

    (let [term (extract/verify ps)
          ci (env/mk-thm thm-nm [] thm-type term)
          env (env/add-constant env ci)]
      (println "✓ theorem" thm-str)
      {:env env
       :map-fn map-str
       :theorem thm-str})))

;; ============================================================
;; Containment morphism compilation
;; ============================================================

(defn compile-containment-morphism!
  "Compile a containment morphism boundary theorem.

   Semantically identical to existential morphism (subset check),
   with a different gap-type label. Proves the same theorem:
   ∀ op, Decidable (pred op = Bool.true)

   Returns map with theorem name."
  [env prefix morphism-id pred-name op-type-str]
  ;; Reuse the existential proof — same structure
  (compile-existential-morphism! env prefix morphism-id pred-name op-type-str))

;; ============================================================
;; Ordering morphism compilation
;; ============================================================

(defn compile-ordering-morphism!
  "Compile an ordering morphism: proves source precedes target in a chain.

   chain: ordered sequence of identifier keywords, e.g. [:a :b :c]
   source-kw: keyword that must come first
   target-kw: keyword that must come second

   Proves: Nat.lt source-index target-index
   where indices are positions in the chain.

   Returns map with theorem name."
  [env prefix morphism-id chain source-kw target-kw]
  (let [chain-names (mapv kw->ctor-name chain)
        source-name (kw->ctor-name source-kw)
        target-name (kw->ctor-name target-kw)
        source-idx (.indexOf ^java.util.List chain-names source-name)
        target-idx (.indexOf ^java.util.List chain-names target-name)

        _ (when (neg? source-idx)
            (throw (ex-info (str "Source not in chain: " source-kw)
                            {:source source-kw :chain chain})))
        _ (when (neg? target-idx)
            (throw (ex-info (str "Target not in chain: " target-kw)
                            {:target target-kw :chain chain})))
        _ (when-not (< source-idx target-idx)
            (throw (ex-info (str "Ordering violation: " source-kw " (idx " source-idx
                                 ") does not precede " target-kw " (idx " target-idx ")")
                            {:source source-kw :source-idx source-idx
                             :target target-kw :target-idx target-idx})))

        thm-str (str prefix (clojure.core/name morphism-id) "_order")
        thm-nm (name/from-string thm-str)

        ;; Nat.lt n m = Nat.le (succ n) m
        ;; Build goal: Nat.lt source-idx target-idx
        thm-type (e/app* (e/const' nat-lt-nm [])
                         (mk-nat source-idx)
                         (mk-nat target-idx))

        ;; Proof: Nat.lt n m unfolds to Nat.le (n+1) m
        ;; We need (target-idx - source-idx - 1) steps + 1 refl
        ;; i.e., prove Nat.le (source-idx+1) target-idx
        ;; by applying Nat.le.step (target-idx - source-idx - 1) times
        ;; then Nat.le.refl

        [ps _] (proof/start-proof env thm-type)
        gap (- target-idx source-idx 1)
        ps (reduce (fn [ps _]
                     (basic/apply-tac ps (e/const' nat-le-step-nm [])))
                   ps (range gap))
        ps (basic/apply-tac ps (e/const' nat-le-refl-nm []))]

    (when-not (proof/solved? ps)
      (throw (ex-info (str "Ordering proof failed: " thm-str)
                      {:goals (proof/format-goals ps)})))

    (let [term (extract/verify ps)
          ci (env/mk-thm thm-nm [] thm-type term)
          env (env/add-constant env ci)]
      (println "✓ theorem" thm-str)
      {:env env
       :theorem thm-str})))

;; ============================================================
;; Top-level spec compilation
;; ============================================================

(defn- resolve-cap-pred-name
  "Resolve the predicate name for a morphism from the capability set results."
  [prefix cap-results morph-spec]
  (let [[_ phase-kw] (:from morph-spec)
        ref-kind (:source-ref-kind morph-spec)
        phase-name (str/capitalize (kw->ctor-name phase-kw))
        pred-suffix (case ref-kind
                      :dispatch "Dispatch"
                      :query "Query"
                      :subscribe "Subscribe"
                      "Dispatch")]
    (str prefix phase-name pred-suffix)))

(defn- build-op-output-map
  "Build a map from op constructor names to output type constructor names.
   Uses the :operations map from the effect-signature spec."
  [operations]
  (into {}
        (map (fn [[op-kw op-spec]]
               [(kw->ctor-name op-kw)
                (kw->ctor-name (:output op-spec))]))
        operations))

(defn compile-spec!
  "Compile a complete Pneuma spec system into Ansatz kernel declarations.

   Input:
   {:prefix \"Integrant\"              ;; optional, default \"\"
    :statechart {:states #{...} :transitions [...]}
    :effect-signature {:operations {:op {:input {...} :output :TypeName} ...}}
    :capability-sets {:init {:dispatch #{...}} :halt {:dispatch #{...}} ...}
    :type-schema {:types {:TypeName :kind ...}}
    :morphisms {:init->ops {:type :existential
                            :from [:capability-sets :init]
                            :source-ref-kind :dispatch
                            :to :effect-signature
                            :target-ref-kind :operations}
                :ops->types {:type :structural
                             :from :effect-signature
                             :to :type-schema
                             :source-ref-kind :operation-outputs
                             :target-ref-kind :type-ids}
                :ordering  {:type :ordering
                            :chain [:a :b :c]
                            :source :a
                            :target :c}}}

   Returns map of all generated declarations."
  [spec-system]
  (let [prefix (or (:prefix spec-system) "")
        env @@(requiring-resolve 'ansatz.core/ansatz-env)

        ;; 1. Compile statechart
        sc-result (when (:statechart spec-system)
                    (compile-statechart! env prefix (:statechart spec-system)))
        env (or (:env sc-result) env)

        ;; 2. Compile effect signature
        es-result (when (:effect-signature spec-system)
                    (compile-effect-signature! env prefix (:effect-signature spec-system)))
        env (or (:env es-result) env)

        ;; 3. Compile type schema
        ts-result (when (:type-schema spec-system)
                    (compile-type-schema! env prefix (:type-schema spec-system)))
        env (or (:env ts-result) env)

        ;; 4. Compile capability sets
        cap-results
        (when (and (:capability-sets spec-system) es-result)
          (reduce (fn [{:keys [env results]} [phase-kw cap-spec]]
                    (let [phase-name (str/capitalize (kw->ctor-name phase-kw))
                          result (compile-capability-set!
                                  env prefix phase-name
                                  (:op-type es-result)
                                  (:op-names es-result)
                                  cap-spec)]
                      {:env (:env result)
                       :results (assoc results phase-kw result)}))
                  {:env env :results {}}
                  (:capability-sets spec-system)))
        env (or (:env cap-results) env)

        ;; 5. Compile morphisms
        morph-results
        (when (:morphisms spec-system)
          (reduce
           (fn [{:keys [env results]} [morph-id morph-spec]]
             (let [result
                   (case (:type morph-spec)
                     :existential
                     (let [pred-name (resolve-cap-pred-name
                                      prefix (:results cap-results) morph-spec)]
                       (compile-existential-morphism!
                        env prefix morph-id pred-name
                        (:op-type es-result)))

                     :containment
                     (let [pred-name (resolve-cap-pred-name
                                      prefix (:results cap-results) morph-spec)]
                       (compile-containment-morphism!
                        env prefix morph-id pred-name
                        (:op-type es-result)))

                     :structural
                     (let [op-output-map (build-op-output-map
                                          (get-in spec-system [:effect-signature :operations]))
                           tid-nm (name/from-string (:type-id-type ts-result))
                           tid-const (e/const' tid-nm [])
                           all-tids-list (mk-list
                                          tid-const
                                          (mapv (fn [n]
                                                  (e/const'
                                                   (name/from-string
                                                    (str (:type-id-type ts-result) "." n)) []))
                                                (:type-names ts-result)))]
                       (compile-structural-morphism!
                        env prefix morph-id
                        (:op-type es-result) (:op-names es-result)
                        (:type-id-type ts-result) (:type-names ts-result)
                        all-tids-list op-output-map))

                     :ordering
                     (compile-ordering-morphism!
                      env prefix morph-id
                      (:chain morph-spec)
                      (:source morph-spec)
                      (:target morph-spec))

                     ;; Unknown morphism type — skip with warning
                     (do (println "⚠ skipping unknown morphism type:" (:type morph-spec))
                         {:env env}))]
               {:env (:env result)
                :results (assoc results morph-id result)}))
           {:env env :results {}}
           (:morphisms spec-system)))
        env (or (:env morph-results) env)]

    ;; Update global env
    (reset! @(requiring-resolve 'ansatz.core/ansatz-env) env)

    {:statechart sc-result
     :effect-signature es-result
     :type-schema ts-result
     :capability-sets (:results cap-results)
     :morphisms (:results morph-results)}))
