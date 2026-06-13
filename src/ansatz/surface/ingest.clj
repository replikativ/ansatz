(ns ansatz.surface.ingest
  "Low-level Clojure-ingestion helpers shared by the elaborator (ansatz.surface.elaborate)
   and the DSL driver (ansatz.core), kept here to break what would otherwise be a circular
   dependency between them. These are pure surface concerns — macroexpand policy, parameter
   metadata parsing, and the structure-field registry — with no kernel or elaboration deps.")

;; ── Structure-field registry ────────────────────────────────────────────────────────────
;; type-name → {:fields [field-name …], :ctor-sym symbol}. Populated by ansatz.core's
;; `structure`/`defrecord` machinery; read by keyword projection in the elaborator and by
;; codegen in ansatz.core.
(defonce ^{:doc "Structure field registry for defrecord compilation."}
  structure-registry (atom {}))

;; ── Custom elaboration forms (lean4 macro_rules-shaped) ─────────────────────────────────
;; symbol → (fn [arg-forms] → surface-form). The elaborator expands the form and re-elaborates
;; the result — syntax→syntax, so extensions compose with every surface feature for free.
(defonce ^{:doc "Custom surface-form registry: symbol → (fn [args] surface-form)."}
  elaborator-registry (atom {}))

;; lean4 elab_rules (syntax → TERM, with elaborator access) — for TYPE-DIRECTED forms that
;; macro_rules (syntax → syntax, above) cannot express: the registered fn receives the live
;; elaboration state and the argument FORMS and returns a kernel Expr. Extension authors use
;; the stable helpers in ansatz.surface.api (elab-subterm / arg-type) — not elaborator internals.
(defonce ^{:doc "Term-elaborator registry: symbol → (fn [est args] → kernel Expr)."}
  term-elaborator-registry (atom {}))

;; Keyword projection over NON-structure receivers: the elaborator's `(:k x)` case handles
;; registered structures natively; for any other receiver it consults this registry by the
;; receiver's TYPE-HEAD name (e.g. "Value" → the dynamic-EDN vget builder). The handler
;; receives the FULL keyword (namespace included) and the elaborated receiver Expr.
(defonce ^{:doc "Keyword-access registry: type-head name (string) → (fn [est kw receiver-expr] → Expr)."}
  keyword-access-registry (atom {}))

;; ── Macroexpand-by-default policy ───────────────────────────────────────────────────────
(defonce ^{:doc "Macros NOT to auto-expand (ansatz has a better typed handler). By unqualified
   name. Only SEMANTIC mismatches belong here, not naming accidents: `cond` because Clojure's
   :else/truthy semantics differ from the elaborator's typed cond handling."}
  no-expand-macros
  (atom '#{cond}))

(defn expand-macro?
  "Should the elaborator macroexpand-1 this list head? True iff it resolves to a macro and is
   not in no-expand-macros (matched by unqualified name, so clojure.core/when etc. count)."
  [head]
  (boolean (and (symbol? head)
                (not (contains? @no-expand-macros (symbol (name head))))
                (try (some-> (resolve head) meta :macro) (catch Throwable _ nil)))))

;; ── core-lift: clojure.core ops → per-element-type kernel ops (type-directed) ────────────
;; The elaborator infers the operand's type head and picks the matching kernel op (defaulting
;; to Nat when the head isn't listed). This is the data half of the "lift clojure.core given
;; the type" design; extend as Int/Float/… ops land in the env. (Float.* and Int Bool-compare
;; ops are absent in Init today, so they're simply not listed.)
(def arith-lift
  "op-name → {operand-type-head → kernel constant}. Type-directed +/-/* lift."
  {"+" {"Nat" "Nat.add", "Int" "Int.add"}
   "-" {"Nat" "Nat.sub", "Int" "Int.sub"}
   "*" {"Nat" "Nat.mul", "Int" "Int.mul"}})

;; ── Parameter metadata parsing ──────────────────────────────────────────────────────────
(defn binder-type
  "A binder's declared type, read from metadata: prefer ^{:- T} (for compound types like
   (List Nat)), else the ^Type :tag shorthand (for simple types like ^Nat). Returns the type
   form, or nil for an untyped binder (→ the elaborator infers it)."
  [sym]
  (let [m (meta sym)] (or (:- m) (:tag m))))

(defn metadata-params?
  "Is this a METADATA parameter/binder vector (types ride as metadata on the binders),
   vs the legacy positional/`:-`-separator form? True iff some element carries :-, :tag, or
   :inst metadata. (A bare `[n Nat]` or `[n :- Nat]` carries none → legacy.)"
  [params]
  (boolean (some (fn [x] (let [m (meta x)] (or (:- m) (:tag m) (:inst m)))) params)))

(defn parse-params
  "Parse a parameter vector into triples [name type-form binder-info]. Surfaces, auto-detected:
     metadata (preferred, for a/defn):  [^Nat n  ^{:- (List Nat)} xs  ^:inst inst]
     :- separator (natural for proof binders / a/theorem):  [n :- Nat,  h :- (= Nat n n)]
     positional pairs (older):           [n Nat]
   Metadata composes — types ride on the binder symbols, so the binding vector stays a normal
   Clojure vector; ^:inst marks an instance binder."
  [params]
  (if (metadata-params? params)
    (mapv (fn [sym]
            (let [binfo (if (:inst (meta sym)) :inst-implicit :default)]
              [(with-meta sym nil) (binder-type sym) binfo]))
          params)
    (let [cleaned (remove #{:-} params)
          result (atom [])
          remaining (atom (vec cleaned))]
      (while (seq @remaining)
        (let [r @remaining
              pname (first r)
              ptype (second r)]
          (if (and (> (count r) 2) (= :inst (nth r 2)))
            (do (swap! result conj [pname ptype :inst-implicit])
                (reset! remaining (vec (drop 3 r))))
            (do (swap! result conj [pname ptype :default])
                (reset! remaining (vec (drop 2 r)))))))
      @result)))
