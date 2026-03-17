;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; Lean 4 syntax emitter — produces valid, fully explicit Lean 4 code from Ansatz expressions.

(ns ansatz.surface.lean
  "Emit valid Lean 4 syntax from Ansatz expressions.
   Uses fully explicit @-prefixed notation (no implicit argument insertion,
   no notation sugar). All universe levels are rendered explicitly when present.

   Main entry points:
     (emit-term expr)            → String of valid Lean 4 term syntax
     (emit-def name type value)  → String of a complete `def` declaration
     (emit-theorem name type proof) → String of a complete `theorem` declaration"
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [clojure.string :as str]))

;; ============================================================
;; Name escaping
;; ============================================================

(defn- needs-escaping?
  "Returns true if a Lean identifier component needs backtick escaping.
   Lean identifiers may contain alphanumerics, underscores, dots, and
   single quotes. Anything else requires escaping."
  [^String s]
  (not (re-matches #"[a-zA-Z_][a-zA-Z0-9_']*(\.[a-zA-Z_][a-zA-Z0-9_']*)*" s)))

(defn- escape-name
  "Escape a name for Lean 4 if it contains special characters."
  [^String s]
  (if (or (str/blank? s) (needs-escaping? s))
    (str "«" s "»")
    s))

;; ============================================================
;; Level rendering
;; ============================================================

(defn- emit-level
  "Render a universe level for Lean 4 syntax."
  [l]
  (let [n (lvl/to-nat l)]
    (if n
      (str n)
      (case (lvl/tag l)
        :zero "0"
        :succ (str "(" (emit-level (lvl/succ-pred l)) " + 1)")
        :max  (str "(max " (emit-level (lvl/max-lhs l)) " " (emit-level (lvl/max-rhs l)) ")")
        :imax (str "(imax " (emit-level (lvl/imax-lhs l)) " " (emit-level (lvl/imax-rhs l)) ")")
        :param (let [pn (lvl/param-name l)]
                 (if (instance? ansatz.kernel.Name pn)
                   (escape-name (name/->string pn))
                   (str pn)))))))

(defn- emit-levels
  "Render universe level list as `.{l1, l2, ...}` or empty string if no levels."
  [levels]
  (if (seq levels)
    (str ".{" (str/join ", " (map emit-level levels)) "}")
    ""))

;; ============================================================
;; Sort rendering
;; ============================================================

(defn- emit-sort
  "Render a Sort expression. Prop = Sort 0, Type = Sort 1, etc."
  [level]
  (let [n (lvl/to-nat level)]
    (cond
      (and n (zero? n)) "Prop"
      (and n (= n 1))   "Type"
      n                  (str "Sort " n)
      ;; Non-concrete level
      (lvl/succ? level)
      (let [pred (lvl/succ-pred level)
            pn (lvl/to-nat pred)]
        (if (and pn (zero? pn))
          "Type"
          (str "Type " (emit-level pred))))
      :else (str "Sort " (emit-level level)))))

;; ============================================================
;; Core term emitter
;; ============================================================

(defn- fresh-binder-name
  "Generate a binder name, using the given name or falling back to a generated one."
  [n ctx]
  (let [base (cond
               (nil? n) nil
               (instance? ansatz.kernel.Name n)
               (let [s (name/->string n)]
                 (when-not (= s "[anonymous]") s))
               :else (str n))
        base (or base "x")
        ;; Ensure uniqueness by appending a suffix if name already in context
        candidate (if (some #{base} ctx)
                    (loop [i 1]
                      (let [c (str base "_" i)]
                        (if (some #{c} ctx)
                          (recur (inc i))
                          c)))
                    base)]
    candidate))

(defn- complex-expr?
  "Returns true if an expression needs parentheses when used as an argument."
  [e]
  (case (e/tag e)
    (:app :lam :forall :let) true
    false))

(defn emit-term
  "Emit a Ansatz expression as valid Lean 4 syntax.
   Uses fully explicit @-prefixed notation.
   ctx is a vector of binder names for de Bruijn index resolution."
  ([expr] (emit-term expr []))
  ([expr ctx]
   (case (e/tag expr)
     ;; Bound variable — look up name from context
     :bvar (let [idx (e/bvar-idx expr)
                 ri (- (count ctx) 1 idx)]
             (if (and (>= ri 0) (< ri (count ctx)))
               (escape-name (nth ctx ri))
               (str "_bv" idx)))

     ;; Sort
     :sort (emit-sort (e/sort-level expr))

     ;; Constant reference
     :const (let [n (name/->string (e/const-name expr))
                  ls (e/const-levels expr)]
              (str "@" (escape-name n) (emit-levels ls)))

     ;; Application — flatten the spine
     :app (let [[head args] (e/get-app-fn-args expr)
                head-str (emit-term head ctx)
                ;; If head is a const, it already has @; otherwise wrap if complex
                head-out (if (e/const? head)
                           head-str
                           (if (complex-expr? head)
                             (str "(" head-str ")")
                             head-str))
                arg-strs (map (fn [a]
                                (if (complex-expr? a)
                                  (str "(" (emit-term a ctx) ")")
                                  (emit-term a ctx)))
                              args)]
            (str head-out " " (str/join " " arg-strs)))

     ;; Lambda
     :lam (let [bname (fresh-binder-name (e/lam-name expr) ctx)
                ty-str (emit-term (e/lam-type expr) ctx)
                new-ctx (conj ctx bname)
                body-str (emit-term (e/lam-body expr) new-ctx)]
            (str "fun (" (escape-name bname) " : " ty-str ") => " body-str))

     ;; Forall / Pi
     :forall (let [bname (fresh-binder-name (e/forall-name expr) ctx)
                   ty-str (emit-term (e/forall-type expr) ctx)
                   body (e/forall-body expr)
                   ;; Check if this is a non-dependent arrow (body doesn't use the binder)
                   non-dep? (zero? (e/bvar-range body))]
               (if non-dep?
                 ;; Non-dependent arrow: A -> B
                 (let [lhs (if (e/forall? (e/forall-type expr))
                             (str "(" ty-str ")")
                             ty-str)
                       ;; For non-dependent, body has no reference to bvar 0,
                       ;; but we still need a placeholder in ctx for correct indexing
                       new-ctx (conj ctx bname)
                       body-str (emit-term body new-ctx)]
                   (str lhs " \u2192 " body-str))
                 ;; Dependent: forall (a : T), body
                 (let [new-ctx (conj ctx bname)
                       body-str (emit-term body new-ctx)]
                   (str "\u2200 (" (escape-name bname) " : " ty-str "), " body-str))))

     ;; Let binding
     :let (let [bname (fresh-binder-name (e/let-name expr) ctx)
                ty-str (emit-term (e/let-type expr) ctx)
                val-str (emit-term (e/let-value expr) ctx)
                new-ctx (conj ctx bname)
                body-str (emit-term (e/let-body expr) new-ctx)]
            (str "let " (escape-name bname) " : " ty-str " := " val-str "; " body-str))

     ;; Natural number literal
     :lit-nat (str (e/lit-nat-val expr))

     ;; String literal
     :lit-str (pr-str (e/lit-str-val expr))

     ;; Metadata — transparent, emit inner expression
     :mdata (emit-term (e/mdata-expr expr) ctx)

     ;; Projection
     :proj (let [tn (escape-name (name/->string (e/proj-type-name expr)))
                 idx (e/proj-idx expr)
                 struct-str (let [s (e/proj-struct expr)]
                              (if (complex-expr? s)
                                (str "(" (emit-term s ctx) ")")
                                (emit-term s ctx)))]
             (str "@" tn "." idx " " struct-str))

     ;; Free variable (should not appear in emitted code normally)
     :fvar (str "_fv" (e/fvar-id expr)))))

;; ============================================================
;; Top-level declaration emitters
;; ============================================================

(defn emit-def
  "Emit a Lean 4 `def` declaration.
   name-str is a string, type and value are Ansatz expressions."
  [name-str type value]
  (let [n (escape-name name-str)
        ty (emit-term type)
        val (emit-term value)]
    (str "def " n " : " ty " :=\n  " val)))

(defn emit-theorem
  "Emit a Lean 4 `theorem` declaration.
   name-str is a string, type and proof are Ansatz expressions."
  [name-str type proof]
  (let [n (escape-name name-str)
        ty (emit-term type)
        pf (emit-term proof)]
    (str "theorem " n " : " ty " :=\n  " pf)))
