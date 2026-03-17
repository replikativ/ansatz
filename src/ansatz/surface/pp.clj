;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; Pretty-printer for Ansatz expressions — renders human-readable Lean-like text.

(ns ansatz.surface.pp
  "Pretty-printer that renders Ansatz expressions as readable Lean-like text.

   `(pp expr)` renders without environment (uses generic binder names).
   `(pp env expr)` renders with environment for name resolution.

   Output uses Lean-like syntax:
   - `∀ (a : Nat), body` for dependent forall
   - `A → B` for non-dependent arrow
   - `fun (a : Nat) => body` for lambda
   - `let a : T := v in body` for let
   - `@Name.{levels}` for constants with universe levels
   - `Prop`, `Type`, `Type n` for sorts"
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [clojure.string :as str]))

(def ^:private ^:const max-depth 50)

(def ^:private generated-names
  "Infinite lazy seq of binder names: a, b, c, ..., z, a1, b1, ..."
  (let [letters (map #(str (char %)) (range (int \a) (inc (int \z))))]
    (concat letters
            (for [n (rest (range))
                  l letters]
              (str l n)))))

(defn- binder-name-str
  "Get a human-readable name for a binder. If the stored name is nil or
   anonymous, generate one based on the current context size."
  [binder-name ctx]
  (let [n (when binder-name (name/->string binder-name))]
    (if (or (nil? n) (= n "[anonymous]") (str/blank? n))
      (nth generated-names (count ctx))
      n)))

(defn- pp-level
  "Pretty-print a universe level."
  [l]
  (lvl/->string l))

(defn- pp-levels
  "Pretty-print universe level arguments for a constant.
   Returns empty string if all levels are zero, otherwise .{l1, l2, ...}."
  [levels]
  (if (or (empty? levels)
          (every? #(lvl/level-zero? %) levels))
    ""
    (str ".{" (str/join ", " (map pp-level levels)) "}")))

(defn- sort-string
  "Render a sort expression."
  [level]
  (let [n (lvl/to-nat level)]
    (cond
      (and n (zero? n)) "Prop"
      (and n (= n 1))   "Type"
      (some? n)          (str "Type " (dec n))
      ;; Non-concrete level: Sort (succ u) => Type u
      (lvl/succ? level) (str "Type " (pp-level (lvl/succ-pred level)))
      :else             (str "Sort " (pp-level level)))))

(defn- needs-parens-as-arg?
  "Does expr need parentheses when used as a function argument?"
  [expr]
  (case (e/tag expr)
    :app true
    :lam true
    :forall true
    :let true
    false))

(defn- needs-parens-as-arrow-lhs?
  "Does expr need parentheses when used on the left side of →?"
  [expr]
  ;; Forall on the left of arrow needs parens: (∀ x, A) → B
  (case (e/tag expr)
    :forall true
    :lam true
    :let true
    false))

(defn- pp*
  "Core pretty-print function.
   ctx is a vector of binder name strings, innermost last (index 0 = outermost).
   Bvar n maps to ctx[(count ctx) - 1 - n]."
  [expr ctx depth]
  (if (>= depth max-depth)
    "..."
    (let [d (inc depth)]
      (case (e/tag expr)
        :bvar
        (let [idx (e/bvar-idx expr)
              pos (- (count ctx) 1 idx)]
          (if (and (>= pos 0) (< pos (count ctx)))
            (nth ctx pos)
            (str "#" idx)))

        :sort
        (sort-string (e/sort-level expr))

        :const
        (let [n (name/->string (e/const-name expr))
              ls (e/const-levels expr)
              lvl-str (pp-levels ls)]
          (if (seq lvl-str)
            (str "@" n lvl-str)
            n))

        :app
        (let [[head args] (e/get-app-fn-args expr)
              head-str (pp* head ctx d)
              arg-strs (map (fn [a]
                              (let [s (pp* a ctx d)]
                                (if (needs-parens-as-arg? a)
                                  (str "(" s ")")
                                  s)))
                            args)]
          (str head-str " " (str/join " " arg-strs)))

        :lam
        (let [bname (binder-name-str (e/lam-name expr) ctx)
              ty-str (pp* (e/lam-type expr) ctx d)
              ctx' (conj ctx bname)
              body-str (pp* (e/lam-body expr) ctx' d)
              info (e/lam-info expr)]
          (case info
            :implicit (str "fun {" bname " : " ty-str "} => " body-str)
            :inst-implicit (str "fun [" bname " : " ty-str "] => " body-str)
            :strict-implicit (str "fun ⦃" bname " : " ty-str "⦄ => " body-str)
            (str "fun (" bname " : " ty-str ") => " body-str)))

        :forall
        (let [body (e/forall-body expr)
              ;; Non-dependent arrow: bvar 0 does not appear in body
              non-dep? (zero? (e/bvar-range body))]
          (if non-dep?
            ;; Arrow notation: A → B
            (let [ty-str (pp* (e/forall-type expr) ctx d)
                  lhs (if (needs-parens-as-arrow-lhs? (e/forall-type expr))
                        (str "(" ty-str ")")
                        ty-str)
                  ;; For non-dependent arrow, we still enter the binder scope
                  ;; but the name won't be used. Push a dummy name.
                  ctx' (conj ctx "_")
                  body-str (pp* body ctx' d)]
              (str lhs " → " body-str))
            ;; Dependent forall
            (let [bname (binder-name-str (e/forall-name expr) ctx)
                  ty-str (pp* (e/forall-type expr) ctx d)
                  ctx' (conj ctx bname)
                  body-str (pp* body ctx' d)
                  info (e/forall-info expr)]
              (case info
                :implicit (str "∀ {" bname " : " ty-str "}, " body-str)
                :inst-implicit (str "∀ [" bname " : " ty-str "], " body-str)
                :strict-implicit (str "∀ ⦃" bname " : " ty-str "⦄, " body-str)
                (str "∀ (" bname " : " ty-str "), " body-str)))))

        :let
        (let [bname (binder-name-str (e/let-name expr) ctx)
              ty-str (pp* (e/let-type expr) ctx d)
              val-str (pp* (e/let-value expr) ctx d)
              ctx' (conj ctx bname)
              body-str (pp* (e/let-body expr) ctx' d)]
          (str "let " bname " : " ty-str " := " val-str " in " body-str))

        :lit-nat
        (str (e/lit-nat-val expr))

        :lit-str
        (pr-str (e/lit-str-val expr))

        :mdata
        (pp* (e/mdata-expr expr) ctx d)

        :proj
        (let [struct-str (pp* (e/proj-struct expr) ctx d)
              s (if (needs-parens-as-arg? (e/proj-struct expr))
                  (str "(" struct-str ")")
                  struct-str)]
          (str s "." (e/proj-idx expr)))

        :fvar
        (str "?fv" (e/fvar-id expr))))))

(defn pp
  "Pretty-print a Ansatz expression as readable Lean-like text.
   With one argument, uses generic binder names.
   With two arguments, the first is an env (currently unused, reserved for
   future name resolution)."
  ([expr]
   (pp* expr [] 0))
  ([_env expr]
   (pp* expr [] 0)))
