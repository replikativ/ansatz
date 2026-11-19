(ns ansatz.clj-contract
  "The clojure.core contract of `a/defn` bodies, as data.

   Each row is one Clojure spelling at one type, with the status Ansatz has TODAY:
     :agree     the compiled function computes clojure.core's value on every call where
                clojure.core returns one
     :refuse    the definition is not accepted (with `:reason` once the refusal is structured)
     :diverges  the definition is accepted and computes a different value: a known bug, kept as
                a strict expected failure so the PR that fixes it must flip the row
     :domain    agreement on the inputs `:domain` admits only

   The table is checked by test/ansatz/clj_core_conformance_test.clj (bundled Init) and
   clj_core_conformance_mathlib_test.clj (rows whose `:requires` constants only a Mathlib store
   has), and rendered to doc/clojure-contract.md by `contract-markdown`; a test keeps that
   document equal to the rendering. Row keys:
     :id :group :form :params [[sym type-form] …] :ret type-form :expect :reason :lean?
     :requires #{constant-name …}  :domain '(fn [args…] bool)  :note"
  (:require [clojure.string :as str]
            [ansatz.surface.ingest :as ingest]))

(def setup-forms
  "Declarations the rows refer to, evaluated once before the table runs."
  ['(ansatz.core/structure CcPoint [] (x Nat) (y Nat))])

(def float-consts #{"Float" "instOfScientificFloat" "Float.floor" "Float.lt"})

(def rows
  [;; ── arithmetic ──────────────────────────────────────────────────────────────────────
   {:id :add/nat :group :arithmetic :form '(+ a b) :params '[[a Nat] [b Nat]] :ret 'Nat :expect :agree}
   {:id :add/int :group :arithmetic :form '(+ a b) :params '[[a Int] [b Int]] :ret 'Int :expect :agree}
   {:id :add/nary :group :arithmetic :form '(+ a b c) :params '[[a Nat] [b Nat] [c Nat]] :ret 'Nat :expect :agree}
   {:id :add/zero-arity :group :arithmetic :form '(+) :params '[[a Nat]] :ret 'Nat :expect :agree
    :note "0, as in Clojure."}
   {:id :add/unary :group :arithmetic :form '(+ a) :params '[[a Nat]] :ret 'Nat :expect :agree}
   {:id :mul/nat :group :arithmetic :form '(* a b) :params '[[a Nat] [b Nat]] :ret 'Nat :expect :agree}
   {:id :mul/int :group :arithmetic :form '(* a b) :params '[[a Int] [b Int]] :ret 'Int :expect :agree}
   {:id :mul/zero-arity :group :arithmetic :form '(*) :params '[[a Nat]] :ret 'Nat :expect :agree}
   {:id :mul/unary :group :arithmetic :form '(* a) :params '[[a Nat]] :ret 'Nat :expect :agree}
   {:id :sub/nat :group :arithmetic :form '(- a b) :params '[[a Nat] [b Nat]] :ret 'Nat :expect :refuse
    :reason :nat-sub-may-be-negative :note "Accepted where b ≤ a follows from the guards in scope."}
   {:id :sub/nat-guarded :group :arithmetic :form '(if (<= b a) (- a b) 0) :params '[[a Nat] [b Nat]]
    :ret 'Nat :expect :agree :note "Under a guard that rules out a negative result."}
   {:id :sub/nat-lean :group :arithmetic :form '(- a b) :params '[[a Nat] [b Nat]] :ret 'Nat
    :lean? true :expect :diverges :note "Under `a/defn ^:lean` the body keeps Lean's truncation."}
   {:id :sub/nat-literal :group :arithmetic :form '(- a 1) :params '[[a Nat]] :ret 'Nat :expect :refuse
    :reason :nat-sub-may-be-negative}
   {:id :sub/nat-literal-guarded :group :arithmetic :form '(if (== a 0) 0 (- a 1)) :params '[[a Nat]]
    :ret 'Nat :expect :agree}
   {:id :sub/nary-nat :group :arithmetic :form '(- a b c) :params '[[a Nat] [b Nat] [c Nat]] :ret 'Nat
    :expect :refuse :reason :nat-sub-may-be-negative}
   {:id :sub/nary-nat-guarded :group :arithmetic :form '(if (<= (+ b c) a) (- a b c) 0)
    :params '[[a Nat] [b Nat] [c Nat]] :ret 'Nat :expect :agree}
   {:id :sub/nat-let-guard :group :arithmetic :form '(let [m (+ a b)] (- m a)) :params '[[a Nat] [b Nat]]
    :ret 'Nat :expect :agree :note "A let binding is a fact: m = a + b."}
   {:id :sub/int :group :arithmetic :form '(- a b) :params '[[a Int] [b Int]] :ret 'Int :expect :agree}
   {:id :sub/nary-int :group :arithmetic :form '(- a b c) :params '[[a Int] [b Int] [c Int]] :ret 'Int
    :expect :agree}
   {:id :sub/nat-at-int :group :arithmetic :form '(- a 1) :params '[[a Nat]] :ret 'Int :expect :agree
    :note "The declared Int type is the expected type: ↑a - 1 at Int, as Lean's binop%."}
   {:id :add/nat-int :group :arithmetic :form '(+ a i) :params '[[a Nat] [i Int]] :ret 'Int :expect :agree
    :note "A Nat leaf in an Int tree is coerced."}
   {:id :neg/int :group :arithmetic :form '(- a) :params '[[a Int]] :ret 'Int :expect :agree}
   {:id :neg/nat :group :arithmetic :form '(- a) :params '[[a Nat]] :ret 'Nat :expect :refuse
    :reason :nat-negation}
   {:id :literal/negative-int :group :arithmetic :form '(+ a -3) :params '[[a Int]] :ret 'Int :expect :agree}
   {:id :quot/nat :group :arithmetic :form '(quot a b) :params '[[a Nat] [b Nat]] :ret 'Nat :expect :agree
    :note "Division by zero: Clojure throws, Lean returns 0 (outside the contract)."}
   {:id :rem/nat :group :arithmetic :form '(rem a b) :params '[[a Nat] [b Nat]] :ret 'Nat :expect :agree}
   {:id :quot/int :group :arithmetic :form '(quot a b) :params '[[a Int] [b Int]] :ret 'Int :expect :agree
    :requires #{"Int.tdiv"} :note "Int.tdiv: truncation toward zero."}
   {:id :rem/int :group :arithmetic :form '(rem a b) :params '[[a Int] [b Int]] :ret 'Int :expect :agree
    :requires #{"Int.tmod"}}
   {:id :quot/float :group :arithmetic :form '(quot a b) :params '[[a Float] [b Float]] :ret 'Float
    :expect :agree :requires float-consts :note "Truncation toward zero, not real division."}
   {:id :rem/float :group :arithmetic :form '(rem a b) :params '[[a Float] [b Float]] :ret 'Float
    :expect :agree :requires float-consts}
   {:id :mod/float :group :arithmetic :form '(mod a b) :params '[[a Float] [b Float]] :ret 'Float
    :expect :agree :requires float-consts :note "clojure.core/mod: the remainder takes the divisor's sign."}
   {:id :mod/nat :group :arithmetic :form '(mod a b) :params '[[a Nat] [b Nat]] :ret 'Nat :expect :agree}
   {:id :mod/int :group :arithmetic :form '(mod a b) :params '[[a Int] [b Int]] :ret 'Int :expect :agree
    :requires #{"Int.fmod"} :note "Int.fmod (floored), never Lean's `%` on Int, which is Int.emod."}
   {:id :div/nat :group :arithmetic :form '(/ a b) :params '[[a Nat] [b Nat]] :ret 'Nat :expect :refuse
    :note "Clojure's `/` on integers is Ratio division; it is never lifted to floor division."}
   {:id :inc/nat :group :arithmetic :form '(inc a) :params '[[a Nat]] :ret 'Nat :expect :refuse
    :note "Not in the core surface (wandler adds it)."}
   {:id :dec/nat :group :arithmetic :form '(dec a) :params '[[a Nat]] :ret 'Nat :expect :refuse}
   {:id :max/nat :group :arithmetic :form '(max a b) :params '[[a Nat] [b Nat]] :ret 'Nat :expect :refuse}
   {:id :add/float :group :arithmetic :form '(+ a b) :params '[[a Float] [b Float]] :ret 'Float
    :expect :agree :requires float-consts}

   ;; ── comparison ──────────────────────────────────────────────────────────────────────
   {:id :lt/nat :group :comparison :form '(< a b) :params '[[a Nat] [b Nat]] :ret 'Bool :expect :agree}
   {:id :le/nat :group :comparison :form '(<= a b) :params '[[a Nat] [b Nat]] :ret 'Bool :expect :agree}
   {:id :gt/nat :group :comparison :form '(> a b) :params '[[a Nat] [b Nat]] :ret 'Bool :expect :agree}
   {:id :ge/nat :group :comparison :form '(>= a b) :params '[[a Nat] [b Nat]] :ret 'Bool :expect :agree}
   {:id :eqeq/nat :group :comparison :form '(== a b) :params '[[a Nat] [b Nat]] :ret 'Bool :expect :agree}
   {:id :eq/nat :group :comparison :form '(= a b) :params '[[a Nat] [b Nat]] :ret 'Bool :expect :agree}
   {:id :lt/int :group :comparison :form '(< a b) :params '[[a Int] [b Int]] :ret 'Bool :expect :agree}
   {:id :le/int :group :comparison :form '(<= a b) :params '[[a Int] [b Int]] :ret 'Bool :expect :agree}
   {:id :eq/int :group :comparison :form '(= a b) :params '[[a Int] [b Int]] :ret 'Bool :expect :agree}
   {:id :lt/nat-int :group :comparison :form '(< a i) :params '[[a Nat] [i Int]] :ret 'Bool :expect :agree}
   {:id :eq/string :group :comparison :form '(= a b) :params '[[a String] [b String]] :ret 'Bool :expect :agree}
   {:id :eq/bool :group :comparison :form '(= p q) :params '[[p Bool] [q Bool]] :ret 'Bool :expect :agree}
   {:id :lt/chain :group :comparison :form '(< a b c) :params '[[a Nat] [b Nat] [c Nat]] :ret 'Bool
    :expect :agree :note "Chains pairwise; (< T a b) with a type T is the Prop form."}
   {:id :eq/chain :group :comparison :form '(= a b c) :params '[[a Nat] [b Nat] [c Nat]] :ret 'Bool
    :expect :agree}
   {:id :lt/unary :group :comparison :form '(< a) :params '[[a Nat]] :ret 'Bool :expect :agree}
   {:id :lt/float :group :comparison :form '(< a b) :params '[[a Float] [b Float]] :ret 'Bool
    :expect :agree :requires float-consts :note "Float.lt is Bool-valued in Lean 4.33.1."}
   {:id :le/float :group :comparison :form '(<= a b) :params '[[a Float] [b Float]] :ret 'Bool
    :expect :agree :requires float-consts}
   {:id :eq/float-literal :group :comparison :form '(= a 0) :params '[[a Float]] :ret 'Bool
    :expect :refuse :reason :float-int-equality :requires float-consts}
   {:id :eqeq/float-literal :group :comparison :form '(== a 0) :params '[[a Float]] :ret 'Bool
    :expect :agree :requires float-consts}

   ;; ── control ─────────────────────────────────────────────────────────────────────────
   {:id :if/bool :group :control :form '(if p a b) :params '[[p Bool] [a Nat] [b Nat]] :ret 'Nat :expect :agree}
   {:id :if/comparison :group :control :form '(if (< a b) a b) :params '[[a Nat] [b Nat]] :ret 'Nat
    :expect :agree}
   {:id :if/int-comparison :group :control :form '(if (< a 0) (- a) a) :params '[[a Int]] :ret 'Int
    :expect :agree}
   {:id :if/nat-test :group :control :form '(if a 1 2) :params '[[a Nat]] :ret 'Nat :expect :refuse
    :reason :non-bool-test :note "Clojure: every number is truthy."}
   {:id :if/option-test :group :control :form '(if o 1 2) :params '[[o (Option Nat)]] :ret 'Nat
    :expect :refuse :reason :non-bool-test}
   {:id :if/list-test :group :control :form '(if xs 1 2) :params '[[xs (List Nat)]] :ret 'Nat
    :expect :refuse :reason :non-bool-test}
   {:id :if/no-else :group :control :form '(if p a) :params '[[p Bool] [a Nat]] :ret 'Nat :expect :refuse
    :reason :nil-at-type :note "Clojure returns nil when p is false."}
   {:id :when/list :group :control :form '(when p xs) :params '[[p Bool] [xs (List Nat)]] :ret '(List Nat)
    :expect :agree :note "The missing branch is nil, the empty List."}
   {:id :when/nat :group :control :form '(when p a) :params '[[p Bool] [a Nat]] :ret 'Nat :expect :refuse
    :reason :nil-at-type}
   {:id :when/multi :group :control :form '(when p a b) :params '[[p Bool] [a (List Nat)] [b (List Nat)]]
    :ret '(List Nat) :expect :refuse :reason :multi-form-body}
   {:id :cond/else :group :control :form '(cond (< a b) 1 (== a b) 2 :else 3) :params '[[a Nat] [b Nat]]
    :ret 'Nat :expect :agree}
   {:id :cond/no-else :group :control :form '(cond (< a b) 1) :params '[[a Nat] [b Nat]] :ret 'Nat
    :expect :refuse :reason :nil-at-type :note "Clojure returns nil when no clause matches."}
   {:id :cond/keyword :group :control :form '(cond (< a b) 1 :otherwise 2) :params '[[a Nat] [b Nat]]
    :ret 'Nat :expect :agree :note "Any keyword is a catch-all, as in Clojure."}
   {:id :case/literal :group :control :form '(case a 0 10 1 11 12) :params '[[a Nat]] :ret 'Nat :expect :agree}
   {:id :case/no-default :group :control :form '(case a 0 10 1 11) :params '[[a Nat]] :ret 'Nat
    :expect :refuse :reason :case-no-default}
   {:id :and/bool :group :control :form '(and p q) :params '[[p Bool] [q Bool]] :ret 'Bool :expect :agree}
   {:id :or/bool :group :control :form '(or p q) :params '[[p Bool] [q Bool]] :ret 'Bool :expect :agree}
   {:id :and/nary :group :control :form '(and p q r) :params '[[p Bool] [q Bool] [r Bool]] :ret 'Bool
    :expect :agree}
   {:id :or/value :group :control :form '(or a b) :params '[[a Nat] [b Nat]] :ret 'Nat :expect :refuse
    :reason :non-bool-test :note "An Option's `(or o d)` is under Nil checks."}
   {:id :and/value :group :control :form '(and a b) :params '[[a Nat] [b Nat]] :ret 'Nat :expect :refuse
    :reason :non-bool-test}
   {:id :not/bool :group :control :form '(not p) :params '[[p Bool]] :ret 'Bool :expect :agree
    :note "Bool.not."}
   {:id :not/nat :group :control :form '(not a) :params '[[a Nat]] :ret 'Bool :expect :refuse
    :reason :non-bool-test :note "Clojure: every number is truthy, so (not a) is false."}
   {:id :if-not/bool :group :control :form '(if-not p a b) :params '[[p Bool] [a Nat] [b Nat]] :ret 'Nat
    :expect :agree}

   ;; ── nil checks ──────────────────────────────────────────────────────────────────────
   {:id :if-some/nat :group :nil :form '(if-some [x o] (+ x 1) 0) :params '[[o (Option Nat)]] :ret 'Nat
    :expect :agree :note "Option.elim o 0 (fun x => x + 1), Lean's `if let some x := o`."}
   {:id :if-some/bool :group :nil :form '(if-some [x o] (if x 1 2) 3) :params '[[o (Option Bool)]] :ret 'Nat
    :expect :agree :note "Any element type: if-some tests for nil only."}
   {:id :if-some/list :group :nil :form '(if-some [ys o] ys [7]) :params '[[o (Option (List Nat))]]
    :ret '(List Nat) :expect :agree}
   {:id :if-some/no-else-list :group :nil :form '(if-some [x o] [x]) :params '[[o (Option Nat)]]
    :ret '(List Nat) :expect :agree :note "The missing branch is nil, the empty List."}
   {:id :if-some/no-else-nat :group :nil :form '(if-some [x o] x) :params '[[o (Option Nat)]] :ret 'Nat
    :expect :refuse :reason :nil-at-type}
   {:id :when-some/list :group :nil :form '(when-some [x o] [x x]) :params '[[o (Option Nat)]]
    :ret '(List Nat) :expect :agree}
   {:id :when-some/nat :group :nil :form '(when-some [x o] x) :params '[[o (Option Nat)]] :ret 'Nat
    :expect :refuse :reason :nil-at-type}
   {:id :if-some/not-optional :group :nil :form '(if-some [x a] x 0) :params '[[a Nat]] :ret 'Nat
    :expect :refuse :reason :not-optional :note "A Nat is never nil: bind it with let."}
   {:id :if-let/nat :group :nil :form '(if-let [x o] (* x 2) 7) :params '[[o (Option Nat)]] :ret 'Nat
    :expect :agree :note "A number is never nil or false: truthiness and the none test agree."}
   {:id :if-let/int :group :nil :form '(if-let [x o] (- x) 7) :params '[[o (Option Int)]] :ret 'Int
    :expect :agree}
   {:id :if-let/string :group :nil :form '(if-let [s o] s "none") :params '[[o (Option String)]]
    :ret 'String :expect :agree}
   {:id :if-let/structure :group :nil :form '(if-let [p o] (:x p) 0) :params '[[o (Option CcPoint)]]
    :ret 'Nat :expect :agree :note "A structure with fields runs as a record."}
   {:id :when-let/list :group :nil :form '(when-let [x o] [x]) :params '[[o (Option Nat)]]
    :ret '(List Nat) :expect :agree}
   {:id :if-let/bool :group :nil :form '(if-let [x p] (if x 1 3) 2) :params '[[p Bool]] :ret 'Nat
    :expect :agree :note "On a Bool, Clojure's own (let [x p] (if x … …))."}
   {:id :if-let/option-bool :group :nil :form '(if-let [x o] 1 2) :params '[[o (Option Bool)]] :ret 'Nat
    :expect :refuse :reason :truthiness-differs :note "Clojure takes the else branch for false."}
   {:id :if-let/option-option :group :nil :form '(if-let [x o] 1 2) :params '[[o (Option (Option Nat))]]
    :ret 'Nat :expect :refuse :reason :truthiness-differs}
   {:id :if-let/option-list :group :nil :form '(if-let [x o] 1 2) :params '[[o (Option (List Nat))]]
    :ret 'Nat :expect :refuse :reason :truthiness-differs}
   {:id :if-let/option-unit :group :nil :form '(if-let [x o] 1 2) :params '[[o (Option Unit)]]
    :ret 'Nat :expect :refuse :reason :truthiness-differs}
   {:id :if-let/not-optional :group :nil :form '(if-let [x a] x 0) :params '[[a Nat]] :ret 'Nat
    :expect :refuse :reason :not-optional}
   {:id :some?/option :group :nil :form '(some? o) :params '[[o (Option Nat)]] :ret 'Bool :expect :agree
    :note "Option.isSome."}
   {:id :nil?/option :group :nil :form '(nil? o) :params '[[o (Option Bool)]] :ret 'Bool :expect :agree
    :note "Option.isNone."}
   {:id :some?/nat :group :nil :form '(some? a) :params '[[a Nat]] :ret 'Bool :expect :refuse
    :reason :not-optional}
   {:id :nil?/list :group :nil :form '(nil? xs) :params '[[xs (List Nat)]] :ret 'Bool :expect :refuse
    :reason :not-optional :note "nil is the empty List, and (nil? ()) is false."}
   {:id :seq/if :group :nil :form '(if (seq xs) 1 0) :params '[[xs (List Nat)]] :ret 'Nat :expect :agree
    :note "As a test: !xs.isEmpty."}
   {:id :seq/when :group :nil :form '(when (seq xs) xs) :params '[[xs (List Nat)]] :ret '(List Nat)
    :expect :agree}
   {:id :seq/cond :group :nil :form '(cond (seq xs) 1 :else 0) :params '[[xs (List Nat)]] :ret 'Nat
    :expect :agree}
   {:id :seq/and-test :group :nil :form '(if (and p (seq xs)) 1 0) :params '[[p Bool] [xs (List Nat)]]
    :ret 'Nat :expect :agree :note "Inside an and/or that is itself a test."}
   {:id :seq/not :group :nil :form '(not (seq xs)) :params '[[xs (List Nat)]] :ret 'Bool :expect :agree}
   {:id :seq/value :group :nil :form '(seq xs) :params '[[xs (List Nat)]] :ret '(List Nat) :expect :refuse
    :reason :seq-value :note "Clojure returns nil or a seq."}
   {:id :seq/and-value :group :nil :form '(and p (seq xs)) :params '[[p Bool] [xs (List Nat)]] :ret 'Bool
    :expect :refuse :reason :seq-value :note "The and's value would be the seq."}
   {:id :empty?/list :group :nil :form '(empty? xs) :params '[[xs (List Nat)]] :ret 'Bool :expect :agree
    :note "List.isEmpty."}
   {:id :empty?/string :group :nil :form '(empty? s) :params '[[s String]] :ret 'Bool :expect :refuse
    :reason :not-a-list}
   {:id :or/option :group :nil :form '(or o 0) :params '[[o (Option Nat)]] :ret 'Nat :expect :agree
    :note "Option.getD o 0."}
   {:id :or/option-int :group :nil :form '(or o -1) :params '[[o (Option Int)]] :ret 'Int :expect :agree}
   {:id :or/option-nary :group :nil :form '(or o q 5) :params '[[o (Option Nat)] [q (Option Nat)]] :ret 'Nat
    :expect :agree :note "Option.getD o (Option.getD q 5)."}
   {:id :or/option-bool :group :nil :form '(or o true) :params '[[o (Option Bool)]] :ret 'Bool
    :expect :refuse :reason :truthiness-differs :note "Clojure: (or false true) is true."}

   ;; ── bodies and bindings ─────────────────────────────────────────────────────────────
   {:id :do/single :group :bodies :form '(do a) :params '[[a Nat]] :ret 'Nat :expect :agree}
   {:id :do/empty :group :bodies :form '(do) :params '[[a Nat]] :ret 'Nat :expect :refuse :reason :empty-do}
   {:id :do/multi :group :bodies :form '(do b a) :params '[[a Nat] [b Nat]] :ret 'Nat :expect :refuse
    :reason :multi-form-body}
   {:id :let/basic :group :bodies :form '(let [x (+ a 1)] (* x x)) :params '[[a Nat]] :ret 'Nat :expect :agree}
   {:id :let/multi-body :group :bodies :form '(let [x a] x (+ x 1)) :params '[[a Nat]] :ret 'Nat
    :expect :refuse :reason :multi-form-body}
   {:id :fn/multi-body :group :bodies :form '((fn [^{:- Nat} x] x (+ x 1)) a) :params '[[a Nat]] :ret 'Nat
    :expect :refuse :reason :multi-form-body}
   {:id :fn/beta :group :bodies :form '((fn [^{:- Nat} x] (+ x x)) a) :params '[[a Nat]] :ret 'Nat
    :expect :agree}
   {:id :fn/untyped-binder :group :bodies :form '((fn [x] (+ x x)) a) :params '[[a Nat]] :ret 'Nat
    :expect :refuse :note "A lambda binder needs a type."}
   {:id :loop/count :group :bodies :form '(loop [i a acc 0] (if (== i 0) acc (recur (dec i) (+ acc i))))
    :params '[[a Nat]] :ret 'Nat :expect :agree}
   {:id :loop/multi-body :group :bodies :form '(loop [i a] i i) :params '[[a Nat]] :ret 'Nat :expect :refuse
    :reason :multi-form-body}

   ;; ── data and nil ────────────────────────────────────────────────────────────────────
   {:id :get/keyword :group :data :form '(get p :x) :params '[[p CcPoint]] :ret 'Nat :expect :agree}
   {:id :get/keyword-default :group :data :form '(get p :x 7) :params '[[p CcPoint]] :ret 'Nat
    :expect :agree :note "A structure field is always present, so the default is unreachable."}
   {:id :keyword/call :group :data :form '(:y p) :params '[[p CcPoint]] :ret 'Nat :expect :agree}
   {:id :keyword/call-default :group :data :form '(:y p 7) :params '[[p CcPoint]] :ret 'Nat :expect :agree}
   {:id :keyword/default-non-structure :group :data :form '(:x o 7) :params '[[o (Option Nat)]] :ret 'Nat
    :expect :refuse :reason :get-default}
   {:id :get/non-keyword :group :data :form '(get xs 0) :params '[[xs (List Nat)]] :ret 'Nat :expect :refuse
    :reason :get-non-keyword}
   {:id :nil/list :group :data :form 'nil :params '[[a Nat]] :ret '(List Nat) :expect :agree
    :note "nil is the empty List."}
   {:id :option/argument :group :data :form 'o :params '[[o (Option Int)]] :ret '(Option Int) :expect :agree
    :note "An Option crosses unchanged: nil, or the value itself."}
   {:id :vector/literal :group :data :form '[a b] :params '[[a Nat] [b Nat]] :ret '(List Nat) :expect :agree}
   {:id :eq/list-nil :group :data :form '(= xs nil) :params '[[xs (List Nat)]] :ret 'Bool :expect :refuse
    :reason :nil-vs-empty}])

;; ── Rendering ────────────────────────────────────────────────────────────────────────────

(def ^:private group-titles
  [[:arithmetic "Arithmetic"] [:comparison "Comparison"] [:control "Control flow and truthiness"]
   [:nil "Nil checks"] [:bodies "Bodies and bindings"] [:data "Data and nil"]])

(def ^:private status-text
  {:agree "faithful" :refuse "refused" :diverges "**diverges** (known bug)" :domain "faithful on a domain"})

(defn- cell [s] (str/replace (str s) "|" "\\|"))

(defn- types-text [{:keys [params ret]}]
  (str (if (seq params)
         (str/join ", " (map (fn [[p t]] (str p " : " (pr-str t))) params))
         "—")
       " → " (pr-str ret)))

(defn contract-markdown
  "The contract document, rendered from `rows`. doc/clojure-contract.md must equal this."
  []
  (str/join
   "\n"
   (concat
    ["<!-- Generated by ansatz.clj-contract/contract-markdown; do not edit by hand. -->"
     "<!-- Regenerate: clj -M -e \"(require 'ansatz.clj-contract) (ansatz.clj-contract/write-contract!)\" -->"
     ""
     "# The clojure.core contract of `a/defn` bodies"
     ""
     "An `a/defn` body is Clojure. The invariant Ansatz works toward: every accepted Clojure"
     "spelling computes the value clojure.core computes, on every call where clojure.core returns;"
     "anything else is refused when the definition is elaborated. Proof terms, theorem statements,"
     "tactic arguments and explicit Lean spellings (`Nat.sub`, `HSub.hSub`, `(sub Nat a b)`) keep"
     "their Lean meaning."
     ""
     "Each row below is checked by `test/ansatz/clj_core_conformance_test.clj`: the row's form is"
     "defined with `a/defn` over the stated types, then run against the same form evaluated by"
     "clojure.core on generated inputs (edge values first: 0, 1, negatives, ±0.0, NaN, the empty"
     "list, nil). Calls where clojure.core throws (division by zero, overflow) are outside the"
     "contract."
     ""
     "A row checks one spelling; a definition composes them. `ansatz.clj-check/check-clojure!`"
     "runs the same comparison for a whole `a/defn` (its body evaluated by clojure.core, self-calls"
     "fuel-limited, so a Clojure reading that does not terminate counts as a divergence);"
     "`^:check` on the name runs it when the definition is made, and `deftest-clojure` makes it a"
     "test."
     ""
     "Status:"
     ""
     "- **faithful**: agrees with clojure.core on every returning call."
     "- **refused**: the definition is not accepted."
     "- **diverges**: accepted, and computes a different value. These are known bugs, listed so that"
     "  they are visible; each is checked to still diverge, so a fix has to update this table."
     ""
     "Representation: a `List` is a Clojure sequence and `nil` is the empty list, so `nil` and `()`"
     "are the same value (Clojure distinguishes them only under `=`). An `Option` is `nil` or the"
     "value itself, as Clojure passes it. Only a `some x` whose x itself runs as `nil` (`none`, the"
     "empty list, `Unit`) or is already boxed runs as a box, a value Clojure has no spelling for."
     "Rows marked *(needs …)* use constants the bundled Init does not carry; they run against a"
     "Mathlib store."
     ""
     "Truthiness: Ansatz keeps Lean's semantics and does not model Clojure's truthiness. A test"
     "is a Bool. A nil check is accepted where it means the same as a Lean construct (*Nil"
     "checks*): `if-some` on any Option, `if-let` and `(or o d)` on an Option whose values never"
     "run as `nil` or `false` (numbers, strings, characters, structures and inductives whose every"
     "constructor has fields), `some?`/`nil?` on an Option, `(seq xs)` as a test and `empty?` on a"
     "List. Elsewhere the form is refused with a hint to the explicit test."
     ""
     "Scope: the rules hold in `a/defn` bodies (and the loop helpers hoisted from them). Types,"
     "propositions, theorem statements, tactic terms and `:termination-by` measures keep Lean's"
     "meaning. `a/defn ^:lean name …` opts a definition out, for a body written in Lean style."
     "A namespace declared `(ns ^:ansatz/lean my.model …)` (or with `{:ansatz/lean true}` as its"
     "attribute map) opts out every `a/defn` in it; `^{:lean false}` on a name there opts back in."
     ""]
    (mapcat
     (fn [[g title]]
       (concat
        [(str "## " title) ""
         "| Form | Types | Status | Note |"
         "|---|---|---|---|"]
        (for [r rows :when (= g (:group r))]
          (str "| " (when (:lean? r) "`^:lean` ") "`" (cell (pr-str (:form r))) "` | " (cell (types-text r)) " | "
               (status-text (:expect r))
               (when-let [reason (:reason r)] (str " (`" reason "`)"))
               " | "
               (cell (str (:note r)
                          (when-let [req (seq (:requires r))]
                            (str (when (:note r) " ") "*(needs " (str/join ", " (sort req)) ")*"))))
               " |"))
        [""]))
     group-titles)
    ["## Refusal reasons"
     ""
     "A refused form throws `ex-info` with `{:kind :clj/refused :reason r :form f :hint h}`."
     ""
     "| Reason | Meaning |"
     "|---|---|"]
    (for [[r text] ingest/refusal-reasons]
      (str "| `" r "` | " (cell text) " |"))
    [""])))

(def contract-path "doc/clojure-contract.md")

(defn write-contract!
  "Regenerate doc/clojure-contract.md from the table."
  []
  (spit contract-path (contract-markdown)))
