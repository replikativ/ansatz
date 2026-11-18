(ns ansatz.clj-model.contract
  "The contract of the Clojure model (ansatz.clj-model), as data: each row is a Clojure form over
   parameters drawn from an EDN generator kind. The form is translated into the model and run
   against clojure.core (ansatz.clj-check/run-model-row): wherever the model answers, it must
   agree with clojure.core under a strict `=`; `:max-no-claim` bounds the fraction of returning
   calls where it does not answer. Rendered to doc/clojure-model-contract.md by
   `contract-markdown`; a test keeps the document equal to the rendering.
   Row keys: :id :group :form :params [[sym kind] …] :max-no-claim :note"
  (:require [clojure.string :as str]
            [ansatz.clj-model.translate :as translate]))

(def rows
  [;; ── numbers ────────────────────────────────────────────────────────────────────────
   {:id :add/long :group :numbers :form '(+ a b) :params '[[a :int] [b :int]] :max-no-claim 0.0
    :note "A long result out of range is none: Clojure throws on overflow."}
   {:id :add/num :group :numbers :form '(+ a b) :params '[[a :num] [b :num]] :max-no-claim 0.6
    :note "Mixed long/double is no claim in G1."}
   {:id :add/any :group :numbers :form '(+ a b) :params '[[a :any] [b :any]] :max-no-claim 0.5}
   {:id :add/nary :group :numbers :form '(+ a b c) :params '[[a :int] [b :int] [c :int]] :max-no-claim 0.0}
   {:id :add/unary :group :numbers :form '(+ a) :params '[[a :any]] :max-no-claim 0.0
    :note "(+ x) casts x to Number: (+ nil) is nil."}
   {:id :add/zero :group :numbers :form '(+) :params '[[a :any]] :max-no-claim 0.0}
   {:id :sub/long :group :numbers :form '(- a b) :params '[[a :int] [b :int]] :max-no-claim 0.05
    :note "Boxed `-` negates its second operand first: subtracting Long/MIN_VALUE throws even when the difference fits."}
   {:id :neg/long :group :numbers :form '(- a) :params '[[a :num]] :max-no-claim 0.0
    :note "(- Long/MIN_VALUE) overflows."}
   {:id :mul/long :group :numbers :form '(* a b) :params '[[a :int] [b :int]] :max-no-claim 0.0}
   {:id :mul/double :group :numbers :form '(* a b) :params '[[a :num] [b :num]] :max-no-claim 0.6}
   {:id :inc/num :group :numbers :form '(inc a) :params '[[a :num]] :max-no-claim 0.0}
   {:id :dec/num :group :numbers :form '(dec a) :params '[[a :num]] :max-no-claim 0.0}
   {:id :lt/num :group :numbers :form '(< a b) :params '[[a :num] [b :num]] :max-no-claim 0.6}
   {:id :le/long :group :numbers :form '(<= a b) :params '[[a :int] [b :int]] :max-no-claim 0.0}
   {:id :gt/num :group :numbers :form '(> a b) :params '[[a :num] [b :num]] :max-no-claim 0.6}
   {:id :ge/num :group :numbers :form '(>= a b) :params '[[a :num] [b :num]] :max-no-claim 0.6
    :note "Doubles compare by IEEE: NaN is neither >= nor <."}
   {:id :lt/chain :group :numbers :form '(< a b c) :params '[[a :int] [b :int] [c :any]] :max-no-claim 0.2
    :note "Pairwise with Clojure's short circuit: (< 1 0 \"x\") is false."}
   {:id :lt/unary :group :numbers :form '(< a) :params '[[a :any]] :max-no-claim 0.0
    :note "(< x) is true for any x."}
   {:id :zero/num :group :numbers :form '(zero? a) :params '[[a :num]] :max-no-claim 0.0}
   {:id :pos/num :group :numbers :form '(pos? a) :params '[[a :num]] :max-no-claim 0.0}
   {:id :neg/num :group :numbers :form '(neg? a) :params '[[a :num]] :max-no-claim 0.0}

   ;; ── equality ───────────────────────────────────────────────────────────────────────
   {:id :eq/any :group :equality :form '(= a b) :params '[[a :any] [b :any]] :max-no-claim 0.05
    :note "Numeric category kept ((= 1 1.0) is false); NaN is no claim (a boxed NaN equals itself by identity)."}
   {:id :eq/coll :group :equality :form '(= a b) :params '[[a :coll] [b :coll]] :max-no-claim 0.0
    :note "Sequentials by element ((= [1 2] '(1 2)) is true), maps and sets order-free."}
   {:id :eq/map :group :equality :form '(= a b) :params '[[a :map] [b :map]] :max-no-claim 0.0}
   {:id :eq/self :group :equality :form '(= a a) :params '[[a :any]] :max-no-claim 0.05}
   {:id :eq/chain :group :equality :form '(= a b c) :params '[[a :key] [b :key] [c :key]] :max-no-claim 0.0}
   {:id :neq/any :group :equality :form '(not= a b) :params '[[a :any] [b :any]] :max-no-claim 0.05}

   ;; ── truthiness and control ─────────────────────────────────────────────────────────
   {:id :nil?/any :group :control :form '(nil? a) :params '[[a :any]] :max-no-claim 0.0}
   {:id :some?/any :group :control :form '(some? a) :params '[[a :any]] :max-no-claim 0.0}
   {:id :not/any :group :control :form '(not a) :params '[[a :any]] :max-no-claim 0.0
    :note "Only nil and false are falsey: (not 0), (not \"\") and (not ()) are false."}
   {:id :identity/any :group :control :form '(identity a) :params '[[a :any]] :max-no-claim 0.0}
   {:id :if/any :group :control :form '(if a b c) :params '[[a :any] [b :int] [c :key]] :max-no-claim 0.0}
   {:id :when/any :group :control :form '(when a b) :params '[[a :any] [b :int]] :max-no-claim 0.0}
   {:id :and/any :group :control :form '(and a b) :params '[[a :any] [b :any]] :max-no-claim 0.0}
   {:id :or/any :group :control :form '(or a b) :params '[[a :any] [b :any]] :max-no-claim 0.0}
   {:id :cond/long :group :control :form '(cond (< a b) a (> a b) b :else 0) :params '[[a :int] [b :int]]
    :max-no-claim 0.0}
   {:id :let/long :group :control :form '(let [x (+ a 1)] (* x x)) :params '[[a :int]] :max-no-claim 0.0}
   {:id :thread/map :group :control :form '(-> m (assoc :x 1) (dissoc :a)) :params '[[m :map]]
    :max-no-claim 0.2 :note "A dissoc on a map of 9+ entries is no claim (hash-map order)."}
   {:id :throw/any :group :control :form '(if a (throw (ex-info "no" {})) b) :params '[[a :any] [b :int]]
    :max-no-claim 0.0 :note "throw is no claim."}

   ;; ── types ──────────────────────────────────────────────────────────────────────────
   {:id :string?/any :group :types :form '(string? a) :params '[[a :any]] :max-no-claim 0.0}
   {:id :keyword?/any :group :types :form '(keyword? a) :params '[[a :any]] :max-no-claim 0.0}
   {:id :number?/any :group :types :form '(number? a) :params '[[a :any]] :max-no-claim 0.0}
   {:id :int?/any :group :types :form '(int? a) :params '[[a :any]] :max-no-claim 0.0}
   {:id :map?/any :group :types :form '(map? a) :params '[[a :any]] :max-no-claim 0.0}
   {:id :vector?/any :group :types :form '(vector? a) :params '[[a :any]] :max-no-claim 0.0}

   ;; ── collections ────────────────────────────────────────────────────────────────────
   {:id :get/map :group :collections :form '(get m k) :params '[[m :map] [k :key]] :max-no-claim 0.0}
   {:id :get/any :group :collections :form '(get m k) :params '[[m :any] [k :key]] :max-no-claim 0.1
    :note "get on a string is no claim in G1; on a number it is nil, as in Clojure."}
   {:id :get/default :group :collections :form '(get m k d) :params '[[m :coll] [k :key] [d :int]]
    :max-no-claim 0.1 :note "The default only when the key is absent: (get {:a nil} :a 5) is nil."}
   {:id :get/vector :group :collections :form '(get v i) :params '[[v :coll] [i :int]] :max-no-claim 0.1
    :note "An index outside int range is no claim: Clojure reads it with intValue, which wraps."}
   {:id :kw/get :group :collections :form '(:a m) :params '[[m :any]] :max-no-claim 0.1}
   {:id :kw/default :group :collections :form '(:a m 0) :params '[[m :map]] :max-no-claim 0.0}
   {:id :contains/coll :group :collections :form '(contains? m k) :params '[[m :coll] [k :key]]
    :max-no-claim 0.0}
   {:id :assoc/map :group :collections :form '(assoc m k v) :params '[[m :map] [k :key] [v :int]]
    :max-no-claim 0.0 :note "An existing key keeps its place, a new key goes last."}
   {:id :assoc/coll :group :collections :form '(assoc m 0 v) :params '[[m :coll] [v :int]] :max-no-claim 0.0}
   {:id :assoc/many :group :collections :form '(assoc m :a 1 :b v) :params '[[m :map] [v :any]]
    :max-no-claim 0.0}
   {:id :dissoc/map :group :collections :form '(dissoc m k) :params '[[m :map] [k :key]] :max-no-claim 0.2}
   {:id :count/coll :group :collections :form '(count c) :params '[[c :coll]] :max-no-claim 0.0}
   {:id :count/any :group :collections :form '(count c) :params '[[c :any]] :max-no-claim 0.35
    :note "count of a string is no claim in G1 (Lean counts code points, Java UTF-16 units)."}
   {:id :literal/vector :group :collections :form '[a {:k b} "s" :kw nil] :params '[[a :any] [b :int]]
    :max-no-claim 0.0}
   {:id :literal/quote :group :collections :form ''(1 x [2]) :params '[[a :any]] :max-no-claim 0.0}])

(def group-titles
  [[:numbers "Numbers"] [:equality "Equality"] [:control "Truthiness and control"]
   [:types "Type predicates"] [:collections "Collections"]])

(defn- cell [s] (str/replace (str s) "|" "\\|"))

(defn contract-markdown
  "The model contract document, rendered from `rows`. doc/clojure-model-contract.md must equal this."
  []
  (str/join
   "\n"
   (concat
    ["<!-- Generated by ansatz.clj-model.contract/contract-markdown; do not edit by hand. -->"
     "<!-- Regenerate: clj -M -e \"(require 'ansatz.clj-model.contract) (ansatz.clj-model.contract/write-contract!)\" -->"
     ""
     "# The Clojure model contract"
     ""
     "`(a/foreign ^:model f [x :- T …] R (fn [x …] body))` translates the function's Clojure source"
     "into a kernel model of plain Clojure (`ansatz.clj-model`), so `f` becomes a definition rather"
     "than an axiom. Every model operation returns `Option CljM.V`: `some v` claims that clojure.core"
     "returns a value whose EDN is `v`; `none` claims nothing (clojure.core throws, a long overflows,"
     "or the case is not modelled). The model is strict, so it can only miss values, never invent them."
     ""
     "Each row below is checked by `test/ansatz/clj_model_contract_test.clj`: the form is translated"
     "into the model and run against clojure.core on generated EDN (edge values first: nil, booleans,"
     "`Long/MIN_VALUE`/`MAX_VALUE`, ±0.0, NaN, a non-BMP string, keywords, `()`, `[]`, small maps,"
     "a `hash-map`-built small map, a map over 8 entries, sets, a lazy seq). Verdicts per call:"
     ""
     "- **agree**: the model answers and clojure.core returns the same value under a strict `=`"
     "  (a vector is not a seq, integers and doubles differ, maps and sets are order-free);"
     "- **throws**: the model answers none and clojure.core throws;"
     "- **no claim**: the model answers none and clojure.core returns; the row's *max no-claim*"
     "  bounds their fraction among returning calls;"
     "- **model bug**: the model answers and clojure.core differs or throws. Any one fails the row."
     ""
     "A row checks one form; `ansatz.clj-check/check-model!` runs the same comparison for a"
     "modelled function, and checks conformance on inputs from its declared types."
     ""]
    (mapcat
     (fn [[g title]]
       (concat
        [(str "## " title) ""
         "| Form | Inputs | Max no-claim | Note |"
         "|---|---|---|---|"]
        (for [r rows :when (= g (:group r))]
          (str "| `" (cell (pr-str (:form r))) "` | "
               (cell (str/join ", " (map (fn [[p k]] (str p " : " (name k))) (:params r))))
               " | " (:max-no-claim r) " | " (cell (:note r "")) " |"))
        [""]))
     group-titles)
    ["## Refused forms"
     ""
     "Translation refuses what the model cannot express with `ex-info`"
     "`{:kind :clj/refused :reason r :form f}`."
     ""
     "| Reason | Meaning |"
     "|---|---|"]
    (for [[r text] translate/refusal-reasons]
      (str "| `" r "` | " (cell text) " |"))
    [""])))

(def contract-path "doc/clojure-model-contract.md")

(defn write-contract!
  "Regenerate doc/clojure-model-contract.md from the table."
  []
  (spit contract-path (contract-markdown)))
