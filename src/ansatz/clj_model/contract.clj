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
   {:id :literal/quote :group :collections :form ''(1 x [2]) :params '[[a :any]] :max-no-claim 0.0}

   ;; ── sequences (G2) ─────────────────────────────────────────────────────────────────
   {:id :seq/any :group :sequences :form '(seq c) :params '[[c :seqable]] :max-no-claim 0.1
    :note "A seq over a hash set or a map of 9+ entries is hash-ordered: the model answers with its elements, order unknown."}
   {:id :first/any :group :sequences :form '(first c) :params '[[c :seqable]] :max-no-claim 0.35
    :note "No claim on a hash-ordered collection of 2+ elements."}
   {:id :rest/any :group :sequences :form '(rest c) :params '[[c :seqable]] :max-no-claim 0.4
    :note "(rest [1]) is () (list? true); a seq rested to nothing may be () or an empty lazy seq: no claim."}
   {:id :next/any :group :sequences :form '(next c) :params '[[c :seqable]] :max-no-claim 0.35}
   {:id :second/any :group :sequences :form '(second c) :params '[[c :seqable]] :max-no-claim 0.35}
   {:id :last/ints :group :sequences :form '(last c) :params '[[c :ints]] :max-no-claim 0.3}
   {:id :empty?/any :group :sequences :form '(empty? c) :params '[[c :any]] :max-no-claim 0.05}
   {:id :cons/any :group :sequences :form '(cons x c) :params '[[x :key] [c :seqable]] :max-no-claim 0.1
    :note "(cons x nil) is a list, any other cons a seq."}
   {:id :conj/coll :group :sequences :form '(conj c x) :params '[[c :coll] [x :any]] :max-no-claim 0.15
    :note "Prepends to lists and seqs, appends to vectors, adds to sets; onto a map only nil, a [k v] vector or a map."}
   {:id :conj/many :group :sequences :form '(conj c x y) :params '[[c :coll] [x :key] [y :int]] :max-no-claim 0.15}
   {:id :into/coll :group :sequences :form '(into a b) :params '[[a :coll] [b :seqable]] :max-no-claim 0.45
    :note "Into a vector, list or seq needs the source's order; into a set or a map does not (a map of 2-8 entries needs it again)."}
   {:id :into/xform :group :sequences :form '(into [] (comp (map inc) (filter odd?)) c) :params '[[c :ints]]
    :max-no-claim 0.35 :note "map/filter/remove/keep transducers, and comp of them."}
   {:id :vec/any :group :sequences :form '(vec c) :params '[[c :seqable]] :max-no-claim 0.35}
   {:id :set/any :group :sequences :form '(set c) :params '[[c :seqable]] :max-no-claim 0.1}
   {:id :list/any :group :sequences :form '(list a b) :params '[[a :any] [b :any]] :max-no-claim 0.0}
   {:id :vector/any :group :sequences :form '(vector a b) :params '[[a :any] [b :any]] :max-no-claim 0.0}
   {:id :hash-set/key :group :sequences :form '(hash-set a b) :params '[[a :key] [b :key]] :max-no-claim 0.0}
   {:id :hash-map/nine :group :sequences
    :form '(hash-map :a a :b b :c 3 :d 4 :e 5 :f 6 :g 7 :h 8 :i 9) :params '[[a :any] [b :int]] :max-no-claim 0.05
    :note "hash-map builds a hash map: claimed only with 0 or 9+ entries (a smaller one would leave the model's domain)."}
   {:id :range/one :group :sequences :form '(range n) :params '[[n :int]] :max-no-claim 0.25
    :note "Over 100000 elements is no claim."}
   {:id :range/two :group :sequences :form '(range a b) :params '[[a :int] [b :int]] :max-no-claim 0.35}
   {:id :range/step :group :sequences :form '(range a b s) :params '[[a :int] [b :int] [s :int]] :max-no-claim 0.5
    :note "A zero step is an infinite seq: no claim."}
   {:id :take/any :group :sequences :form '(take n c) :params '[[n :int] [c :seqable]] :max-no-claim 0.35}
   {:id :drop/any :group :sequences :form '(drop n c) :params '[[n :int] [c :seqable]] :max-no-claim 0.45
    :note "Dropping a vector to nothing is () (IDrop); another seq may give () or an empty lazy seq: no claim."}
   {:id :reverse/any :group :sequences :form '(reverse c) :params '[[c :seqable]] :max-no-claim 0.35}
   {:id :nth/any :group :sequences :form '(nth c i) :params '[[c :seqable] [i :int]] :max-no-claim 0.1}
   {:id :nth/default :group :sequences :form '(nth c i :nf) :params '[[c :seqable] [i :int]] :max-no-claim 0.15}
   {:id :concat/any :group :sequences :form '(concat a b) :params '[[a :seqable] [b :seqable]] :max-no-claim 0.15}
   {:id :distinct/ints :group :sequences :form '(distinct c) :params '[[c :ints]] :max-no-claim 0.1}
   {:id :sort/ints :group :sequences :form '(sort c) :params '[[c :ints]] :max-no-claim 0.0
    :note "Of a hash set too: sorting forgets the order."}
   {:id :sort/any :group :sequences :form '(sort c) :params '[[c :seqable]] :max-no-claim 0.6
    :note "compare on longs, BMP strings, simple keywords, chars, booleans, nil; anything else no claim."}
   {:id :sort-keys/map :group :sequences :form '(sort (keys m)) :params '[[m :kmap]] :max-no-claim 0.0
    :note "(first (keys m)) is no claim on a large map; (sort (keys m)) is not."}
   {:id :keys/map :group :sequences :form '(keys m) :params '[[m :kmap]] :max-no-claim 0.0}
   {:id :vals/any :group :sequences :form '(vals m) :params '[[m :any]] :max-no-claim 0.05}
   {:id :frequencies/ints :group :sequences :form '(frequencies c) :params '[[c :ints]] :max-no-claim 0.25}
   {:id :max/num :group :sequences :form '(max a b) :params '[[a :num] [b :num]] :max-no-claim 0.8
    :note "Longs only; a double is no claim."}
   {:id :min/long :group :sequences :form '(min a b c) :params '[[a :int] [b :int] [c :int]] :max-no-claim 0.0}
   {:id :count/string :group :sequences :form '(count s) :params '[[s :string]] :max-no-claim 0.2
    :note "Java counts UTF-16 units: a string outside the BMP is no claim."}
   {:id :seq?/any :group :sequences :form '[(seq? x) (list? x) (set? x) (coll? x) (sequential? x)]
    :params '[[x :any]] :max-no-claim 0.0}
   {:id :preds/any :group :sequences :form '[(boolean? x) (symbol? x) (char? x) (true? x) (false? x) (boolean x)]
    :params '[[x :any]] :max-no-claim 0.0}
   {:id :even?/int :group :sequences :form '[(even? x) (odd? x)] :params '[[x :int]] :max-no-claim 0.0}

   ;; ── maps (G2) ──────────────────────────────────────────────────────────────────────
   {:id :get-in/value :group :maps :form '(get-in m [:a :b]) :params '[[m :value]] :max-no-claim 0.0}
   {:id :get-in/keys :group :maps :form '(get-in m ks) :params '[[m :value] [ks :coll]] :max-no-claim 0.35}
   {:id :get-in/default :group :maps :form '(get-in m [:a k] d) :params '[[m :value] [k :key] [d :int]]
    :max-no-claim 0.1}
   {:id :assoc-in/value :group :maps :form '(assoc-in m [:a :b] v) :params '[[m :value] [v :int]] :max-no-claim 0.1}
   {:id :update/inc :group :maps :form '(update m :a inc) :params '[[m :value]] :max-no-claim 0.1}
   {:id :update/args :group :maps :form '(update m :a + x) :params '[[m :map] [x :int]] :max-no-claim 0.15}
   {:id :update-in/fn :group :maps :form '(update-in m [:a :b] (fn [x] (if (number? x) (inc x) 0)))
    :params '[[m :value]] :max-no-claim 0.1}
   {:id :select-keys/vec :group :maps :form '(select-keys m [:a :b]) :params '[[m :value]] :max-no-claim 0.0}
   {:id :select-keys/any :group :maps :form '(select-keys m ks) :params '[[m :coll] [ks :coll]] :max-no-claim 0.35
    :note "Keys from a hash set give a map of unknown insertion order: no claim for 2-8 entries."}
   {:id :merge/map :group :maps :form '(merge a b) :params '[[a :map] [b :map]] :max-no-claim 0.0}
   {:id :merge/any :group :maps :form '(merge a b c) :params '[[a :coll] [b :value] [c :key]] :max-no-claim 0.2
    :note "(merge) of no truthy argument is nil; (merge 5) is 5."}
   {:id :update-vals/kmap :group :maps :form '(update-vals m inc) :params '[[m :kmap]] :max-no-claim 0.0}
   {:id :into-map/kmap :group :maps :form '(into {} (map (fn [e] [(first e) (* 2 (second e))]) m)) :params '[[m :kmap]]
    :max-no-claim 0.05 :note "Small maps iterate in insertion order, so the rebuilt map has a known order."}
   {:id :reduce-map/kmap :group :maps :form '(reduce (fn [acc e] (+ acc (second e))) 0 m) :params '[[m :kmap]]
    :max-no-claim 0.35 :note "Reducing a map of 9+ entries (a hash map) is no claim: the order may matter."}
   {:id :group-by/ints :group :maps :form '(group-by odd? c) :params '[[c :ints]] :max-no-claim 0.25}
   ;; a hash map never turns back into an array map: shrinking one keeps hash order
   {:id :shrink/dissoc :group :maps :form '(vec (keys (dissoc m :a))) :params '[[m :mixmap]] :max-no-claim 0.6
    :note "dissoc on a map of 9+ entries is no claim: the 8-entry result is still a hash map."}
   {:id :shrink/reduce-dissoc :group :maps :form '(vec (keys (reduce dissoc m [:a :b]))) :params '[[m :mixmap]]
    :max-no-claim 0.6}
   {:id :shrink/fold :group :maps :form '(reduce (fn [acc e] (conj acc (first e))) [] (dissoc m :b))
    :params '[[m :mixmap]] :max-no-claim 0.6}
   {:id :shrink/select-keys :group :maps :form '(vec (keys (select-keys m [:c :a :b]))) :params '[[m :mixmap]]
    :max-no-claim 0.0 :note "select-keys builds from {}: an array map in the order of the keys asked for."}
   {:id :shrink/into-filter :group :maps :form '(vec (keys (into {} (filter (fn [e] (odd? (second e))) m))))
    :params '[[m :mixmap]] :max-no-claim 0.6
    :note "Filtering a hash map gives an array map in hash order: no claim for 2-8 entries."}
   {:id :shrink/update-vals :group :maps :form '(vec (keys (update-vals m inc))) :params '[[m :mixmap]]
    :max-no-claim 0.6 :note "update-vals keeps a hash map a hash map."}
   {:id :shrink/sorted :group :maps :form '(vec (keys (into {} (take 3 (sort-by first m))))) :params '[[m :mixmap]]
    :max-no-claim 0.0 :note "A sorted source has a known order whatever map it came from."}
   {:id :shrink/frequencies :group :maps :form '(vec (keys (frequencies (vals m)))) :params '[[m :mixmap]]
    :max-no-claim 0.6}
   {:id :shrink/merge :group :maps :form '(vec (keys (merge {:z 0} m))) :params '[[m :mixmap]] :max-no-claim 0.6}

   ;; ── functions (G2) ─────────────────────────────────────────────────────────────────
   {:id :map/inc :group :functions :form '(map inc c) :params '[[c :ints]] :max-no-claim 0.05}
   {:id :map/literal :group :functions :form '(map (fn [x] (* x x)) c) :params '[[c :ints]] :max-no-claim 0.05}
   {:id :map/two :group :functions :form '(map + a b) :params '[[a :ints] [b :ints]] :max-no-claim 0.45}
   {:id :mapv/any :group :functions :form '(mapv some? c) :params '[[c :seqable]] :max-no-claim 0.35}
   {:id :filter/odd :group :functions :form '(filter odd? c) :params '[[c :ints]] :max-no-claim 0.0}
   {:id :filterv/any :group :functions :form '(filterv nil? c) :params '[[c :seqable]] :max-no-claim 0.35}
   {:id :remove/any :group :functions :form '(remove nil? c) :params '[[c :seqable]] :max-no-claim 0.1}
   {:id :keep/ints :group :functions :form '(keep (fn [x] (when (odd? x) (* 2 x))) c) :params '[[c :ints]]
    :max-no-claim 0.05}
   {:id :reduce/plus :group :functions :form '(reduce + c) :params '[[c :ints]] :max-no-claim 0.25
    :note "(reduce + []) is (+) = 0; reducing a hash set of 2+ elements is no claim."}
   {:id :reduce/init :group :functions :form '(reduce conj [] c) :params '[[c :seqable]] :max-no-claim 0.35}
   {:id :reduce/literal :group :functions :form '(reduce (fn [a b] (if (< a b) b a)) x c) :params '[[x :int] [c :ints]]
    :max-no-claim 0.25}
   {:id :some/ints :group :functions :form '(some (fn [x] (when (even? x) x)) c) :params '[[c :ints]]
    :max-no-claim 0.1 :note "On a hash set every call must answer and the truthy answers agree."}
   {:id :every/ints :group :functions :form '(every? pos? c) :params '[[c :ints]] :max-no-claim 0.0}
   {:id :not-any/ints :group :functions :form '(not-any? neg? c) :params '[[c :ints]] :max-no-claim 0.0}
   {:id :kw-fn/coll :group :functions :form '(map :a c) :params '[[c :coll]] :max-no-claim 0.15}
   {:id :set-fn/ints :group :functions :form '(filter #{1 2} c) :params '[[c :ints]] :max-no-claim 0.0}
   {:id :map-fn/value :group :functions :form '(m k) :params '[[m :coll] [k :key]] :max-no-claim 0.1
    :note "A map, set or keyword called as a function looks up; a vector indexes (throwing out of range)."}
   {:id :makers/ints :group :functions
    :form '[(map (partial + 1) c) (map (comp inc inc) c) (filter (complement odd?) c) (map (constantly 0) c)
            (map (juxt inc dec) c)]
    :params '[[c :ints]] :max-no-claim 0.05}
   {:id :closure/ints :group :functions :form '(let [f (fn [x] (+ x a))] (map f c)) :params '[[a :int] [c :ints]]
    :max-no-claim 0.05}
   {:id :sort-by/ints :group :functions :form '(sort-by - c) :params '[[c :ints]] :max-no-claim 0.05}
   {:id :sort-by/kw :group :functions :form '(sort-by :a c) :params '[[c :coll]] :max-no-claim 0.6}
   {:id :varargs/literal :group :functions :form '((fn [& xs] xs) a b) :params '[[a :any] [b :any]] :max-no-claim 0.0}
   {:id :arities/literal :group :functions :form '[((fn ([x] x) ([x y] y) ([x y & m] m)) a) ((fn ([x] x) ([x y] y)) a b)]
    :params '[[a :any] [b :any]] :max-no-claim 0.0}
   {:id :case/any :group :functions :form '(case x 1 :one (2 3) :two-three :a :kw "s" :str nil :nil [1] :vec :default)
    :params '[[x :any]] :max-no-claim 0.05 :note "case is hashed-key equality: a double test or value is no claim."}
   {:id :case/no-default :group :functions :form '(case x :a 1 :b 2) :params '[[x :key]] :max-no-claim 0.0
    :note "No match and no default throws."}
   {:id :condp/int :group :functions :form '(condp = x 1 :a 2 :b :c) :params '[[x :any]] :max-no-claim 0.05}

   ;; ── strings (G2) ───────────────────────────────────────────────────────────────────
   {:id :str/any :group :strings :form '(str a b) :params '[[a :any] [b :any]] :max-no-claim 0.6
    :note "str of a double or a collection is no claim (Java's toString)."}
   {:id :str/scalars :group :strings :form '(str a "-" b) :params '[[a :key] [b :int]] :max-no-claim 0.0}
   {:id :subs/one :group :strings :form '(subs s i) :params '[[s :string] [i :int]] :max-no-claim 0.3
    :note "BMP strings only: Java indexes UTF-16 units."}
   {:id :subs/two :group :strings :form '(subs s i j) :params '[[s :string] [i :int] [j :int]] :max-no-claim 0.3}
   {:id :name/any :group :strings :form '(name x) :params '[[x :any]] :max-no-claim 0.05}
   {:id :keyword/any :group :strings :form '(keyword x) :params '[[x :any]] :max-no-claim 0.05}
   {:id :keyword/two :group :strings :form '(keyword a b) :params '[[a :string] [b :string]] :max-no-claim 0.6}
   {:id :join/sep :group :strings :form '(clojure.string/join ", " c) :params '[[c :ints]] :max-no-claim 0.3}
   {:id :join/any :group :strings :form '(clojure.string/join c) :params '[[c :seqable]] :max-no-claim 0.6}
   {:id :blank/any :group :strings :form '(clojure.string/blank? s) :params '[[s :string]] :max-no-claim 0.2}
   {:id :case-conv/string :group :strings
    :form '[(clojure.string/upper-case s) (clojure.string/lower-case s)] :params '[[s :string]] :max-no-claim 0.2
    :note "ASCII only: Java's case mapping is Unicode-aware."}
   ;; ── destructuring (G2b) ─────────────────────────────────────────────────────────────
   {:id :destr/vector :group :destructuring :form '(let [[a b] c] [a b]) :params '[[c :seqable]] :max-no-claim 0.35
    :note "nth with a nil default: a map or a set throws."}
   {:id :destr/rest :group :destructuring :form '(let [[a & r :as all] c] [a r all]) :params '[[c :seqable]]
    :max-no-claim 0.35 :note "With & the pattern reads by seq/first/next, so a small map destructures too."}
   {:id :destr/keys :group :destructuring :form '(let [{:keys [a b] :or {b 5} :as all} m] [a b all])
    :params '[[m :any]] :max-no-claim 0.2
    :note "A seq destructured as a map is keyword arguments (Java interop since 1.11): no claim."}
   {:id :destr/nested :group :destructuring :form '(let [{x :a [y z] :b} m] [x y z]) :params '[[m :value]]
    :max-no-claim 0.2}
   {:id :destr/strs :group :destructuring :form '(let [{:strs [a] :syms [b]} m] [a b]) :params '[[m :coll]]
    :max-no-claim 0.35 :note "Lists and seqs in the input are keyword arguments: no claim."}
   {:id :destr/fn :group :destructuring :form '(map (fn [[k v]] [v k]) m) :params '[[m :kmap]] :max-no-claim 0.05}
   {:id :destr/fn-map :group :destructuring :form '((fn [{:keys [a] :or {a 0}}] (inc a)) m) :params '[[m :value]]
    :max-no-claim 0.05}

   {:id :affix/string :group :strings
    :form '[(clojure.string/starts-with? s t) (clojure.string/ends-with? s t) (clojure.string/includes? s t)]
    :params '[[s :string] [t :string]] :max-no-claim 0.0}

   ;; ── recursion (G3) ──────────────────────────────────────────────────────────────────
   {:id :loop/sum :group :recursion :form '(loop [s (seq c) acc 0] (if s (recur (next s) (+ acc (first s))) acc))
    :params '[[c :ints]] :max-no-claim 0.3 :note "Fuel: the weight of the values in scope. A hash set of 2+ elements is no claim (its order)."}
   {:id :loop/destructure :group :recursion :form '(loop [[x & more] (seq c) acc []] (if x (recur more (conj acc x)) acc))
    :params '[[c :ints]] :max-no-claim 0.3}
   {:id :loop/literal-bound :group :recursion :form '(loop [i 0 acc []] (if (< i 10) (recur (inc i) (conj acc i)) acc))
    :params '[[a :any]] :max-no-claim 0.0 :note "No argument carries the 10: the integer literals of the body count toward the fuel."}
   {:id :loop/scope-bound :group :recursion :form '(loop [i 0 acc 0] (if (< i (count c)) (recur (inc i) (+ acc i)) acc))
    :params '[[c :coll]] :max-no-claim 0.0 :note "Counting up to a bound in scope: the bound's weight counts."}
   {:id :loop/nested :group :recursion
    :form '(loop [s (seq c) acc []] (if s (recur (next s) (conj acc (loop [j (min (max (first s) 0) 5) n 0] (if (pos? j) (recur (dec j) (inc n)) n)))) acc))
    :params '[[c :ints]] :max-no-claim 0.3}
   {:id :self/next :group :recursion :form '((fn len [s] (if (seq s) (inc (len (next s))) 0)) c)
    :params '[[c :seqable]] :max-no-claim 0.35 :note "A non-tail self-call: a JVM frame per level (see the stack stance above)."}
   {:id :self/rest :group :recursion :form '((fn len [s] (if (seq s) (inc (len (rest s))) 0)) c)
    :params '[[c :seqable]] :max-no-claim 0.75
    :note "`rest` of a one-element seq other than a list is no claim (an EmptyList or an empty LazySeq); recur with `next` answers."}
   {:id :self/tree :group :recursion
    :form '((fn walk [t] (cond (map? t) (reduce + 0 (map walk (vals t))) (vector? t) (reduce + 0 (map walk t)) (int? t) t :else 0)) v)
    :params '[[v :value]] :max-no-claim 0.05 :note "Recursion through `map` over nested maps and vectors: depth below the weight."}
   {:id :self/count-down :group :recursion :form '((fn f [n acc] (if (pos? n) (f (dec n) (conj acc n)) acc)) (min n 40) [])
    :params '[[n :int]] :max-no-claim 0.0 :note "An integer counts |i| + 1 toward the weight."}
   {:id :fn/recur :group :recursion :form '((fn [n acc] (if (pos? n) (recur (dec n) (* acc 2)) acc)) (min n 70) 1)
    :params '[[n :int]] :max-no-claim 0.0 :note "Past 62 doublings the long overflows: Clojure throws, the model is none."}
   {:id :fn/multi-arity :group :recursion :form '((fn f ([x] (f x 0)) ([x acc] (if (seq x) (recur (next x) (inc acc)) acc))) c)
    :params '[[c :seqable]] :max-no-claim 0.35 :note "An arity calling another: the arities are one group."}
   {:id :fn/variadic-recur :group :recursion :form '((fn f [acc & xs] (if xs (recur (+ acc (first xs)) (next xs)) acc)) 0 a b c)
    :params '[[a :int] [b :int] [c :int]] :max-no-claim 0.0 :note "recur passes the rest parameter as it is (a seq or nil)."}
   {:id :letfn/even-odd :group :recursion
    :form '(letfn [(ev? [n] (if (zero? n) true (od? (dec n)))) (od? [n] (if (zero? n) false (ev? (dec n))))] [(ev? (count c)) (od? (count c))])
    :params '[[c :coll]] :max-no-claim 0.0 :note "Mutual recursion: one group, one fuel."}
   {:id :hof/recursive-literal :group :recursion
    :form '(map (fn f [n] (if (pos? n) (* n (f (dec n))) 1)) (map (fn [x] (min (max x 0) 20)) c))
    :params '[[c :ints]] :max-no-claim 0.1 :note "A recursive fn literal passed to a higher-order function."}])

(def group-titles
  [[:numbers "Numbers"] [:equality "Equality"] [:control "Truthiness and control"]
   [:types "Type predicates"] [:collections "Collections"] [:sequences "Sequences"] [:maps "Maps"]
   [:functions "Functions"] [:strings "Strings"] [:destructuring "Destructuring"] [:recursion "Recursion"]])

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
     "Iteration order. A map of at most 8 entries is a Clojure array map and iterates in insertion"
     "order, which the model tracks. A larger map or any set iterates in hash order, which it does"
     "not: a seq over one is marked unordered (compared below as a multiset), and order-sensitive"
     "uses of it (`first`, `nth`, `reduce`, `vec`, `str`, a small map built from it) answer none."
     "A small hash map (from `hash-map`, or `dissoc` on a large map) is outside the model's domain;"
     "the rows skip inputs that contain one."
     ""
     "Functions are a second sort `CljM.V → … → Option CljM.V`: fn literals, core functions,"
     "`partial`, `comp`, `complement`, `constantly`, `juxt`, keywords, maps and sets may be called or"
     "passed to a modelled higher-order function; a function returned or stored is refused."
     ""
     "Recursion. Self-calls, `loop`/`recur`, `letfn` and mutually recursive `a/defmodel` functions"
     "are a group run by a fixpoint on a Nat fuel that bounds the depth of nested calls; out of fuel"
     "is no claim. The default fuel of an entry is 1 + the weight of its arguments and of every value"
     "in scope + the magnitudes of the integer literals in the group's bodies, where the weight counts"
     "the nodes of a value, an integer as |i| + 1 and a string as its length + 1. So recursion that"
     "walks into a collection, shortens a string, counts an integer toward 0, or counts up to a bound"
     "in scope or in the source is never cut short; other recursion (Collatz, growing arguments) can"
     "be, and `^{:fuel form}` on the fn name or the loop's binding vector sets the fuel instead."
     ""
     "Stack. The claim is what Clojure returns given enough stack and heap. `loop`/`recur` run in"
     "constant stack, so their claims hold on any stack; a non-tail self-call takes a JVM frame per"
     "level, so an input deep enough (around 10^4 levels on a default thread stack) throws"
     "StackOverflowError where the model answers. The checks below count such a call as *resource*,"
     "neither agreement nor a model bug."
     ""
     "Calls of other functions: an `a/defmodel` function is modelled from its source (each strongly"
     "connected group once); an `a/defn` over Nat, Int, Bool, String or Float is called through the"
     "boundary codecs; any other function is an opaque axiom `V → … → Option V`, which assumes it is"
     "pure and is listed by `a/trust-report`."
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
     "- **model bug**: the model answers and clojure.core differs or throws. Any one fails the row;"
     "- **resource**: the model answers and clojure.core runs out of stack or heap (see above)."
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
