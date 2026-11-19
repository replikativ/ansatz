(ns ansatz.clj-model.colls
  "The G2 part of the Clojure model (ansatz.clj-model): sequences, maps, sets, higher-order
   functions and strings, each `CljM.V… → Option CljM.V` with `none` = no claim.

   Iteration order. A map of at most 8 entries is a Clojure array map: it iterates in insertion
   order, which is the order of its entry chain (assoc keeps an existing key's place and puts a
   new key last, as PersistentArrayMap does). A larger map is a hash map and a set is a hash set:
   they iterate in hash order, which the model does not know. A seq over a hash-ordered
   collection of 2+ elements is `vlseq false …` (tainted). Order-sensitive uses of a tainted
   seq (first, nth, reduce, vec, a vector or list built from it, str, `=` against a sequential)
   are none; order-free uses (count, empty?, set, sort, every?, frequencies, into a set) answer.
   A map built from a tainted source has an unknown insertion order: with 2 to 8 entries it is
   none (it would be an array map whose order the model cannot state).
   `hash-map` builds a hash map, so it answers only with 0 or 9+ entries. A small hash map
   passed in from outside is outside the model's domain (the Value boundary passes array maps).

   Functions. A function argument has the model's second sort `CljM.V → … → Option CljM.V`
   (curried); the translator builds it from a fn literal, a core function, a keyword, or a
   value invoked as a function (`CljM.invoke`).

   Strings. Lean counts code points, Java UTF-16 units: string ops that index or count answer
   only for strings in the Basic Multilingual Plane; case conversion and blank? only for ASCII.
   Sorting compares longs, strings, simple keywords, chars, booleans and nil (Clojure's
   `compare`); any other comparison is none, so ties are always between identical values."
  (:require [ansatz.clj-model :as m :refer [c vm defm bindV bindB someV boolV OV OB OOV noneV noneB someT someF]]))

(def ^:private F1 '(=> CljM.V (Option CljM.V)))
(def ^:private F2 '(=> CljM.V (=> CljM.V (Option CljM.V))))
(def ^:private OS '(Option String))
(def ^:private OI '(Option Int))
(def ^:private LC '(List Char))
(def ^:private vnil* (c 'vnil))
(def ^:private noneS (m/none-of 'String))
(def ^:private noneI (m/none-of 'Int))

(defn- bindS [x [v] body] (list 'Option.bind x (list 'fn [v :- 'String] body)))
(defn- bindI [x [v] body] (list 'Option.bind x (list 'fn [v :- 'Int] body)))
(defn- vcons* [h t] (c 'vcons h t))
(defn- lmatch
  "`(match xs (List Char) ret (nil n) (cons [h t] k))`."
  [xs ret n [h t] k]
  (list 'match xs LC ret (list 'nil n) (list 'cons [h t] k)))
(defn- chain-fold
  "A def recursing over the chain `cs`: `nil-body` at its end, `cons-body` (over h t) at a cell."
  [nm params ret nil-body cons-body]
  (defm nm params ret (vm 'cs ret nil-body {'vcons [['h 't] cons-body]})))

;; ── Strings as lists of code points ─────────────────────────────────────────────────────

(def ^:private string-forms
  [(defm 'CljM.noChars [] LC (list (symbol "@List.nil") 'Char))
   (defm 'CljM.charsC [['cs LC]] 'CljM.V (lmatch 'cs 'CljM.V vnil* '[h t] (vcons* (c 'vchar 'h) '(CljM.charsC t))))
   (defm 'CljM.strLt [['a LC] ['b LC]] 'Bool
     (lmatch 'a 'Bool (lmatch 'b 'Bool false '[h t] true) '[h t]
             (lmatch 'b 'Bool false '[h2 t2]
                     '(if (< (Char.toNat h) (Char.toNat h2)) true
                          (if (== (Char.toNat h) (Char.toNat h2)) (CljM.strLt t t2) false)))))
   (defm 'CljM.prefixL [['a LC] ['b LC]] 'Bool
     (lmatch 'a 'Bool true '[h t] (lmatch 'b 'Bool false '[h2 t2] '(if (== h h2) (CljM.prefixL t t2) false))))
   (defm 'CljM.infixL [['a LC] ['b LC]] 'Bool
     (lmatch 'b 'Bool '(CljM.prefixL a CljM.noChars) '[h t] '(if (CljM.prefixL a (List.cons h t)) true (CljM.infixL a t))))
   (defm 'CljM.asciiL [['a LC]] 'Bool (lmatch 'a 'Bool true '[h t] '(Bool.and (< (Char.toNat h) 128) (CljM.asciiL t))))
   (defm 'CljM.slashes [['a LC]] 'Nat (lmatch 'a 'Nat 0 '[h t] '(if (== (Char.toNat h) 47) (+ 1 (CljM.slashes t)) (CljM.slashes t))))
   (defm 'CljM.afterSlash [['a LC]] LC (lmatch 'a LC 'CljM.noChars '[h t] '(if (== (Char.toNat h) 47) t (CljM.afterSlash t))))
   (defm 'CljM.beforeSlash [['a LC]] LC (lmatch 'a LC 'CljM.noChars '[h t] '(if (== (Char.toNat h) 47) CljM.noChars (List.cons h (CljM.beforeSlash t)))))
   ;; Character/isWhitespace on ASCII: \t \n \u000B \f \r, the separators \u001C-\u001F, space
   (defm 'CljM.blankL [['a LC]] 'Bool
     (lmatch 'a 'Bool true '[h t] '(Bool.and (Bool.or (Bool.and (<= 9 (Char.toNat h)) (<= (Char.toNat h) 13))
                                                      (Bool.and (<= 28 (Char.toNat h)) (<= (Char.toNat h) 32)))
                                             (CljM.blankL t))))
   (defm 'CljM.upperL [['a LC]] LC
     (lmatch 'a LC 'CljM.noChars '[h t]
             '(List.cons (if (Bool.and (<= 97 (Char.toNat h)) (<= (Char.toNat h) 122)) (Char.ofNat (- (Char.toNat h) 32)) h)
                         (CljM.upperL t))))
   (defm 'CljM.lowerL [['a LC]] LC
     (lmatch 'a LC 'CljM.noChars '[h t]
             '(List.cons (if (Bool.and (<= 65 (Char.toNat h)) (<= (Char.toNat h) 90)) (Char.ofNat (+ (Char.toNat h) 32)) h)
                         (CljM.lowerL t))))
   ;; a keyword/symbol string "ns/name" or "name" that Clojure splits the same way: no slash, or
   ;; one slash with a non-empty namespace and name
   (defm 'CljM.simpleName '[[s String]] 'Bool
     '(if (== (CljM.slashes (String.toList s)) 0) true
          (Bool.and (== (CljM.slashes (String.toList s)) 1)
                    (Bool.and (< 0 (List.length (CljM.beforeSlash (String.toList s))))
                              (< 0 (List.length (CljM.afterSlash (String.toList s))))))))
   (defm 'CljM.strOf '[[v CljM.V]] OS (vm 'v OS noneS {'vstr [['s] '(Option.some s)]}))
   (defm 'CljM.longOf '[[v CljM.V]] OI (vm 'v OI noneI {'vlong [['i] '(Option.some i)]}))
   (defm 'CljM.intOf '[[v CljM.V]] OI (vm 'v OI noneI {'vlong [['i] (list 'if '(CljM.inInt i) '(Option.some i) noneI)]}))
   (defm 'CljM.bmpStrOf '[[v CljM.V]] OS
     (vm 'v OS noneS {'vstr [['s] (list 'if '(CljM.bmpL (String.toList s)) '(Option.some s) noneS)]}))])

;; ── Element chains, order, construction ─────────────────────────────────────────────────

(def ^:private seq-forms
  [(defm 'CljM.entriesC '[[e CljM.V]] 'CljM.V
     (vm 'e 'CljM.V vnil* {'ventry [['k 'w 'r] (vcons* (c 'vvec (vcons* 'k (vcons* 'w vnil*))) '(CljM.entriesC r))]}))
   (defm 'CljM.keysC '[[e CljM.V]] 'CljM.V (vm 'e 'CljM.V vnil* {'ventry [['k 'w 'r] (vcons* 'k '(CljM.keysC r))]}))
   (defm 'CljM.valsC '[[e CljM.V]] 'CljM.V (vm 'e 'CljM.V vnil* {'ventry [['k 'w 'r] (vcons* 'w '(CljM.valsC r))]}))
   ;; the elements of a seqable value, in its iteration order where known; none if not seqable
   (defm 'CljM.elems '[[v CljM.V]] OV
     (vm 'v OV noneV {'vnil [[] (someV vnil*)] 'vlist [['it] (someV 'it)] 'vlseq [['o 'it] (someV 'it)]
                      'vvec [['it] (someV 'it)] 'vmap [['e] (someV '(CljM.entriesC e))] 'vset [['it] (someV 'it)]
                      'vstr [['s] (list 'if '(CljM.bmpL (String.toList s)) (someV '(CljM.charsC (String.toList s))) noneV)]}))
   ;; is the iteration order known? (a hash map or hash set of 2+ elements, or a tainted seq: no)
   (defm 'CljM.ord '[[v CljM.V]] 'Bool
     (vm 'v 'Bool true {'vlseq [['o 'it] 'o] 'vmap [['e] '(<= (CljM.clen e) 8)] 'vset [['it] '(<= (CljM.clen it) 1)]}))
   (defm 'CljM.oelems '[[v CljM.V]] OV (list 'if '(CljM.ord v) '(CljM.elems v) noneV))
   ;; a sequential's elements (nth works on it): nil, list, vector, ordered seq, BMP string
   (defm 'CljM.selems '[[v CljM.V]] OV
     (vm 'v OV noneV {'vnil [[] (someV vnil*)] 'vlist [['it] (someV 'it)] 'vvec [['it] (someV 'it)]
                      'vlseq [['o 'it] (list 'if 'o (someV 'it) noneV)]
                      'vstr [['s] '(CljM.elems (CljM.V.vstr s))]}))
   (defm 'CljM.mkSeq '[[o Bool] [it CljM.V]] 'CljM.V (c 'vlseq '(Bool.or o (<= (CljM.clen it) 1)) 'it))
   (defm 'CljM.allOrd '[[cs CljM.V]] 'Bool (vm 'cs 'Bool true {'vcons [['h 't] '(Bool.and (CljM.ord h) (CljM.allOrd t))]}))
   (defm 'CljM.appendC '[[a CljM.V] [b CljM.V]] 'CljM.V (vm 'a 'CljM.V 'b {'vcons [['h 't] (vcons* 'h '(CljM.appendC t b))]}))
   (defm 'CljM.revC '[[a CljM.V] [acc CljM.V]] 'CljM.V (vm 'a 'CljM.V 'acc {'vcons [['h 't] (list 'CljM.revC 't (vcons* 'h 'acc))]}))
   (defm 'CljM.lastC '[[a CljM.V]] 'CljM.V
     (vm 'a 'CljM.V vnil* {'vcons [['h 't] (list 'if '(CljM.isNil t) 'h '(CljM.lastC t))]}))
   (defm 'CljM.takeC '[[n Nat] [cs CljM.V]] 'CljM.V
     (list 'match 'n 'Nat 'CljM.V (list 'zero vnil*)
           (list 'succ '[j] (vm 'cs 'CljM.V vnil* {'vcons [['h 't] (vcons* 'h '(CljM.takeC j t))]}))))
   (defm 'CljM.dropC '[[n Nat] [cs CljM.V]] 'CljM.V
     (list 'match 'n 'Nat 'CljM.V '(zero cs) (list 'succ '[j] '(CljM.dropC j (CljM.tl cs)))))
   (defm 'CljM.rangeC '[[i Int] [step Int] [n Nat]] 'CljM.V
     (list 'match 'n 'Nat 'CljM.V (list 'zero vnil*) (list 'succ '[j] (vcons* (c 'vlong 'i) '(CljM.rangeC (+ i step) step j)))))
   ;; membership by hashed-key equivalence (as a hash set / map lookup): none = undecided
   (chain-fold 'CljM.memC '[[x CljM.V] [cs CljM.V]] OB someF
               (bindB '(CljM.keq x h) ['q] (list 'if 'q someT '(CljM.memC x t))))
   ;; first occurrences, by hashed-key equivalence
   (defm 'CljM.dedupC '[[cs CljM.V] [seen CljM.V]] OV
     (vm 'cs OV (someV vnil*)
         {'vcons [['h 't] (bindB '(CljM.memC h seen) ['q]
                                 (list 'if 'q '(CljM.dedupC t seen)
                                       (bindV '(CljM.dedupC t (CljM.V.vcons h seen)) ['r] (someV (vcons* 'h 'r)))))]}))
   ;; dedupe a chain whose order may be unknown: only when there are no duplicates (which
   ;; duplicate survives would depend on the order)
   (defm 'CljM.dedupO '[[o Bool] [cs CljM.V]] OV
     (bindV '(CljM.dedupC cs CljM.V.vnil) ['r]
            (list 'if '(Bool.or o (== (CljM.clen r) (CljM.clen cs))) (someV 'r) noneV)))
   ;; map entries built from a source of order `o`: an array map (2-8 entries) needs a known order
   (defm 'CljM.mapOk '[[o Bool] [e CljM.V]] OV
     (list 'if '(Bool.or o (Bool.or (<= (CljM.clen e) 1) (<= 9 (CljM.clen e)))) (someV (c 'vmap 'e)) noneV))
   ;; structural equality of scalars (false for anything else): agreement of unordered results
   (defm 'CljM.same '[[a CljM.V] [b CljM.V]] 'Bool
     (vm 'a 'Bool false {'vnil [[] '(CljM.isNil b)]
                         'vbool [['x] '(Option.getD (CljM.eqBool x b) false)]
                         'vlong [['i] '(Option.getD (CljM.eqLong i b) false)]
                         'vchar [['x] '(Option.getD (CljM.eqChar x b) false)]
                         'vstr [['s] '(Option.getD (CljM.eqStr s b) false)]
                         'vkw [['s] '(Option.getD (CljM.eqKw s b) false)]
                         'vsym [['s] '(Option.getD (CljM.eqSym s b) false)]}))])

;; ── seq, first, rest, … ─────────────────────────────────────────────────────────────────

(def ^:private access-forms
  [(defm 'CljM.seq '[[v CljM.V]] OV
     (bindV '(CljM.elems v) ['it]
            (list 'if '(CljM.isNil it) (someV vnil*)
                  (vm 'v OV (someV '(CljM.mkSeq (CljM.ord v) it)) {'vlist [['x] (someV 'v)]}))))
   (defm 'CljM.first '[[v CljM.V]] OV (bindV '(CljM.oelems v) ['it] (someV '(CljM.hd it))))
   ;; rest: () when nothing is left, except after a seq whose last element remains (a lazy seq
   ;; rests to an empty lazy seq, a chunked seq or range to ()): no claim
   (defm 'CljM.rest '[[v CljM.V]] OV
     (bindV '(CljM.oelems v) ['it]
            (list 'if '(<= (CljM.clen it) 1)
                  (vm 'v OV (someV (c 'vlist vnil*))
                      {'vlseq [['o 'x] (list 'if '(CljM.isNil it) (someV (c 'vlist vnil*)) noneV)]})
                  (vm 'v OV (someV (c 'vlseq true '(CljM.tl it))) {'vlist [['x] (someV (c 'vlist '(CljM.tl it)))]}))))
   (defm 'CljM.next '[[v CljM.V]] OV
     (bindV '(CljM.oelems v) ['it]
            (list 'if '(<= (CljM.clen it) 1) (someV vnil*)
                  (vm 'v OV (someV (c 'vlseq true '(CljM.tl it))) {'vlist [['x] (someV (c 'vlist '(CljM.tl it)))]}))))
   (defm 'CljM.second '[[v CljM.V]] OV (bindV '(CljM.oelems v) ['it] (someV '(CljM.hd (CljM.tl it)))))
   (defm 'CljM.last '[[v CljM.V]] OV (bindV '(CljM.oelems v) ['it] (someV '(CljM.lastC it))))
   (defm 'CljM.emptyQ '[[v CljM.V]] OV (bindV '(CljM.elems v) ['it] (boolV '(CljM.isNil it))))
   ;; nth: an index is read as an int (no claim outside int range or for a double); maps and
   ;; sets throw; nil gives nil (or the default)
   (defm 'CljM.nthAt ['[it CljM.V] '[k CljM.V] ['d OV]] OV
     (vm 'k OV noneV {'vlong [['i] (list 'if '(CljM.inInt i)
                                         (list 'if '(Bool.and (<= 0 i) (< i (Int.ofNat (CljM.clen it))))
                                               (someV '(CljM.cnth it (Int.toNat i))) 'd)
                                         noneV)]}))
   (defm 'CljM.nth '[[v CljM.V] [k CljM.V]] OV
     (vm 'v OV (bindV '(CljM.selems v) ['it] (list 'CljM.nthAt 'it 'k noneV))
         {'vnil [[] (vm 'k OV noneV {'vlong [['i] (list 'if '(CljM.inInt i) (someV vnil*) noneV)]})]}))
   ;; with a default, a negative index is the default whatever the collection (RT.nthFrom)
   (defm 'CljM.nth3 '[[v CljM.V] [k CljM.V] [d CljM.V]] OV
     (list 'if '(Option.getD (Option.map (fn [i :- Int] (Bool.and (CljM.inInt i) (< i 0))) (CljM.longOf k)) false) (someV 'd)
           (vm 'v OV (bindV '(CljM.selems v) ['it] '(CljM.nthAt it k (Option.some d)))
               {'vnil [[] (vm 'k OV noneV {'vlong [['i] (list 'if '(CljM.inInt i) (someV 'd) noneV)]})]})))
   (defm 'CljM.cons '[[x CljM.V] [v CljM.V]] OV
     (vm 'v OV (bindV '(CljM.elems v) ['it] (someV '(CljM.mkSeq (CljM.ord v) (CljM.V.vcons x it))))
         {'vnil [[] (someV (c 'vlist (vcons* 'x vnil*)))]}))
   (defm 'CljM.vec '[[v CljM.V]] OV (bindV '(CljM.oelems v) ['it] (someV (c 'vvec 'it))))
   (defm 'CljM.set '[[v CljM.V]] OV (bindV '(CljM.elems v) ['it] (bindV '(CljM.dedupO (CljM.ord v) it) ['r] (someV (c 'vset 'r)))))
   (defm 'CljM.reverse '[[v CljM.V]] OV (bindV '(CljM.oelems v) ['it] (someV (c 'vlist '(CljM.revC it CljM.V.vnil)))))
   ;; keys/vals of any empty seqable are nil; of a non-empty non-map they throw
   (defm 'CljM.keys '[[m CljM.V]] OV
     (vm 'm OV (bindV '(CljM.elems m) ['it] (list 'if '(CljM.isNil it) (someV vnil*) noneV))
         {'vmap [['e] (list 'if '(CljM.isNil e) (someV vnil*) (someV '(CljM.mkSeq (<= (CljM.clen e) 8) (CljM.keysC e))))]}))
   (defm 'CljM.vals '[[m CljM.V]] OV
     (vm 'm OV (bindV '(CljM.elems m) ['it] (list 'if '(CljM.isNil it) (someV vnil*) noneV))
         {'vmap [['e] (list 'if '(CljM.isNil e) (someV vnil*) (someV '(CljM.mkSeq (<= (CljM.clen e) 8) (CljM.valsC e))))]}))
   ;; take/drop: lazy seqs; of a hash-ordered seq only the whole or nothing is known.
   ;; drop on a vector (clojure.lang.IDrop) is () when nothing remains; on another seq it may
   ;; be () or an empty lazy seq: no claim
   (defm 'CljM.take '[[n CljM.V] [v CljM.V]] OV
     (bindI '(CljM.longOf n) ['i]
            (bindV '(CljM.elems v) ['it]
                   (list 'if '(<= i 0) (someV (c 'vlseq true vnil*))
                         (list 'if '(<= (Int.ofNat (CljM.clen it)) i) (someV '(CljM.mkSeq (CljM.ord v) it))
                               (list 'if '(CljM.ord v) (someV (c 'vlseq true '(CljM.takeC (Int.toNat i) it))) noneV))))))
   (defm 'CljM.drop '[[n CljM.V] [v CljM.V]] OV
     ;; IDrop takes an int: a count outside int range throws there (no claim anywhere)
     (bindI '(CljM.intOf n) ['i]
            (bindV '(CljM.elems v) ['it]
                   (bindV (list 'if '(<= i 0) (someV '(CljM.mkSeq (CljM.ord v) it))
                                (list 'if '(<= (Int.ofNat (CljM.clen it)) i) (someV (c 'vlseq true vnil*))
                                      (list 'if '(CljM.ord v) (someV (c 'vlseq true '(CljM.dropC (Int.toNat i) it))) noneV)))
                          ['r]
                          (list 'if '(CljM.isNil (CljM.items r))
                                (vm 'v OV (someV 'r) {'vvec [['x] (someV (c 'vlist vnil*))] 'vlseq [['o 'x] noneV]
                                                      'vmap [['e] (list 'if '(<= (CljM.clen e) 8) (someV (c 'vlist vnil*)) (someV 'r))]})
                                (someV 'r))))))
   (defm 'CljM.rangeN '[[i Int] [j Int] [k Int]] 'Nat
     '(Nat.div (+ (Int.natAbs (- j i)) (- (Int.natAbs k) 1)) (Int.natAbs k)))
   (defm 'CljM.range '[[a CljM.V] [b CljM.V] [s CljM.V]] OV
     (bindI '(CljM.longOf a) ['i]
            (bindI '(CljM.longOf b) ['j]
                   (bindI '(CljM.longOf s) ['k]
                          (list 'if '(== k 0) noneV
                                (list 'if '(Bool.or (Bool.and (< 0 k) (<= j i)) (Bool.and (< k 0) (<= i j))) (someV (c 'vlist vnil*))
                                      ;; count = ceil(|j - i| / |k|)
                                      (list 'if '(< 100000 (CljM.rangeN i j k)) noneV
                                            (someV (c 'vlseq true '(CljM.rangeC i k (CljM.rangeN i j k)))))))))))])

;; ── conj, into, merge, maps ─────────────────────────────────────────────────────────────

(def ^:private build-forms
  [(defm 'CljM.assocAll '[[m CljM.V] [e CljM.V]] OV
     (vm 'e OV (someV 'm) {'ventry [['k 'w 'r] (bindV '(CljM.assoc m k w) ['m2] '(CljM.assocAll m2 r))]}))
   (defm 'CljM.conj1 '[[v CljM.V] [x CljM.V]] OV
     (vm 'v OV noneV
         {'vnil [[] (someV (c 'vlist (vcons* 'x vnil*)))]
          'vlist [['it] (someV (c 'vlist (vcons* 'x 'it)))]
          'vlseq [['o 'it] (someV '(CljM.mkSeq o (CljM.V.vcons x it)))]
          'vvec [['it] (someV (c 'vvec '(CljM.appendC it (CljM.V.vcons x CljM.V.vnil))))]
          'vset [['it] (bindB '(CljM.memC x it) ['q] (list 'if 'q (someV 'v) (someV (c 'vset '(CljM.appendC it (CljM.V.vcons x CljM.V.vnil))))))]
          ;; onto a map: nil, a [k v] vector, or a map
          'vmap [['e] (vm 'x OV noneV
                          {'vnil [[] (someV 'v)]
                           'vvec [['it] (list 'if '(== (CljM.clen it) 2) '(CljM.assoc v (CljM.hd it) (CljM.hd (CljM.tl it))) noneV)]
                           'vmap [['e2] '(CljM.assocAll v e2)]})]}))
   (chain-fold 'CljM.conjC '[[v CljM.V] [cs CljM.V]] OV (someV 'v) (bindV '(CljM.conj1 v h) ['v2] '(CljM.conjC v2 t)))
   ;; the keys of a chain of [k v] vectors are pairwise distinct (none: not pairs, or undecided)
   (chain-fold 'CljM.pairKeys '[[cs CljM.V]] OV (someV vnil*)
               (vm 'h OV noneV {'vvec [['it] (list 'if '(== (CljM.clen it) 2)
                                                   (bindV '(CljM.pairKeys t) ['r] (someV (vcons* '(CljM.hd it) 'r))) noneV)]}))
   (defm 'CljM.into '[[to CljM.V] [from CljM.V]] OV
     (bindV '(CljM.elems from) ['it]
            (list 'if '(CljM.ord from) '(CljM.conjC to it)
                  (vm 'to OV noneV
                      {'vset [['e] (bindV '(CljM.dedupO false it) ['u] '(CljM.conjC to u))]
                       'vmap [['e] (bindV '(CljM.pairKeys it) ['ks] (bindV '(CljM.dedupO false ks) ['u]
                                                                           (bindV '(CljM.conjC to it) ['r] '(CljM.mapOk false (CljM.items r)))))]}))))
   (chain-fold 'CljM.anyTruthy '[[cs CljM.V]] 'Bool false '(Bool.or (CljM.truthy h) (CljM.anyTruthy t)))
   (chain-fold 'CljM.mergeC '[[acc CljM.V] [cs CljM.V]] OV (someV 'acc)
               (bindV (list 'CljM.conj1 (list 'if '(CljM.truthy acc) 'acc (c 'vmap vnil*)) 'h) ['a2] '(CljM.mergeC a2 t)))
   ;; (merge & maps): nil when no argument is truthy, else conj each onto the first (or {})
   (defm 'CljM.merge '[[args CljM.V]] OV
     (list 'if '(CljM.anyTruthy args) (vm 'args OV (someV vnil*) {'vcons [['h 't] '(CljM.mergeC h t)]}) (someV vnil*)))
   ;; (hash-map …) builds a hash map: claimed only when its order is never observed as an array map's
   (defm 'CljM.hashMapOk '[[m CljM.V]] OV
     (vm 'm OV noneV {'vmap [['e] (list 'if '(Bool.or (CljM.isNil e) (<= 9 (CljM.clen e))) (someV 'm) noneV)]}))
   (defm 'CljM.hashSet '[[args CljM.V]] OV (bindV '(CljM.dedupC args CljM.V.vnil) ['r] (someV (c 'vset 'r))))
   ;; RT.find: the entry of key k as a one-cell entry chain, vnil when absent
   (defm 'CljM.findEC '[[k CljM.V] [e CljM.V]] OV
     (vm 'e OV noneV {'vnil [[] (someV vnil*)]
                      'ventry [['k2 'w 'r] (bindB '(CljM.keq k k2) ['q]
                                                  (list 'if 'q (someV (c 'ventry 'k2 'w vnil*)) '(CljM.findEC k r)))]}))
   (defm 'CljM.findE '[[m CljM.V] [k CljM.V]] OV
     (vm 'm OV noneV
         {'vnil [[] (someV vnil*)]
          'vmap [['e] '(CljM.findEC k e)]
          'vvec [['it] (vm 'k OV (someV vnil*)
                           {'vlong [['i] (list 'if '(CljM.inInt i)
                                               (list 'if '(Bool.and (<= 0 i) (< i (Int.ofNat (CljM.clen it))))
                                                     (someV (c 'ventry 'k '(CljM.cnth it (Int.toNat i)) vnil*)) (someV vnil*))
                                               noneV)]})]}))
   (chain-fold 'CljM.selC '[[m CljM.V] [cs CljM.V] [acc CljM.V]] OV (someV 'acc)
               (bindV '(CljM.findE m h) ['e]
                      (vm 'e OV noneV {'vnil [[] '(CljM.selC m t acc)]
                                       'ventry [['k 'w 'r] (bindV '(CljM.assocC k w acc) ['a2] '(CljM.selC m t a2))]})))
   (defm 'CljM.selectKeys '[[m CljM.V] [ks CljM.V]] OV
     (bindV '(CljM.elems ks) ['it] (bindV '(CljM.selC m it CljM.V.vnil) ['e] '(CljM.mapOk (CljM.ord ks) e))))
   (chain-fold 'CljM.getInC '[[m CljM.V] [cs CljM.V]] OV (someV 'm) (bindV '(CljM.get m h) ['x] '(CljM.getInC x t)))
   (defm 'CljM.getIn '[[m CljM.V] [ks CljM.V]] OV (bindV '(CljM.oelems ks) ['it] '(CljM.getInC m it)))
;; does (get m k) find k? (as a V boolean; none where get's answer is not modelled)
   (defm 'CljM.has '[[m CljM.V] [k CljM.V]] OV
     (vm 'm OV (boolV false) {'vmap [['e] '(CljM.containsQ m k)] 'vset [['e] '(CljM.containsQ m k)]
                              'vvec [['it] '(CljM.containsQ m k)]
                              'vstr [['s] (vm 'k OV (boolV false) {'vlong [['i] noneV] 'vdouble [['f] noneV]})]
                              'vcons [['h 't] noneV] 'ventry [['x 'y 'z] noneV]}))
   ;; get-in with a default: the default as soon as a key is absent
   (chain-fold 'CljM.getInD '[[m CljM.V] [cs CljM.V] [d CljM.V]] OV (someV 'm)
               (bindV '(CljM.has m h) ['p]
                      (list 'if '(CljM.truthy p) (bindV '(CljM.get m h) ['x] '(CljM.getInD x t d)) (someV 'd))))
   (defm 'CljM.getIn3 '[[m CljM.V] [ks CljM.V] [d CljM.V]] OV (bindV '(CljM.oelems ks) ['it] '(CljM.getInD m it d)))
   ;; assoc-in / update-in destructure [k & ks] (nth): ks must be sequential
   (chain-fold 'CljM.assocInC '[[m CljM.V] [k CljM.V] [cs CljM.V] [v CljM.V]] OV '(CljM.assoc m k v)
               (bindV '(CljM.get m k) ['x] (bindV '(CljM.assocInC x h t v) ['r] '(CljM.assoc m k r))))
   (defm 'CljM.assocIn '[[m CljM.V] [ks CljM.V] [v CljM.V]] OV
     (bindV '(CljM.selems ks) ['it] (vm 'it OV '(CljM.assoc m CljM.V.vnil v) {'vcons [['k 't] '(CljM.assocInC m k t v)]})))
   (chain-fold 'CljM.updateInC [['f F1] '[m CljM.V] '[k CljM.V] '[cs CljM.V]] OV
               (bindV '(CljM.get m k) ['x] (bindV '(f x) ['y] '(CljM.assoc m k y)))
               (bindV '(CljM.get m k) ['x] (bindV '(CljM.updateInC f x h t) ['r] '(CljM.assoc m k r))))
   (defm 'CljM.updateIn [['m 'CljM.V] ['ks 'CljM.V] ['f F1]] OV
     (bindV '(CljM.selems ks) ['it] (vm 'it OV '(CljM.updateInC f m CljM.V.vnil CljM.V.vnil)
                                        {'vcons [['k 't] '(CljM.updateInC f m k t)]})))
   ;; update-vals keeps every key in place
   (defm 'CljM.updValsC [['f F1] '[e CljM.V]] OV
     (vm 'e OV (someV vnil*) {'ventry [['k 'w 'r] (bindV '(f w) ['y] (bindV '(CljM.updValsC f r) ['r2]
                                                                            (someV (c 'ventry 'k 'y 'r2))))]}))
   (defm 'CljM.updateVals [['m 'CljM.V] ['f F1]] OV
     (vm 'm OV noneV {'vnil [[] (someV (c 'vmap vnil*))]
                      'vmap [['e] (bindV '(CljM.updValsC f e) ['r] (someV (c 'vmap 'r)))]}))])

;; ── Higher-order functions ──────────────────────────────────────────────────────────────

(def ^:private hof-forms
  [(chain-fold 'CljM.mapC [['f F1] '[cs CljM.V]] OV (someV vnil*)
               (bindV '(f h) ['y] (bindV '(CljM.mapC f t) ['r] (someV (vcons* 'y 'r)))))
   (chain-fold 'CljM.filterC [['f F1] '[keep Bool] '[cs CljM.V]] OV (someV vnil*)
               (bindV '(f h) ['q] (bindV '(CljM.filterC f keep t) ['r]
                                         (list 'if '(CljM.truthy q) (list 'if 'keep (someV (vcons* 'h 'r)) (someV 'r))
                                               (list 'if 'keep (someV 'r) (someV (vcons* 'h 'r)))))))
   (chain-fold 'CljM.keepC [['f F1] '[cs CljM.V]] OV (someV vnil*)
               (bindV '(f h) ['y] (bindV '(CljM.keepC f t) ['r] (list 'if '(CljM.isNil y) (someV 'r) (someV (vcons* 'y 'r))))))
   (chain-fold 'CljM.foldC [['f F2] '[acc CljM.V] '[cs CljM.V]] OV (someV 'acc)
               (bindV '(f acc h) ['a2] '(CljM.foldC f a2 t)))
   (defm 'CljM.zipC [['f F2] '[a CljM.V] '[b CljM.V]] OV
     (vm 'a OV (someV vnil*) {'vcons [['h 't] (vm 'b OV (someV vnil*)
                                                  {'vcons [['h2 't2] (bindV '(f h h2) ['y] (bindV '(CljM.zipC f t t2) ['r] (someV (vcons* 'y 'r))))]})]}))
   ;; some / every? on an ordered seq short-circuit in order; on a hash-ordered one every call
   ;; must answer (Clojure's order may reach a throwing call first), and `some` needs the truthy
   ;; answers to agree
   (chain-fold 'CljM.someC [['f F1] '[cs CljM.V]] OV (someV vnil*)
               (bindV '(f h) ['y] (list 'if '(CljM.truthy y) (someV 'y) '(CljM.someC f t))))
   (chain-fold 'CljM.everyC [['f F1] '[cs CljM.V]] OV (boolV true)
               (bindV '(f h) ['y] (list 'if '(CljM.truthy y) '(CljM.everyC f t) (boolV false))))
   (chain-fold 'CljM.firstTruthy '[[cs CljM.V]] 'CljM.V vnil* '(if (CljM.truthy h) h (CljM.firstTruthy t)))
   (chain-fold 'CljM.agree '[[x CljM.V] [cs CljM.V]] 'Bool true
               '(Bool.and (Bool.or (Bool.not (CljM.truthy h)) (CljM.same x h)) (CljM.agree x t)))
   (chain-fold 'CljM.allTruthy '[[cs CljM.V]] 'Bool true '(Bool.and (CljM.truthy h) (CljM.allTruthy t)))
   (defm 'CljM.map [['f F1] '[v CljM.V]] OV
     (bindV '(CljM.elems v) ['it] (bindV '(CljM.mapC f it) ['r] (someV '(CljM.mkSeq (CljM.ord v) r)))))
   (defm 'CljM.map2 [['f F2] '[a CljM.V] '[b CljM.V]] OV
     (bindV '(CljM.oelems a) ['x] (bindV '(CljM.oelems b) ['y] (bindV '(CljM.zipC f x y) ['r] (someV (c 'vlseq true 'r))))))
   (defm 'CljM.mapv [['f F1] '[v CljM.V]] OV (bindV '(CljM.oelems v) ['it] (bindV '(CljM.mapC f it) ['r] (someV (c 'vvec 'r)))))
   (defm 'CljM.filter [['f F1] '[v CljM.V]] OV
     (bindV '(CljM.elems v) ['it] (bindV '(CljM.filterC f true it) ['r] (someV '(CljM.mkSeq (CljM.ord v) r)))))
   (defm 'CljM.remove [['f F1] '[v CljM.V]] OV
     (bindV '(CljM.elems v) ['it] (bindV '(CljM.filterC f false it) ['r] (someV '(CljM.mkSeq (CljM.ord v) r)))))
   (defm 'CljM.filterv [['f F1] '[v CljM.V]] OV (bindV '(CljM.oelems v) ['it] (bindV '(CljM.filterC f true it) ['r] (someV (c 'vvec 'r)))))
   (defm 'CljM.keep [['f F1] '[v CljM.V]] OV
     (bindV '(CljM.elems v) ['it] (bindV '(CljM.keepC f it) ['r] (someV '(CljM.mkSeq (CljM.ord v) r)))))
   (defm 'CljM.reduce [['f0 OV] ['f F2] '[v CljM.V]] OV
     (bindV '(CljM.oelems v) ['it] (vm 'it OV 'f0 {'vcons [['h 't] '(CljM.foldC f h t)]})))
   (defm 'CljM.reduce3 [['f F2] '[init CljM.V] '[v CljM.V]] OV (bindV '(CljM.oelems v) ['it] '(CljM.foldC f init it)))
   (defm 'CljM.some [['f F1] '[v CljM.V]] OV
     (bindV '(CljM.elems v) ['it]
            (list 'if '(CljM.ord v) '(CljM.someC f it)
                  (bindV '(CljM.mapC f it) ['rs] (list 'if '(CljM.agree (CljM.firstTruthy rs) rs) (someV '(CljM.firstTruthy rs)) noneV)))))
   (defm 'CljM.every [['f F1] '[v CljM.V]] OV
     (bindV '(CljM.elems v) ['it]
            (list 'if '(CljM.ord v) '(CljM.everyC f it) (bindV '(CljM.mapC f it) ['rs] (boolV '(CljM.allTruthy rs))))))
   (chain-fold 'CljM.groupC [['f F1] '[acc CljM.V] '[cs CljM.V]] OV (someV 'acc)
               (bindV '(f h) ['k] (bindV '(CljM.get3 acc k (CljM.V.vvec CljM.V.vnil)) ['g]
                                         (bindV '(CljM.conj1 g h) ['g2] (bindV '(CljM.assoc acc k g2) ['a2] '(CljM.groupC f a2 t))))))
   (defm 'CljM.groupBy [['f F1] '[v CljM.V]] OV (bindV '(CljM.oelems v) ['it] (list 'CljM.groupC 'f (c 'vmap vnil*) 'it)))
   (chain-fold 'CljM.freqC '[[acc CljM.V] [cs CljM.V]] OV (someV 'acc)
               (bindV '(CljM.get3 acc h (CljM.V.vlong 0)) ['n]
                      (bindV '(CljM.inc n) ['n2] (bindV '(CljM.assoc acc h n2) ['a2] '(CljM.freqC a2 t)))))
   (defm 'CljM.frequencies '[[v CljM.V]] OV
     (bindV '(CljM.elems v) ['it] (bindV (list 'CljM.freqC (c 'vmap vnil*) 'it) ['r] '(CljM.mapOk (CljM.ord v) (CljM.items r)))))
   ;; distinct destructures its argument with nth: a set or a map throws
   (defm 'CljM.distinct '[[v CljM.V]] OV
     (bindV (vm 'v OV '(CljM.elems v) {'vset [['x] noneV] 'vmap [['x] noneV]}) ['it] (bindV '(CljM.dedupO (CljM.ord v) it) ['r] (someV '(CljM.mkSeq (CljM.ord v) r)))))
   (defm 'CljM.concatC '[[cs CljM.V]] OV
     (vm 'cs OV (someV vnil*) {'vcons [['h 't] (bindV '(CljM.elems h) ['x] (bindV '(CljM.concatC t) ['r] (someV '(CljM.appendC x r))))]}))
   (defm 'CljM.concat '[[args CljM.V]] OV (bindV '(CljM.concatC args) ['r] (someV '(CljM.mkSeq (CljM.allOrd args) r))))
   (defm 'CljM.fold1 [['f F2] '[cs CljM.V]] OV (vm 'cs OV noneV {'vcons [['h 't] '(CljM.foldC f h t)]}))])

;; ── Comparison and sorting ──────────────────────────────────────────────────────────────

(def ^:private sort-forms
  [(defm 'CljM.cmpLt '[[a CljM.V] [b CljM.V]] OB
     (let [nil-b (fn [arms] (vm 'b OB noneB (assoc arms 'vnil [[] someF])))]
       (vm 'a OB noneB
           {'vnil [[] '(Option.some (Bool.not (CljM.isNil b)))]
            'vlong [['i] (nil-b {'vlong [['j] '(Option.some (< i j))]})]
            'vbool [['x] (nil-b {'vbool [['y] '(Option.some (Bool.and (Bool.not x) y))]})]
            'vchar [['x] (nil-b {'vchar [['y] '(Option.some (< (Char.toNat x) (Char.toNat y)))]})]
            'vstr [['s] (nil-b {'vstr [['t] (list 'if '(Bool.and (CljM.bmpL (String.toList s)) (CljM.bmpL (String.toList t)))
                                                  '(Option.some (CljM.strLt (String.toList s) (String.toList t))) noneB)]})]
            'vkw [['s] (nil-b {'vkw [['t] (list 'if '(Bool.and (== (CljM.slashes (String.toList s)) 0)
                                                               (Bool.and (== (CljM.slashes (String.toList t)) 0)
                                                                         (Bool.and (CljM.bmpL (String.toList s)) (CljM.bmpL (String.toList t)))))
                                                '(Option.some (CljM.strLt (String.toList s) (String.toList t))) noneB)]})]})))
   ;; stable insertion of a decorated cell (ventry key x vnil), x coming before the cells of
   ;; `cs` in the input: after the keys smaller than its own, before the rest
   (chain-fold 'CljM.insK '[[x CljM.V] [cs CljM.V]] OV (someV (vcons* 'x vnil*))
               (bindB '(CljM.cmpLt (CljM.hd h) (CljM.hd x)) ['q]
                      (list 'if 'q (bindV '(CljM.insK x t) ['r] (someV (vcons* 'h 'r))) (someV (vcons* 'x '(CljM.V.vcons h t))))))
   (chain-fold 'CljM.sortK '[[cs CljM.V]] OV (someV vnil*) (bindV '(CljM.sortK t) ['r] '(CljM.insK h r)))
   (chain-fold 'CljM.decorate [['f F1] '[cs CljM.V]] OV (someV vnil*)
               (bindV '(f h) ['k] (bindV '(CljM.decorate f t) ['r] (someV (vcons* (c 'ventry 'k 'h vnil*) 'r)))))
   (chain-fold 'CljM.undecorate '[[cs CljM.V]] 'CljM.V vnil* (vcons* '(CljM.ev h) '(CljM.undecorate t)))
   ;; consecutive sorted keys strictly increase (no ties)
   (chain-fold 'CljM.strictK '[[cs CljM.V]] 'Bool true
               (vm 't 'Bool true {'vcons [['h2 't2] '(Bool.and (Option.getD (CljM.cmpLt (CljM.hd h) (CljM.hd h2)) false)
                                                               (CljM.strictK t))]}))
   ;; (sort-by f coll): () when empty; ties keep the input order, so a hash-ordered input with
   ;; tied keys is none (sort itself only ties identical values)
   (defm 'CljM.sortBy [['f F1] '[v CljM.V]] OV
     (bindV '(CljM.elems v) ['it]
            (list 'if '(CljM.isNil it) (someV (c 'vlist vnil*))
                  (bindV '(CljM.decorate f it) ['d]
                         (bindV '(CljM.sortK d) ['s]
                                (list 'if '(Bool.or (CljM.ord v) (CljM.strictK s))
                                      (someV (c 'vlseq true '(CljM.undecorate s))) noneV))))))
   (defm 'CljM.sort '[[v CljM.V]] OV (list 'CljM.sortBy '(fn [x :- CljM.V] (Option.some x)) 'v))
   (defm 'CljM.max2 '[[a CljM.V] [b CljM.V]] OV
     (vm 'a OV noneV {'vlong [['i] (vm 'b OV noneV {'vlong [['j] (list 'if '(< i j) (someV 'b) (someV 'a))]})]}))
   (defm 'CljM.min2 '[[a CljM.V] [b CljM.V]] OV
     (vm 'a OV noneV {'vlong [['i] (vm 'b OV noneV {'vlong [['j] (list 'if '(< j i) (someV 'b) (someV 'a))]})]}))
   ;; (max x) is x whatever it is; more arguments compare as longs (doubles: no claim)
   (defm 'CljM.max '[[args CljM.V]] OV '(CljM.fold1 (fn [a :- CljM.V, b :- CljM.V] (CljM.max2 a b)) args))
   (defm 'CljM.min '[[args CljM.V]] OV '(CljM.fold1 (fn [a :- CljM.V, b :- CljM.V] (CljM.min2 a b)) args))])

;; ── Strings ─────────────────────────────────────────────────────────────────────────────

(def ^:private str-forms
  [;; decimal digits (Long.toString / BigInteger.toString), with fuel for 40 digits
   (defm 'CljM.digits [['fuel 'Nat] ['n 'Nat] ['acc LC]] '(Option (List Char))
     (list 'match 'fuel 'Nat '(Option (List Char)) (list 'zero (m/none-of LC))
           '(succ [f] (if (== (Nat.div n 10) 0)
                        (Option.some (List.cons (Char.ofNat (+ 48 (Nat.mod n 10))) acc))
                        (CljM.digits f (Nat.div n 10) (List.cons (Char.ofNat (+ 48 (Nat.mod n 10))) acc))))))
   (defm 'CljM.str1 '[[v CljM.V]] OS
     (vm 'v OS noneS {'vnil [[] '(Option.some "")]
                      'vbool [['b] '(Option.some (if b "true" "false"))]
                      'vlong [['i] '(Option.bind (CljM.digits 40 (Int.natAbs i) CljM.noChars)
                                                 (fn [ds :- (List Char)]
                                                   (Option.some (String.ofList (if (< i 0) (List.cons (Char.ofNat 45) ds) ds)))))]
                      'vchar [['x] '(Option.some (String.ofList (List.cons x CljM.noChars)))]
                      'vstr [['s] '(Option.some s)]
                      'vkw [['s] '(Option.some (String.append ":" s))]
                      'vsym [['s] '(Option.some s)]}))
   (chain-fold 'CljM.strC '[[cs CljM.V]] OS '(Option.some "")
               (bindS '(CljM.str1 h) ['a] (bindS '(CljM.strC t) ['b] '(Option.some (String.append a b)))))
   (defm 'CljM.str '[[args CljM.V]] OV (bindS '(CljM.strC args) ['s] (someV (c 'vstr 's))))
   ;; clojure.string/join: str of each element, the separator str'd between them
   (chain-fold 'CljM.joinC '[[sep String] [cs CljM.V]] OS '(Option.some "")
               (bindS '(CljM.str1 h) ['a]
                      (list 'if '(CljM.isNil t) '(Option.some a)
                            (bindS '(CljM.joinC sep t) ['b] '(Option.some (String.append a (String.append sep b)))))))
   (defm 'CljM.join '[[v CljM.V]] OV (bindV '(CljM.oelems v) ['it] '(CljM.str it)))
   (defm 'CljM.join2 '[[sep CljM.V] [v CljM.V]] OV
     (bindS '(CljM.str1 sep) ['s] (bindV '(CljM.oelems v) ['it] (bindS '(CljM.joinC s it) ['r] (someV (c 'vstr 'r))))))
   (defm 'CljM.subs3 '[[v CljM.V] [a CljM.V] [b CljM.V]] OV
     (bindS '(CljM.bmpStrOf v) ['s]
            (bindI '(CljM.longOf a) ['i]
                   (bindI '(CljM.longOf b) ['j]
                          (list 'if '(Bool.and (<= 0 i) (Bool.and (<= i j) (<= j (Int.ofNat (List.length (String.toList s))))))
                                (someV (c 'vstr '(String.ofList (List.take (Int.toNat (- j i)) (List.drop (Int.toNat i) (String.toList s))))))
                                noneV)))))
   (defm 'CljM.subs '[[v CljM.V] [a CljM.V]] OV
     (bindS '(CljM.bmpStrOf v) ['s] '(CljM.subs3 v a (CljM.V.vlong (Int.ofNat (List.length (String.toList s)))))))
   (defm 'CljM.name '[[v CljM.V]] OV
     (let [nm (list 'if '(CljM.simpleName s)
                    (someV (c 'vstr '(if (== (CljM.slashes (String.toList s)) 0) s (String.ofList (CljM.afterSlash (String.toList s))))))
                    noneV)]
       (vm 'v OV noneV {'vstr [['s] (someV 'v)] 'vkw [['s] nm] 'vsym [['s] nm]})))
   (defm 'CljM.keyword '[[v CljM.V]] OV
     (let [kw (list 'if '(CljM.simpleName s) (someV (c 'vkw 's)) noneV)]
       (vm 'v OV (someV vnil*) {'vkw [['s] (someV 'v)] 'vstr [['s] kw] 'vsym [['s] kw]
                                'vcons [['h 't] noneV] 'ventry [['k 'w 'r] noneV]})))
   (defm 'CljM.keyword2 '[[n CljM.V] [v CljM.V]] OV
     (bindS '(CljM.strOf v) ['s]
            (vm 'n OV noneV {'vnil [[] (list 'if '(== (CljM.slashes (String.toList s)) 0) (someV (c 'vkw 's)) noneV)]
                             'vstr [['p] (list 'if '(Bool.and (== (CljM.slashes (String.toList p)) 0)
                                                              (Bool.and (< 0 (List.length (String.toList p)))
                                                                        (< 0 (List.length (String.toList s)))))
                                               (someV (c 'vkw '(String.append p (String.append "/" s)))) noneV)]})))
   ;; blank? is true for nil and false ((if s …)); on a string, all whitespace (ASCII only)
   (defm 'CljM.blankQ '[[v CljM.V]] OV
     (list 'if '(Bool.not (CljM.truthy v)) (boolV true)
           (bindS '(CljM.strOf v) ['s] (list 'if '(CljM.asciiL (String.toList s)) (boolV '(CljM.blankL (String.toList s))) noneV))))
   (defm 'CljM.upperCase '[[v CljM.V]] OV
     (bindS '(CljM.strOf v) ['s] (list 'if '(CljM.asciiL (String.toList s)) (someV (c 'vstr '(String.ofList (CljM.upperL (String.toList s))))) noneV)))
   (defm 'CljM.lowerCase '[[v CljM.V]] OV
     (bindS '(CljM.strOf v) ['s] (list 'if '(CljM.asciiL (String.toList s)) (someV (c 'vstr '(String.ofList (CljM.lowerL (String.toList s))))) noneV)))
   (defm 'CljM.startsWithQ '[[v CljM.V] [w CljM.V]] OV
     (bindS '(CljM.strOf v) ['s] (bindS '(CljM.strOf w) ['t] (boolV '(CljM.prefixL (String.toList t) (String.toList s))))))
   (defm 'CljM.endsWithQ '[[v CljM.V] [w CljM.V]] OV
     (bindS '(CljM.strOf v) ['s] (bindS '(CljM.strOf w) ['t] (boolV '(CljM.prefixL (List.reverse (String.toList t)) (List.reverse (String.toList s)))))))
   (defm 'CljM.includesQ '[[v CljM.V] [w CljM.V]] OV
     (bindS '(CljM.strOf v) ['s] (bindS '(CljM.strOf w) ['t] (boolV '(CljM.infixL (String.toList t) (String.toList s))))))])

;; ── Predicates and invocation ───────────────────────────────────────────────────────────

(def ^:private misc-forms
  [(m/pred 'CljM.seqQ '{vlist [[it] true] vlseq [[o it] true]})
   (m/pred 'CljM.listQ '{vlist [[it] true]})
   (m/pred 'CljM.setQ '{vset [[it] true]})
   (m/pred 'CljM.collQ '{vlist [[it] true] vlseq [[o it] true] vvec [[it] true] vmap [[it] true] vset [[it] true]})
   (m/pred 'CljM.sequentialQ '{vlist [[it] true] vlseq [[o it] true] vvec [[it] true]})
   (m/pred 'CljM.booleanQ '{vbool [[b] true]})
   (m/pred 'CljM.symbolQ '{vsym [[s] true]})
   (m/pred 'CljM.charQ '{vchar [[x] true]})
   (m/pred 'CljM.trueQ '{vbool [[b] b]})
   (m/pred 'CljM.falseQ '{vbool [[b] (Bool.not b)]})
   (defm 'CljM.boolean '[[v CljM.V]] OV (boolV '(CljM.truthy v)))
   (defm 'CljM.evenQ '[[v CljM.V]] OV (vm 'v OV noneV {'vlong [['i] (boolV '(== (Int.emod i 2) 0))]}))
   (defm 'CljM.oddQ '[[v CljM.V]] OV (vm 'v OV noneV {'vlong [['i] (boolV '(Bool.not (== (Int.emod i 2) 0)))]}))
   ;; a value called as a function: keywords and symbols look themselves up, maps and sets
   ;; look the argument up, a vector indexes (throwing out of range)
   (defm 'CljM.invoke '[[f CljM.V] [x CljM.V]] OV
     (vm 'f OV noneV {'vkw [['s] '(CljM.get x f)] 'vsym [['s] '(CljM.get x f)]
                      'vmap [['e] '(CljM.get f x)] 'vset [['e] '(CljM.get f x)]
                      'vvec [['it] (list 'CljM.nthAt 'it 'x noneV)]}))
   ;; case: the value against a group of literal tests, by hashed-key equality (case* hashes)
   (defm 'CljM.caseIn '[[x CljM.V] [cs CljM.V]] OV (bindB '(CljM.memC x cs) ['q] (boolV 'q)))
   (defm 'CljM.invoke3 '[[f CljM.V] [x CljM.V] [d CljM.V]] OV
     (vm 'f OV noneV {'vkw [['s] '(CljM.get3 x f d)] 'vsym [['s] '(CljM.get3 x f d)]
                      'vmap [['e] '(CljM.get3 f x d)] 'vset [['e] '(CljM.get3 f x d)]}))])

(defn model-forms
  "The G2 model forms, in dependency order (after ansatz.clj-model's G1 forms)."
  []
  (concat string-forms seq-forms access-forms build-forms hof-forms sort-forms str-forms misc-forms))
