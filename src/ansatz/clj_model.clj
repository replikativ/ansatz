(ns ansatz.clj-model
  "A kernel model of plain Clojure: the universe `CljM.V`, truthiness, numbers, equality and
   the scalar/lookup ops here (G1); sequences, maps, sets, higher-order functions and strings in
   ansatz.clj-model.colls (G2); the fuel-indexed fixpoints recursion runs on here (G3). Each op
   is `V… → Option V`, where `none` means NO CLAIM (clojure.core throws, the op is not
   modelled, a long overflows, or the answer depends on something the model does not track). Adequacy is one-directional: the model returning `some v` means clojure.core
   returns a value whose EDN is `v`.

   The DSL keeps Lean semantics; Clojure's semantics lives here. `a/foreign ^:model` translates
   a foreign function's source into this model (ansatz.clj-model.translate), so the function
   becomes a definition instead of an axiom (ansatz.clj-model.boundary).

   The model is written as `a/defn ^:lean` forms generated below and installed lazily by
   `install-model!` (generated as code, not a literal, so AOT stays under the 64 KB limit).
   Binary ops match the first argument, then a per-constructor helper (15 + 15 arms).
   Recursive equality takes Nat fuel (sized from the operands); running out is `none`.
   The ops are specified on encodings of Clojure values; on an ill-formed `V` (a bare chain
   cell used as a value) they answer `none` where that is cheap and are otherwise unspecified.
   Map order: a map of 9+ entries is a hash map in Clojure, so `dissoc` on one is `none`
   (its result's iteration order is the hash order, which the boundary would otherwise see).

   Runtime: a `CljM.V` runs in the tagged inductive representation `[cidx field…]`;
   `edn->cljv` / `cljv->edn` convert, and `strict=` compares results (seqs ≠ vectors,
   maps/sets order-free, numeric category kept, NaN = NaN, 0.0 ≠ -0.0)."
  (:require [ansatz.core :as a]
            [ansatz.config :as config]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.codegen.decl :as decl]
            [ansatz.codegen.lean-runtime :as rt]))

;; ── The universe ────────────────────────────────────────────────────────────────────────
;; Constructor order is APPEND-ONLY: the runtime representation and every exhaustive match
;; depend on it. Chains (cons cells, map entries) end in `vnil`.

(def ctors
  "[ctor [[field type] …]] in constructor-index order."
  '[[vnil []]
    [vbool [[b Bool]]]
    [vlong [[i Int]]]                    ;; any integer; outside long range = a BigInt
    [vdouble [[f Float]]]
    [vchar [[c Char]]]
    [vstr [[s String]]]
    [vkw [[s String]]]                   ;; "ns/name" or "name"
    [vsym [[s String]]]
    [vcons [[h CljM.V] [t CljM.V]]]      ;; sequence/set chain cell
    [ventry [[k CljM.V] [v CljM.V] [r CljM.V]]] ;; map chain cell
    [vlist [[items CljM.V]]]             ;; list? (PersistentList, ())
    [vlseq [[ordered Bool] [items CljM.V]]] ;; other seqs; ordered=false: hash order unknown
    [vvec [[items CljM.V]]]
    [vmap [[entries CljM.V]]]            ;; insertion order, no duplicate keys
    [vset [[items CljM.V]]]])

(def ctor-index (into {} (map-indexed (fn [i [c _]] [c i]) ctors)))

(def OV '(Option CljM.V))
(def OB '(Option Bool))
(def OOV '(Option (Option CljM.V)))

(defn none-of [t] (list (symbol "@Option.none") t))
(def noneV (none-of 'CljM.V))
(def noneB (none-of 'Bool))
(def noneOV (none-of OV))
(def someT '(Option.some true))
(def someF '(Option.some false))

(defn c [ctor & args]
  (let [s (symbol (str "CljM.V." ctor))] (if (seq args) (list* s args) s)))

(defn vm
  "`(match disc CljM.V ret …)`: `dflt` for every constructor except `overrides`
   (ctor → [[field-binders] body])."
  [disc ret dflt overrides]
  (list* 'match-as disc 'CljM.V ret
         (map (fn [[ct fs]]
                (if-let [[bs body] (get overrides ct)]
                  (if (empty? fs) (list ct body) (list ct (vec bs) body))
                  (if (empty? fs) (list ct dflt) (list ct (vec (repeatedly (count fs) #(gensym "_"))) dflt))))
              ctors)))

(defn defm [nm params ret body]
  (list 'ansatz.core/defn nm (vec (mapcat (fn [[p t]] [p :- t]) params)) ret body))

(defn bindV [x [v] body] (list 'Option.bind x (list 'fn [v :- 'CljM.V] body)))
(defn bindB [x [v] body] (list 'Option.bind x (list 'fn [v :- 'Bool] body)))
(defn someV [x] (list 'Option.some x))
(defn boolV [b] (someV (c 'vbool b)))

(def ^:private long-min -9223372036854775808)
(def ^:private long-max 9223372036854775807)

;; ── Form generators ─────────────────────────────────────────────────────────────────────

(defn- arith-forms
  "`op` on longs (overflow in range → none; a BigInt operand → exact) and on doubles; mixed
   long/double is none until rows settle it. `guard`: a Bool term over j that makes the long
   case none (boxed `-` negates its second operand first, so subtracting Long/MIN_VALUE throws
   whatever the first operand is)."
  [op sym & [guard]]
  (let [L (symbol (str "CljM." op "L")) D (symbol (str "CljM." op "D"))
        long-body (list 'if '(Bool.and (CljM.inLong i) (CljM.inLong j))
                        (list 'CljM.lres (list sym 'i 'j))
                        (someV (c 'vlong (list sym 'i 'j))))]
    [(defm L '[[i Int] [b CljM.V]] OV
       (vm 'b OV noneV {'vlong [['j] (if guard (list 'if guard noneV long-body) long-body)]}))
     (defm D '[[f Float] [b CljM.V]] OV
       (vm 'b OV noneV {'vdouble [['g] (someV (c 'vdouble (list sym 'f 'g)))]}))
     (defm (symbol (str "CljM." op)) '[[a CljM.V] [b CljM.V]] OV
       (vm 'a OV noneV {'vlong [['i] (list L 'i 'b)] 'vdouble [['f] (list D 'f 'b)]}))]))

(defn- cmp-forms
  "A comparison on longs (exact, BigInt included) and on doubles (IEEE)."
  [op sym]
  (let [L (symbol (str "CljM." op "L")) D (symbol (str "CljM." op "D"))]
    [(defm L '[[i Int] [b CljM.V]] OV (vm 'b OV noneV {'vlong [['j] (boolV (list sym 'i 'j))]}))
     (defm D '[[f Float] [b CljM.V]] OV (vm 'b OV noneV {'vdouble [['g] (boolV (list sym 'f 'g))]}))
     (defm (symbol (str "CljM." op)) '[[a CljM.V] [b CljM.V]] OV
       (vm 'a OV noneV {'vlong [['i] (list L 'i 'b)] 'vdouble [['f] (list D 'f 'b)]}))]))

(defn- unary-num [nm long-body double-body]
  (defm nm '[[a CljM.V]] OV (vm 'a OV noneV {'vlong [['i] long-body] 'vdouble [['f] double-body]})))

(defn pred [nm overrides]
  (defm nm '[[a CljM.V]] OV (boolV (vm 'a 'Bool false overrides))))

(defn- scalar-eq [nm ty ct]
  (defm nm [['x ty] '[b CljM.V]] OB (vm 'b OB someF {ct [['y] '(Option.some (== x y))]})))

(defn- eqF-form
  "Clojure `=` with fuel. Modes: 0 equiv; 3 hashed-key equivalence (as 0, but doubles, maps
   and sets are none: hashing ±0.0 and NaN differs from equiv); 1 every element/entry of
   chain `a` is in chain `b`; 2 the probe cell `a` is in chain `b` (keys by mode 3, map values
   by mode 0)."
  []
  (let [rec (fn [m x y] (list 'CljM.eqF 'n m x y))
        seq-arm (fn [items] (list 'if '(== (CljM.seqKind b) 1) (rec 'mode items '(CljM.items b))
                                  (list 'if '(== (CljM.seqKind b) 0) someF noneB)))
        coll-arm (fn [is?] (list 'if '(== mode 3) (list 'if (list is? 'b) noneB someF)
                                 (list 'if (list is? 'b)
                                       (list 'if '(== (CljM.clen e) (CljM.clen (CljM.items b)))
                                             (rec 1 'e '(CljM.items b)) someF)
                                       someF)))
        equiv (vm 'a OB noneB
                  {'vnil [[] '(Option.some (CljM.isNil b))]
                   'vbool [['x] '(CljM.eqBool x b)]
                   'vlong [['i] '(CljM.eqLong i b)]
                   ;; hashed: ±0.0 and NaN hash apart from equiv; a double never matches a non-double
                   'vdouble [['f] (list 'if '(== mode 3) (vm 'b OB someF {'vdouble [['g] noneB]}) '(CljM.eqDouble f b))]
                   'vchar [['x] '(CljM.eqChar x b)]
                   'vstr [['s] '(CljM.eqStr s b)]
                   'vkw [['s] '(CljM.eqKw s b)]
                   'vsym [['s] '(CljM.eqSym s b)]
                   'vcons [['h 't] (list 'if '(CljM.isCons b)
                                         (bindB (rec 'mode 'h '(CljM.hd b)) ['q]
                                                (list 'if 'q (rec 'mode 't '(CljM.tl b)) someF))
                                         someF)]
                   'vlist [['it] (seq-arm 'it)]
                   'vvec [['it] (seq-arm 'it)]
                   'vlseq [['o 'it] (list 'if 'o (seq-arm 'it)
                                          (list 'if '(== (CljM.seqKind b) 0) someF noneB))]
                   'vmap [['e] (coll-arm 'CljM.isMap)]
                   'vset [['e] (coll-arm 'CljM.isSet)]})
        sub (vm 'a OB noneB
                {'vnil [[] someT]
                 'vcons [['h 't] (bindB (rec 2 (c 'vcons 'h (c 'vnil)) 'b) ['q]
                                        (list 'if 'q (rec 1 't 'b) someF))]
                 'ventry [['k 'w 'r] (bindB (rec 2 (c 'ventry 'k 'w (c 'vnil)) 'b) ['q]
                                            (list 'if 'q (rec 1 'r 'b) someF))]})
        mem (vm 'b OB noneB
                {'vnil [[] someF]
                 'vcons [['h 't] (bindB (rec 3 '(CljM.hd a) 'h) ['q]
                                        (list 'if 'q someT (rec 2 'a 't)))]
                 'ventry [['k 'w 'r] (bindB (rec 3 '(CljM.hd a) 'k) ['q]
                                            (list 'if 'q (rec 0 '(CljM.ev a) 'w) (rec 2 'a 'r)))]})]
    (defm 'CljM.eqF '[[fuel Nat] [mode Nat] [a CljM.V] [b CljM.V]] OB
      (list 'match-as 'fuel 'Nat OB
            (list 'zero noneB)
            (list 'succ '[n] (list 'if '(== mode 1) sub (list 'if '(== mode 2) mem equiv)))))))

(declare recursion-forms)

(defn model-forms
  "The `a/defn ^:lean` forms defining `CljM.V` and the ops (G1 here, G2 in ansatz.clj-model.colls),
   in dependency order."
  []
  (concat
   [(list* 'ansatz.core/inductive 'CljM.V []
           (map (fn [[ct fs]] (list* ct (map vec fs))) ctors))
    (defm 'CljM.truthy '[[v CljM.V]] 'Bool (vm 'v 'Bool true '{vnil [[] false] vbool [[b] b]}))
    (defm 'CljM.inLong '[[i Int]] 'Bool (list 'Bool.and (list '<= long-min 'i) (list '<= 'i long-max)))
    (defm 'CljM.inInt '[[i Int]] 'Bool '(Bool.and (<= -2147483648 i) (<= i 2147483647)))
    (defm 'CljM.lres '[[r Int]] OV (list 'if '(CljM.inLong r) (someV (c 'vlong 'r)) noneV))
    ;; structural helpers
    (defm 'CljM.isNil '[[v CljM.V]] 'Bool (vm 'v 'Bool false '{vnil [[] true]}))
    (defm 'CljM.isCons '[[v CljM.V]] 'Bool (vm 'v 'Bool false '{vcons [[h t] true]}))
    (defm 'CljM.isMap '[[v CljM.V]] 'Bool (vm 'v 'Bool false '{vmap [[e] true]}))
    (defm 'CljM.isSet '[[v CljM.V]] 'Bool (vm 'v 'Bool false '{vset [[e] true]}))
    (defm 'CljM.hd '[[v CljM.V]] 'CljM.V (vm 'v 'CljM.V (c 'vnil) '{vcons [[h t] h] ventry [[k w r] k]}))
    (defm 'CljM.tl '[[v CljM.V]] 'CljM.V (vm 'v 'CljM.V (c 'vnil) '{vcons [[h t] t] ventry [[k w r] r]}))
    (defm 'CljM.ev '[[v CljM.V]] 'CljM.V (vm 'v 'CljM.V (c 'vnil) '{ventry [[k w r] w]}))
    (defm 'CljM.items '[[v CljM.V]] 'CljM.V
      (vm 'v 'CljM.V (c 'vnil) '{vlist [[it] it] vlseq [[o it] it] vvec [[it] it] vmap [[it] it] vset [[it] it]}))
    (defm 'CljM.seqKind '[[v CljM.V]] 'Nat
      (vm 'v 'Nat 0 '{vlist [[it] 1] vvec [[it] 1] vlseq [[o it] (if o 1 2)]}))
    (defm 'CljM.clen '[[v CljM.V]] 'Nat
      (vm 'v 'Nat 0 '{vcons [[h t] (+ 1 (CljM.clen t))] ventry [[k w r] (+ 1 (CljM.clen r))]}))
    (defm 'CljM.size '[[v CljM.V]] 'Nat
      (vm 'v 'Nat 1 '{vcons [[h t] (+ 1 (+ (CljM.size h) (CljM.size t)))]
                      ventry [[k w r] (+ 1 (+ (CljM.size k) (+ (CljM.size w) (CljM.size r))))]
                      vlist [[it] (+ 1 (CljM.size it))] vlseq [[o it] (+ 1 (CljM.size it))]
                      vvec [[it] (+ 1 (CljM.size it))] vmap [[it] (+ 1 (CljM.size it))]
                      vset [[it] (+ 1 (CljM.size it))]}))
    ;; a string in the Basic Multilingual Plane: code points = Java's UTF-16 units
    (defm 'CljM.bmpL '[[cs (List Char)]] 'Bool
      '(match-as cs (List Char) Bool (nil true) (cons [h t] (Bool.and (< (Char.toNat h) 65536) (CljM.bmpL t)))))
    (defm 'CljM.cnth '[[c CljM.V] [n Nat]] 'CljM.V
      '(match-as n Nat CljM.V (zero (CljM.hd c)) (succ [j] (CljM.cnth (CljM.tl c) j))))
    ;; equality
    (scalar-eq 'CljM.eqBool 'Bool 'vbool)
    (scalar-eq 'CljM.eqLong 'Int 'vlong)
    (scalar-eq 'CljM.eqChar 'Char 'vchar)
    (scalar-eq 'CljM.eqStr 'String 'vstr)
    (scalar-eq 'CljM.eqKw 'String 'vkw)
    (scalar-eq 'CljM.eqSym 'String 'vsym)
    ;; NaN compares unequal in Float.beq but a boxed NaN equals itself under identity: no claim
    (defm 'CljM.eqDouble '[[f Float] [b CljM.V]] OB
      (vm 'b OB someF {'vdouble [['g] (list 'if '(Bool.and (Float.beq f f) (Float.beq g g))
                                            '(Option.some (Float.beq f g)) noneB)]}))
    (eqF-form)
    (defm 'CljM.fuel '[[a CljM.V] [b CljM.V]] 'Nat '(+ 4 (* 2 (+ (CljM.size a) (CljM.size b)))))
    (defm 'CljM.keq '[[a CljM.V] [b CljM.V]] OB '(CljM.eqF (CljM.fuel a b) 3 a b))
    (defm 'CljM.eq '[[a CljM.V] [b CljM.V]] OV (bindB '(CljM.eqF (CljM.fuel a b) 0 a b) ['q] (boolV 'q)))
    (defm 'CljM.neq '[[a CljM.V] [b CljM.V]] OV (bindB '(CljM.eqF (CljM.fuel a b) 0 a b) ['q] (boolV '(Bool.not q))))
    ;; truthiness and identity
    (defm 'CljM.nilQ '[[a CljM.V]] OV (boolV '(CljM.isNil a)))
    (defm 'CljM.someQ '[[a CljM.V]] OV (boolV '(Bool.not (CljM.isNil a))))
    (defm 'CljM.not '[[a CljM.V]] OV (boolV '(Bool.not (CljM.truthy a))))
    (defm 'CljM.identity '[[a CljM.V]] OV (someV 'a))]
   ;; numbers
   (arith-forms "add" '+)
   (arith-forms "sub" '- (list '== 'j long-min))
   (arith-forms "mul" '*)
   (cmp-forms "lt" '<)
   (cmp-forms "le" '<=)
   [(defm 'CljM.gt '[[a CljM.V] [b CljM.V]] OV '(CljM.lt b a))
    (defm 'CljM.ge '[[a CljM.V] [b CljM.V]] OV '(CljM.le b a))
    ;; (+ x) is (cast Number x), and (cast Number nil) is nil
    (defm 'CljM.num '[[a CljM.V]] OV (vm 'a OV noneV {'vnil [[] (someV 'a)] 'vlong [['i] (someV 'a)]
                                                      'vdouble [['f] (someV 'a)]}))
    (unary-num 'CljM.neg (list 'if '(CljM.inLong i) '(CljM.lres (- i)) (someV (c 'vlong '(- i))))
               (someV (c 'vdouble '(- f))))
    (unary-num 'CljM.inc (list 'if '(CljM.inLong i) '(CljM.lres (+ i 1)) (someV (c 'vlong '(+ i 1))))
               (someV (c 'vdouble '(+ f 1.0))))
    (unary-num 'CljM.dec (list 'if '(CljM.inLong i) '(CljM.lres (- i 1)) (someV (c 'vlong '(- i 1))))
               (someV (c 'vdouble '(- f 1.0))))
    (unary-num 'CljM.zeroQ (boolV '(== i 0)) (boolV '(Float.beq f 0.0)))
    (unary-num 'CljM.posQ (boolV '(< 0 i)) (boolV '(< 0.0 f)))
    (unary-num 'CljM.negQ (boolV '(< i 0)) (boolV '(< f 0.0)))
    ;; type predicates
    (pred 'CljM.stringQ '{vstr [[s] true]})
    (pred 'CljM.keywordQ '{vkw [[s] true]})
    (pred 'CljM.numberQ '{vlong [[i] true] vdouble [[f] true]})
    (pred 'CljM.intQ '{vlong [[i] (CljM.inLong i)]})
    (pred 'CljM.mapQ '{vmap [[e] true]})
    (pred 'CljM.vectorQ '{vvec [[e] true]})
    ;; lookup in a map entry chain / set chain: none = undecided, some none = absent
    (defm 'CljM.find '[[k CljM.V] [c CljM.V]] OOV
      (vm 'c OOV noneOV {'vnil [[] (someV noneV)]
                         'ventry [['k2 'w 'r] (bindB '(CljM.keq k k2) ['q]
                                                     (list 'if 'q '(Option.some (Option.some w)) '(CljM.find k r)))]}))
    (defm 'CljM.sfind '[[k CljM.V] [c CljM.V]] OOV
      (vm 'c OOV noneOV {'vnil [[] (someV noneV)]
                         'vcons [['h 't] (bindB '(CljM.keq k h) ['q]
                                                (list 'if 'q '(Option.some (Option.some h)) '(CljM.sfind k t)))]}))
    (defm 'CljM.lookD [['o OOV] '[d CljM.V]] OV
      (list 'Option.bind 'o (list 'fn ['r :- OV] '(Option.some (Option.getD r d)))))
    (defm 'CljM.found [['o OOV]] OV
      (list 'Option.bind 'o (list 'fn ['r :- OV] (boolV '(Option.isSome r)))))
    ;; vectors: an integer key is read with intValue (it wraps outside int range: no claim)
    (defm 'CljM.vecGet '[[it CljM.V] [k CljM.V] [d CljM.V]] OV
      (vm 'k OV (someV 'd)
          {'vlong [['i] (list 'if '(CljM.inInt i)
                              (list 'if '(Bool.and (<= 0 i) (< i (Int.ofNat (CljM.clen it))))
                                    (someV '(CljM.cnth it (Int.toNat i))) (someV 'd))
                              noneV)]}))
    (defm 'CljM.vecHas '[[it CljM.V] [k CljM.V]] OV
      (vm 'k OV (boolV false)
          {'vlong [['i] (list 'if '(CljM.inInt i)
                              (boolV '(Bool.and (<= 0 i) (< i (Int.ofNat (CljM.clen it)))))
                              noneV)]}))
    (defm 'CljM.get3 '[[m CljM.V] [k CljM.V] [d CljM.V]] OV
      (vm 'm OV (someV 'd) {'vmap [['e] '(CljM.lookD (CljM.find k e) d)]
                            'vset [['e] '(CljM.lookD (CljM.sfind k e) d)]
                            'vvec [['it] '(CljM.vecGet it k d)]
                            ;; a number key indexes the string (a char): no claim in G1
                            'vstr [['s] (vm 'k OV (someV 'd) {'vlong [['i] noneV] 'vdouble [['f] noneV]})]
                            'vcons [['h 't] noneV] 'ventry [['x 'y 'z] noneV]}))
    (defm 'CljM.get '[[m CljM.V] [k CljM.V]] OV (list 'CljM.get3 'm 'k (c 'vnil)))
    (defm 'CljM.containsQ '[[m CljM.V] [k CljM.V]] OV
      (vm 'm OV noneV {'vnil [[] (boolV false)]
                       'vmap [['e] '(CljM.found (CljM.find k e))]
                       'vset [['e] '(CljM.found (CljM.sfind k e))]
                       'vvec [['it] '(CljM.vecHas it k)]}))
    ;; assoc: an existing key keeps its place (and its key object), a new key goes last
    (defm 'CljM.assocC '[[k CljM.V] [v CljM.V] [c CljM.V]] OV
      (vm 'c OV noneV {'vnil [[] (someV (c 'ventry 'k 'v (c 'vnil)))]
                       'ventry [['k2 'w 'r]
                                (bindB '(CljM.keq k k2) ['q]
                                       (list 'if 'q (someV (c 'ventry 'k2 'v 'r))
                                             (bindV '(CljM.assocC k v r) ['r2] (someV (c 'ventry 'k2 'w 'r2)))))]}))
    (defm 'CljM.assocN0 '[[c CljM.V] [v CljM.V]] OV
      (vm 'c OV noneV {'vnil [[] (someV (c 'vcons 'v (c 'vnil)))] 'vcons [['h 't] (someV (c 'vcons 'v 't))]}))
    (defm 'CljM.assocN '[[c CljM.V] [n Nat] [v CljM.V]] OV
      (list 'match-as 'n 'Nat OV
            '(zero (CljM.assocN0 c v))
            (list 'succ '[j] (vm 'c OV noneV {'vcons [['h 't] (bindV '(CljM.assocN t j v) ['t2]
                                                                     (someV (c 'vcons 'h 't2)))]}))))
    (defm 'CljM.vecAssoc '[[it CljM.V] [k CljM.V] [v CljM.V]] OV
      (vm 'k OV noneV {'vlong [['i] (list 'if '(Bool.and (CljM.inInt i) (<= 0 i))
                                          (bindV '(CljM.assocN it (Int.toNat i) v) ['it2] (someV (c 'vvec 'it2)))
                                          noneV)]}))
    (defm 'CljM.assoc '[[m CljM.V] [k CljM.V] [v CljM.V]] OV
      (vm 'm OV noneV {'vnil [[] (someV (c 'vmap (c 'ventry 'k 'v (c 'vnil))))]
                       'vmap [['e] (bindV '(CljM.assocC k v e) ['e2] (someV (c 'vmap 'e2)))]
                       'vvec [['it] '(CljM.vecAssoc it k v)]}))
    (defm 'CljM.dissocC '[[k CljM.V] [c CljM.V]] OV
      (vm 'c OV noneV {'vnil [[] (someV (c 'vnil))]
                       'ventry [['k2 'w 'r]
                                (bindB '(CljM.keq k k2) ['q]
                                       (list 'if 'q (someV 'r)
                                             (bindV '(CljM.dissocC k r) ['r2] (someV (c 'ventry 'k2 'w 'r2)))))]}))
    ;; a map of 9+ entries is a hash map; after dissoc its order is the hash order: no claim
    (defm 'CljM.dissoc '[[m CljM.V] [k CljM.V]] OV
      (vm 'm OV noneV {'vnil [[] (someV (c 'vnil))]
                       'vmap [['e] (list 'if '(<= 9 (CljM.clen e)) noneV
                                         (bindV '(CljM.dissocC k e) ['e2] (someV (c 'vmap 'e2))))]}))
    (defm 'CljM.count '[[m CljM.V]] OV
      (let [n (someV (c 'vlong '(Int.ofNat (CljM.clen it))))]
        (vm 'm OV noneV {'vnil [[] (someV (c 'vlong 0))]
                         'vlist [['it] n] 'vlseq [['o 'it] n] 'vvec [['it] n] 'vmap [['it] n] 'vset [['it] n]
                         ;; a string: UTF-16 units, which are code points in the BMP
                         'vstr [['s] (list 'if '(CljM.bmpL (String.toList s))
                                           (someV (c 'vlong '(Int.ofNat (List.length (String.toList s))))) noneV)]})))]
   ;; G2: sequences, maps, sets, higher-order functions, strings
   ((requiring-resolve 'ansatz.clj-model.colls/model-forms))
   ;; G3: recursion
   (recursion-forms)))

;; ── Recursion (G3) ──────────────────────────────────────────────────────────────────────
;; A recursive Clojure function (self-calls, `recur`, `loop`, `letfn`, mutually recursive
;; a/defmodel functions) is a GROUP of members, one per arity, translated into one functional
;;   F : (Nat → V → … → Option V) → Nat → V → … → Option V      (self, member tag, arguments)
;; and run by `CljM.fix<k> F fuel tag x…`: structural recursion on the Nat fuel, `none` (no
;; claim) when it runs out. Fuel bounds the DEPTH of nested calls, not their number.

(def max-fix-arity
  "The most arguments a recursive member takes (`CljM.fix1` … `CljM.fix8`)."
  8)

(defn fix-type
  "`Nat → V → … → Option V` with `k` value arguments: a group's `self`."
  [k]
  (list '=> 'Nat (reduce (fn [acc _] (list '=> 'CljM.V acc)) OV (range k))))

(defn- fix-form [k]
  (let [nm (symbol (str "CljM.fix" k))
        xs (mapv #(symbol (str "x" %)) (range 1 (inc k)))
        ys (mapv #(symbol (str "y" %)) (range 1 (inc k)))
        vs (fn [zs] (vec (mapcat (fn [z] [z :- 'CljM.V]) zs)))]
    (list 'ansatz.core/defn nm (into ['F :- (list '=> (fix-type k) (fix-type k)) 'fuel :- 'Nat 'tag :- 'Nat] (vs xs)) OV
          (list 'match-as 'fuel 'Nat OV
                (list 'zero noneV)
                ;; the approximant is eta-expanded, so a compiled fix runs lazily
                (list 'succ '[n] (list* 'F (list 'fn (into '[t :- Nat] (vs ys)) (list* nm 'F 'n 't ys)) 'tag xs))))))

(defn recursion-forms
  "`CljM.weight` (the default fuel measure), `CljM.toFuel` (a user `:fuel` value) and the
   fixpoint combinators `CljM.fix1` … `CljM.fix8`."
  []
  (into
   [;; nodes, where an integer counts |i| + 1 and a string its length + 1: recursion that
    ;; walks a collection, shortens a string or counts an integer toward 0 has depth below it
    (defm 'CljM.weight '[[v CljM.V]] 'Nat
      (vm 'v 'Nat 1 '{vlong [[i] (+ (Int.natAbs i) 1)]
                      vstr [[s] (+ (List.length (String.toList s)) 1)]
                      vcons [[h t] (+ (+ (CljM.weight h) (CljM.weight t)) 1)]
                      ventry [[k w r] (+ (+ (CljM.weight k) (+ (CljM.weight w) (CljM.weight r))) 1)]
                      vlist [[it] (+ (CljM.weight it) 1)] vlseq [[o it] (+ (CljM.weight it) 1)]
                      vvec [[it] (+ (CljM.weight it) 1)] vmap [[it] (+ (CljM.weight it) 1)]
                      vset [[it] (+ (CljM.weight it) 1)]}))
    (defm 'CljM.toFuel [['r OV]] 'Nat
      (list 'Option.getD (list 'Option.bind 'r (list 'fn '[v :- CljM.V]
                                                     (vm 'v '(Option Nat) (none-of 'Nat)
                                                         {'vlong [['i] '(Option.some (Int.toNat i))]})))
            0))]
   (map fix-form (range 1 (inc max-fix-arity)))))

;; ── Installation ────────────────────────────────────────────────────────────────────────

(defn installed? []
  (some? (env/lookup (a/env) (name/from-string (str "CljM.fix" max-fix-arity)))))

(def ^:private model-ns 'ansatz.clj-model.kernel)

(defn- the-model-ns []
  (or (find-ns model-ns)
      (let [n (create-ns model-ns)] (binding [*ns* n] (refer-clojure)) n)))

(defn install-model!
  "Define `CljM.V` and the model's ops on the current env (an Init env: Int, Float, Char, String,
   Option). Idempotent. Returns :installed."
  []
  (locking #'install-model!
    (when-not (installed?)
      (binding [a/*verbose* false
                config/*clj-surface* false
                *ns* (the-model-ns)]
        (doseq [f (model-forms)] (eval f)))))
  :installed)

(defn model-fn
  "The compiled runtime function of a model constant (e.g. \"CljM.add\"), defined by
   install-model! or by the boundary codecs."
  [kname]
  (or (some (fn [n] (some-> (find-ns n) (ns-resolve (decl/runtime-name (symbol kname))) deref))
            [model-ns 'ansatz.clj-model.boundary])
      (throw (ex-info "clj-model: no compiled model function" {:name kname}))))

;; ── Runtime representation ──────────────────────────────────────────────────────────────

(defn- long-range? [x] (and (<= Long/MIN_VALUE x) (<= x Long/MAX_VALUE)))

(defn- rt-int [x] (if (long-range? x) (long x) (bigint x)))

(defn- chain [xs] (reduce (fn [acc x] [(ctor-index 'vcons) x acc]) [0] (reverse xs)))

(defn edn->cljv
  "A Clojure value → the runtime `CljM.V`. Seqs in their iteration order (hash order for hash
   maps and sets; `vlseq` is marked ordered: the caller's seq has a definite order)."
  [x]
  (cond
    (nil? x) [0]
    (boolean? x) [1 x]
    (or (instance? Long x) (instance? Integer x) (instance? Short x) (instance? Byte x)
        (instance? clojure.lang.BigInt x) (instance? BigInteger x)) [2 (rt-int x)]
    (or (instance? Double x) (instance? Float x)) [3 (double x)]
    (char? x) [4 (long (int x))]
    (string? x) [5 x]
    (keyword? x) [6 (subs (str x) 1)]
    (symbol? x) [7 (str x)]
    (map? x) [13 (reduce (fn [acc [k v]] [9 (edn->cljv k) (edn->cljv v) acc]) [0] (reverse (seq x)))]
    (set? x) [14 (chain (map edn->cljv x))]
    (vector? x) [12 (chain (map edn->cljv x))]
    (list? x) [10 (chain (map edn->cljv x))]
    (seq? x) [11 true (chain (map edn->cljv x))]
    :else (throw (ex-info "edn->cljv: no model for this value" {:x x :class (class x)}))))

(declare cljv->edn)

(defn- unchain [c]
  (loop [c c acc []]
    (case (long (nth c 0))
      0 acc
      8 (recur (nth c 2) (conj acc (cljv->edn (nth c 1))))
      9 (recur (nth c 3) (conj acc [(cljv->edn (nth c 1)) (cljv->edn (nth c 2))]))
      (throw (ex-info "cljv->edn: malformed chain" {:c c})))))

(defn cljv->edn
  "The runtime `CljM.V` → its Clojure value (maps built in chain order, so a map of up to 8
   entries iterates in the model's order)."
  [v]
  (case (long (nth v 0))
    0 nil
    1 (nth v 1)
    2 (nth v 1)
    3 (nth v 1)
    4 (char (nth v 1))
    5 (nth v 1)
    6 (keyword (nth v 1))
    7 (symbol (nth v 1))
    10 (apply list (unchain (nth v 1)))
    ;; seq? but not list?, like (map f xs); a hash-ordered seq is marked: its order is unknown
    11 (cond-> (lazy-seq (seq (unchain (nth v 2)))) (not (nth v 1)) (with-meta {::unordered true}))
    12 (vec (unchain (nth v 1)))
    13 (reduce (fn [m [k x]] (assoc m k x)) {} (unchain (nth v 1)))
    14 (set (unchain (nth v 1)))
    (throw (ex-info "cljv->edn: a bare chain cell is not a value" {:v v}))))

(defn pack-args
  "A model's runtime arguments for `xs` (runtime CljM.V values): the fixed ones, then (for a
   variadic model, `arity` {:clj-model/fixed n :clj-model/rest? true}) the extra ones as a seq
   or nil, as Clojure passes them."
  [{:clj-model/keys [fixed rest?]} xs]
  (if rest?
    (let [extra (drop fixed xs)]
      (conj (vec (take fixed xs)) (if (empty? extra) [0] [(ctor-index 'vlseq) true (chain extra)])))
    (vec xs)))

(defn opt-value
  "Decode a compiled `Option` result in the runtime's representation
   (ansatz.codegen.lean-runtime): `none` is nil, `some x` is x, or a SomeBox when x itself
   runs as nil or is a box. Returns {:some x}, or nil for `none`."
  [r]
  (when (some? r) {:some (rt/some-val r)}))

;; ── Strict Clojure equality (for comparing results) ─────────────────────────────────────

(defn- seq-kind [x] (cond (vector? x) :vector (list? x) :list (seq? x) :seq))

(declare strict=)

(defn- same-elements? [xs ys]
  (and (= (count xs) (count ys))
       (empty? (reduce (fn [ys x]
                         (let [i (first (keep-indexed (fn [i y] (when (strict= x y) i)) ys))]
                           (if i (into (subvec ys 0 i) (subvec ys (inc i))) (reduced [::no]))))
                       (vec ys) xs))))

(defn strict=
  "Clojure `=` that also keeps what `=` forgets but the EDN shows: a vector is not a seq, a
   list is not another seq, integers and doubles differ, 0.0 ≠ -0.0; NaN equals NaN. Maps and
   sets are compared order-free, and so is a seq the model marks hash-ordered (cljv->edn)."
  [x y]
  (cond
    (and (or (::unordered (meta x)) (::unordered (meta y))) (= :seq (seq-kind x)) (= :seq (seq-kind y)))
    (same-elements? x y)
    (and (integer? x) (integer? y)) (== x y)
    (and (instance? Double x) (instance? Double y)) (.equals ^Double x y)
    (or (number? x) (number? y)) false
    (and (map? x) (map? y)) (and (= (count x) (count y))
                                 (every? (fn [[k v]] (and (contains? y k) (strict= v (get y k)))) x))
    (and (set? x) (set? y)) (same-elements? (seq x) (seq y))
    (or (map? x) (map? y) (set? x) (set? y)) false
    (and (seq-kind x) (seq-kind y)) (and (= (seq-kind x) (seq-kind y))
                                         (= (count x) (count y))
                                         (every? true? (map strict= x y)))
    (or (seq-kind x) (seq-kind y)) false
    :else (= x y)))
