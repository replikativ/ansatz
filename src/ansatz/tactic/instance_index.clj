;; Follows Lean 4 (../lean4, checkout 55f80e10a3; behaviour checked against Lean 4.33.1):
;; Meta/DiscrTree/{Types,Basic,Main}.lean, Meta/Instances.lean (mkInstanceKey, computeSynthOrder),
;; Class.lean (checkOutParam, computeOutLevelParams), Lean/Data/Name.lean (quickCmp).

(ns ansatz.tactic.instance-index
  "Lean's global instance index: every registered instance keyed by the discrimination-tree path
   of its type's conclusion (`mkInstanceKey`), with the order in which its instance arguments are
   synthesized (`computeSynthOrder`).

   The registry (`:instances`, Lean's dump: class, name, priority per instance) does not carry the
   keys, so they are computed here from the instance declarations. A store can persist them in its
   derived `:instances` blob (`annotate-registry`); entries without them are keyed on demand.

   Keys follow `DiscrTree.mkPath`: reducible whnf (`reduceDT`), instance-implicit arguments,
   non-type implicit arguments and proofs as stars, numerals as literals, Nat offsets as stars,
   arities, projections and arrows. Children of a trie node are ordered by Lean's `Key.lt`, which
   orders constants by Lean's NAME HASH (`Name.quickCmp`), reproduced exactly here — the order of
   `getUnify` results, and so the order among instances of equal priority, depends on it.

   Deviations, forced by what the exported environment records:
   - \"reducible\" is `ansatz.meta/reducible-const?` (abbrev hints minus class projections); a
     `@[reducible] def` with regular hints is not unfolded.
   - the classes are the env's class extension plus the registries' classes (`mk-ctx`).
   - `ansatz.core/structure` gives class projections an explicit `self`; it is read as Lean's
     instance-implicit one (`class-self-position`).
   - no smart-unfolding/matcher stuckness (`getKeyArgs` under `isDefEqStuckEx`)."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta :as meta])
  (:import [ansatz.kernel Name ConstantInfo Env]
           [java.nio.charset StandardCharsets]))

;; ============================================================
;; Lean's Name.hash and Name.quickCmp
;; ============================================================

(def ^:private ^:const murmur-m (unchecked-long 0xc6a4a7935bd1e995))

(defn- mix-hash
  "lean_uint64_mix_hash (lean.h)."
  ^long [^long h ^long k]
  (let [k (unchecked-multiply k murmur-m)
        k (bit-xor k (unsigned-bit-shift-right k 47))
        k (bit-xor k murmur-m)
        h (bit-xor h k)]
    (unchecked-multiply h murmur-m)))

(defn- murmur64a
  "MurmurHash64A (runtime/hash.cpp), Lean's string hash with seed 11."
  ^long [^bytes data ^long seed]
  (let [len (alength data)
        nblocks (quot len 8)
        h (loop [i 0 h (bit-xor seed (unchecked-multiply (long len) murmur-m))]
            (if (< i nblocks)
              (let [base (* i 8)
                    k (loop [j 7 k 0]
                        (if (neg? j) k
                            (recur (dec j) (bit-or (bit-shift-left k 8)
                                                   (bit-and (long (aget data (+ base j))) 0xff)))))
                    k (unchecked-multiply k murmur-m)
                    k (bit-xor k (unsigned-bit-shift-right k 47))
                    k (unchecked-multiply k murmur-m)]
                (recur (inc i) (unchecked-multiply (bit-xor h k) murmur-m)))
              h))
        tail (rem len 8)
        base (* nblocks 8)
        h (if (pos? tail)
            (unchecked-multiply
             (loop [j (dec tail) h h]
               (if (neg? j) h
                   (recur (dec j) (bit-xor h (bit-shift-left (bit-and (long (aget data (+ base j))) 0xff)
                                                             (* 8 j))))))
             murmur-m)
            h)
        h (bit-xor h (unsigned-bit-shift-right h 47))
        h (unchecked-multiply h murmur-m)]
    (bit-xor h (unsigned-bit-shift-right h 47))))

(def ^:private name-hashes (java.util.concurrent.ConcurrentHashMap.))

(defn lean-name-hash
  "Lean's `Name.hash` (Init/Prelude.lean): anonymous 1723, `mixHash` of the prefix hash with the
   component's hash (a string's MurmurHash64A, a number's value). A UInt64 held in a long."
  ^long [^Name n]
  (if (or (nil? n) (name/anonymous? n))
    1723
    (let [hit (.get ^java.util.concurrent.ConcurrentHashMap name-hashes n)]
      (if hit
        (long hit)
        (let [p (lean-name-hash (.prefix n))
              h (if (= Name/STR (.tag n))
                  (mix-hash p (murmur64a (.getBytes ^String (.str n) StandardCharsets/UTF_8) 11))
                  (mix-hash p (.num n)))]
          (.put ^java.util.concurrent.ConcurrentHashMap name-hashes n h)
          h)))))

(defn- quick-cmp-aux
  "Lean's `Name.quickCmpAux`: last components first."
  [^Name a ^Name b]
  (let [an? (or (nil? a) (name/anonymous? a))
        bn? (or (nil? b) (name/anonymous? b))]
    (cond
      (and an? bn?) 0
      an? -1
      bn? 1
      (and (= Name/NUM (.tag a)) (= Name/NUM (.tag b)))
      (let [c (compare (.num a) (.num b))] (if (zero? c) (recur (.prefix a) (.prefix b)) c))
      (= Name/NUM (.tag a)) -1
      (= Name/NUM (.tag b)) 1
      :else (let [c (compare (.str a) (.str b))]
              (if (zero? c) (recur (.prefix a) (.prefix b)) (Integer/signum (int c)))))))

(defn name-quick-cmp
  "Lean's `Name.quickCmp`: by hash (unsigned), then structurally."
  [a b]
  (if (identical? a b)
    0
    (let [c (Long/compareUnsigned (lean-name-hash a) (lean-name-hash b))]
      (if (zero? c) (quick-cmp-aux a b) (Integer/signum (int c))))))

;; ============================================================
;; Keys — Lean's DiscrTree.Key and Key.lt
;; ============================================================
;; [:star] [:other] [:lit v] [:fvar id arity] [:const Name arity] [:arrow] [:proj Name idx arity]

(def star [:star])
(def other [:other])
(def arrow [:arrow])

(defn- ctor-idx ^long [k]
  (case (nth k 0) :star 0 :other 1 :lit 2 :fvar 3 :const 4 :arrow 5 :proj 6))

(defn- lit-lt? [a b]
  (cond
    (and (string? a) (string? b)) (neg? (compare a b))
    (string? a) false
    (string? b) true
    :else (< (bigint a) (bigint b))))

(defn key-lt?
  "Lean's `Key.lt`."
  [k1 k2]
  (let [t1 (nth k1 0) t2 (nth k2 0)]
    (cond
      (and (= t1 :lit) (= t2 :lit)) (lit-lt? (nth k1 1) (nth k2 1))
      (and (= t1 :fvar) (= t2 :fvar)) (or (< (long (nth k1 1)) (long (nth k2 1)))
                                          (and (= (nth k1 1) (nth k2 1)) (< (long (nth k1 2)) (long (nth k2 2)))))
      (and (= t1 :const) (= t2 :const)) (let [c (name-quick-cmp (nth k1 1) (nth k2 1))]
                                          (or (neg? c) (and (zero? c) (< (long (nth k1 2)) (long (nth k2 2))))))
      (and (= t1 :proj) (= t2 :proj)) (let [c (name-quick-cmp (nth k1 1) (nth k2 1))]
                                        (or (neg? c)
                                            (and (zero? c) (< (long (nth k1 2)) (long (nth k2 2))))
                                            (and (zero? c) (= (nth k1 2) (nth k2 2))
                                                 (< (long (nth k1 3)) (long (nth k2 3))))))
      :else (< (ctor-idx k1) (ctor-idx k2)))))

(defn key-arity
  "Lean's `Key.arity`."
  ^long [k]
  (case (nth k 0)
    :const (nth k 2)
    :fvar (nth k 2)
    :arrow 1
    :proj (inc (long (nth k 3)))
    0))

;; ============================================================
;; Trie — Lean's DiscrTree.Trie (sorted children, insertVal)
;; ============================================================

(def empty-trie {:vs [] :cs []})

(defn- child-index
  "Binary search of `k` among the sorted children: index, or (- -1 insertion-point)."
  [cs k]
  (loop [lo 0 hi (dec (count cs))]
    (if (> lo hi)
      (- -1 lo)
      (let [mid (quot (+ lo hi) 2)
            mk (nth (nth cs mid) 0)]
        (cond (key-lt? mk k) (recur (inc mid) hi)
              (key-lt? k mk) (recur lo (dec mid))
              :else mid)))))

(defn- insert-val
  "Lean's `insertVal`: an equal value (same instance) is replaced in place, else appended."
  [vs v]
  (if-let [i (first (keep-indexed (fn [i x] (when (= (:name x) (:name v)) i)) vs))]
    (assoc vs i v)
    (conj vs v)))

(defn- insert-aux [node keys i v]
  (if (< i (count keys))
    (let [k (nth keys i)
          cs (:cs node)
          j (child-index cs k)]
      (if (neg? j)
        (let [p (- -1 j)]
          (assoc node :cs (into (conj (subvec cs 0 p) [k (insert-aux empty-trie keys (inc i) v)]) (subvec cs p))))
        (assoc node :cs (assoc cs j [k (insert-aux (nth (nth cs j) 1) keys (inc i) v)]))))
    (update node :vs insert-val v)))

(defn trie-insert
  "Lean's `insertKeyValue` on one root's trie (the root map is keyed by `(first keys)`)."
  [roots keys v]
  (update roots (first keys) #(insert-aux (or % empty-trie) keys 1 v)))

;; ============================================================
;; reduceDT and key arguments
;; ============================================================

(def ^:private ignored
  "Lean's `tmpStar`: an argument the tree does not index."
  ::ignored)

(defn- whnf-core [mctx st x]
  (meta/whnf-at mctx st x :none))

(defn- unfold-reducible
  "Lean's `unfoldDefinition?` at reducible transparency."
  [st x]
  (let [h (e/get-app-fn x)]
    (when (and (e/const? h) (meta/reducible-const? (:env st) (e/const-name h)))
      (meta/unfold-const-app (:env st) x))))

(defn- eta-expanded-strict
  "Lean's `Expr.etaExpandedStrict?`: `fun x₁ … xₙ => f x₁ … xₙ` (n ≥ 1, f closed in them) ↦ f."
  [x]
  (when (e/lam? x)
    (let [[n body] (loop [x x n 0] (if (e/lam? x) (recur (e/lam-body x) (inc n)) [n x]))
          [f args] (e/get-app-fn-args body)
          k (count args)]
      (when (>= k n)
        (let [tail (subvec (vec args) (- k n))]
          (when (every? true? (map-indexed (fn [i a] (and (e/bvar? a) (= (e/bvar-idx a) (- n 1 i)))) tail))
            (let [g (reduce e/app f (subvec (vec args) 0 (- k n)))]
              (when-not (e/has-loose-bvars? g n)
                ;; lower the remaining loose bvars by n
                (e/instantiate g (vec (repeat n (e/bvar 0))))))))))))

(defn- bad-key? [f]
  (not (or (e/lit-nat? f) (e/lit-str? f) (e/const? f) (e/fvar? f) (e/proj? f) (e/forall? f))))

(defn reduce-dt
  "Lean's `reduceDT`: `reduce` (whnfCore, reducible delta, strict eta) for nested terms;
   `reduceUntilBadKey` for the root, which stops before an unfolding that would expose a bad key."
  [mctx st x root?]
  (if root?
    (loop [x x]
      (let [x (loop [x (whnf-core mctx st x)]
                (if-let [x' (unfold-reducible st x)]
                  (let [x' (meta/zonk-expr mctx x')]
                    (if (bad-key? (e/get-app-fn x')) x (recur (whnf-core mctx st x'))))
                  x))]
        (if-let [x' (eta-expanded-strict x)] (recur x') x)))
    (loop [x x]
      (let [x (whnf-core mctx st x)]
        (if-let [x' (unfold-reducible st x)]
          (recur (meta/zonk-expr mctx x'))
          (if-let [x' (eta-expanded-strict x)] (recur x') x))))))

(defn- const-named? [x s] (and (e/const? x) (= s (name/->string (e/const-name x)))))

(defn- numeral? [x]
  (or (e/lit-nat? x)
      (let [[f args] (e/get-app-fn-args x)]
        (and (e/const? f)
             (let [n (name/->string (e/const-name f)) c (count args)]
               (cond (and (= n "Nat.succ") (= c 1)) (numeral? (first args))
                     (and (= n "OfNat.ofNat") (= c 3)) (numeral? (second args))
                     (and (= n "Nat.zero") (= c 0)) true
                     :else false))))))

(defn- to-nat-lit
  "Lean's `toNatLit?`."
  [x]
  (when (numeral? x)
    (loop [x x add 0]
      (if (e/lit-nat? x)
        (+ (e/lit-nat-val x) add)
        (let [[f args] (e/get-app-fn-args x) n (name/->string (e/const-name f))]
          (case n
            "Nat.succ" (recur (first args) (inc add))
            "OfNat.ofNat" (recur (second args) add)
            "Nat.zero" add))))))

(defn- nat-type? [mctx st x]
  (const-named? (try (meta/whnf mctx st x) (catch clojure.lang.ExceptionInfo _ x)) "Nat"))

(defn- offset?
  "Lean's `isOffset`."
  [mctx st fname x]
  (let [[_ args] (e/get-app-fn-args x) c (count args) n (name/->string fname)]
    (cond (and (= n "Nat.add") (= c 2)) (numeral? (last args))
          (and (= n "Add.add") (= c 4)) (and (nat-type? mctx st (first args)) (numeral? (last args)))
          (and (= n "HAdd.hAdd") (= c 6)) (and (nat-type? mctx st (second args)) (numeral? (last args)))
          :else (and (= n "Nat.succ") (= c 1)))))

(defn- infer [mctx st x]
  (try (meta/infer-type mctx st x) (catch clojure.lang.ExceptionInfo _ nil)))

(defn- is-type? [mctx st x]
  (when-let [t (infer mctx st x)]
    (e/sort? (try (meta/whnf mctx st t) (catch clojure.lang.ExceptionInfo _ t)))))

(defn- is-proof? [mctx st x]
  (when-let [t (infer mctx st x)]
    (when-let [s (infer mctx st t)]
      (let [s (try (meta/whnf mctx st s) (catch clojure.lang.ExceptionInfo _ s))]
        (and (e/sort? s) (lvl/level-zero? (meta/zonk-level mctx (e/sort-level s))))))))

(defn class-type?
  "Lean's `isClass?` on a type: the head of its reducing forall telescope is a class. `class?` is
   a predicate on constant names."
  [mctx st class? ty]
  (loop [t ty st st fuel 64]
    (let [t (meta/zonk-expr mctx t)]
      (cond
        (zero? fuel) false
        (e/forall? t) (let [fid (swap! (:next-id st) inc)
                            st (assoc st :lctx (assoc (:lctx st) fid {:tag :local :id fid :name (e/forall-name t) :type (e/forall-type t)}))]
                        (recur (e/instantiate1 (e/forall-body t) (e/fvar fid)) st (dec fuel)))
        :else (let [h (e/get-app-fn t)]
                (if (and (e/const? h) (class? (e/const-name h)))
                  true
                  (let [t' (meta/whnf-at mctx st t :reducible)]
                    (if (= t' t) false (recur t' st (dec fuel))))))))))

(defn class-self-position
  "The position of the `self` argument when `n` is a projection function of a CLASS. Lean
   generates it instance-implicit (`[self : C α]`); `ansatz.core/structure` generates it explicit,
   so binder infos read from the declaration are normalised at this position."
  [env n]
  (when-let [{:keys [from-class? num-params]} (meta/projection-fn-info env n)]
    (when from-class? num-params)))

(defn- param-infos
  "Lean's `getFunInfoNArgs … |>.paramInfo` as the tree uses it: per parameter its binder info and
   `isInstance` (a class type under a non-explicit binder)."
  [ctx mctx st f nargs]
  (let [self-pos (when (e/const? f) (class-self-position (:env ctx) (e/const-name f)))
        compute (fn []
                  (loop [t (infer mctx st f) st st i 0 acc []]
                    (cond
                      (or (nil? t) (>= i nargs)) acc
                      (e/forall? t)
                      (let [bi (e/forall-info t)
                            d (e/forall-type t)
                            bi (if (= i self-pos) :inst-implicit bi)
                            inst? (and (not= :default bi) (class-type? mctx st (:class? ctx) d))
                            fid (swap! (:next-id st) inc)
                            st' (assoc st :lctx (assoc (:lctx st) fid {:tag :local :id fid :name (e/forall-name t) :type d}))]
                        (recur (e/instantiate1 (e/forall-body t) (e/fvar fid)) st' (inc i)
                               (conj acc {:bi bi :instance? inst?})))
                      :else (let [t' (meta/whnf-at mctx st t :reducible)]
                              (if (e/forall? t') (recur t' st i acc) acc)))))]
    (if (and (e/const? f) (:param-cache ctx))
      (let [k [(e/const-name f) nargs]
            cache (:param-cache ctx)]
        (or (get @cache k) (let [r (compute)] (swap! cache assoc k r) r)))
      (compute))))

(defn- ignore-arg? [mctx st a i infos]
  (if (< i (count infos))
    (let [{:keys [bi instance?]} (nth infos i)]
      (cond instance? true
            (#{:implicit :strict-implicit} bi) (not (is-type? mctx st a))
            :else (is-proof? mctx st a)))
    (is-proof? mctx st a)))

(defn- push-args
  "Lean's `pushArgs`: the key of `x` and the todo stack extended with its indexed arguments."
  [ctx mctx st root? todo x]
  (if (identical? x ignored)
    [star todo]
    (let [x (reduce-dt mctx st x root?)
          [f args] (e/get-app-fn-args x)
          nargs (count args)
          push (fn [k todo]
                 (let [infos (param-infos ctx mctx st f nargs)]
                   [k (reduce (fn [todo i]
                                (let [a (nth args i)]
                                  (conj todo (if (ignore-arg? mctx st a i infos) ignored a))))
                              todo (range (dec nargs) -1 -1))]))]
      (case (e/tag f)
        :lit-nat [[:lit (e/lit-nat-val f)] todo]
        :lit-str [[:lit (e/lit-str-val f)] todo]
        :const (let [c (e/const-name f)]
                 (or (when-not root?
                       (if-let [v (to-nat-lit x)]
                         [[:lit v] todo]
                         (when (offset? mctx st c x) [star todo])))
                     (push [:const c nargs] todo)))
        :proj (let [s (e/proj-type-name f)
                    a (e/proj-struct f)]
                (push [:proj s (e/proj-idx f) nargs]
                      (conj todo (if ((:class? ctx) s) ignored a))))
        :fvar (push [:fvar (e/fvar-id f) nargs] todo)
        :mvar [star todo]
        :forall [arrow (conj todo (e/forall-type f))]
        [other todo]))))

(defn mk-path
  "Lean's `DiscrTree.mkPath` for `x` (which may contain metavariables of `mctx`)."
  [ctx mctx st x]
  (loop [todo [x] keys [] root? true]
    (if (empty? todo)
      keys
      (let [[k todo] (push-args ctx mctx st root? (pop todo) (peek todo))]
        (recur todo (conj keys k) false)))))

(defn- key-args
  "Lean's `getKeyArgs`: the key of a query term and its arguments (reversed, so the first is on
   top of the todo stack). Arguments are not filtered on the query side. A metavariable is a star
   for `getUnify` under `isDefEqStuckEx` (as instance synthesis runs it) and `.other` for
   `getMatch` (it matches only star edges)."
  [mctx st x root? match?]
  (let [x (reduce-dt mctx st x root?)]
    (or (when-not root? (when-let [v (to-nat-lit x)] [[:lit v] []]))
        (let [[f args] (e/get-app-fn-args x)
              rev (vec (rseq (vec args)))]
          (case (e/tag f)
            :lit-nat [[:lit (e/lit-nat-val f)] []]
            :lit-str [[:lit (e/lit-str-val f)] []]
            :const [[:const (e/const-name f) (count args)] rev]
            :fvar [[:fvar (e/fvar-id f) (count args)] rev]
            :mvar [(if match? other star) []]
            :proj [[:proj (e/proj-type-name f) (e/proj-idx f) (count args)] (into [(e/proj-struct f)] rev)]
            :forall [arrow [(e/forall-type f)]]
            [other []])))))

(defn get-unify
  "Lean's `DiscrTree.getUnify`: the values whose keys may unify with `x`, in Lean's order (the
   root's star values, then a traversal visiting star edges before the matching edge).
   `roots` is {root-key → trie}; `root-trie` fetches one lazily."
  [mctx st root-trie x]
  (let [[k args] (key-args mctx st x true false)]
    (letfn [(process [skip todo node result]
              (let [{:keys [vs cs]} node]
                (if (pos? skip)
                  (reduce (fn [r [ck c]] (process (+ (dec skip) (key-arity ck)) todo c r)) result cs)
                  (cond
                    (empty? todo) (into result vs)
                    (empty? cs) result
                    :else
                    (let [x (peek todo)
                          todo (pop todo)
                          [k args] (key-args mctx st x false false)]
                      (if (= (nth k 0) :star)
                        (reduce (fn [r [ck c]] (process (key-arity ck) todo c r)) result cs)
                        (let [result (let [[k0 c0] (nth cs 0)]
                                       (if (= (nth k0 0) :star) (process 0 todo c0 result) result))
                              j (child-index cs k)]
                          (if (neg? j)
                            result
                            (process 0 (into todo args) (nth (nth cs j) 1) result)))))))))]
      (if (= (nth k 0) :star)
        ;; a star query (never a class application) — every root
        (throw (ex-info "instance index: a star query has no class" {:query x}))
        (let [result (vec (:vs (root-trie star)))]
          (if-let [c (root-trie k)]
            (process 0 args c result)
            result))))))

(defn get-match
  "Lean's `DiscrTree.getMatch`: the values whose keys match `x` (whose metavariables are not
   instantiated by matching), in Lean's order."
  [mctx st root-trie x]
  (let [[k args] (key-args mctx st x true true)]
    (letfn [(walk [todo node result]
              (let [{:keys [vs cs]} node]
                (cond
                  (empty? todo) (into result vs)
                  (empty? cs) result
                  :else
                  (let [x (peek todo)
                        todo (pop todo)
                        [k args] (key-args mctx st x false true)
                        [k0 c0] (nth cs 0)
                        result (if (= :star (nth k0 0)) (walk todo c0 result) result)]
                    (if (= :star (nth k 0))
                      result
                      (let [j (child-index cs k)]
                        (if (neg? j) result (walk (into todo args) (nth (nth cs j) 1) result))))))))]
      (let [result (vec (:vs (root-trie star)))]
        (if (= :star (nth k 0))
          result
          (if-let [c (root-trie k)] (walk args c result) result))))))

;; ============================================================
;; Classes: out-params and out-level-params (Class.lean)
;; ============================================================

(defn- has-loose-bvar?
  "Does `x` contain the loose bound variable `k` (counted at the top of `x`)?"
  [x k]
  (letfn [(go [x d]
              (when (e/has-loose-bvars? x d)
                (case (e/tag x)
                  :bvar (= (e/bvar-idx x) (+ k d))
                  :app (or (go (e/app-fn x) d) (go (e/app-arg x) d))
                  :lam (or (go (e/lam-type x) d) (go (e/lam-body x) (inc d)))
                  :forall (or (go (e/forall-type x) d) (go (e/forall-body x) (inc d)))
                  :let (or (go (e/let-type x) d) (go (e/let-value x) d) (go (e/let-body x) (inc d)))
                  :mdata (go (e/mdata-expr x) d)
                  :proj (go (e/proj-struct x) d)
                  false)))]
    (boolean (go x 0))))

(defn- level-params-in
  "The universe parameter names occurring in `x`."
  [x]
  (let [acc (java.util.HashSet.)]
    (letfn [(lv [l]
              (when (lvl/has-param? l)
                (case (lvl/tag l)
                  :param (.add acc (lvl/param-name l))
                  :succ (lv (lvl/succ-pred l))
                  :max (do (lv (lvl/max-lhs l)) (lv (lvl/max-rhs l)))
                  :imax (do (lv (lvl/imax-lhs l)) (lv (lvl/imax-rhs l)))
                  nil)))
            (go [x]
                (when (e/has-level-param-flag x)
                  (case (e/tag x)
                    :sort (lv (e/sort-level x))
                    :const (run! lv (e/const-levels x))
                    :app (do (go (e/app-fn x)) (go (e/app-arg x)))
                    :lam (do (go (e/lam-type x)) (go (e/lam-body x)))
                    :forall (do (go (e/forall-type x)) (go (e/forall-body x)))
                    :let (do (go (e/let-type x)) (go (e/let-value x)) (go (e/let-body x)))
                    :mdata (go (e/mdata-expr x))
                    :proj (go (e/proj-struct x))
                    nil)))]
      (go x))
    (set acc)))

(defn- app-of? [x s]
  (const-named? (e/get-app-fn x) s))

(defn class-info
  "Lean's classExtension entry for class `cls`, computed from its declaration as `addClass` does:
   {:out-params #{i} — `checkOutParam`: `outParam` binders and instance-implicit binders depending
                        on one,
    :semi-out-params #{i} — binders of type `semiOutParam _`,
    :out-level-params #{i} — `computeOutLevelParams`: universe params occurring only in out-param
                        domains}. nil when the constant is unknown."
  [^Env env cls]
  (when-let [^ConstantInfo ci (env/lookup env cls)]
    (loop [t (.type ci) i 0 outs #{} semis #{} nonout-levels #{}]
      (if (e/forall? t)
        (let [d (e/forall-type t)
              out? (or (app-of? d "outParam")
                       (and (= :inst-implicit (e/forall-info t))
                            (some (fn [j] (has-loose-bvar? d (- i 1 j))) outs)))]
          (recur (e/forall-body t) (inc i) (if out? (conj outs i) outs)
                 (if (app-of? d "semiOutParam") (conj semis i) semis)
                 (if out? nonout-levels (into nonout-levels (level-params-in d)))))
        {:out-params outs
         :semi-out-params semis
         :out-level-params (into #{} (keep-indexed (fn [i p] (when-not (contains? nonout-levels p) i)))
                                 (vec (.levelParams ci)))}))))

;; ============================================================
;; computeSynthOrder (Instances.lean)
;; ============================================================

(defn- fvar-ids-in
  "The fvar ids occurring in `x` (after zonking)."
  [x]
  (let [acc (java.util.HashSet.)]
    (letfn [(go [x]
                (when (e/has-fvar-flag x)
                  (case (e/tag x)
                    :fvar (.add acc (e/fvar-id x))
                    :app (do (go (e/app-fn x)) (go (e/app-arg x)))
                    :lam (do (go (e/lam-type x)) (go (e/lam-body x)))
                    :forall (do (go (e/forall-type x)) (go (e/forall-body x)))
                    :let (do (go (e/let-type x)) (go (e/let-value x)) (go (e/let-body x)))
                    :mdata (go (e/mdata-expr x))
                    :proj (go (e/proj-struct x))
                    nil)))]
      (go x))
    (set acc)))

(defn- open-telescope
  "forallTelescopeReducing at `mode` transparency: [st' fvar-ids binder-infos types body]."
  [mctx st ty mode]
  (loop [t ty st st ids [] bis [] types []]
    (let [t (meta/zonk-expr mctx t)]
      (if (e/forall? t)
        (let [fid (swap! (:next-id st) inc)
              d (e/forall-type t)
              st (assoc st :lctx (assoc (:lctx st) fid {:tag :local :id fid :name (e/forall-name t) :type d
                                                        :binder-info (e/forall-info t)}))]
          (recur (e/instantiate1 (e/forall-body t) (e/fvar fid)) st (conj ids fid) (conj bis (e/forall-info t)) (conj types d)))
        (let [t' (if (= mode :default) (meta/whnf mctx st t) (meta/whnf-at mctx st t mode))]
          (if (e/forall? t')
            (recur t' st ids bis types)
            [st ids bis types t]))))))

(defn semi-out-positions
  "Lean `computeSynthOrder.getSemiOutParamPositionsOf`."
  [ctx class-ty]
  (let [h (e/get-app-fn class-ty)]
    (if (e/const? h)
      (let [{:keys [out-params semi-out-params]} ((:class-info ctx) (e/const-name h))]
        (into (or out-params #{}) semi-out-params))
      #{})))

(defn compute-synth-order
  "Lean's `computeSynthOrder` for an instance of type `inst-type` (level params kept), at
   reducible transparency. `proj-info` is the instance's projection-function info. Returns the
   positions of the instance-implicit binders in synthesis order: a subgoal is ready once its
   non-(semi-)out-param arguments are known; the conclusion's non-out arguments are known from the
   start; synthesizing a subgoal makes its type and value known. When no subgoal is ready (Lean
   refuses to register such an instance) the first remaining one is taken."
  [ctx mctx st inst-type proj-info]
  (let [[st xs bis types body] (open-telescope mctx st inst-type :reducible)
        n (count xs)
        pos-of (zipmap xs (range))
        known (volatile! #{})
        assign-in! (fn assign-in! [x]
                     (doseq [fid (fvar-ids-in x)]
                       (when-let [j (pos-of fid)]
                         (when-not (contains? @known j)
                           (vswap! known conj j)
                           (assign-in! (nth types j))))))
        unknown-in? (fn [x] (some (fn [fid] (when-let [j (pos-of fid)] (not (contains? @known j)))) (fvar-ids-in x)))
        ty (meta/whnf-at mctx st body :reducible)
        ty-outs (semi-out-positions ctx ty)]
    (doseq [[i a] (map-indexed vector (e/get-app-args ty))]
      (when-not (contains? ty-outs i) (assign-in! a)))
    (loop [to-synth (filterv #(or (= :inst-implicit (nth bis %))
                                  (and proj-info (:from-class? proj-info) (= % (:num-params proj-info))))
                             (range n))
           synthed []]
      (if (empty? to-synth)
        synthed
        (let [ready? (fn [i]
                       (let [arg-ty (nth types i)]
                         (if (and proj-info (= (:num-params proj-info) i))
                           (do (assign-in! arg-ty) true)
                           (let [[st' _ _ _ b] (open-telescope mctx st arg-ty :reducible)
                                 b (meta/whnf-at mctx st' b :reducible)
                                 outs (semi-out-positions ctx b)]
                             (every? (fn [[j a]] (or (contains? outs j) (not (unknown-in? a))))
                                     (map-indexed vector (e/get-app-args b)))))))
              nxt (or (first (filter ready? to-synth)) (first to-synth))]
          (assign-in! (nth types nxt))
          (vswap! known conj nxt)
          (recur (filterv #(not= % nxt) to-synth) (conj synthed nxt)))))))

;; ============================================================
;; Instance entries: keys and synthesis order
;; ============================================================

(def index-version
  "Version of the key/synth-order computation persisted in registry entries (`:dt-version`). An
   entry computed by another version is recomputed."
  2)

(defn mk-ctx
  "A key-computation context over `env` and the registry `index` (classes = Lean's class extension
   and the registry's classes)."
  [^Env env index]
  (let [classes (env/get-extension env :classes #{})
        env-index (env/get-extension env :instances {})
        ;; Lean's classExtension: the env's exported classes, and the classes of the registries
        ;; at hand (the store's and the one synthesis was asked to use)
        class? (fn [n] (or (contains? index n) (contains? env-index n) (contains? classes (name/->string n))))
        ci-cache (atom {})]
    {:env env
     :class? class?
     :class-info (fn [n] (if-let [hit (find @ci-cache n)] (val hit)
                                 (let [r (class-info env n)] (swap! ci-cache assoc n r) r)))
     :param-cache (atom {})
     :st (tc/mk-tc-state env)}))

(defn- fresh-st [ctx]
  (let [st (:st ctx)] (assoc st :lctx (:lctx st))))

(defn instance-keys
  "Lean's `mkInstanceKey`: the type opened with metavariables (`forallMetaTelescopeReducing`, at
   default transparency), then `mkPath` of its conclusion."
  [ctx ^ConstantInfo ci]
  (let [st (fresh-st ctx)]
    (loop [t (.type ci) mctx meta/empty-context]
      (let [t (meta/zonk-expr mctx t)]
        (if (e/forall? t)
          (let [id (swap! (:next-id st) inc)
                mctx (meta/add-expr-mvar-decl mctx id (e/forall-type t) (:lctx st))]
            (recur (e/instantiate1 (e/forall-body t) (e/mvar id)) mctx))
          (let [t' (meta/whnf mctx st t)]
            (if (e/forall? t')
              (recur t' mctx)
              (mk-path ctx mctx st t))))))))

(defn entry-data
  "{:keys :synth-order} of a registry entry for instance `n` in `env`, or nil when `env` lacks it."
  [ctx n]
  (when-let [^ConstantInfo ci (env/lookup (:env ctx) n)]
    {:keys (instance-keys ctx ci)
     :synth-order (compute-synth-order ctx meta/empty-context (fresh-st ctx) (.type ci)
                                       (meta/projection-fn-info (:env ctx) n))}))

(defn annotated?
  "Does the registry entry carry keys and synthesis order of the current version?"
  [entry]
  (and (= index-version (:dt-version entry)) (:keys entry) (:synth-order entry)))

(defn annotate-registry
  "The registry with every entry's `:keys`, `:synth-order` (and `:dt-version`) computed from
   `env` — what a store persists in its derived `:instances` blob so that sessions never load
   candidate declarations to select them. Entries `env` lacks are kept unannotated.
   `parallelism` threads share the work (lookups dominate)."
  [^Env env index & {:keys [parallelism] :or {parallelism 1}}]
  (let [;; the class extension as a session sees it: which structures are classes decides which
        ;; projections stay folded and which arguments are instances
        env (if (env/get-extension env :instances nil) env (env/with-extension env :instances index))
        ctxs (vec (repeatedly parallelism #(mk-ctx env index)))
        entries (vec (for [[cls es] index [i en] (map-indexed vector es)] [cls i en]))
        pool (java.util.concurrent.Executors/newFixedThreadPool parallelism)
        chunks (partition-all (max 1 (quot (+ (count entries) parallelism -1) parallelism)) entries)
        futs (mapv (fn [ctx chunk]
                     (.submit pool ^Callable (fn []
                                               (mapv (fn [[cls i en]]
                                                       [cls i (cond
                                                                ;; never a candidate in this env
                                                                (nil? (env/lookup env (:name en)))
                                                                (assoc en :keys [] :synth-order [] :dt-version index-version)
                                                                :else
                                                                (if-let [d (try (entry-data ctx (:name en))
                                                                                (catch clojure.lang.ExceptionInfo _ nil))]
                                                                  (assoc en :keys (:keys d) :synth-order (:synth-order d)
                                                                         :dt-version index-version)
                                                                  en))])
                                                     chunk))))
                   ctxs chunks)]
    (try
      (reduce (fn [idx [cls i en]] (assoc-in idx [cls i] en))
              index (mapcat #(.get ^java.util.concurrent.Future %) futs))
      (finally (.shutdown pool)))))
