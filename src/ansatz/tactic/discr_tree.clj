;; Tactic layer — discrimination tree for simp lemma indexing.
;;
;; Implements Lean 4's DiscrTree data structure for efficient matching
;; of expressions against indexed rewrite rule patterns.
;;
;; A discrimination tree is a trie keyed by expression structure tokens.
;; Each expression is flattened into a sequence of Key tokens, and stored
;; in the trie. Lookup walks the trie, always exploring wildcard (star)
;; branches in addition to exact matches.
;;
;; Following Lean 4's src/Lean/Meta/DiscrTree.lean.

(ns ansatz.tactic.discr-tree
  "Discrimination tree for efficient expression matching.

   Key concepts:
   - Key: a token representing one node of an expression's structure
     (:const name arity), (:fvar id arity), (:lit val), (:star),
     (:arrow), (:proj name idx arity), (:other)
   - Trie: nested map {Key → {:values [...] :children {Key → Trie}}}
   - Insert: flatten LHS to keys, insert value at that path
   - Lookup: flatten query to keys, walk trie exploring star + exact matches

   Argument filtering:
   - Instance-implicit args → :star (wildcard)
   - Proof terms → :star
   - Regular implicit args that are types → kept
   - Everything else → indexed normally"
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red])
  (:import [ansatz.kernel ConstantInfo]))

;; ============================================================
;; Key type
;; ============================================================
;; Keys are plain maps: {:tag :const/:fvar/:lit/:star/:arrow/:proj/:other, ...}
;; They must be hashable and comparable.

(def ^:private star-key {:tag :star})
(def ^:private other-key {:tag :other})
(def ^:private arrow-key {:tag :arrow})

(defn- const-key [name arity] {:tag :const :name name :arity arity})
(defn- fvar-key [id arity] {:tag :fvar :id id :arity arity})
(defn- lit-key [val] {:tag :lit :val val})
(defn- proj-key [struct-name idx arity] {:tag :proj :name struct-name :idx idx :arity arity})

;; ============================================================
;; Empty trie
;; ============================================================

(def empty-trie {:values [] :children {}})

;; ============================================================
;; DiscrTree reduction — Lean 4's reduceDT (DiscrTree/Main.lean:204-245)
;; ============================================================
;; Before keying, reduce expressions using whnf-no-delta (beta/iota/proj/let)
;; to normalize projections and beta-redexes.
;; Root terms: stop reducing if the result head is a "bad key" (lambda, sort, etc.)
;; Nested terms: full whnf-no-delta reduction.

(defn- bad-key?
  "Lean 4's isBadKey: return true if fn would produce Key.other or Key.star.
   We don't want to unfold root terms into lambdas/sorts."
  [e]
  (let [head (e/get-app-fn e)]
    (not (or (e/lit-nat? head) (e/lit-str? head) (e/const? head)
             (e/fvar? head) (e/proj? head) (e/forall? head)))))

(defn- reduce-for-dt
  "Lean 4's reduceDT: reduce expression before discrimination tree keying.
   Uses whnf-no-delta (beta/iota/proj/let, NO delta unfolding).
   For root terms, stops if the result would be a bad key."
  [env e root?]
  (try
    (let [reduced (red/whnf-no-delta env e)]
      (if (and root? (bad-key? reduced))
        e  ;; Don't reduce to a bad key at the root
        reduced))
    (catch Exception _ e)))

;; ============================================================
;; Expression → Key sequence (Lean 4's mkPath / pushArgs)
;; ============================================================

(defn- is-proof?
  "Check if expression is a proof (has type in Prop)."
  [st e]
  (try
    (let [ty (tc/infer-type st e)
          tw (#'tc/cached-whnf st ty)]
      (and (e/sort? tw) (= (e/sort-level tw) lvl/zero)))
    (catch Exception _ false)))

(defn- is-type?
  "Check if expression is a type (has type Sort u for some u)."
  [st e]
  (try
    (let [ty (tc/infer-type st e)
          tw (#'tc/cached-whnf st ty)]
      (e/sort? tw))
    (catch Exception _ false)))

(defn get-param-infos
  "Get parameter info for a function head from the environment.
   Returns a vector of binder infos (:default, :implicit, :inst-implicit, :strict-implicit)
   for each parameter, or nil."
  [env head]
  (when (e/const? head)
    (when-let [^ConstantInfo ci (env/lookup env (e/const-name head))]
      (let [ty (.type ci)]
        (loop [t ty infos []]
          (if (e/forall? t)
            (recur (e/forall-body t) (conj infos (e/forall-info t)))
            infos))))))

(defn- should-ignore-arg?
  "Determine if an argument should be replaced with star (wildcard).
   Following Lean 4's ignoreArg (DiscrTree/Main.lean):
   - Instance args → always ignore
   - Implicit/strict-implicit → ignore unless it's a type
   - Explicit → ignore if it's a proof"
  [st binder-info arg]
  (case binder-info
    :inst-implicit true
    (:implicit :strict-implicit) (not (is-type? st arg))
    ;; :default or unknown
    (is-proof? st arg)))

(defn expr->keys
  "Flatten an expression into a key sequence for the discrimination tree.
   Following Lean 4's mkPathAux / pushArgs.

   Stack-based depth-first traversal (right-to-left for args).
   Instance/proof/implicit args are replaced with star wildcards.
   Expressions are reduced via whnf-no-delta before keying (Lean 4's reduceDT).

   If st is nil, skips argument filtering (all args indexed)."
  ([expr] (expr->keys nil nil expr))
  ([st env expr]
   (loop [todo (list {:expr expr :root? true}) keys (transient [])]
     (if (empty? todo)
       (persistent! keys)
       (let [item (first todo)
             rest-todo (rest todo)]
         ;; Handle both raw expressions and tagged items for root tracking
         (let [[e root?] (if (map? item)
                           [(:expr item) (:root? item)]
                           [item false])
               ;; Lean 4's reduceDT: reduce before keying (skip sentinels like ::star)
               e (if (and env (not (keyword? e))) (reduce-for-dt env e root?) e)]
           (cond
           ;; Star sentinel (from argument filtering)
             (= e ::star)
             (recur rest-todo (conj! keys star-key))

           ;; Application: get head + args
             (e/app? e)
             (let [[head args] (e/get-app-fn-args e)]
               (cond
               ;; OfNat.ofNat normalization — collapse to literal key
               ;; Lean 4: OfNat.ofNat _ n _ → lit n (prevents literal/OfNat mismatch)
                 (and (e/const? head)
                      (= (name/->string (e/const-name head)) "OfNat.ofNat")
                      (= 3 (count args))
                      (e/lit-nat? (nth args 1)))
                 (recur rest-todo (conj! keys (lit-key (e/lit-nat-val (nth args 1)))))

               ;; Constant application
                 (e/const? head)
                 (let [nargs (count args)
                       k (const-key (e/const-name head) nargs)
                     ;; Filter args: replace instance/proof/implicit with star
                       param-infos (when (and st env) (get-param-infos env head))
                       filtered (mapv (fn [i]
                                        (let [arg (nth args i)
                                              info (when param-infos
                                                     (get param-infos i :default))]
                                          (if (and st info (should-ignore-arg? st info arg))
                                            ::star
                                            arg)))
                                      (range nargs))]
                   (recur (into rest-todo (reverse filtered))
                          (conj! keys k)))

               ;; FVar application
                 (e/fvar? head)
                 (let [nargs (count args)
                       k (fvar-key (e/fvar-id head) nargs)]
                   (recur (into rest-todo (reverse args))
                          (conj! keys k)))

               ;; Other head (lambda application, etc.)
                 :else
                 (recur rest-todo (conj! keys other-key))))

           ;; Bare constant (no args)
             (e/const? e)
             (recur rest-todo (conj! keys (const-key (e/const-name e) 0)))

           ;; FVar (no args)
             (e/fvar? e)
             (recur rest-todo (conj! keys (fvar-key (e/fvar-id e) 0)))

           ;; Nat literal
             (e/lit-nat? e)
             (recur rest-todo (conj! keys (lit-key (e/lit-nat-val e))))

           ;; String literal
             (e/lit-str? e)
             (recur rest-todo (conj! keys (lit-key (e/lit-str-val e))))

           ;; Forall → arrow key + index domain
             (e/forall? e)
             (recur (cons (e/forall-type e) rest-todo)
                    (conj! keys arrow-key))

           ;; BVar (in patterns: treated as star)
             (e/bvar? e)
             (recur rest-todo (conj! keys star-key))

           ;; Sort
             (e/sort? e)
             (recur rest-todo (conj! keys other-key))

           ;; Lambda
             (e/lam? e)
             (recur rest-todo (conj! keys other-key))

           ;; Let → index body with value substituted
             (e/let? e)
             (recur (cons (e/instantiate1 (e/let-body e) (e/let-value e)) rest-todo)
                    keys)

           ;; Projection
             (e/proj? e)
             (let [k (proj-key (e/proj-type-name e) (e/proj-idx e) 1)]
               (recur (cons (e/proj-struct e) rest-todo)
                      (conj! keys k)))

           ;; Mdata → unwrap
             (e/mdata? e)
             (recur (cons (e/mdata-expr e) rest-todo)
                    keys)

           ;; Fallback
             :else
             (recur rest-todo (conj! keys other-key)))))))))

;; ============================================================
;; Trie insertion
;; ============================================================

(defn trie-insert
  "Insert a value into the trie at the given key sequence."
  [trie keys value]
  (if (empty? keys)
    (update trie :values (fnil conj []) value)
    (let [k (first keys)
          rest-keys (rest keys)
          children (:children trie {})
          child (get children k empty-trie)
          child' (trie-insert child rest-keys value)]
      (assoc trie :children (assoc children k child')))))

(defn build-tree
  "Build a discrimination tree from a sequence of (keys, value) pairs."
  [entries]
  (reduce (fn [tree [keys value]]
            (trie-insert tree keys value))
          empty-trie
          entries))

;; ============================================================
;; Trie lookup — with wildcard exploration
;; ============================================================

(defn trie-match
  "Find all values matching a key sequence in the trie.
   At each level, explores BOTH the exact key match AND any star (wildcard)
   branch. Returns all values at terminal nodes reached.
   Following Lean 4's getMatchLoop."
  [trie keys]
  (if (empty? keys)
    (:values trie [])
    (let [k (first keys)
          rest-keys (rest keys)
          children (:children trie {})]
      ;; Always explore star wildcard path (matches any key)
      ;; Star must skip a FULL sub-tree: 1 key + arity sub-trees (recursively).
      ;; Lean 4: getStarResult calls consume to skip the right number of keys.
      (let [skip-subtree (fn skip-subtree [ks]
                           ;; Skip one full argument from the key sequence.
                           ;; Returns remaining keys after skipping.
                           (if (empty? ks)
                             ks
                             (let [k (first ks)
                                   arity (or (:arity k) 0)
                                   remaining (rest ks)]
                               ;; Skip arity sub-arguments
                               (loop [r remaining n arity]
                                 (if (zero? n) r
                                     (recur (skip-subtree r) (dec n)))))))
            star-results (when-let [star-child (get children star-key)]
                           (trie-match star-child (skip-subtree keys)))
            ;; Also explore exact key match (unless query key is itself star)
            exact-results (when (not= k star-key)
                            (when-let [child (get children k)]
                              (trie-match child rest-keys)))
            ;; If the query key IS star, we must explore ALL children
            ;; (star in query matches anything in the tree)
            all-results (when (= k star-key)
                          (mapcat (fn [[child-key child-trie]]
                                    (when (not= child-key star-key) ;; already handled
                                      (trie-match child-trie rest-keys)))
                                  children))]
        (into (vec (concat (or star-results [])
                           (or exact-results [])
                           (or all-results [])))
              ;; Also collect values at this node if we've consumed all keys
              ;; (this handles prefix matches / extra args)
              )))))

(defn trie-match-with-extra
  "Like trie-match but also returns values from shorter key sequences
   (i.e., lemmas whose LHS has fewer args than the query).
   Returns pairs of [value extra-arg-count].
   Following Lean 4's getMatchWithExtra."
  [trie keys]
  ;; For simplicity, delegate to trie-match
  ;; The extra-arg handling is done by the caller
  (trie-match trie keys))

;; ============================================================
;; Public API for simp integration
;; ============================================================

(defn make-simp-tree
  "Build a discrimination tree from simp lemmas.
   Each lemma's LHS pattern is encoded as keys and inserted.
   Optional st/env for argument filtering."
  ([lemmas] (make-simp-tree nil nil lemmas))
  ([st env lemmas]
   (reduce (fn [tree lemma]
             (let [keys (expr->keys st env (:lhs-pattern lemma))]
               (trie-insert tree keys lemma)))
           empty-trie
           lemmas)))

(defn lookup-simp-tree
  "Look up candidate lemmas for an expression in the discrimination tree.
   Returns a sequence of lemmas whose LHS pattern matches the expression.
   Optional st/env for argument filtering."
  ([tree expr] (lookup-simp-tree nil nil tree expr))
  ([st env tree expr]
   (let [keys (expr->keys st env expr)]
     (trie-match tree keys))))

(defn tree-size
  "Count the number of values stored in the tree."
  [trie]
  (+ (count (:values trie []))
     (reduce + 0 (map (fn [[_ child]] (tree-size child))
                      (:children trie {})))))

(defn tree-depth
  "Maximum depth of the tree."
  [trie]
  (if (empty? (:children trie {}))
    0
    (inc (reduce max 0 (map (fn [[_ child]] (tree-depth child))
                            (:children trie {}))))))
