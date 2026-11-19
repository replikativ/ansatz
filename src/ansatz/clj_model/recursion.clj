(ns ansatz.clj-model.recursion
  "Conformance proofs of recursive models (ansatz.clj-model G3).

   A recursive group runs as `CljM.fix<k> F fuel tag x…`, structural recursion on the fuel
   (`none` when it runs out). The conformance goal of a model that enters a group is, after the
   default computation (proof/compute-script), `Q (CljM.fix<k> F e tag a…)`: the group's result
   at the default fuel `e`, inside the context `Q` the entry puts it in (the result decoder).

   `CljM.fix<k>.induct`, proved once per k, is the adequacy argument:
     for an invariant `I` on arguments, a measure `μ` and a property `Q` of results, if one
     step of `F` establishes `Q` whenever its recursive calls on arguments in `I` of smaller
     measure do, then `Q (fix<k> F fuel t x…)` for every fuel above `μ t x…`.
   So no fuel arithmetic and no unfolding of the fixpoint at a symbolic fuel is needed: the step
   is proved with `self` abstract.

   The default choice, `prove-group!`:
   - μ is the sum of `CljM.weight` of the arguments, the measure the default fuel is built from
     (ansatz.clj-model/recursion-forms), so `μ a… < e` holds at every entry;
   - Q is the entry's context, the goal with the group call abstracted;
   - I is a disjunction of templates `∃ v…, x₁ = A₁[v…] ∧ …`, the shapes the arguments take.
     The templates start from the entry's arguments, as functions of the parameters' variables;
     a recursive call whose arguments match no template adds a template, until one step from
     every template ends in calls on templates (at most `max-rounds`).
   The step from template A is: case-split its List variables, unfold `F` with `self` abstract,
   compute with `clj_model`, split the `if`s, and close every remaining goal, a recursive call
   `Q (self t' y…)`, by the hypothesis: `y…` in `I` by matching a template (`clj_model_inv`),
   the measure decrease by simp and omega.

   This proves recursion whose recursive calls are in a position `Q` reads (tail calls, as
   `loop`/`recur` always are, and calls whose result the step only needs to decode as `Q`
   does). A call whose result the step computes with (`(inc (len (next s)))`) needs a stronger
   `Q` than the entry's, which this does not guess; nor does it look inside a nested group."
  (:require [clojure.string :as str]
            [ansatz.core :as a]
            [ansatz.state :as state]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.proof :as tp])
  (:import [ansatz.kernel ConstantInfo Expr]))

;; ── Expressions ─────────────────────────────────────────────────────────────────────────

(defn- nm [s] (name/from-string s))
(defn- c [s] (e/const' (nm s) []))
(def ^:private l1 (lvl/succ lvl/zero))
(def ^:private V (c "CljM.V"))
(def ^:private NatT (c "Nat"))
(def ^:private Prop (e/sort' lvl/zero))
(def ^:private OptV (e/app (e/const' (nm "Option") [lvl/zero]) V))

(defn- arrows [doms cod] (reduce (fn [acc d] (e/forall' "_" d acc :default)) cod (reverse doms)))

(defn- self-type [k] (arrows (cons NatT (repeat k V)) OptV))

(def ^:private fresh (atom 7000000000))
(defn- fresh-id [] (swap! fresh inc))

(defn- pi
  "∀ binders, body. `binders` [[id name type] …], outermost first; a type may mention the
   fvars of earlier binders."
  [binders body]
  (reduce (fn [b [id n t]] (e/forall' n t (e/abstract1 b id) :default)) body (rseq (vec binders))))

(defn- lam*
  [binders body]
  (reduce (fn [b [id n t]] (e/lam n t (e/abstract1 b id) :default)) body (rseq (vec binders))))

(defn- nat-lt [a b]
  (e/app* (e/const' (nm "LT.lt") [lvl/zero]) NatT (c "instLTNat") a b))

(defn- nat-add [a b]
  (e/app* (e/const' (nm "HAdd.hAdd") [lvl/zero lvl/zero lvl/zero]) NatT NatT NatT
          (e/app* (e/const' (nm "instHAdd") [lvl/zero]) NatT (c "instAddNat")) a b))

(defn- eqV [a b] (e/app* (e/const' (nm "Eq") [l1]) V a b))
(defn- and* [ps] (reduce (fn [acc p] (e/app* (c "And") p acc)) (last ps) (reverse (butlast ps))))
(defn- or* [ps] (reduce (fn [acc p] (e/app* (c "Or") p acc)) (last ps) (reverse (butlast ps))))

(defn- sort-level-of [env ty]
  (let [st (tc/mk-tc-state env)]
    (e/sort-level (#'tc/cached-whnf st (tc/infer-type st ty)))))

(defn- fvars-in
  "The fvar ids occurring in `x`, in first-occurrence order."
  [x]
  (let [out (java.util.LinkedHashSet.)
        seen (java.util.IdentityHashMap.)]
    (letfn [(walk [x]
              (when-not (.containsKey seen x)
                (.put seen x true)
                (case (e/tag x)
                  :fvar (.add out (e/fvar-id x))
                  :app (do (walk (e/app-fn x)) (walk (e/app-arg x)))
                  :lam (do (walk (e/lam-type x)) (walk (e/lam-body x)))
                  :forall (do (walk (e/forall-type x)) (walk (e/forall-body x)))
                  :let (do (walk (e/let-type x)) (walk (e/let-value x)) (walk (e/let-body x)))
                  :proj (walk (e/proj-struct x))
                  :mdata (walk (e/mdata-expr x))
                  nil)))]
      (walk x))
    (vec out)))

(defn- replace-subterm
  "`x` with every subterm equal to `old` replaced by `new` (an fvar, so no binder shifting)."
  [x old new]
  (letfn [(go [x]
              (if (= x old)
                new
                (case (e/tag x)
                  :app (let [f (go (e/app-fn x)) a (go (e/app-arg x))]
                         (if (and (identical? f (e/app-fn x)) (identical? a (e/app-arg x))) x (e/app f a)))
                  :lam (let [t (go (e/lam-type x)) b (go (e/lam-body x))]
                         (if (and (identical? t (e/lam-type x)) (identical? b (e/lam-body x))) x
                             (e/lam (e/lam-name x) t b (e/lam-info x))))
                  :forall (let [t (go (e/forall-type x)) b (go (e/forall-body x))]
                            (if (and (identical? t (e/forall-type x)) (identical? b (e/forall-body x))) x
                                (e/forall' (e/forall-name x) t b (e/forall-info x))))
                  x)))]
    (go x)))

;; ── The group call in a goal ────────────────────────────────────────────────────────────

(defn fix-call
  "The first `CljM.fix<k> F fuel tag a…` application in `x` (fully applied, k = 1…8), as
   {:k :F :fuel :tag :args :expr}, or nil."
  [x]
  (let [seen (java.util.IdentityHashMap.)]
    (letfn [(walk [x]
              (when-not (.containsKey seen x)
                (.put seen x true)
                (or (when (e/app? x)
                      (let [[h args] (e/get-app-fn-args x)]
                        (when (e/const? h)
                          (when-let [[_ k] (re-matches #"CljM\.fix(\d)" (name/->string (e/const-name h)))]
                            (let [k (parse-long k)]
                              (when (= (count args) (+ 3 k))
                                {:k k :F (nth args 0) :fuel (nth args 1) :tag (nth args 2)
                                 :args (vec (drop 3 args)) :expr x}))))))
                    (case (e/tag x)
                      :app (or (walk (e/app-fn x)) (walk (e/app-arg x)))
                      :lam (or (walk (e/lam-type x)) (walk (e/lam-body x)))
                      :forall (or (walk (e/forall-type x)) (walk (e/forall-body x)))
                      nil))))]
      (walk x))))

;; ── The generic lemma CljM.fix<k>.induct ────────────────────────────────────────────────

(defn- induct-name [k] (str "CljM.fix" k ".induct"))

(defn ensure-induct!
  "Prove `CljM.fix<k>.induct` once per env:
     ∀ F I Q μ, (∀ self t x…, I t x… → (∀ t' y…, I t' y… → μ t' y… < μ t x… → Q (self t' y…))
                              → Q (F self t x…))
              → ∀ fuel t x…, I t x… → μ t x… < fuel → Q (CljM.fix<k> F fuel t x…)
   by induction on the fuel: at 0 the measure bound is false, at n + 1 the fixpoint unfolds
   to `F (CljM.fix<k> F n)` and the step applies, its recursive calls by the induction
   hypothesis (μ t' y… < μ t x… < n + 1)."
  [k]
  (let [nme (induct-name k)]
    (when-not (env/lookup @state/ansatz-env (nm nme))
      (let [xs (mapv #(symbol (str "x" %)) (range 1 (inc k)))
            ys (mapv #(symbol (str "y" %)) (range 1 (inc k)))
            vt (fn [zs] (vec (mapcat (fn [z] [z 'CljM.V]) zs)))
            selft (list* '=> 'Nat (concat (repeat k 'CljM.V) ['(Option CljM.V)]))
            params ['F :- (list '=> selft selft)
                    'I :- (list* '=> 'Nat (concat (repeat k 'CljM.V) ['Prop]))
                    'Q :- '(=> (Option CljM.V) Prop)
                    'mu :- (list* '=> 'Nat (concat (repeat k 'CljM.V) ['Nat]))
                    'step :- (list 'forall (into ['self selft 't 'Nat] (vt xs))
                                   (list '=> (list* 'I 't xs)
                                         (list 'forall (into ['t2 'Nat] (vt ys))
                                               (list '=> (list* 'I 't2 ys) (list '< (list* 'mu 't2 ys) (list* 'mu 't xs))
                                                     (list 'Q (list* 'self 't2 ys))))
                                         (list 'Q (list* 'F 'self 't xs))))
                    'fuel :- 'Nat]
            prop (list 'forall (into ['t 'Nat] (vt xs))
                       (list '=> (list* 'I 't xs) (list '< (list* 'mu 't xs) 'fuel)
                             (list 'Q (list* (symbol (str "CljM.fix" k)) 'F 'fuel 't xs))))
            intro-x (list* 'intro 't (concat xs '[hI hmu]))
            tactics ['(induction fuel)
                     intro-x '(omega)
                     '(rename_i n ih) intro-x (list 'rw [(symbol (str "CljM.fix" k ".eq_2"))])
                     '(apply step) '(exact hI)
                     (list* 'intro 't2 (concat ys '[hI2 hlt])) '(apply ih) '(exact hI2) '(omega)]]
        (binding [a/*verbose* false]
          (a/prove-theorem (symbol nme) params prop tactics))))
    nme))

;; ── Templates, I, μ, Q ──────────────────────────────────────────────────────────────────

(defn- template
  "A template from argument expressions `args` in the local context `lctx`: its variables are
   the fvars of `args` with their names and types."
  [lctx args]
  (let [ids (distinct (mapcat fvars-in args))]
    {:vars (mapv (fn [id] (let [d (get lctx id)] [id (or (:name d) (str "v" id)) (:type d)])) ids)
     :args (vec args)}))

(defn- template-key
  "A template up to the names of its variables."
  [{:keys [vars args]}]
  [(mapv #(nth % 2) vars) (mapv #(e/abstract-many % (mapv first vars)) args)])

(defn- disjunct
  "`∃ v…, x₁ = A₁ ∧ …` for template `tm` and argument expressions `xs`."
  [env {:keys [vars args]} xs]
  (let [body (and* (mapv eqV xs args))]
    (reduce (fn [b [id n t]]
              (e/app* (e/const' (nm "Exists") [(sort-level-of env t)]) t
                      (e/lam n t (e/abstract1 b id) :default)))
            body (rseq vars))))

(defn- inv-app [env templates xs] (or* (mapv #(disjunct env % xs) templates)))

(defn- nat-sub [a b]
  (e/app* (e/const' (nm "HSub.hSub") [lvl/zero lvl/zero lvl/zero]) NatT NatT NatT
          (e/app* (e/const' (nm "instHSub") [lvl/zero]) NatT (c "instSubNat")) a b))

(defn- nat-lit [n] (e/app* (e/const' (nm "OfNat.ofNat") [lvl/zero]) NatT (e/lit-nat n)
                           (e/app (c "instOfNatNat") (e/lit-nat n))))

(defn- weight [x] (e/app (c "CljM.weight") x))

(defn- measures
  "The measures tried for a group of k arguments and m members, in order:
   - the summed weight of the arguments (no accumulator: every call walks into its data);
   - for each position i, the weight of argument i - 1, plus m - 1 - t: one argument walks into
     its data and the others accumulate; a call to a later member on the same data (an arity
     calling the next, `([xs] (f xs 0))`) decreases the second part. The default fuel bounds
     the entry's data weight + 1, which the - 1 leaves room for."
  [k m]
  (into [{:sum true}] (map (fn [i] {:pos i :m m}) (range k))))

(defn- mu-app [mu t xs]
  (if (:sum mu)
    (reduce nat-add (map weight xs))
    (nat-add (nat-sub (weight (nth xs (:pos mu))) (nat-lit 1))
             (nat-sub (nat-lit (dec (:m mu))) t))))

(defn- binders [k]
  (let [t [(fresh-id) "t" NatT]
        xs (mapv (fn [i] [(fresh-id) (str "x" i) V]) (range 1 (inc k)))]
    [t xs]))

(defn- inv-lam [env templates k]
  (let [[t xs] (binders k)]
    (lam* (cons t xs) (inv-app env templates (mapv (comp e/fvar first) xs)))))

(defn- mu-lam [mu k]
  (let [[t xs] (binders k)]
    (lam* (cons t xs) (mu-app mu (e/fvar (first t)) (mapv (comp e/fvar first) xs)))))

(defn- q-lam [{:keys [q-body r-id]}] (lam* [[r-id "r" OptV]] q-body))
(defn- q-app [{:keys [q-body r-id]} x] (e/instantiate1 (e/abstract1 q-body r-id) x))

;; ── The tactic clj_model_inv: `I t y…` by a template ────────────────────────────────────

(defn- match-pattern
  "First-order match of `pat` (its loose bvars ≥ `depth` are the pattern variables, bvar
   `depth + i` the i-th innermost) against the closed `target`. Returns {i expr} or nil."
  [pat target]
  (let [subst (volatile! {})]
    (letfn [(go [p t depth]
                (cond
                  (and (e/bvar? p) (>= (e/bvar-idx p) depth))
                  (let [i (- (e/bvar-idx p) depth)]
                    (and (not (e/has-loose-bvars? t))
                         (if-let [old (get @subst i)] (= old t) (do (vswap! subst assoc i t) true))))
                  (not= (e/tag p) (e/tag t)) false
                  :else
                  (case (e/tag p)
                    :app (and (go (e/app-fn p) (e/app-fn t) depth) (go (e/app-arg p) (e/app-arg t) depth))
                    :lam (and (go (e/lam-type p) (e/lam-type t) depth) (go (e/lam-body p) (e/lam-body t) (inc depth)))
                    :forall (and (go (e/forall-type p) (e/forall-type t) depth)
                                 (go (e/forall-body p) (e/forall-body t) (inc depth)))
                    (= p t))))]
      (when (go pat target 0) @subst))))

(defn- const-app? [x s n]
  (let [[h args] (e/get-app-fn-args x)]
    (when (and (e/const? h) (= s (name/->string (e/const-name h))) (= n (count args))) args)))

(defn- prove-disjunct
  "A proof of the disjunct `d` (`∃ v…, x = A ∧ …` with the x concrete), or nil."
  [d]
  (let [;; peel the ∃ chain: [[level type lam] …] and the equations' body
        [exs body] (loop [x d acc []]
                     (if-let [[t p] (const-app? x "Exists" 2)]
                       (recur (e/lam-body p) (conj acc [(first (e/const-levels (e/get-app-fn x))) t p]))
                       [acc x]))
        m (count exs)
        eqs (loop [x body acc []]
              (if-let [[p q] (const-app? x "And" 2)] (recur q (conj acc p)) (conj acc x)))
        ;; match every `x = A` (A under the m binders: bvar 0 is the innermost ∃ variable)
        subst (reduce (fn [s q]
                        (when s
                          (when-let [[_ x pat] (const-app? q "Eq" 3)]
                            (when-let [s2 (match-pattern pat x)]
                              (when (every? (fn [[i v]] (or (not (contains? s i)) (= v (get s i)))) s2)
                                (merge s s2))))))
                      {} eqs)]
    (when (and subst (= m (count subst)))
      (let [ws (mapv #(get subst (- m 1 %)) (range m))  ; outermost first
            refl (fn [q] (let [[ty x _] (const-app? q "Eq" 3)]
                           (e/app* (e/const' (nm "Eq.refl") (e/const-levels (e/get-app-fn q))) ty x)))
            inst-eqs (mapv #(e/instantiate % ws) eqs)
            conj-proof (reduce (fn [acc [p q]] (e/app* (c "And.intro") p q (refl p) acc))
                               (refl (last inst-eqs))
                               (reverse (map vector (butlast inst-eqs)
                                             (map (fn [i] (and* (subvec inst-eqs i)))
                                                  (range 1 (count inst-eqs))))))]
        ;; Exists.intro from the innermost out: ∃ v_i, P_i(v_i) with the outer ws substituted
        (reduce (fn [acc i]
                  (let [[u t p] (nth exs i)
                        p' (e/instantiate p (subvec ws 0 i))]
                    (e/app* (e/const' (nm "Exists.intro") [u]) t p' (nth ws i) acc)))
                conj-proof (reverse (range m)))))))

(defn- prove-inv
  "A proof of the disjunction `goal` by its first disjunct that a template matches, or nil."
  [goal]
  (let [ds (loop [x goal acc []]
             (if-let [[p q] (const-app? x "Or" 2)] (recur q (conj acc [p q])) (conj acc [x nil])))]
    (some (fn [i]
            (when-let [pr (prove-disjunct (first (nth ds i)))]
              ;; wrap: Or.inr for each disjunct before i, Or.inl at i (unless it is the last)
              (let [pr (if (< i (dec (count ds)))
                         (let [[p q] (nth ds i)] (e/app* (c "Or.inl") p q pr))
                         pr)]
                (reduce (fn [acc j] (let [[p q] (nth ds j)] (e/app* (c "Or.inr") p q acc)))
                        pr (reverse (range i))))))
          (range (count ds)))))

(defn- inv-tactic
  "`clj_model_inv`: close a goal `I t y…` (a disjunction of templates) by the template that
   matches `y…`."
  [ps _]
  (let [g (tp/current-goal ps)
        _ (when-not g (throw (ex-info "Tactic error: clj_model_inv: no goals" {:kind :tactic-error})))
        goal (:type g)]
    (if-let [pr (prove-inv goal)]
      (basic/exact ps pr)
      (throw (ex-info "Tactic error: clj_model_inv: no template matches" {:kind :tactic-error})))))

(a/register-tactic! 'clj_model_inv inv-tactic)

;; ── Proving a group ─────────────────────────────────────────────────────────────────────

(def max-rounds
  "How often a recursive call's arguments may add a template before the group is given up."
  4)

(defn- run [ps tac] (a/run-tactic ps tac))

(defn- attempt [ps tac]
  (try (a/run-tactic ps tac)
       (catch clojure.lang.ExceptionInfo ex
         (if (#{:tactic-error :elab-error} (:kind (ex-data ex))) nil (throw ex)))))

(defn- on-goal
  "Run `f` on goal `gid` of `ps` alone; returns `f`'s value with the other goals restored, or
   `f`'s value as is when it is not a proof state (nil, a marker)."
  [ps gid f]
  (let [others (vec (remove #{gid} (:goals ps)))
        r (f (assoc ps :goals [gid]))]
    (if (map? r) (assoc r :goals (into (vec (:goals r)) others)) r)))

(defn- finish
  "Add the theorem `cname : goal` proved by the solved `ps` to `ps`'s env; the new env."
  [ps cname goal]
  (extract/verify ps)
  (env/check-constant (:env ps) (env/mk-thm (nm cname) [] goal (extract/extract ps))))

(defn- self-call
  "The arguments [t y…] of the first application of the fvar `self-id` in `x`, or nil."
  [x self-id k]
  (let [seen (java.util.IdentityHashMap.)]
    (letfn [(walk [x]
              (when-not (.containsKey seen x)
                (.put seen x true)
                (or (when (e/app? x)
                      (let [[h args] (e/get-app-fn-args x)]
                        (when (and (e/fvar? h) (= self-id (e/fvar-id h)) (= (count args) (inc k))) args)))
                    (case (e/tag x)
                      :app (or (walk (e/app-fn x)) (walk (e/app-arg x)))
                      :lam (or (walk (e/lam-type x)) (walk (e/lam-body x)))
                      nil))))]
      (walk x))))

(defn- local-id [g n] (last (keep (fn [[id d]] (when (= n (:name d)) id)) (sort-by key (:lctx g)))))

(defn- list-type? [t] (let [h (e/get-app-fn t)] (and (e/const? h) (= "List" (name/->string (e/const-name h))))))

(defn- step-statement
  "∀ a…, ∀ self t, (∀ t' y…, I y… → μ t' y… < μ t A… → Q (self t' y…)) → Q (F self t A…)."
  [env {:keys [k F] :as grp} mu templates tm]
  (let [vars (mapv (fn [[id _ t] i] [id (str "a" i) t]) (:vars tm) (range))
        self [(fresh-id) "self" (self-type k)]
        t [(fresh-id) "t" NatT]
        t2 [(fresh-id) "t2" NatT]
        ys (mapv (fn [i] [(fresh-id) (str "y" i) V]) (range 1 (inc k)))
        yv (mapv (comp e/fvar first) ys)
        hyp (pi (into [t2] ys)
                (arrows [(inv-app env templates yv)
                         (nat-lt (mu-app mu (e/fvar (first t2)) yv) (mu-app mu (e/fvar (first t)) (:args tm)))]
                        (q-app grp (apply e/app* (e/fvar (first self)) (e/fvar (first t2)) yv))))
        h [(fresh-id) "hrec" hyp]]
    (pi (into vars [self t h])
        (q-app grp (apply e/app* F (e/fvar (first self)) (e/fvar (first t)) (:args tm))))))

(defn- close-call
  "Close the goal `ps` (alone), a recursive call `Q (self t' y…)`, by `hrec`: `y…` in the
   invariant by a template, the measure decrease by simp and omega. Returns the solved state,
   ::no-template when no template matches `y…`, ::measure when the decrease is not shown, or nil."
  [ps]
  (when-let [ps2 (attempt ps '(apply hrec))]
    (let [[ig mg] (:goals ps2)]
      (when (and ig mg)
        (if-let [ps3 (attempt (assoc ps2 :goals [ig mg]) '(clj_model_inv))]
          (let [ps4 (or (attempt ps3 (list 'simp [(symbol "clj_model")])) ps3)]
            (if (empty? (:goals ps4)) ps4 (or (attempt ps4 '(omega)) ::measure)))
          ::no-template)))))

(def ^:private unsettled
  "Heads that leave a recursive call's argument undetermined (a branch on unknown data): such an
   argument is no template; the step case-splits the template's lists instead."
  #{"Bool.rec" "ite" "dite" "Option.bind" "Option.rec"})

(defn- settled?
  "Is `x` free of `unsettled` heads and matchers?"
  [x]
  (let [found (volatile! false)
        seen (java.util.IdentityHashMap.)]
    (letfn [(walk [x]
              (when-not (or @found (.containsKey seen x))
                (.put seen x true)
                (case (e/tag x)
                  :const (let [n (name/->string (e/const-name x))]
                           (when (or (unsettled n) (re-find #"\.(match_\d+|casesOn|rec)$" n)
                                     ;; a model op other than a constructor or an encoder is stuck
                                     ;; on unknown data (`CljM.tl (encListC xs)`)
                                     (and (str/starts-with? n "CljM.") (not (str/starts-with? n "CljM.V."))
                                          (not (re-find #"^CljM\.enc" n))))
                             (vreset! found true)))
                  :app (do (walk (e/app-fn x)) (walk (e/app-arg x)))
                  :lam (do (walk (e/lam-type x)) (walk (e/lam-body x)))
                  nil)))]
      (walk x))
    (not @found)))

(defn- step-attempt
  "One attempt at the step from template `tm`: `split?` case-splits its List variables first."
  [env grp mu templates tm cname unfold split?]
  (let [goal (step-statement env grp mu templates tm)
        names (mapv #(str "a" %) (range (count (:vars tm))))
        [ps _] (tp/start-proof env goal)
        ps (if (seq names) (basic/intros ps names) ps)  ; no names would introduce every binder
        ps (if split?
             (reduce (fn [ps [[_ _ t] n]]
                       (if (list-type? t) (or (attempt ps (list 'all_goals (list 'cases (symbol n)))) ps) ps))
                     ps (map vector (:vars tm) names))
             ps)
        ps (run ps '(all_goals (intro self t hrec)))
        s (symbol "clj_model")
        ps (run ps (list 'all_goals (list 'try (list 'simp (conj (vec unfold) s)))))
        ps (run ps (list 'repeat '(any_goals (split_ifs)) (list 'all_goals (list 'try (list 'simp_all [s])))))
        k (:k grp)]
    (loop [ps ps todo (vec (:goals ps)) new [] failed [] measure []]
      (if-let [gid (first todo)]
        (let [g (first (tp/goals (assoc ps :goals [gid])))
              self-id (local-id g "self")
              call (when self-id (self-call (:type g) self-id k))
              ;; only a call in the position Q reads; `apply` on anything else would fall back to
              ;; normalizing the goal deeply, which diverges on the model's literal bounds
              tail? (and call (= (:type g) (q-app grp (apply e/app* (e/fvar self-id) call))))
              closed (when tail? (on-goal ps gid close-call))]
          (cond
            (or (nil? call) (nil? closed)) (recur ps (subvec todo 1) new (conj failed (:type g)) measure)
            (= ::measure closed) (recur ps (subvec todo 1) new failed (conj measure (:type g)))
            (= ::no-template closed)
            (if (every? settled? (rest call))
              (recur ps (subvec todo 1) (conj new (template (:lctx g) (vec (rest call)))) failed measure)
              (recur ps (subvec todo 1) new (conj failed (:type g)) measure))
            :else (recur closed (subvec todo 1) new failed measure)))
        (cond
          (seq failed) {:failed failed}
          (seq new) {:new new}
          (seq measure) {:measure measure}
          :else {:env (finish ps cname goal)})))))

(defn- prove-step
  "Prove the step from template `tm` in `env`. Returns {:env env'} on success, {:new [template …]}
   when recursive calls leave the templates, {:measure [goal …]} when only the measure fails, or
   {:failed [goal …]}. Without case splits first (a template's list stays general, so the
   templates it adds do); with them when a call's argument is left undetermined."
  [env grp mu templates tm cname unfold]
  (let [r (step-attempt env grp mu templates tm cname unfold false)]
    (if (and (:failed r) (some #(list-type? (nth % 2)) (:vars tm)))
      (step-attempt env grp mu templates tm cname unfold true)
      r)))

(defn- glue-statement
  "∀ self t x…, I x… → (∀ t' y…, I y… → μ t' y… < μ t x… → Q (self t' y…)) → Q (F self t x…):
   the `step` premise of CljM.fix<k>.induct."
  [env {:keys [k F] :as grp} mu templates]
  (let [self [(fresh-id) "self" (self-type k)]
        t [(fresh-id) "t" NatT]
        xs (mapv (fn [i] [(fresh-id) (str "x" i) V]) (range 1 (inc k)))
        xv (mapv (comp e/fvar first) xs)
        t2 [(fresh-id) "t2" NatT]
        ys (mapv (fn [i] [(fresh-id) (str "y" i) V]) (range 1 (inc k)))
        yv (mapv (comp e/fvar first) ys)
        hyp (pi (into [t2] ys)
                (arrows [(inv-app env templates yv)
                         (nat-lt (mu-app mu (e/fvar (first t2)) yv) (mu-app mu (e/fvar (first t)) xv))]
                        (q-app grp (apply e/app* (e/fvar (first self)) (e/fvar (first t2)) yv))))]
    (pi (into [self t] xs)
        (arrows [(inv-app env templates xv) hyp]
                (q-app grp (apply e/app* F (e/fvar (first self)) (e/fvar (first t)) xv))))))

(defn- prove-glue
  "Prove the step premise from the per-template steps `step-names`: destructure the invariant
   (one alternative per template, its equations substituted) and apply that template's step."
  [env {:keys [k] :as grp} mu templates step-names cname]
  (let [goal (glue-statement env grp mu templates)
        xs (mapv #(symbol (str "x" %)) (range 1 (inc k)))
        pats (map-indexed (fn [j tm]
                            (let [vs (mapv #(symbol (str "a" j "_" %)) (range (count (:vars tm))))
                                  p (into vs (repeat k 'rfl))]
                              [vs (if (= 1 (count p)) (first p) p)]))
                          templates)
        [ps _] (tp/start-proof env goal)
        ps (run ps (list* 'intro 'self 't (concat xs '[hI hrec])))
        ps (run ps (list 'rcases 'hI 'with (if (= 1 (count pats)) (second (first pats)) (cons 'or (map second pats)))))
        ps (reduce (fn [ps [[vs _] sn]] (run ps (list 'exact (concat [(symbol sn)] vs '[self t hrec]))))
                   ps (map vector pats step-names))]
    (finish ps cname goal)))

(defn- rec-statement
  "∀ fuel t x…, I x… → μ t x… < fuel → Q (CljM.fix<k> F fuel t x…)."
  [env {:keys [k F] :as grp} mu templates]
  (let [fuel [(fresh-id) "fuel" NatT]
        t [(fresh-id) "t" NatT]
        xs (mapv (fn [i] [(fresh-id) (str "x" i) V]) (range 1 (inc k)))
        xv (mapv (comp e/fvar first) xs)]
    (pi (into [fuel t] xs)
        (arrows [(inv-app env templates xv) (nat-lt (mu-app mu (e/fvar (first t)) xv) (e/fvar (first fuel)))]
                (q-app grp (apply e/app* (c (str "CljM.fix" k)) F (e/fvar (first fuel)) (e/fvar (first t)) xv))))))

(defn- prove-steps
  "The steps of every template under measure `mu`, discovering templates: {:env :steps :templates}
   on success, else {:failed …} / {:measure …} / {:templates :calls} when they do not close."
  [grp mu templates cname unfold]
  (loop [templates (vec templates) round 0]
    (let [res (reduce (fn [{:keys [env steps new measure]} [j tm]]
                        (let [sn (str cname ".step" j)
                              r (prove-step env grp mu templates tm sn unfold)]
                          (cond
                            (:failed r) (reduced r)
                            (:new r) {:env env :steps steps :new (into new (:new r)) :measure measure}
                            (:measure r) {:env env :steps steps :new new :measure (into measure (:measure r))}
                            :else {:env (:env r) :steps (conj steps sn) :new new :measure measure})))
                      {:env @state/ansatz-env :steps [] :new [] :measure []}
                      (map-indexed vector templates))]
      (cond
        (:failed res) res
        (seq (:new res))
        (let [known (set (map template-key templates))
              added (vals (into {} (map (juxt template-key identity))
                                (remove #(known (template-key %)) (:new res))))]
          (if (or (empty? added) (>= round max-rounds))
            {:templates templates :calls (:new res)}
            (recur (into templates added) (inc round))))
        (seq (:measure res)) {:measure (:measure res) :templates templates}
        :else (assoc res :templates templates)))))

(defn- members
  "How many members the group's functional `F` dispatches on: 1 + the largest literal tag of a
   recursive call in its body (and of the entry, `tag0`)."
  [env F tag0]
  (let [body (if (e/const? F) (some-> (env/lookup env (e/const-name F)) env/get-value) F)
        lit (fn [x] (cond (e/lit-nat? x) (e/lit-nat-val x)
                          :else (when-let [[_ v _] (const-app? x "OfNat.ofNat" 3)] (when (e/lit-nat? v) (e/lit-nat-val v)))))
        top (volatile! (or (lit tag0) 0))
        seen (java.util.IdentityHashMap.)]
    (letfn [(walk [x]
              (when-not (.containsKey seen x)
                (.put seen x true)
                (when (e/app? x)
                  (let [[h args] (e/get-app-fn-args x)]
                    (when (and (e/bvar? h) (seq args))
                      (when-let [v (lit (first args))] (vswap! top max v)))))
                (case (e/tag x)
                  :app (do (walk (e/app-fn x)) (walk (e/app-arg x)))
                  :lam (do (walk (e/lam-type x)) (walk (e/lam-body x)))
                  nil)))]
      (when body (walk body)))
    (inc (long @top))))

(defn prove-group!
  "Prove `cname : ∀ fuel t x…, I x… → μ t x… < fuel → Q (CljM.fix<k> F fuel t x…)` for the
   group `grp` ({:k :F :q-body :r-id :tag}) starting from `templates`, adding templates for at
   most `max-rounds` rounds, with the first of `measures` whose decrease every step shows. Adds
   the theorem and its steps to the session env and returns {:name :templates :measure}; throws
   with the goals no step closes."
  [grp templates cname unfold]
  (let [k (:k grp)
        induct (ensure-induct! k)
        m (members @state/ansatz-env (:F grp) (:tag grp))]
    (loop [mus (measures k m) templates (vec templates) last-res nil]
      (if-let [mu (first mus)]
        (let [res (prove-steps grp mu templates cname unfold)]
          (cond
            (:failed res)
            (throw (ex-info (str "clj-model: a recursive call is not closed by the template invariant:\n"
                                 (str/join "\n" (map pr-str (:failed res))))
                            {:kind :clj-model/recursion-unproved :goals (:failed res)}))
            (:calls res)
            (throw (ex-info "clj-model: the recursive calls' arguments do not close under the templates"
                            {:kind :clj-model/recursion-unproved :templates (:templates res) :calls (:calls res)}))
            (seq (:measure res)) (recur (rest mus) (:templates res) res)
            :else
            (let [templates (:templates res)
                  gname (str cname ".step")
                  env (prove-glue (:env res) grp mu templates (:steps res) gname)
                  stmt (rec-statement env grp mu templates)
                  proof (e/app* (c induct) (:F grp) (inv-lam env templates k) (q-lam grp) (mu-lam mu k) (c gname))
                  env (env/check-constant env (env/mk-thm (nm cname) [] stmt proof))]
              (reset! state/ansatz-env env)
              {:name cname :templates templates :measure mu})))
        (throw (ex-info (str "clj-model: no measure decreases on every recursive call:\n"
                             (str/join "\n" (map pr-str (:measure last-res))))
                        {:kind :clj-model/recursion-unproved :goals (:measure last-res)}))))))

;; ── The conformance goal ────────────────────────────────────────────────────────────────

(defn- group-of
  "The group a goal enters: {:grp {:k :F :q-body :r-id} :args […]} for its first CljM.fix<k>
   call, `Q` being the goal with that call abstracted; or nil."
  [goal-type]
  (when-let [{:keys [k F tag args expr]} (fix-call goal-type)]
    (let [r-id (fresh-id)]
      {:grp {:k k :F F :tag tag :q-body (replace-subterm goal-type expr (e/fvar r-id)) :r-id r-id}
       :args args})))

(defn- group-key [{:keys [k F q-body r-id]}] [k F (e/abstract1 q-body r-id)])

(defn recursive-script
  "The tactics that prove the conformance statement `prop` over `params` of a model entering
   recursive groups: `compute` (the default computation) leaves goals `Q (CljM.fix<k> F e t a…)`;
   each group is proved once (`prove-group!`, theorems `<base>.rec<i>`), and the script applies
   it, then shows the entry's arguments in the invariant (`clj_model_inv`) and `μ a… < e`
   (simp, omega). Throws when a goal enters no group or a group is not proved."
  [params prop compute unfold base]
  (let [env (a/env)
        pairs (a/parse-params params)
        goal (:type-ansatz (a/elab-signature env pairs prop))
        [ps _] (tp/start-proof env goal)
        ps (basic/intros ps (mapv (comp str first) pairs))
        ps (reduce run ps compute)
        found (map (fn [g] (assoc (group-of (:type g)) :goal g)) (tp/goals ps))
        _ (when-let [bad (seq (remove :grp found))]
            (throw (ex-info (str "clj-model: the default script leaves goals outside a recursive group:\n"
                                 (str/join "\n" (map (comp pr-str :type :goal) bad)))
                            {:kind :clj-model/recursion-unproved :goals (map (comp :type :goal) bad)})))
        groups (reduce (fn [acc {:keys [grp args goal]}]
                         (let [gk (group-key grp)
                               tm (template (:lctx goal) args)]
                           (if-let [i (first (keep-indexed (fn [i x] (when (= gk (:key x)) i)) acc))]
                             (update-in acc [i :templates] conj tm)
                             (conj acc {:key gk :grp grp :templates [tm]}))))
                       [] found)
        ;; a name not yet declared (an earlier attempt may have proved a group)
        fresh-name (fn [] (first (remove #(env/lookup @state/ansatz-env (nm %))
                                         (map #(str base ".rec" %) (range)))))
        names (mapv (fn [{:keys [grp templates]}]
                      (let [tms (vals (into {} (map (juxt template-key identity)) templates))]
                        (:name (prove-group! grp tms (fresh-name) unfold))))
                    groups)
        s (symbol "clj_model")]
    (vec (concat compute
                 (when (seq names)
                   [(list 'all_goals (list 'try (cons 'first (map (fn [n] (list 'apply (symbol n))) names))))
                    '(all_goals (try (clj_model_inv)))
                    (list 'all_goals (list 'try (list 'simp [s])))
                    '(all_goals (try (omega)))])))))
