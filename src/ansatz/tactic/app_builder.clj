;; Port of the part of Lean/Meta/AppBuilder.lean that tactics use to build proof terms:
;; `mkAppM` (implicit arguments inferred from the explicit ones, instance arguments
;; synthesized) and `mkAppOptM`.
(ns ansatz.tactic.app-builder
  "Build `@c a₁ … aₙ` from a constant and its EXPLICIT arguments, as Lean's `mkAppM` does:
   implicit arguments (and universe parameters) are read off the types of the explicit
   arguments, instance-implicit arguments that matching did not fix are synthesized.

   Lean unifies binder types with argument types through `isDefEq` on metavariables. Here
   the binder telescope is opened with holes and each binder type is matched first-order
   against the argument's type: a hole is assigned the first subterm it meets, and
   positions that do not match structurally (typically instance subterms such as
   `Preorder.toLE α inst` against `Int.instLEInt`) are skipped. Those are left to the
   kernel, which checks every term the tactics produce; `check` below runs it eagerly."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.instance :as inst])
  (:import [ansatz.kernel TypeChecker]))

(defn- error! [msg data]
  (throw (ex-info (str "mkAppM: " msg) (assoc data :kind :tactic-error))))

(defn- strip [x]
  (if (and x (e/mdata? x)) (recur (e/mdata-expr x)) x))

(defn- unfold-ge-gt
  "`a ≥ b` / `a > b` are reducible notations for `b ≤ a` / `b < a` (whnfR unfolds them)."
  [x]
  (let [[h args] (e/get-app-fn-args x)]
    (if (and (e/const? h) (= 4 (count args)))
      (case (name/->string (e/const-name h))
        "GE.ge" (e/app* (e/const' (name/from-string "LE.le") (e/const-levels h))
                        (nth args 0) (nth args 1) (nth args 3) (nth args 2))
        "GT.gt" (e/app* (e/const' (name/from-string "LT.lt") (e/const-levels h))
                        (nth args 0) (nth args 1) (nth args 3) (nth args 2))
        x)
      x)))

;; ------------------------------------------------------------------
;; first-order matching of a binder telescope against concrete types
;; ------------------------------------------------------------------

(defn- match-level [lholes pl tl]
  (cond
    (and (lvl/param? pl) (contains? @lholes (lvl/param-name pl)))
    (when (nil? (get @lholes (lvl/param-name pl)))
      (swap! lholes assoc (lvl/param-name pl) tl))
    (and (lvl/succ? pl) (lvl/succ? tl)) (match-level lholes (lvl/succ-pred pl) (lvl/succ-pred tl))
    (and (lvl/max? pl) (lvl/max? tl))
    (do (match-level lholes (lvl/max-lhs pl) (lvl/max-lhs tl))
        (match-level lholes (lvl/max-rhs pl) (lvl/max-rhs tl)))
    :else nil))

(defn- match-expr
  "Assign holes so that `pat` (a binder type of the telescope, whose loose bvars at depth
   `offset` and above are the holes, innermost last) becomes `tgt`. Mismatches are ignored."
  [holes lholes n pat tgt offset]
  (let [pat (unfold-ge-gt (strip pat)) tgt (unfold-ge-gt (strip tgt))]
    (cond
      (and (e/bvar? pat) (>= (e/bvar-idx pat) offset))
      (let [i (- n 1 (- (e/bvar-idx pat) offset))]
        (when (and (<= 0 i) (< i n) (nil? (nth @holes i))
                   (or (zero? offset) (not (e/has-loose-bvars? tgt))))
          (swap! holes assoc i tgt)))

      (and (e/app? pat) (e/app? tgt))
      (let [[pf pargs] (e/get-app-fn-args pat)
            [tf targs] (e/get-app-fn-args tgt)
            np (count pargs) nt (count targs)
            pf* (strip pf) tf* (strip tf)
            same-head? (or (and (e/const? pf*) (e/const? tf*) (= (e/const-name pf*) (e/const-name tf*)))
                           (and (e/fvar? pf*) (= pf* tf*))
                           (not (or (e/const? pf*) (e/fvar? pf*))))]
        (cond
          ;; different head constants: no information (e.g. two instance paths to `0`)
          (not same-head?) nil
          (= np nt)
          (do (match-expr holes lholes n pf tf offset)
              (dorun (map #(match-expr holes lholes n %1 %2 offset) pargs targs)))
          ;; a hole applied to arguments (`R b 0` for `{R : α → α → Prop}`): the hole takes
          ;; the target's head applied to its leading arguments (first-order approximation)
          (and (< np nt) (e/bvar? (strip pf)) (>= (e/bvar-idx (strip pf)) offset))
          (do (match-expr holes lholes n pf (apply e/app* tf (take (- nt np) targs)) offset)
              (dorun (map #(match-expr holes lholes n %1 %2 offset) pargs (drop (- nt np) targs))))
          :else nil))

      (and (e/const? pat) (e/const? tgt) (= (e/const-name pat) (e/const-name tgt)))
      (dorun (map #(match-level lholes %1 %2) (e/const-levels pat) (e/const-levels tgt)))

      (and (e/sort? pat) (e/sort? tgt)) (match-level lholes (e/sort-level pat) (e/sort-level tgt))

      (and (e/forall? pat) (e/forall? tgt))
      (do (match-expr holes lholes n (e/forall-type pat) (e/forall-type tgt) offset)
          (match-expr holes lholes n (e/forall-body pat) (e/forall-body tgt) (inc offset)))

      (and (e/lam? pat) (e/lam? tgt))
      (do (match-expr holes lholes n (e/lam-type pat) (e/lam-type tgt) offset)
          (match-expr holes lholes n (e/lam-body pat) (e/lam-body tgt) (inc offset)))

      :else nil)))

(defn- instantiate-holes
  "Instantiate the loose bvars of `body` (under n binders) with the hole values."
  [body vals]
  (e/instantiate body vals))

(defn- level-subst [lholes]
  (into {} (keep (fn [[k v]] (when v [k v]))) lholes))

(defn infer-type [st x] (tc/infer-type st x))

(declare mk-app)

(def ^:private mixin-instances
  "Order mixins whose Mathlib instances ansatz's synthesis does not reach (it does not unify
   the instance paths of their arguments, e.g. `Distrib.toAdd` against the `AddGroup` one):
   each is tried by its structure-projection instance, applied as `mkAppM` does, against the
   goal. The kernel checks the resulting instance argument."
  {"ExistsAddOfLE" ["AddGroup.existsAddOfLE"]
   "PosMulMono" ["IsOrderedRing.toPosMulMono"]
   "MulPosMono" ["IsOrderedRing.toMulPosMono"]
   "PosMulStrictMono" ["IsStrictOrderedRing.toPosMulStrictMono"]
   "MulPosStrictMono" ["IsStrictOrderedRing.toMulPosStrictMono"]
   "AddLeftMono" ["IsOrderedAddMonoid.toAddLeftMono"]
   "AddRightMono" ["IsOrderedAddMonoid.toAddRightMono"]
   "AddLeftReflectLE" ["IsOrderedCancelAddMonoid.toAddLeftReflectLE"]
   "AddLeftReflectLT" ["IsOrderedCancelAddMonoid.toAddLeftReflectLT"]
   "IsOrderedCancelAddMonoid" ["IsStrictOrderedRing.toIsOrderedCancelAddMonoid"]
   "ZeroLEOneClass" ["IsOrderedRing.toZeroLEOneClass"]
   "HasDistribNeg" ["NonUnitalNonAssocRing.toHasDistribNeg"]
   "AddLeftStrictMono" ["IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono"
                        "addLeftStrictMono_of_addLeftReflectLE"]
   "IsOrderedAddMonoid" ["IsOrderedRing.toIsOrderedAddMonoid"]
   "IsOrderedRing" ["IsStrictOrderedRing.toIsOrderedRing"]})

(def ^:private ^:dynamic *fallback-depth* 0)

(defn- mixin-fallback [st goal]
  (let [[h _] (e/get-app-fn-args (strip goal))]
    (when (and (e/const? h) (< *fallback-depth* 3))
      (some (fn [ctor]
              (when (env/lookup (:env st) (name/from-string ctor))
                (binding [*fallback-depth* (inc *fallback-depth*)]
                  (try (let [{:keys [term type]} (mk-app st ctor [] :expected goal)]
                         ;; only an instance of exactly the goal's class instance
                         (when (tc/is-def-eq st type goal) term))
                       (catch Exception _ nil)))))
            (get mixin-instances (name/->string (e/const-name h)))))))

(defn mk-app
  "Lean's `mkAppM c args` (and, with `:expected`, the conclusion matched against an expected
   type first, as `apply` does). Options:
   - `:levels`   universe levels for c (otherwise inferred)
   - `:expected` a type the conclusion must have, matched before the arguments
   - `:explicit` a map binder-index → value fixing any argument up front
   Returns {:term :type}."
  [st cname args & {:keys [levels expected explicit types]}]
  (let [env (:env st)
        ci (or (env/lookup env (name/from-string cname))
               (error! (str "unknown constant " cname) {:const cname}))
        lparams (vec (.levelParams ci))
        lholes (atom (if levels {} (zipmap lparams (repeat nil))))
        ;; telescope
        ty0 (.type ci)
        binders (loop [t ty0 acc []]
                  (if (e/forall? t)
                    (recur (e/forall-body t) (conj acc {:type (e/forall-type t) :info (e/forall-info t)}))
                    acc))
        n (count binders)
        holes (atom (vec (repeat n nil)))
        _ (doseq [[i v] explicit] (swap! holes assoc i v))
        explicit-idx (vec (keep-indexed (fn [i b] (when (= :default (:info b)) i)) binders))
        _ (when (> (count args) (count explicit-idx))
            (error! (str "too many explicit arguments for " cname) {:const cname :args (count args)}))
        used (subvec explicit-idx 0 (count args))
        ;; number of binders consumed: through the last explicit argument; with an expected
        ;; type, through the next explicit binder (exclusive)
        ncons (cond
                (seq args) (inc (peek used))
                :else 0)
        ncons (max ncons (count args) (if (seq explicit) (inc (apply max (keys explicit))) 0))
        ;; trailing implicit and instance binders are instantiated too (Lean's mkAppM fills
        ;; them by unification and synthesis), up to the next explicit binder
        ncons (or (some #(when (>= % ncons) %) explicit-idx) n)
        arg-type (fn [x] (if-let [t (get types x)] t (infer-type st x)))]
    ;; explicit args
    (doseq [[i a] (map vector used args)]
      (swap! holes assoc i a))
    ;; conclusion against the expected type
    (when expected
      ;; the conclusion after the remaining binders, whose bvars below `k` are those binders
      (let [rest-ty (loop [t ty0 k 0] (if (< k ncons) (recur (e/forall-body t) (inc k)) t))
            [concl k] (loop [t rest-ty k 0] (if (e/forall? t) (recur (e/forall-body t) (inc k)) [t k]))]
        (match-expr holes lholes ncons concl expected k)))
    ;; argument types against binder types (also for the values fixed up front)
    (doseq [[i a] (concat (map vector used args) (sort-by key explicit))]
      (match-expr holes lholes i (:type (nth binders i)) (arg-type a) 0))
    ;; universe levels that occur only in binder sorts (`{β : Sort v}`): read them off the
    ;; type of the value the binder received
    (when (and (not levels) (some nil? (vals @lholes)))
      (doseq [i (range ncons)]
        (let [bt (strip (:type (nth binders i)))
              v (nth @holes i)]
          (when (and v (e/sort? bt))
            (let [s (try (tc/infer-type st v) (catch Exception _ nil))
                  s (when s (strip s))]
              (when (and s (e/sort? s))
                (match-level lholes (e/sort-level bt) (e/sort-level s))))))))
    ;; synthesize the remaining instance arguments, in order
    (let [lsub (if levels (zipmap lparams levels) (level-subst @lholes))
          _ (when (and (not levels) (some nil? (vals @lholes)))
              (error! (str "could not infer universe levels of " cname)
                      {:const cname :levels @lholes}))
          lvls (mapv lsub lparams)
          inst-ty (fn [i]
                    (let [bt (:type (nth binders i))
                          bt (if (seq lsub) (e/instantiate-level-params bt lsub) bt)]
                      (instantiate-holes bt (subvec @holes 0 i))))]
      (doseq [i (range ncons)]
        (when (nil? (nth @holes i))
          (if (= :inst-implicit (:info (nth binders i)))
            (let [goal (inst-ty i)
                  found (or (some (fn [[id decl]]
                                    (when (= (:type decl) goal) (e/fvar id)))
                                  (:lctx st))
                            (try (inst/synthesize* st env (inst/index-for env) goal 0)
                                 (catch clojure.lang.ExceptionInfo _ nil))
                            (mixin-fallback st goal)
                            (error! (str "failed to synthesize instance for " cname)
                                    {:const cname :goal goal}))]
              (if found
                (swap! holes assoc i found)
                (error! (str "failed to synthesize instance for " cname)
                        {:const cname :goal goal})))
            ;; an implicit argument that is itself an instance (the class parameters of a
            ;; projection like `IsOrderedRing.toMulPosMono {inst : Semiring α}`) is fixed by
            ;; unification in Lean; when matching did not reach it, synthesize it
            (if-let [found (try (inst/synthesize* st env (inst/index-for env) (inst-ty i) 0)
                                (catch Exception _ nil))]
              (swap! holes assoc i found)
              (error! (str "could not infer argument " i " of " cname)
                      {:const cname :binder i})))))
      (let [vals (subvec @holes 0 ncons)
            head (e/const' (name/from-string cname) lvls)
            term (apply e/app* head vals)
            rest-ty (loop [t ty0 k 0] (if (< k ncons) (recur (e/forall-body t) (inc k)) t))
            rest-ty (if (seq lsub) (e/instantiate-level-params rest-ty lsub) rest-ty)]
        {:term term :type (instantiate-holes rest-ty vals)}))))

(defn app-term [st cname args & opts]
  (:term (apply mk-app st cname args opts)))

(defn check
  "Kernel-check `term` in the local context of `st`; return its type."
  [st term]
  (let [checker (TypeChecker. (:env st))]
    (doseq [[id decl] (sort-by key (:lctx st))]
      (.addLocal checker (long id) (str (:name decl)) (:type decl)))
    (.check checker term)))
