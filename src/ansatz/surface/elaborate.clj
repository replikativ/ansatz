;; Surface syntax — runtime elaboration with implicit argument insertion.

(ns ansatz.surface.elaborate
  "Runtime elaboration: transforms surface s-expressions into fully explicit
   Ansatz terms by resolving names, inserting implicit arguments, inferring
   universe levels, and type-checking.

   This is THE elaborator: type-directed, locally nameless with fvar locals,
   with metavariables + instance synthesis.
   It backs `a/defn` bodies+signatures, `a/theorem` goals, proof terms, and tactic-arg
   elaboration. (The legacy bvar-only `term` builder it superseded has been retired.)

   Usage:
     (elaborate env '(forall [a Nat] (Eq a a)))
     ;; => fully explicit: (forall [a Nat] (@Eq.{1} Nat a a))

     (elaborate env '(lam [a Nat] (Eq.refl a))  expected-type)
     ;; => checks against expected-type, infers implicits"
  (:require [clojure.string]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.tc :as tc]
            [ansatz.meta :as meta]
            [ansatz.surface.match :as match]
            [ansatz.surface.ingest :as ingest])
  (:import [ansatz.kernel Env]))

;; ============================================================
;; Elaboration state
;; ============================================================

(defn- mk-elab-state
  "Create elaboration state with metavar tracking."
  ([^Env env]
   (mk-elab-state env {}))
  ([^Env env {:keys [next-id-start initial-meta-mctx collect-from-index holes-as-synthetic-opaque?]
              :or {next-id-start 1000000
                   initial-meta-mctx meta/empty-context
                   holes-as-synthetic-opaque? false}}]
   {:env env
    :tc (tc/mk-tc-state env)
    :next-id (atom next-id-start)  ;; high start to avoid collision with tc ids
    :mctx (atom {})          ;; compatibility metadata/solutions; declarations live in :meta-mctx
    :level-mctx (atom {})    ;; {id → {:solution Level-or-nil}}
    :meta-mctx (atom initial-meta-mctx)
    :collect-from-index (or collect-from-index (:mvar-counter initial-meta-mctx 0))
    :initial-level-mvar-ids (set (keys (:level-depth initial-meta-mctx)))
    :holes-as-synthetic-opaque? holes-as-synthetic-opaque?
    :scope {}                ;; symbol → {:fvar-id long :type Expr}
    :depth 0}))

(defn- fresh-id! [est]
  (let [id (swap! (:next-id est) inc)]
    id))

(defn- expr-mvar-id
  "Return the elaboration mvar id represented by `expr`, accepting both the
   current real-mvar representation and the older fvar compatibility shape."
  [expr]
  (case (e/tag expr)
    :mvar (e/mvar-id expr)
    :fvar (e/fvar-id expr)
    nil))

(declare unify-levels! surface-expr->meta surface-level->meta surface-lctx->meta
         meta-level->surface meta-expr->surface surface-mvar-type meta-mvar-type
         infer-with-mvars whnf-with-mvars)

(defn- fresh-mvar!
  "Create a fresh expression metavariable with the given type. The mirrored
   compatibility context keeps lightweight metadata while declarations and
   assignments live in `:meta-mctx`."
  ([est type]
   (fresh-mvar! est type {}))
  ([est type {:keys [kind user-name inst-implicit?]
              :or {kind :natural}}]
   (let [id (fresh-id! est)]
     (swap! (:mctx est) assoc id (cond-> {:solution nil :kind kind}
                                   user-name (assoc :user-name user-name)
                                   inst-implicit? (assoc :inst-implicit true)))
     (swap! (:meta-mctx est)
            meta/add-expr-mvar-decl id
            (surface-expr->meta est type)
            (surface-lctx->meta est (:lctx (:tc est)))
            (cond-> {:kind kind}
              user-name (assoc :user-name user-name)
              inst-implicit? (assoc :inst-implicit? true)))
     (e/mvar id))))

(defn- mark-inst-implicit!
  [est mvar]
  (let [id (expr-mvar-id mvar)]
    (swap! (:mctx est) assoc-in [id :inst-implicit] true)
    (swap! (:mctx est) assoc-in [id :kind] :synthetic)
    (swap! (:meta-mctx est)
           #(-> %
                (meta/set-expr-mvar-kind id :synthetic)
                (meta/set-expr-mvar-inst-implicit id true)))))

(defn- fresh-level-mvar!
  "Create a fresh universe level metavariable.
   Returns a real Level.mvar; the compatibility context keeps a display name."
  [est]
  (let [id (fresh-id! est)
        n (name/from-string (str "?u" id))]
    (swap! (:level-mctx est) assoc id {:name n :solution nil})
    (swap! (:meta-mctx est) meta/add-level-mvar-decl id)
    (lvl/mvar id)))

(defn- solve-mvar!
  "Assign a solution to a metavariable. Returns true if successful.
   Also attempts to solve level metavars by inferring the type of the solution
   and unifying with the expected type."
  [est id solution]
  (when (meta/expr-decl @(:meta-mctx est) id)
    (if-let [assigned (meta/expr-assignment @(:meta-mctx est) id)]
      ;; Already solved — check consistency against the metacontext assignment.
      (= (meta-expr->surface est assigned) solution)
      (let [meta-solution (surface-expr->meta est solution)]
        (swap! (:meta-mctx est)
               meta/checked-assign-expr id meta-solution
               {:check-type? false
                :unification? true})
        (when (contains? @(:mctx est) id)
          (swap! (:mctx est) assoc-in [id :solution] solution))
        ;; Try to solve level metavars: if the mvar's expected type is Sort ?u
        ;; and solution's type is Sort N, unify ?u = N
        (try
          (let [expected-type (surface-mvar-type est id)
                actual-type (infer-with-mvars est solution)
                expected-whnf (whnf-with-mvars est expected-type)
                actual-whnf (whnf-with-mvars est actual-type)]
            (when (and (e/sort? expected-whnf) (e/sort? actual-whnf))
              (unify-levels! est (e/sort-level expected-whnf) (e/sort-level actual-whnf))))
          (catch Exception _ nil))
        true))))

(defn- mvar-solution [est id]
  (or (when-let [solution (meta/expr-assignment @(:meta-mctx est) id)]
        (meta-expr->surface est solution))
      (get-in @(:mctx est) [id :solution])))

(defn- level-mvar-solution [est id]
  (or (when-let [solution (meta/level-assignment @(:meta-mctx est) id)]
        (meta-level->surface est solution))
      (get-in @(:level-mctx est) [id :solution])))

(defn- solve-level-mvar!
  "Assign a solution to a level metavariable."
  [est id solution]
  (when (contains? (:level-depth @(:meta-mctx est)) id)
    (if (meta/level-assignment @(:meta-mctx est) id)
      true
      (do (swap! (:meta-mctx est)
                 meta/checked-assign-level id (surface-level->meta est solution))
          (when (contains? @(:level-mctx est) id)
            (swap! (:level-mctx est) assoc-in [id :solution] solution))
          true))))

;; ============================================================
;; Metavariable zonking (substitute solutions)
;; ============================================================

(defn- zonk-level
  "Substitute solved level metavariables in a level."
  [est l]
  (if (nil? l) l
      (let [tag (.tag ^ansatz.kernel.Level l)]
        (case tag
          0 l ;; zero
          1 (let [pred (lvl/succ-pred l)
                  pred' (zonk-level est pred)]
              (if (identical? pred pred') l (lvl/succ pred')))
          2 (let [lhs (zonk-level est (lvl/max-lhs l))
                  rhs (zonk-level est (lvl/max-rhs l))]
              (lvl/level-max lhs rhs))
          3 (let [lhs (zonk-level est (lvl/imax-lhs l))
                  rhs (zonk-level est (lvl/imax-rhs l))]
              (lvl/imax lhs rhs))
          4 (let [n (lvl/param-name l)
                  id (some (fn [[id m]]
                             (when (= (:name m) n) id))
                           @(:level-mctx est))]
              (if-let [solution (when id (level-mvar-solution est id))]
                (zonk-level est solution)
                l))
          5 (let [id (lvl/mvar-id l)]
              (if-let [solution (level-mvar-solution est id)]
                (zonk-level est solution)
                l))))))

(defn- zonk
  "Substitute all solved metavariables in an expression."
  [est expr]
  (case (e/tag expr)
    :mvar (let [id (e/mvar-id expr)]
            (if-let [sol (mvar-solution est id)]
              (zonk est sol)
              expr))
    :fvar (let [id (e/fvar-id expr)]
            (if-let [sol (mvar-solution est id)]
              (zonk est sol)
              expr))
    :app (let [f (zonk est (e/app-fn expr))
               a (zonk est (e/app-arg expr))]
           (if (and (identical? f (e/app-fn expr))
                    (identical? a (e/app-arg expr)))
             expr
             (e/app f a)))
    :lam (let [ty (zonk est (e/lam-type expr))
               body (zonk est (e/lam-body expr))]
           (if (and (identical? ty (e/lam-type expr))
                    (identical? body (e/lam-body expr)))
             expr
             (e/lam (e/lam-name expr) ty body (e/lam-info expr))))
    :forall (let [ty (zonk est (e/forall-type expr))
                  body (zonk est (e/forall-body expr))]
              (if (and (identical? ty (e/forall-type expr))
                       (identical? body (e/forall-body expr)))
                expr
                (e/forall' (e/forall-name expr) ty body (e/forall-info expr))))
    :let (let [ty (zonk est (e/let-type expr))
               val (zonk est (e/let-value expr))
               body (zonk est (e/let-body expr))]
           (e/let' (e/let-name expr) ty val body))
    :const (let [levels (e/const-levels expr)
                 levels' (mapv #(zonk-level est %) levels)]
             (if (= levels levels')
               expr
               (e/const' (e/const-name expr) levels')))
    :sort (let [l (e/sort-level expr)
                l' (zonk-level est l)]
            (if (identical? l l') expr (e/sort' l')))
    :proj (let [s (zonk est (e/proj-struct expr))]
            (if (identical? s (e/proj-struct expr))
              expr
              (e/proj (e/proj-type-name expr) (e/proj-idx expr) s)))
    :mdata (let [x (zonk est (e/mdata-expr expr))]
             (if-let [fvar-ids (::meta/abstract-fvars (e/mdata-data expr))]
               (if (seq (meta/collect-expr-mvars x))
                 (if (identical? x (e/mdata-expr expr))
                   expr
                   (e/mdata (e/mdata-data expr) x))
                 (e/abstract-many x fvar-ids))
               (if (identical? x (e/mdata-expr expr))
                 expr
                 (e/mdata (e/mdata-data expr) x))))
    ;; Atoms
    expr))

(defn- legacy-level-mvar-id
  "Return the level mvar id represented by `l`, accepting both real Level.mvar
   nodes and the older synthetic Level.param compatibility shape."
  [est l]
  (cond
    (lvl/mvar? l)
    (lvl/mvar-id l)

    (lvl/param? l)
    (let [n (lvl/param-name l)]
      (some (fn [[id m]] (when (= (:name m) n) id))
            @(:level-mctx est)))))

(defn- surface-level->meta
  "Translate live surface levels to metacontext-shaped levels. Level mvars are
   already real `Level.mvar` nodes; the synthetic param path remains for
   compatibility with older elaborator artifacts."
  [est l]
  (if (nil? l)
    l
    (case (lvl/tag l)
      :zero l
      :succ (let [p (surface-level->meta est (lvl/succ-pred l))]
              (if (identical? p (lvl/succ-pred l)) l (lvl/succ p)))
      :max (let [a (surface-level->meta est (lvl/max-lhs l))
                 b (surface-level->meta est (lvl/max-rhs l))]
             (if (and (identical? a (lvl/max-lhs l))
                      (identical? b (lvl/max-rhs l)))
               l
               (lvl/level-max a b)))
      :imax (let [a (surface-level->meta est (lvl/imax-lhs l))
                  b (surface-level->meta est (lvl/imax-rhs l))]
              (if (and (identical? a (lvl/imax-lhs l))
                       (identical? b (lvl/imax-rhs l)))
                l
                (lvl/imax a b)))
      :param (if-let [id (legacy-level-mvar-id est l)]
               (lvl/mvar id)
               l)
      :mvar l)))

(defn- surface-expr->meta
  "Translate live surface expressions to metacontext-shaped expressions.
   Expression mvars are already real `Expr.mvar` nodes; the legacy fvar path is
   retained for compatibility. Level mvars are already real `Level.mvar` nodes,
   with legacy synthetic params still accepted."
  [est expr]
  (let [mctx @(:mctx est)]
    (letfn [(go [expr]
              (case (e/tag expr)
                :fvar (if (contains? mctx (e/fvar-id expr))
                        (e/mvar (e/fvar-id expr))
                        expr)
                :sort (let [u (surface-level->meta est (e/sort-level expr))]
                        (if (identical? u (e/sort-level expr))
                          expr
                          (e/sort' u)))
                :const (let [levels (e/const-levels expr)
                             levels' (mapv #(surface-level->meta est %) levels)]
                         (if (= levels levels')
                           expr
                           (e/const' (e/const-name expr) levels')))
                :app (let [f (go (e/app-fn expr))
                           a (go (e/app-arg expr))]
                       (if (and (identical? f (e/app-fn expr))
                                (identical? a (e/app-arg expr)))
                         expr
                         (e/app f a)))
                :lam (let [t (go (e/lam-type expr))
                           b (go (e/lam-body expr))]
                       (if (and (identical? t (e/lam-type expr))
                                (identical? b (e/lam-body expr)))
                         expr
                         (e/lam (e/lam-name expr) t b (e/lam-info expr))))
                :forall (let [t (go (e/forall-type expr))
                              b (go (e/forall-body expr))]
                          (if (and (identical? t (e/forall-type expr))
                                   (identical? b (e/forall-body expr)))
                            expr
                            (e/forall' (e/forall-name expr) t b (e/forall-info expr))))
                :let (let [t (go (e/let-type expr))
                           v (go (e/let-value expr))
                           b (go (e/let-body expr))]
                       (if (and (identical? t (e/let-type expr))
                                (identical? v (e/let-value expr))
                                (identical? b (e/let-body expr)))
                         expr
                         (e/let' (e/let-name expr) t v b)))
                :mdata (let [x (go (e/mdata-expr expr))]
                         (if (identical? x (e/mdata-expr expr))
                           expr
                           (e/mdata (e/mdata-data expr) x)))
                :proj (let [s (go (e/proj-struct expr))]
                        (if (identical? s (e/proj-struct expr))
                          expr
                          (e/proj (e/proj-type-name expr) (e/proj-idx expr) s)))
                expr))]
      (go expr))))

(defn- surface-lctx->meta
  "Convert mvar-shaped data inside a local context to real metacontext nodes."
  [est lctx]
  (reduce-kv
   (fn [acc id decl]
     (assoc acc id
            (cond-> decl
              (:type decl) (update :type #(surface-expr->meta est (zonk est %)))
              (:value decl) (update :value #(surface-expr->meta est (zonk est %))))))
   {}
   lctx))

(defn- meta-level->surface
  "Translate metacontext-shaped levels back to the live surface representation.
   Level mvars are now live `Level.mvar` nodes; the param path remains for
   compatibility with older elaborator artifacts."
  [est l]
  (if (nil? l)
    l
    (case (lvl/tag l)
      :zero l
      :succ (let [p (meta-level->surface est (lvl/succ-pred l))]
              (if (identical? p (lvl/succ-pred l)) l (lvl/succ p)))
      :max (let [a (meta-level->surface est (lvl/max-lhs l))
                 b (meta-level->surface est (lvl/max-rhs l))]
             (if (and (identical? a (lvl/max-lhs l))
                      (identical? b (lvl/max-rhs l)))
               l
               (lvl/level-max a b)))
      :imax (let [a (meta-level->surface est (lvl/imax-lhs l))
                  b (meta-level->surface est (lvl/imax-rhs l))]
              (if (and (identical? a (lvl/imax-lhs l))
                       (identical? b (lvl/imax-rhs l)))
                l
                (lvl/imax a b)))
      :mvar l
      :param l)))

(defn- meta-expr->surface
  "Translate metacontext-shaped data back to the live surface representation.
   Expression and universe mvars are now live `Expr.mvar`/`Level.mvar` nodes."
  [est expr]
  (letfn [(go [expr]
            (case (e/tag expr)
              :mvar expr
              :sort (let [u (meta-level->surface est (e/sort-level expr))]
                      (if (identical? u (e/sort-level expr))
                        expr
                        (e/sort' u)))
              :const (let [levels (e/const-levels expr)
                           levels' (mapv #(meta-level->surface est %) levels)]
                       (if (= levels levels')
                         expr
                         (e/const' (e/const-name expr) levels')))
              :app (let [f (go (e/app-fn expr))
                         a (go (e/app-arg expr))]
                     (if (and (identical? f (e/app-fn expr))
                              (identical? a (e/app-arg expr)))
                       expr
                       (e/app f a)))
              :lam (let [t (go (e/lam-type expr))
                         b (go (e/lam-body expr))]
                     (if (and (identical? t (e/lam-type expr))
                              (identical? b (e/lam-body expr)))
                       expr
                       (e/lam (e/lam-name expr) t b (e/lam-info expr))))
              :forall (let [t (go (e/forall-type expr))
                            b (go (e/forall-body expr))]
                        (if (and (identical? t (e/forall-type expr))
                                 (identical? b (e/forall-body expr)))
                          expr
                          (e/forall' (e/forall-name expr) t b (e/forall-info expr))))
              :let (let [t (go (e/let-type expr))
                         v (go (e/let-value expr))
                         b (go (e/let-body expr))]
                     (if (and (identical? t (e/let-type expr))
                              (identical? v (e/let-value expr))
                              (identical? b (e/let-body expr)))
                       expr
                       (e/let' (e/let-name expr) t v b)))
              :mdata (let [x (go (e/mdata-expr expr))]
                       (if (identical? x (e/mdata-expr expr))
                         expr
                         (e/mdata (e/mdata-data expr) x)))
              :proj (let [s (go (e/proj-struct expr))]
                      (if (identical? s (e/proj-struct expr))
                        expr
                        (e/proj (e/proj-type-name expr) (e/proj-idx expr) s)))
              expr))]
    (go expr)))

(defn- meta-mvar-type
  "Return the metacontext-shaped type of expression mvar `id`, after zonking."
  [est id]
  (let [mctx @(:meta-mctx est)]
    (when-let [decl (meta/expr-decl mctx id)]
      (meta/zonk-expr mctx (:type decl)))))

(defn- surface-mvar-type
  "Return the live surface-shaped type of expression mvar `id`."
  [est id]
  (when-let [type (meta-mvar-type est id)]
    (meta-expr->surface est type)))

(defn- sync-legacy-levels-from-meta!
  "Mirror solved universe levels from `:meta-mctx` back into the legacy
   compatibility level context."
  [est]
  (let [mctx @(:meta-mctx est)]
    (doseq [[id _] @(:level-mctx est)]
      (when-let [solution (meta/level-assignment mctx id)]
        (swap! (:level-mctx est) assoc-in [id :solution]
               (meta-level->surface est solution))))))

(defn- sync-legacy-exprs-from-meta!
  "Mirror solved expression mvars from `:meta-mctx` back into the legacy
   compatibility expression context."
  [est]
  (let [mctx @(:meta-mctx est)]
    (doseq [[id _] @(:mctx est)]
      (when-let [solution (meta/expr-assignment mctx id)]
        (swap! (:mctx est) assoc-in [id :solution]
               (meta-expr->surface est solution))))))

(defn- sync-meta-decls!
  "Keep the mirrored metacontext declarations readable after legacy zonking by
   instantiating assigned mvars in their types/local contexts."
  [est]
  (swap! (:meta-mctx est)
         (fn [mctx]
           (reduce meta/instantiate-mvar-decl-mvars mctx (keys (:decls mctx))))))

(defn- unsolved-mvars [est]
  (let [mctx @(:meta-mctx est)
        legacy @(:mctx est)]
    (->> (:decls mctx)
         (remove (fn [[id _]] (meta/expr-assigned-or-delayed? mctx id)))
         (sort-by first)
         (mapv (fn [[id decl]]
                 [id (cond-> {:kind (:kind decl)
                              :index (:index decl)
                              :user-name (:user-name decl)}
                       (or (:inst-implicit? decl)
                           (get-in legacy [id :inst-implicit]))
                       (assoc :inst-implicit true))])))))

(defn- unsolved-levels [est]
  (let [mctx @(:meta-mctx est)
        legacy @(:level-mctx est)]
    (->> (:level-depth mctx)
         (remove (fn [[id _]] (meta/level-assignment mctx id)))
         (sort-by first)
         (mapv (fn [[id _]]
                 [id {:name (or (get-in legacy [id :name])
                                (name/from-string (str "?u" id)))}])))))

(defn- fresh-result-mvar-ids
  "Lean-style collection boundary for tactic holes: only unassigned mvars that
   occur in the zonked result become collected holes."
  [mctx expr start-index]
  (->> (meta/expr-mvars-no-delayed mctx expr)
       distinct
       (filter (fn [id]
                 (let [decl (meta/expr-decl mctx id)]
                   (and decl
                        (>= (:index decl 0) start-index)
                        (not (meta/expr-assigned-or-delayed? mctx id))))))
       (sort-by #(get-in mctx [:decls % :index] 0))
       vec))

(defn- fresh-result-level-ids
  "Collect new unassigned universe mvars that occur in the zonked result."
  [mctx expr old-level-ids]
  (->> (meta/unassigned-level-mvars mctx expr)
       distinct
       (remove old-level-ids)
       sort
       vec))

(declare elab-error! solve-instance-mvars!)

(defn- strict-finalize [est expr]
  (solve-instance-mvars! est)
  (let [result (zonk est expr)
        unsolved (unsolved-mvars est)
        unsolved-levels (unsolved-levels est)]
    (when (seq unsolved)
      (elab-error! "Unsolved metavariables"
                   {:count (count unsolved)
                    :mvars (mapv (fn [[id _]]
                                    {:id id :type (surface-mvar-type est id)})
                                  unsolved)}))
    (when (seq unsolved-levels)
      (elab-error! "Unsolved universe level metavariables"
                   {:count (count unsolved-levels)
                    :names (mapv (fn [[_ m]] (:name m)) unsolved-levels)}))
    result))

(defn- collecting-finalize [est expr]
  (solve-instance-mvars! est)
  (let [legacy-result (zonk est expr)
        _ (sync-meta-decls! est)
        result (surface-expr->meta est legacy-result)
        start (:collect-from-index est 0)
        mctx @(:meta-mctx est)
        legacy @(:mctx est)
        unsolved (mapv (fn [id]
                         (let [decl (meta/expr-decl mctx id)]
                           [id (cond-> {:kind (:kind decl)
                                        :index (:index decl)
                                        :user-name (:user-name decl)}
                                 (or (:inst-implicit? decl)
                                     (get-in legacy [id :inst-implicit]))
                                 (assoc :inst-implicit true))]))
                       (fresh-result-mvar-ids mctx result start))
        old-levels (:initial-level-mvar-ids est #{})
        level-legacy @(:level-mctx est)
        unsolved-levels (mapv (fn [id]
                                [id {:name (or (get-in level-legacy [id :name])
                                               (name/from-string (str "?u" id)))}])
                              (fresh-result-level-ids mctx result old-levels))]
    {:expr result
     :meta-mctx @(:meta-mctx est)
     :holes (mapv (fn [[id m]]
                    {:id id
                     :expr (e/mvar id)
                     :type (meta-mvar-type est id)
                     :kind (:kind m)
                     :user-name (:user-name m)
                     :inst-implicit? (boolean (:inst-implicit m))})
                  unsolved)
     :level-holes (mapv (fn [[id m]]
                          {:id id
                           :level (lvl/mvar id)
                           :name (:name m)})
                        unsolved-levels)}))

;; ============================================================
;; Level parsing (same as surface.term)
;; ============================================================

(defn- parse-level-token [s]
  (if-let [n (try (Long/parseLong (str s)) (catch NumberFormatException _ nil))]
    (lvl/from-nat n)
    (lvl/param (name/from-string (str s)))))

(defn- parse-levels
  "Parse universe levels from 'Foo.{1,2}'. Returns [base-name levels-or-nil]."
  [sym-str]
  (if-let [idx (clojure.string/index-of sym-str ".{")]
    (let [base (subs sym-str 0 idx)
          lvl-str (subs sym-str (+ idx 2) (dec (count sym-str)))
          parts (clojure.string/split lvl-str #"\s*,\s*")
          levels (mapv parse-level-token parts)]
      [base levels])
    [sym-str nil]))

;; ============================================================
;; Binder parsing (same as surface.term)
;; ============================================================

(defn- parse-binders [binder-vec]
  (let [tokens (remove (fn [t] (or (= (str t) ",") (= (str t) ":") (= (str t) ":-"))) binder-vec)]
    (loop [ts (seq tokens) result []]
      (if (or (nil? ts) (empty? ts))
        result
        (let [nam (first ts)
              typ (second ts)]
          (when (nil? typ)
            (throw (ex-info (str "Binder missing type for: " nam) {:name nam})))
          (recur (nnext ts) (conj result [nam typ])))))))

;; ============================================================
;; First-order unification
;; ============================================================

(defn- unify-levels!
  "Try to unify two levels, solving level metavars."
  [est l1 l2]
  (let [l1 (surface-level->meta est (zonk-level est l1))
        l2 (surface-level->meta est (zonk-level est l2))]
    (when-let [mctx (meta/is-level-def-eq @(:meta-mctx est) l1 l2)]
      (reset! (:meta-mctx est) mctx)
      (sync-legacy-levels-from-meta! est)
      true)))

(defn- unify!
  "First-order unification of two expressions, solving metavars in est.
   Returns true on success."
  [est a b]
  (sync-meta-decls! est)
  (let [a (surface-expr->meta est (zonk est a))
        b (surface-expr->meta est (zonk est b))
        st (tc/attach-lctx (tc/mk-tc-state (:env est)) (:lctx (:tc est)))]
    (when-let [mctx (meta/is-def-eq @(:meta-mctx est) st a b)]
      (reset! (:meta-mctx est) mctx)
      (sync-legacy-levels-from-meta! est)
      (sync-legacy-exprs-from-meta! est)
      true)))

(defn- infer-with-mvars
  "Infer the type of an expression that may still mention elaboration mvars.

   Lean keeps elaboration metavariables in the metacontext consulted by
   Meta.inferType. We mirror that: expression holes are live `Expr.mvar` nodes,
   universe holes are live `Level.mvar` nodes, legacy fvar/level-param
   placeholders are still accepted, and the inferred type is translated back to
   the live surface shape."
  [est expr]
  (sync-meta-decls! est)
  (let [expr (surface-expr->meta est (zonk est expr))
        st (tc/attach-lctx (tc/mk-tc-state (:env est)) (:lctx (:tc est)))
        inferred (meta/infer-type @(:meta-mctx est) st expr)]
    (zonk est (meta-expr->surface est inferred))))

(defn- whnf-with-mvars
  "Weak-head normalize an elaborator expression through the metacontext."
  [est expr]
  (sync-meta-decls! est)
  (let [expr (surface-expr->meta est (zonk est expr))
        st (tc/attach-lctx (tc/mk-tc-state (:env est)) (:lctx (:tc est)))
        reduced (meta/whnf @(:meta-mctx est) st expr)]
    (zonk est (meta-expr->surface est reduced))))

;; ============================================================
;; Core elaboration
;; ============================================================

(declare elab-term)

(defn- elab-error! [msg data]
  (throw (ex-info (str "Elaboration error: " msg) (merge {:kind :elab-error} data))))

(defn- resolve-const
  "Resolve a constant name, creating level metavars if levels not provided."
  [est base-name explicit-levels]
  (let [cname (name/from-string base-name)
        ci (env/lookup (:env est) cname)]
    (when-not ci
      (elab-error! (str "Unknown constant: " base-name) {:name base-name}))
    (let [level-params (env/ci-level-params ci)
          levels (if explicit-levels
                   explicit-levels
                   ;; Create fresh level metavars for each param
                   (mapv (fn [_] (fresh-level-mvar! est)) level-params))]
      (when (not= (count levels) (count level-params))
        (elab-error! (str "Wrong number of universe levels for " base-name)
                     {:expected (count level-params) :actual (count levels)}))
      (e/const' cname levels))))

(defn- strip-at-prefix
  "If sym-str starts with @, return [true stripped] else [false sym-str]."
  [sym-str]
  (if (clojure.string/starts-with? sym-str "@")
    [true (subs sym-str 1)]
    [false sym-str]))

(defn- resolve-symbol
  "Resolve a symbol: check scope (bound vars) first, then env constants.
   Returns {:expr Expr :explicit? bool} — explicit? means no implicit insertion."
  [est sym]
  (let [sym-str (str sym)
        [explicit? sym-str] (strip-at-prefix sym-str)]
    ;; Bound variable? (:as-term carries a coercion — e.g. a Subtype-typed parameter
    ;; whose references elaborate as its .val, so refined params are usable directly)
    (if-let [{:keys [fvar-id as-term]} (get (:scope est) sym)]
      {:expr (or as-term (e/fvar fvar-id)) :explicit? false}
      ;; Special shortcuts
      (case sym-str
        "Prop" {:expr (e/sort' lvl/zero) :explicit? false}
        "Type" {:expr (e/sort' (lvl/succ lvl/zero)) :explicit? false}
        ;; Parse levels and resolve
        (let [[base-name explicit-levels] (parse-levels sym-str)]
          (if (and (= base-name "Type") explicit-levels)
            {:expr (e/sort' (lvl/succ (first explicit-levels))) :explicit? false}
            {:expr (resolve-const est base-name explicit-levels)
             :explicit? explicit?}))))))

(defn- insert-implicits
  "Given a function expr and its type, insert metavariables for leading
   implicit/instance-implicit arguments. Returns [expr' type'] where
   type' is the remaining (non-implicit) type."
  [est fn-expr fn-type]
  (loop [expr fn-expr
         ty (whnf-with-mvars est fn-type)]
      (if (and (e/forall? ty)
               (let [info (e/forall-info ty)]
                 (or (= info :implicit)
                     (= info :strict-implicit)
                     (= info :inst-implicit))))
        (let [binfo (e/forall-info ty)
              inst? (= binfo :inst-implicit)
              arg-mvar (fresh-mvar! est (e/forall-type ty)
                                    (cond-> {:kind (if inst? :synthetic :natural)}
                                      (e/forall-name ty) (assoc :user-name (e/forall-name ty))
                                      inst? (assoc :inst-implicit? true)))
              ;; Mark instance-implicit mvars so they can be solved by instance
              ;; synthesis (not just unification) before the final unsolved-check.
              _ (when inst? (mark-inst-implicit! est arg-mvar))
              expr' (e/app expr arg-mvar)
              ty' (whnf-with-mvars est (e/instantiate1 (e/forall-body ty) arg-mvar))]
          (recur expr' ty'))
        [expr ty])))

(defn- type-head-name
  "Whnf the (zonked) type and return its head constant's name as a string (e.g. \"Nat\",
   \"Int\"), or nil if the head isn't a constant. Used for type-directed op selection."
  [est ty]
  (let [tw (whnf-with-mvars est ty)
        [h _] (e/get-app-fn-args tw)]
    (when (e/const? h) (name/->string (e/const-name h)))))

(defn- elab-app
  "Elaborate a function application, inserting implicit arguments."
  [est head-sexpr arg-sexprs]
  (let [;; Resolve head, checking for @-prefix
        {:keys [expr explicit?]}
        (if (symbol? head-sexpr)
          (resolve-symbol est head-sexpr)
          {:expr (elab-term est head-sexpr) :explicit? false})
        head-expr expr
        head-type (infer-with-mvars est head-expr)
        ;; Positional convention (matches sexp->ansatz / the prior a/defn bodies): when
        ;; the user supplies exactly the full binder count (implicits INCLUDED, e.g.
        ;; (List.cons Nat x xs) or (TRBTree.node Nat color l v r)), apply positionally —
        ;; i.e. treat like @-explicit (no implicit insertion). Fewer args ⇒ implicits are
        ;; inferred as usual (e.g. (List.cons x xs), (Eq n n)).
        total-binders (loop [t head-type c 0]
                        (if (e/forall? t) (recur (e/forall-body t) (inc c)) c))
        explicit? (or explicit?
                      (and (e/const? head-expr) (pos? (count arg-sexprs))
                           (= (count arg-sexprs) total-binders)))
        ;; Insert leading implicits (unless @-explicit or positional)
        [head-expr head-type] (if explicit?
                                [head-expr head-type]
                                (insert-implicits est head-expr head-type))]
    ;; Apply explicit arguments one at a time
    (loop [expr head-expr
           ty head-type
           args (seq arg-sexprs)]
      (if-not args
        ;; After all args applied, insert trailing implicits
        (if explicit?
          expr
          (first (insert-implicits est expr ty)))
        (let [;; Insert implicit arguments before each explicit arg (unless @-explicit)
              [expr ty] (if explicit?
                          [expr ty]
                          (insert-implicits est expr ty))]
          (if (e/forall? ty)
            (let [arg-expr (elab-term est (first args))
                  ;; Unify arg type with expected domain
                  arg-type (infer-with-mvars est arg-expr)
                  dom-type (e/forall-type ty)]
              (unify! est arg-type dom-type)
              (let [expr' (e/app expr arg-expr)
                    body-inst (e/instantiate1 (e/forall-body ty) arg-expr)
                    ty' (whnf-with-mvars est body-inst)]
                (recur expr' ty' (next args))))
            (elab-error! "Too many arguments"
                         {:fn head-sexpr :remaining-args (vec args)
                          :type ty})))))))

(defn- elab-forall
  "Elaborate a forall expression with binders."
  [est binder-vec body-sexpr]
  (let [binders (parse-binders binder-vec)]
    (letfn [(build [binders est]
              (if (empty? binders)
                (elab-term est body-sexpr)
                (let [[nam typ-sexpr] (first binders)
                      ;; Zonk the binder type so its solved level-mvars (`?u`) are substituted before
                      ;; it is stored into :scope / the tc :lctx. Lean instantiates mvars in binder
                      ;; types; without this the stored type keeps raw `?u`, and a later EAGER kernel
                      ;; infer of a sub-term in ARGUMENT position (elab-app) trips on the opaque `?u`
                      ;; ("Type mismatch in application") — the body position survives only because it
                      ;; reaches the final whole-term zonk. See [[elab-binder-zonk-bug]].
                      typ-expr (zonk est (elab-term est typ-sexpr))
                      fvar-id (fresh-id! est)
                      fv (e/fvar fvar-id)
                      est' (-> est
                               (assoc-in [:scope nam] {:fvar-id fvar-id :type typ-expr})
                               (update :tc update :lctx red/lctx-add-local fvar-id (str nam) typ-expr))
                      body-expr (build (rest binders) est')
                      abs-body (e/abstract1 (meta/abstract-fvars body-expr [fvar-id]) fvar-id)]
                  (e/forall' (str nam) typ-expr abs-body :default))))]
      (build binders est))))

(defn- subtype-as-term
  "If `typ-expr` is a `Subtype B P`, the coercion term `Subtype.val B P fv` (the binder read through its
   carrier) — else nil. Used to auto-coerce a refined binder's references to the underlying value, the
   way a refined a/defn param already is (ansatz.core), so a predicate like `(<= 5 x)` / `(count s)` over
   a `Subtype`-refined element reads naturally. Lean-faithful: this is the `Subtype` → base coercion."
  [typ-expr fv]
  (let [[h args] (e/get-app-fn-args typ-expr)]
    (when (and (e/const? h) (= "Subtype" (name/->string (e/const-name h))) (= 2 (count args)))
      (e/app* (e/const' (name/from-string "Subtype.val") (vec (e/const-levels h)))
              (first args) (second args) fv))))

(defn- elab-lam
  "Elaborate a lambda expression with binders. When `(:coerce-refined-binders est)` is set (the data-
   pipeline SOAC context — wandler.surface.collections/compile-fn turns it on), a `Subtype`-typed binder
   gets an `:as-term` so its references auto-coerce to the carrier value; default off, so proofs and
   ordinary lambdas are unaffected."
  [est binder-vec body-sexpr]
  (let [binders (parse-binders binder-vec)
        coerce? (:coerce-refined-binders est)]
    (letfn [(build [binders est]
              (if (empty? binders)
                (elab-term est body-sexpr)
                (let [[nam typ-sexpr] (first binders)
                      ;; Zonk the binder type so its solved level-mvars (`?u`) are substituted before
                      ;; it is stored into :scope / the tc :lctx. Lean instantiates mvars in binder
                      ;; types; without this the stored type keeps raw `?u`, and a later EAGER kernel
                      ;; infer of a sub-term in ARGUMENT position (elab-app) trips on the opaque `?u`
                      ;; ("Type mismatch in application") — the body position survives only because it
                      ;; reaches the final whole-term zonk. See [[elab-binder-zonk-bug]].
                      typ-expr (zonk est (elab-term est typ-sexpr))
                      fvar-id (fresh-id! est)
                      fv (e/fvar fvar-id)
                      as-term (when coerce? (subtype-as-term typ-expr fv))
                      est' (-> est
                               (assoc-in [:scope nam] (cond-> {:fvar-id fvar-id :type typ-expr}
                                                        as-term (assoc :as-term as-term)))
                               (update :tc update :lctx red/lctx-add-local fvar-id (str nam) typ-expr))
                      body-expr (build (rest binders) est')
                      abs-body (e/abstract1 (meta/abstract-fvars body-expr [fvar-id]) fvar-id)]
                  (e/lam (str nam) typ-expr abs-body :default))))]
      (build binders est))))

(defn- elab-let
  "Elaborate a let expression."
  [est binder-vec body-sexpr]
  (let [tokens (remove (fn [t] (or (= (str t) ":") (= (str t) "="))) binder-vec)
        tokens-vec (vec tokens)]
    (when (not= 3 (count tokens-vec))
      (elab-error! "let binder expects [name type value]" {:binder binder-vec}))
    (let [nam (nth tokens-vec 0)
          typ-sexpr (nth tokens-vec 1)
          val-sexpr (nth tokens-vec 2)
          typ-expr (elab-term est typ-sexpr)
          val-expr (elab-term est val-sexpr)
          fvar-id (fresh-id! est)
          est' (-> est
                   (assoc-in [:scope nam] {:fvar-id fvar-id :type typ-expr})
                   (update :tc update :lctx red/lctx-add-let fvar-id (str nam) typ-expr val-expr))
          body-expr (elab-term est' body-sexpr)
          abs-body (e/abstract1 body-expr fvar-id)]
      (e/let' (str nam) typ-expr val-expr abs-body))))

(defn sizeof-inst
  "Synthesize a SizeOf instance term for supported types: Nat, List of sized, and custom
   inductives with a derived `<T>._sizeOf_inst` (wf-derive-sizeof! in ansatz.core)."
  [env ty]
  (let [[h as] (e/get-app-fn-args ty)]
    (cond
      (and (e/const? h) (= "Nat" (name/->string (e/const-name h))) (empty? as))
      (e/const' (name/from-string "instSizeOfNat") [])
      (and (e/const? h) (= "List" (name/->string (e/const-name h))) (= 1 (count as)))
      (when-let [elt (sizeof-inst env (first as))]
        (e/app* (e/const' (name/from-string "List._sizeOf_inst") (vec (e/const-levels h)))
                (first as) elt))
      (and (e/const? h) (empty? as)
           (env/lookup env (name/mk-str (e/const-name h) "_sizeOf_inst")))
      (e/const' (name/mk-str (e/const-name h) "_sizeOf_inst") [])
      :else nil)))

(defn- recur-form? [x]
  (and (seq? x) (symbol? (first x)) (= "recur" (name (first x)))))

(defn- elab-loop
  "Compile the common counting-loop shape
     (loop [i init, a0 i0, …] (if (== i 0) BASE (recur (dec i) s0 …)))
   to Nat.rec on the decreasing counter i, into the accumulator function space:
     ((Nat.rec (λ_:Nat. T0→…→R) (λ a0…. BASE) (λ k ih a0…. ih s0[i:=k+1] …) init) i0 …)
   The counter must be the first binding, recur's first arg (dec counter), and the test
   (== counter 0). Other loop shapes throw (→ use ^:partial for general loops)."
  [est binder-vec body]
  (let [pairs (vec (partition 2 binder-vec))
        bad (fn [msg] (elab-error!
                       (str "loop: " msg " — only the counting shape "
                            "(loop [i n …] (if (== i 0) base (recur (dec i) …))) is auto-compiled; "
                            "use ^:partial for general loops") {:body body}))
        _ (when (empty? pairs) (bad "needs a counter binding"))
        [ivar iinit] (first pairs)
        accs (vec (rest pairs))
        _ (when-not (and (seq? body) (symbol? (first body)) (= "if" (name (first body)))
                         (= 4 (count body))) (bad "body must be an if"))
        [_ test br-a br-b] body
        recur-br (cond (recur-form? br-b) br-b (recur-form? br-a) br-a :else (bad "no (recur …) branch"))
        base-br (if (identical? recur-br br-b) br-a br-b)
        rargs (vec (rest recur-br))
        dec-arg (first rargs)
        _ (when-not (and (seq? dec-arg) (symbol? (first dec-arg)) (= "dec" (name (first dec-arg)))
                         (= ivar (second dec-arg))) (bad "first recur arg must be (dec counter)"))
        _ (when-not (= (count rargs) (inc (count accs))) (bad "recur arity must match the bindings"))
        _ (when-not (and (seq? test) (symbol? (first test)) (= "==" (name (first test)))
                         (let [a (second test) b (nth test 2)]
                           (or (and (= a ivar) (= b 0)) (and (= a 0) (= b ivar)))))
            (bad "test must be (== counter 0)"))
        steps (vec (rest rargs))
        nat (e/const' (name/from-string "Nat") [])
        succ-of (fn [k] (e/app (e/const' (name/from-string "Nat.succ") []) k))
        iinit* (elab-term est iinit)
        acc-inits* (mapv (fn [[_ ini]] (elab-term est ini)) accs)
        acc-types (mapv (fn [a*] (zonk est (infer-with-mvars est a*))) acc-inits*)
        bind-accs (fn [est0]                          ; → [est' acc-fids]
                    (reduce (fn [[e ids] [[av _] at]]
                              (let [fid (fresh-id! e)]
                                [(-> e (assoc-in [:scope av] {:fvar-id fid :type at})
                                     (update :tc update :lctx red/lctx-add-local fid (str av) at))
                                 (conj ids fid)]))
                            [est0 []] (map vector accs acc-types)))
        wrap-acc-lams (fn [body0]                      ; λ a0 … . body0 (accs already abstracted)
                        (reduce (fn [b i] (e/lam (str (first (nth accs i))) (nth acc-types i) b :default))
                                body0 (reverse (range (count accs)))))
        ;; base : T0→…→R
        [est-b acc-fids-b] (bind-accs est)
        base* (elab-term est-b base-br)
        ret-type (zonk est-b (infer-with-mvars est-b base*))
        base-fn (wrap-acc-lams (e/abstract-many base* acc-fids-b))
        ;; arrow type + motive + universe
        arrow-type (reduce (fn [acc t] (e/forall' "_" t acc :default)) ret-type (reverse acc-types))
        u (let [s (zonk est (infer-with-mvars est arrow-type))]
            (if (e/sort? s) (e/sort-level s) (lvl/succ lvl/zero)))
        motive (e/lam "_" nat arrow-type :default)
        ;; step : λ k ih a0 … . ih s0[i:=succ k] …
        k-fid (fresh-id! est)
        ih-fid (fresh-id! est)
        i-fid (fresh-id! est)
        est-s0 (-> est (assoc-in [:scope ivar] {:fvar-id i-fid :type nat})
                   (update :tc update :lctx red/lctx-add-local i-fid (str ivar) nat))
        [est-s acc-fids-s] (bind-accs est-s0)
        succ-k (succ-of (e/fvar k-fid))
        steps* (mapv (fn [s] (let [s* (elab-term est-s s)]
                               (e/instantiate1 (e/abstract1 s* i-fid) succ-k)))
                     steps)
        step-body (reduce e/app (e/fvar ih-fid) steps*)
        step-abs (e/abstract-many step-body (into [k-fid ih-fid] acc-fids-s))
        step-fn (e/lam (str ivar) nat
                       (e/lam "ih" arrow-type (wrap-acc-lams step-abs) :default) :default)
        nat-rec (e/const' (name/from-string "Nat.rec") [u])]
    (reduce e/app (e/app* nat-rec motive base-fn step-fn iinit*) acc-inits*)))

(def ^:dynamic *bypass-registries-once*
  "When true, the NEXT elab-term seq dispatch skips the user registries (term + macro)
   and falls through to the built-in forms — then resets. The delegation primitive for
   extension authors (api/elab-base): a registered elaborator wrapping a built-in verb
   hands the non-special case back without re-entering itself."
  false)

(defn- registry-lookup
  "Look up a surface-form `head` symbol in `registry`. Direct hit first; if it misses AND `head` is
   namespace-qualified (including via a namespace ALIAS, e.g. `d/q` where `d` aliases `datahike.api`),
   retry under its resolved canonical var symbol (`datahike.api/q`). This lets an elaborator registered
   under a fully-qualified name fire on any alias of it — so a surface `(d/q …)` dispatches exactly like
   the fully-qualified `(datahike.api/q …)`. Resolution uses `*ns*` (the user ns at elaboration), so a
   bare/unqualified head is never resolved (it keeps its registered-vocabulary meaning)."
  [registry head]
  (or (get registry head)
      (when (namespace head)
        (when-let [v (try (resolve head) (catch Throwable _ nil))]
          (when (var? v) (get registry (symbol v)))))))

(defn- hole-symbol?
  "Lean-style placeholder syntax for the surface layer: `_`, `?_`, or any
   symbol whose name starts with `?`."
  [x]
  (and (symbol? x)
       (let [s (str x)]
         (or (= s "_")
             (= s "?_")
             (clojure.string/starts-with? s "?")))))

(defn- fresh-hole!
  "Create a term hole. Its type is itself a metavariable so later
   bidirectional constraints can determine it."
  [est hole-name]
  (if-let [id (when hole-name (get-in @(:meta-mctx est) [:user-names hole-name]))]
    (meta/zonk-expr @(:meta-mctx est) (e/mvar id))
    (let [u (fresh-level-mvar! est)
          type-hole (fresh-mvar! est (e/sort' u))
          kind (if (or hole-name (:holes-as-synthetic-opaque? est))
                 :syntheticOpaque
                 :natural)
          term-hole (fresh-mvar! est type-hole
                                  (cond-> {:kind kind}
                                    hole-name (assoc :user-name hole-name)))]
      term-hole)))

(defn- elab-term
  "Recursively elaborate an s-expression into a Ansatz Expr."
  [est sexpr]
  (cond
    ;; an already-elaborated kernel Expr passes through — term elaborators (elab_rules)
    ;; splice Exprs into surface forms they hand back to elab (quotation with term holes)
    (instance? ansatz.kernel.Expr sexpr) sexpr
    (integer? sexpr) (e/lit-nat sexpr)
    ;; FLOAT literal: a Clojure double → OfScientific.ofScientific Float inst m s e
    ;; (m × 10^±e; BigDecimal's shortest round-trip repr). Float is the computable
    ;; carrier (native double); Real is for proofs, so a bare double means Float.
    (double? sexpr)
    (let [neg? (neg? sexpr)
          bd (java.math.BigDecimal. (Double/toString (Math/abs (double sexpr))))
          scale (.scale bd)
          mant (.unscaledValue bd)
          [sign expn] (if (>= scale 0) [true scale] [false (- scale)])
          FloatT (e/const' (name/from-string "Float") [])
          lit (e/app* (e/const' (name/from-string "OfScientific.ofScientific") [lvl/zero])
                      FloatT (e/const' (name/from-string "instOfScientificFloat") [])
                      (e/lit-nat mant)
                      (e/const' (name/from-string (if sign "Bool.true" "Bool.false")) [])
                      (e/lit-nat expn))]
      (if neg?
        (elab-error! "negative Float literals not yet supported (wrap as (sub Float 0.0 x))"
                     {:form sexpr})
        lit))
    (string? sexpr)  (e/lit-str sexpr)
    (boolean? sexpr) (e/const' (name/from-string (if sexpr "Bool.true" "Bool.false")) [])
    (nil? sexpr)     (elab-term est (symbol "List.nil"))  ;; bare nil = empty List

    (hole-symbol? sexpr)
    (fresh-hole! est (when-not (#{"_" "?_"} (str sexpr)) (name/from-string (subs (str sexpr) 1))))

    (symbol? sexpr)
    ;; A bare symbol in term position: insert its implicit/instance arguments
    ;; (as Lean does for any term, not only application heads) so e.g. List.nil
    ;; becomes List.nil.{?u} ?α rather than the under-applied bare constant.
    (let [{:keys [expr explicit?]} (resolve-symbol est sexpr)]
      (if explicit?
        expr
        (first (insert-implicits est expr (infer-with-mvars est expr)))))

    (seq? sexpr)
    (let [head (first sexpr)
          bypass? *bypass-registries-once*
          _ (when bypass? (set! *bypass-registries-once* false))]
      ;; user-registered surface forms. Term elaborators first (lean4 elab_rules-shaped:
      ;; syntax → kernel Expr with elaborator access, for type-directed forms), then
      ;; macro elaborators (lean4 macro_rules-shaped: syntax → syntax, which re-elaborates) —
      ;; both compose with every surface feature. LEXICAL SCOPING: a LOCAL BINDER shadows the global
      ;; vocabulary — `(get (:scope est) head)` is checked first, so e.g. a binder named `dec`
      ;; (a DecidableEq instance) applied as `(dec a b)` resolves to the binder, NOT the registered
      ;; `dec` (clojure decrement) from the wandler collections vocabulary. (Before this, loading any
      ;; namespace that registered `dec`/`map`/`min`/… globally silently shadowed same-named binders.)
      (if-let [telab (and (symbol? head) (not bypass?)
                          (not (contains? (:scope est) head))
                          (registry-lookup @ingest/term-elaborator-registry head))]
        (telab est (vec (rest sexpr)))
        (if-let [expander (and (symbol? head) (not bypass?)
                               (not (contains? (:scope est) head))
                               (registry-lookup @ingest/elaborator-registry head))]
          (elab-term est (expander (rest sexpr)))
          (case (when (symbol? head) (str head))
            "forall" (let [[_ binder-vec & body-forms] sexpr]
                       (when (not= 1 (count body-forms))
                         (elab-error! "forall expects one body" {:forms body-forms}))
                       (elab-forall est binder-vec (first body-forms)))

            "lam"    (let [[_ binder-vec & body-forms] sexpr]
                       (when (not= 1 (count body-forms))
                         (elab-error! "lam expects one body" {:forms body-forms}))
                       (elab-lam est binder-vec (first body-forms)))

            ;; Non-dependent function type. `arrow` plus the idiomatic `=>` (THE function-type arrow
            ;; per clj-ingest; `->` is ALWAYS Clojure threading, never the arrow) and `→`, with N-ary
            ;; currying: (=> A B C) = A → B → C (right-associated). Each part elaborates in the same
            ;; scope (fvar-based — no de-Bruijn depth shift); `e/arrow` wraps `_ : A`. This brings the
            ;; a/theorem fvar elaborator in line with a/defn, which already accepts `=>` binders.
            ("arrow" "=>" "→")
            (let [parts (rest sexpr)]
              (when (< (count parts) 2)
                (elab-error! "arrow / => expects at least two types" {:form sexpr}))
              (let [exprs (mapv #(elab-term est %) parts)]
                (reduce (fn [b a] (e/arrow a b)) (last exprs) (reverse (butlast exprs)))))

            "Sort"   (let [[_ level-form] sexpr
                           level (cond
                                   (integer? level-form) (lvl/from-nat level-form)
                                   (= 'zero level-form) lvl/zero
                                   :else (elab-error! (str "Unsupported Sort level: " level-form)
                                                      {:level level-form}))]
                       (e/sort' level))

            "let"    (let [[_ binder-vec & body-forms] sexpr
                           toks (remove #(contains? #{":" ":-" "=" ","} (str %)) binder-vec)]
                   ;; ansatz typed surface let is a single [name type value] (3 tokens);
                   ;; Clojure's let (name/value pairs) is a macro → expand to let*.
                       (if (and (= 3 (count toks)) (= 1 (count body-forms)))
                         (elab-let est binder-vec (first body-forms))
                         (elab-term est (macroexpand-1 sexpr))))

            "app"    (let [[_ f a] sexpr]
                       (e/app (elab-term est f) (elab-term est a)))

        ;; Two surface forms funnel to the one inferring compiler (compile-match):
        ;;  - inferring (proofs):    (match discr [pat rhs] …)            — vector alts
        ;;  - explicit (a/defn):     (match scrut type ret (ctor [fields] body) …)
        ;; The explicit form is desugared (drop type+ret, which are a bvar-era workaround
        ;; and dead code respectively; ctor qualification is done inside compile-match).
            "match"  (let [args (vec (rest sexpr))
                           est* (assoc est
                                       :infer-fn infer-with-mvars
                                       :whnf-fn whnf-with-mvars
                                       :unify-fn unify!
                                       :zonk-fn zonk)]
                       (if (vector? (get args 1))
                         (match/compile-match est* elab-term (first args) (mapv vec (rest args)))
                     ;; explicit form: (match scrut type ret (ctor [fields] body) …). Keep the
                     ;; declared ret-type as the motive — it's the type-directed hint that lets
                     ;; under-determined branches (e.g. a bare `nil`) resolve their element type.
                         (let [scrut (first args)
                               declared-ret (try (elab-term est (nth args 2)) (catch Throwable _ nil))
                               alts (mapv (fn [c]
                                            (let [ctor (first c)
                                                  has-fields (and (> (count c) 2) (vector? (second c)))
                                                  fields (if has-fields (second c) [])
                                                  body (if has-fields (nth c 2) (second c))]
                                              [(if (seq fields) (cons ctor (seq fields)) ctor) body]))
                                          (drop 3 args))]
                           (match/compile-match (cond-> est* declared-ret
                                                        (assoc :declared-ret-type declared-ret))
                                                elab-term scrut alts))))

        ;; (=> A B) is handled by the unified arrow clause above (with currying + the → glyph).

        ;; Bool if-then-else → Bool.rec. The motive is the then-branch's type,
        ;; inferred directly (fvar context is present — no open/close needed).
        ;; if over a recognizable comparison lifts to its Prop + Decidable instance and emits
        ;; dite — the shape lean4's @[macro_inline] ite/dite reduce to (Decidable.casesOn),
        ;; whose branch binders CARRY the guard. Downstream this is what gives well-founded
        ;; decrease proofs their hypotheses with no special-casing. A non-comparison Bool
        ;; condition (variable, Bool-valued call) stays on Bool.rec.
            "if" (let [[_ c t e] sexpr
                       cmp (when (and (seq? c) (symbol? (first c)) (= 3 (count c)))
                             (case (str (first c))
                               "==" ["Eq" "Nat.decEq" false]
                               "<"  ["lt" "Nat.decLt" false]
                               ">"  ["lt" "Nat.decLt" true]
                               ("<=" "≤") ["le" "Nat.decLe" false]
                               (">=" "≥") ["le" "Nat.decLe" true]
                               nil))]
                   (if cmp
                     (let [[prop-head dec-name swap?] cmp
                           [a b] (if swap? [(nth c 2) (nth c 1)] [(nth c 1) (nth c 2)])
                           a* (elab-term est a)
                           b* (elab-term est b)
                           ;; Build the Prop with the CONCRETE canonical Nat instance
                           ;; (instLTNat/instLENat), not via (lt Nat a b) — that path
                           ;; leaves an instance MVAR which the paired Nat.decLt/decLe
                           ;; (whose type mentions the canonical instance) cannot match
                           ;; under a strict mid-elaboration infer (e.g. as an argument
                           ;; of List.map, before the synthesis pass runs).
                           prop (case prop-head
                                  "Eq" (elab-term est (list 'Eq 'Nat a b))
                                  "lt" (e/app* (e/const' (name/from-string "LT.lt") [lvl/zero])
                                               (e/const' (name/from-string "Nat") [])
                                               (e/const' (name/from-string "instLTNat") []) a* b*)
                                  "le" (e/app* (e/const' (name/from-string "LE.le") [lvl/zero])
                                               (e/const' (name/from-string "Nat") [])
                                               (e/const' (name/from-string "instLENat") []) a* b*))
                           inst (e/app* (e/const' (name/from-string dec-name) []) a* b*)
                           then-expr (elab-term est t)
                           else-expr (elab-term est e)
                           ret-type (infer-with-mvars est then-expr)
                           ret-sort (infer-with-mvars est ret-type)
                           u (if (e/sort? ret-sort) (e/sort-level ret-sort) (lvl/succ lvl/zero))
                           not-prop (e/app (e/const' (name/from-string "Not") []) prop)]
                       (e/app* (e/const' (name/from-string "dite") [u])
                               ret-type prop inst
                               (e/lam "h" prop (e/lift then-expr 1 0) :default)
                               (e/lam "h" not-prop (e/lift else-expr 1 0) :default)))
                     (let [cond-expr (elab-term est c)
                           then-expr (elab-term est t)
                           else-expr (elab-term est e)
                           ret-type (infer-with-mvars est then-expr)]
                       (e/app* (e/const' (name/from-string "Bool.rec") [(lvl/succ lvl/zero)])
                               (e/lam "_" (e/const' (name/from-string "Bool") []) ret-type :default)
                               else-expr then-expr cond-expr))))

        ;; Prop-valued comparisons over an explicit type: (le T a b) / (lt T a b)
        ;; → LE.le.{?u} T ?inst a b — the instance + level resolve via synthesis.
            ("le" "lt") (let [[_ T a b] sexpr
                              cn  (if (= (str head) "le") "LE.le" "LT.lt")
                              icn (if (= (str head) "le") "LE" "LT")
                              T'  (elab-term est T)
                              a'  (elab-term est a)
                              b'  (elab-term est b)
                          ;; EAGER level: a mid-elaboration infer (e.g. as the argument of Not)
                          ;; cannot apply a const carrying an unsolved level-mvar. T's sort is
                          ;; concrete in practice (Nat/Int/custom : Sort 1 → u = 0); fall back
                          ;; to a level mvar only when it isn't.
                              Ts  (try (zonk est (infer-with-mvars est T')) (catch Exception _ nil))
                              u   (if (and Ts (e/sort? Ts) (lvl/succ? (e/sort-level Ts)))
                                    (lvl/succ-pred (e/sort-level Ts))
                                    (fresh-level-mvar! est))
                              inst (fresh-mvar! est (e/app (e/const' (name/from-string icn) [u]) T')
                                                 {:kind :synthetic :inst-implicit? true})
                              _ (mark-inst-implicit! est inst)]
                          (e/app* (e/const' (name/from-string cn) [u]) T' inst a' b'))

        ;; (= T a b) → Eq T a b (the theorem-statement equality form)
            "="
            ;; `=` is an alias for `==`: 2-arg `(= a b)` is the ordinary Clojure equality (a Bool
            ;; decision, type-directed on the operands — the most common filter); 4-arg `(= T a b)`
            ;; is the Prop `Eq` (for a/theorem goals). Both route through the `==` handler below.
            (elab-term est (cons '== (rest sexpr)))

        ;; Surface comparison glyphs: 3-arg → Prop (le/lt), 2-arg → Bool (Nat.b*).
            ("<" "==" "<=" ">" ">=" "≤" "≥")
            (let [hs (str head)]
              (if (= 4 (count sexpr))
                (let [[_ T a b] sexpr]
                  (if (= hs "==")
                    (elab-term est (list 'Eq T a b))     ; (== T a b) → Eq T a b (Prop)
                    (let [[a* b*] (case hs (">" ">=" "≥") [b a] [a b])
                          rel (case hs ("<" ">") "lt" "le")]
                      (elab-term est (list (symbol rel) T a* b*)))))
                ;; 2-arg Bool comparison, TYPE-DIRECTED on the operands (a non-literal
                ;; operand's type head picks the ops; literals coerce to that type):
                ;; Nat → Nat.b* · Int/Float → Decidable.decide over the order Props ·
                ;; String → decide over String.decEq (== only).
                (let [[rel a-form b-form] (case hs
                                            "<"  [:lt (nth sexpr 1) (nth sexpr 2)]
                                            "==" [:eq (nth sexpr 1) (nth sexpr 2)]
                                            ("<=" "≤") [:le (nth sexpr 1) (nth sexpr 2)]
                                            (">") [:lt (nth sexpr 2) (nth sexpr 1)]
                                            (">=" "≥") [:le (nth sexpr 2) (nth sexpr 1)])
                      a0 (elab-term est a-form)
                      b0 (elab-term est b-form)
                      tn (or (some (fn [x]
                                     (when-not (e/lit-nat? x)
                                       (let [t (zonk est (infer-with-mvars est x))
                                             [th _] (when t (e/get-app-fn-args t))]
                                         (when (and th (e/const? th))
                                           (name/->string (e/const-name th))))))
                                   [a0 b0])
                             "Nat")
                      coerce (fn [x] (if (e/lit-nat? x)
                                       (case tn
                                         "Int"   (e/app (e/const' (name/from-string "Int.ofNat") []) x)
                                         "Float" (e/app (e/const' (name/from-string "Float.ofNat") []) x)
                                         x)
                                       x))
                      a (coerce a0) b (coerce b0)
                      Tc (e/const' (name/from-string tn) [])
                      bool-op (fn [op] (e/app* (e/const' (name/from-string op) []) a b))
                      decide (fn [propc decc]
                               (e/app* (e/const' (name/from-string "Decidable.decide") [])
                                       (e/app* (e/const' (name/from-string propc) []) a b)
                                       (e/app* (e/const' (name/from-string decc) []) a b)))
                      decide-eq (fn []
                                  (e/app* (e/const' (name/from-string "Decidable.decide") [])
                                          (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) Tc a b)
                                          (e/app* (e/const' (name/from-string (str tn ".decEq")) []) a b)))]
                  (if-let [cmp-handler (get @ingest/comparison-registry tn)]
                    ;; type-directed comparison for a registered custom type (e.g. dynamic-EDN
                    ;; Value); pass the PRE-coercion operands — the handler owns unwrapping.
                    (cmp-handler est rel a0 b0)
                    (case tn
                      "Int"   (case rel :lt (decide "Int.lt" "Int.decLt") :le (decide "Int.le" "Int.decLe") :eq (decide-eq))
                      "Float" (case rel :lt (decide "Float.lt" "Float.decLt") :le (decide "Float.le" "Float.decLe") :eq (bool-op "Float.beq"))
                      "String" (case rel :eq (decide-eq)
                                     (elab-error! "String comparison: only == is supported" {:rel rel}))
                      (bool-op (case rel :lt "Nat.blt" :le "Nat.ble" :eq "Nat.beq")))))))

        ;; Dependent if over a Prop condition → dite. The Decidable instance is an
        ;; inst-implicit mvar solved by synthesis (no comparison fallback needed); the
        ;; branch binders (proof of cond / ¬cond) are fvars abstracted back to lambdas.
            "dif" (let [[_ cond-form then-clause else-clause] sexpr
                        [tv tbody] then-clause
                        [ev ebody] else-clause
                        cond-expr (elab-term est cond-form)
                        dec-ty (e/app (e/const' (name/from-string "Decidable") []) cond-expr)
                        inst (fresh-mvar! est dec-ty {:kind :synthetic :inst-implicit? true})
                        _ (mark-inst-implicit! est inst)
                        mk-branch (fn [bv bty body]
                                    (let [fid (fresh-id! est)
                                          est' (-> est
                                                   (assoc-in [:scope bv] {:fvar-id fid :type bty})
                                                   (update :tc update :lctx red/lctx-add-local fid (str bv) bty))
                                          be (elab-term est' body)]
                                      [(e/lam (str bv) bty (e/abstract1 be fid) :default)
                                       (infer-with-mvars est' be)]))
                        [then-fn ret-type] (mk-branch tv cond-expr tbody)
                        not-cond (e/app (e/const' (name/from-string "Not") []) cond-expr)
                        [else-fn _] (mk-branch ev not-cond ebody)
                        ret-sort (infer-with-mvars est ret-type)
                        u (if (e/sort? ret-sort) (e/sort-level ret-sort) (lvl/succ lvl/zero))]
                    (e/app* (e/const' (name/from-string "dite") [u])
                            ret-type cond-expr inst then-fn else-fn))

        ;; Type-directed arithmetic: infer the first operand's type head and pick the matching
        ;; kernel op from the core-lift table (Nat.add / Int.add / …), defaulting to Nat when
        ;; the head isn't listed. Picking the concrete op avoids HAdd's output-param synthesis.
            ("+" "-" "*")
            (let [op (str head)]
              (if (>= (count sexpr) 3)
                (let [a*    (elab-term est (nth sexpr 1))
                      tn    (type-head-name est (infer-with-mvars est a*))
                      const (or (get-in ingest/arith-lift [op tn])
                                (get-in ingest/arith-lift [op "Nat"]))]
                  (elab-app est (symbol const) (rest sexpr)))
                (elab-app est (symbol (get-in ingest/arith-lift [op "Nat"])) (rest sexpr))))

        ;; do → value of the last form (pure setting: earlier forms have no effect).
            "do" (elab-term est (last sexpr))

        ;; (sizeOf x) → SizeOf.sizeOf T inst x — the WF measure for data-typed params.
        ;; The argument's type is INFERRED (fvar scope carries it); the instance is
        ;; synthesized structurally (Nat, List of sized, derived custom instances).
            "sizeOf"
            (let [x* (elab-term est (nth sexpr 1))
                  ty (zonk est (infer-with-mvars est x*))
                  inst (sizeof-inst (:env est) ty)]
              (when-not inst
                (elab-error! (str "sizeOf: no SizeOf instance for type " (e/->string ty)) {:form sexpr}))
              (e/app* (e/const' (name/from-string "SizeOf.sizeOf") [(lvl/succ lvl/zero)]) ty inst x*))

        ;; Clojure loop/recur — the common counting-loop shape compiles to Nat.rec (see elab-loop).
            "loop" (elab-loop est (second sexpr) (last sexpr))

        ;; Clojure fn* (single arity) → lambda. parse-params reads the binders' metadata
        ;; types (^Nat / ^{:- T}); flatten to a [name type …] vec and reuse elab-lam.
            ;; "fn" handled natively (NOT clojure-macroexpanded): typed binders
            ;; ([x :- T] / [x T] / metadata) violate clojure.core/fn's spec
            ("fn" "fn*") (let [cls (rest sexpr)
                               cls (if (symbol? (first cls)) (rest cls) cls)  ; skip optional self-name
                               arities (if (vector? (first cls))
                                         [cls]   ; unwrapped surface (fn [params] body)
                                         (filter #(and (sequential? %) (vector? (first %))) cls))]
                           (when (not= 1 (count arities))
                             (elab-error! "fn: only single-arity lambdas elaborate to kernel terms" {:form sexpr}))
                           (let [[params & body] (first arities)
                                 body-form (if (> (count body) 1) (cons 'do body) (first body))
                                 pairs (ingest/parse-params params)
                                 binder-vec (vec (mapcat (fn [p] [(first p) (second p)]) pairs))]
                             (elab-lam est binder-vec body-form)))

        ;; cond is NOT macroexpanded (Clojure's :else isn't Bool); desugar natively to
        ;; nested if, with :else/:default/true as the catch-all.
            "cond" (letfn [(build [cs]
                             (if (empty? cs)
                               (elab-error! "cond: no clause matched and no :else" {:form sexpr})
                               (let [[t e & more] cs]
                                 (if (contains? #{:else :default true} t)
                                   (elab-term est e)
                                   (e/app* (e/const' (name/from-string "Bool.rec") [(lvl/succ lvl/zero)])
                                           (e/lam "_" (e/const' (name/from-string "Bool") [])
                                                  (infer-with-mvars est (elab-term est e)) :default)
                                           (build more) (elab-term est e) (elab-term est t))))))]
                     (build (rest sexpr)))

        ;; `bif` — Lean's boolean-`if` notation, the escape to the `cond` CONSTANT
        ;; (cond.{u} {α : Type u} (c : Bool) (a b : α) : α). The surface `cond` is overloaded as
        ;; Clojure-style clause-cond (above), so a lemma statement that needs the literal `cond`
        ;; head — e.g. to state `lookup_insert : … = cond (k==k') (some v) (lookup k l)` so that
        ;; `cond_true`/`cond_false` fire by name — spells it `(bif c a b)`. α + the level are
        ;; inferred from `a` (mirrors Lean's `bif` elaborating the implicit motive).
            "bif" (let [[_ c-form a-form b-form] sexpr
                        c (elab-term est c-form)
                        a (elab-term est a-form)
                        b (elab-term est b-form)
                        ;; cond.{u} : {α : Sort u} → Bool → α → α → α. α (implicit, but passed
                        ;; positionally here) = type of `a`; the level param u = the level of α's
                        ;; OWN type (type-of(Option Nat) = Sort 1 ⟹ u = 1), i.e. sort-level of α's type.
                        α (infer-with-mvars est a)
                        αsort (whnf-with-mvars est (infer-with-mvars est α))
                        u (if (e/sort? αsort) (e/sort-level αsort) lvl/zero)]
                    (e/app* (e/const' (name/from-string "cond") [u]) α c a b))

        ;; Clojure let* : [name val name val …] with inferred types → nested let.
            "let*" (let [[_ bindings & body] sexpr]
                     (letfn [(build [ps est]
                               (if (empty? ps)
                                 (elab-term est (if (= 1 (count body)) (first body) (cons 'do body)))
                                 (let [[nm vform] (first ps)
                                       vexpr (elab-term est vform)
                                       vtype (infer-with-mvars est vexpr)
                                       fid (fresh-id! est)
                                       est' (-> est
                                                (assoc-in [:scope nm] {:fvar-id fid :type vtype})
                                                (update :tc update :lctx
                                                        red/lctx-add-let fid (str nm) vtype vexpr))
                                       body-expr (build (rest ps) est')]
                                   (e/let' (str nm) vtype vexpr (e/abstract1 body-expr fid)))))]
                       (build (partition 2 bindings) est)))

        ;; Default: keyword projection / get / cons sugar, then macroexpand any
        ;; clojure macro (cond/->/and/or/…), otherwise application.
            (cond
          ;; (:malli/schema <form>) — a schema marker from the gradual-typing surface
          ;; (ansatz.malli signature-for): translate to the kernel type. requiring-resolve
          ;; is the optionality seam; the marker only ever appears when malli produced it.
              (= :malli/schema head)
              ((requiring-resolve 'ansatz.malli/schema->type-expr) (second sexpr))
          ;; (:field struct) → structure projection
              (keyword? head)
              (let [field-name (name head)
                    struct-expr (elab-term est (second sexpr))
                    struct-type (whnf-with-mvars est (infer-with-mvars est struct-expr))
                    [th _] (e/get-app-fn-args struct-type)
                    tn (when (e/const? th) (name/->string (e/const-name th)))
                    reg (deref ingest/structure-registry)
                    sinfo (get reg tn)
                    fidx (when sinfo (first (keep-indexed (fn [i f] (when (= f field-name) i))
                                                          (:fields sinfo))))]
                (cond
                  fidx (e/proj (name/from-string tn) fidx struct-expr)
                  ;; non-structure receiver: type-directed keyword access via the
                  ;; extension registry (e.g. dynamic-EDN Value → vget)
                  (get @ingest/keyword-access-registry tn)
                  ((get @ingest/keyword-access-registry tn) est head struct-expr)
                  :else (elab-error! (str "Unknown structure field: :" field-name
                                          (when tn (str " (receiver type " tn
                                                        " is not a registered structure and has"
                                                        " no keyword-access handler)")))
                                     {:field field-name :type tn})))
          ;; (get struct :field) → (:field struct)
              (= (str head) "get") (elab-term est (list (nth sexpr 2) (nth sexpr 1)))
          ;; (cons x xs) → List.cons sugar (element type inferred)
              (= (str head) "cons") (elab-app est (symbol "List.cons") (rest sexpr))
          ;; (case x k1 v1 … default) → a bound scrutinee + nested type-directed ==
          ;; chain. Intercepted BEFORE clojure's macroexpansion: case* is a jump-table
          ;; encoding we never want to elaborate. A default is REQUIRED (totality).
              (= (str head) "case")
              (let [[_ scrut & clauses] sexpr]
                (when (even? (count clauses))
                  (elab-error! "case in a verified body requires a default branch (odd clause count)"
                               {:form sexpr}))
                (let [g (gensym "case")
                      default (last clauses)
                      pairs (partition 2 (butlast clauses))]
                  (elab-term est
                             (list 'let [g scrut]
                                   (reduce (fn [acc [k v]] (list 'if (list '== g k) v acc))
                                           default (reverse pairs))))))
              (and (symbol? head) (ingest/expand-macro? head))
              (elab-term est (macroexpand-1 sexpr))
              :else (elab-app est (first sexpr) (rest sexpr)))))))

    ;; vector literal = List literal: [a b c] → (cons a (cons b (cons c nil))).
    ;; Generalizes the bare-nil = List.nil rule above; the element type is
    ;; inferred through List.cons as usual ([] elaborates as List.nil ?α).
    (vector? sexpr)
    (elab-term est (reduce (fn [acc x] (list 'cons x acc)) nil (rseq sexpr)))

    :else
    (elab-error! (str "Unsupported form: " (pr-str sexpr)) {:form sexpr})))

;; ============================================================
;; Instance synthesis for unsolved inst-implicit metavariables
;; ============================================================

(defn- has-unsolved-mvar?
  "True if (zonked) expr still contains an unsolved elaboration mvar."
  [est expr]
  (let [mctx @(:meta-mctx est)
        legacy @(:mctx est)]
    (letfn [(unsolved? [id]
              (if (meta/expr-decl mctx id)
                (not (meta/expr-assigned-or-delayed? mctx id))
                (let [m (get legacy id)]
                  (and m (nil? (:solution m))))))
            (go [x]
                (when (instance? ansatz.kernel.Expr x)
                  (case (e/tag x)
                    :mvar (unsolved? (e/mvar-id x))
                    :fvar (unsolved? (e/fvar-id x))
                    :app (or (go (e/app-fn x)) (go (e/app-arg x)))
                    :lam (or (go (e/lam-type x)) (go (e/lam-body x)))
                    :forall (or (go (e/forall-type x)) (go (e/forall-body x)))
                    :let (or (go (e/let-type x)) (go (e/let-value x)) (go (e/let-body x)))
                    :proj (go (e/proj-struct x))
                    false)))]
      (boolean (go expr)))))

(defn- solve-instance-mvars!
  "Solve unsolved instance-implicit metavariables via the instance-synthesis
   engine (using the elaboration's fvar context, so goals mentioning local
   binders resolve). Loops to a fixpoint: solving one inst may determine another."
  [est]
  (let [synth* (requiring-resolve 'ansatz.tactic.instance/synthesize*)
        build-idx (requiring-resolve 'ansatz.tactic.instance/build-instance-index)
        index (build-idx (:env est))]
    (loop []
      (let [mctx @(:meta-mctx est)
            legacy @(:mctx est)
            pending (->> (:decls mctx)
                         (filter (fn [[id decl]]
                                   (and (or (:inst-implicit? decl)
                                            (get-in legacy [id :inst-implicit]))
                                        (not (meta/expr-assigned-or-delayed? mctx id)))))
                         (sort-by first)
                         vec)
            solved-any (atom false)]
        (doseq [[id _] pending]
          (let [goal (zonk est (surface-mvar-type est id))]
            ;; Only synthesize once the goal is fully determined (no unsolved mvars),
            ;; else we'd resolve against an under-specified class.
            (when-not (has-unsolved-mvar? est goal)
              (when-let [sol (try (synth* (:tc est) (:env est) index goal 0)
                                  (catch Throwable _ nil))]
                (solve-mvar! est id sol)
                ;; Unify the instance's concrete type with the goal so universe
                ;; levels shared with the class head (e.g. LE.le.{?u}) get solved
                ;; (solve-mvar! only propagates levels when both sides are Sorts).
                (try (unify! est (infer-with-mvars est sol) goal)
                     (catch Throwable _ nil))
                (reset! solved-any true)))))
        (when @solved-any (recur))))))

;; ============================================================
;; Public API
;; ============================================================

;; ── Extension-author API (the stable surface behind ansatz.surface.api) ─────────────────
;; Term elaborators (ingest/term-elaborator-registry) receive the live elaboration state
;; `est` and use these — never elaborator internals.

(defn elab-subterm
  "Elaborate a surface form to a kernel Expr inside a term elaborator. The result may
   contain unsolved metavariable fvars; they resolve when the enclosing elaboration zonks."
  [est form]
  (elab-term est form))

(defn elab-base
  "Elaborate `form` with the user registries bypassed for ITS OWN head dispatch only
   (sub-forms dispatch normally) — the delegation primitive for elaborators that WRAP a
   built-in form (e.g. a narrowing `if`)."
  [est form]
  (binding [*bypass-registries-once* true]
    (elab-term est form)))

(defn with-local
  "Run `(f est' fvar-id)` with `sym` bound to a FRESH local of kernel type `ty` in the
   elaboration scope (and the typechecker lctx) — the primitive for NARROWING elaborators
   that rebind a variable at a refined type for one branch (e.g. Option unwrapping).
   Shadows any existing binding of `sym` for the dynamic extent of `f`."
  [est sym ty f]
  (let [fid (fresh-id! est)
        est' (-> est
                 (assoc-in [:scope (symbol sym)] {:fvar-id fid :type ty})
                 (update :tc update :lctx red/lctx-add-local fid (str sym) ty))]
    (f est' fid)))

(defn subterm-type
  "The (whnf'd, zonked) TYPE of an elaborated subterm — for type-directed dispatch
   (e.g. count → vsize / Map.size / List.length depending on the collection type)."
  [est expr]
  (whnf-with-mvars est (infer-with-mvars est expr)))

(defn subterm-whnf
  "whnf a kernel type/term in the elaboration's typechecker context."
  [est expr]
  (whnf-with-mvars est expr))

(defn- attach-elab-lctx
  "Populate an elaboration state with a proof/local context."
  [est lctx]
  (reduce (fn [est [id decl]]
            (if-let [n (:name decl)]
              (let [sym (symbol n)]
                (-> est
                    (assoc-in [:scope sym]
                              (cond-> {:fvar-id id :type (:type decl)}
                                (:as-term decl) (assoc :as-term (:as-term decl))))
                    (update :tc update :lctx
                            red/lctx-add-local id n (:type decl))))
              est))
          est
          lctx))

(defn- check-expected!
  [est expr expected]
  (when expected
    (let [inferred (infer-with-mvars est expr)]
      (when-not (unify! est inferred expected)
        (elab-error! "Type mismatch"
                     {:expected expected :inferred inferred})))))

(defn- finalize-elaboration
  [mode est expr]
  (case mode
    :strict (strict-finalize est expr)
    :collecting (collecting-finalize est expr)))

(defn- elaborate*
  ([mode env lctx sexpr expected]
   (elaborate* mode env lctx sexpr expected {}))
  ([mode env lctx sexpr expected opts]
   (let [est (cond-> (mk-elab-state env opts)
               lctx (attach-elab-lctx lctx))
         expr (elab-term est sexpr)]
     (check-expected! est expr expected)
     (finalize-elaboration mode est expr))))

(defn elaborate
  "Elaborate an s-expression into a fully explicit Ansatz Expr.

   Resolves names, inserts implicit arguments as metavariables,
   infers universe levels, and zonks (substitutes solutions).

   Args:
     env         - kernel Env
     sexpr       - Clojure s-expression (quoted)
     expected    - optional expected type (for bidirectional checking)

   Returns the elaborated Expr.

   Examples:
     (elaborate env '(forall [a Nat] (Eq a a)))
     ;; Inserts implicit type arg for Eq, infers universe level
     ;; => fully explicit Ansatz term with no unsolved metavars

     (elaborate env 'Nat)
     ;; => (const Nat [])"
  ([env sexpr]
   (elaborate env sexpr nil))
  ([env sexpr expected]
   (elaborate* :strict env nil sexpr expected)))

(defn elaborate-collecting
  "Elaborate like `elaborate`, but return unsolved holes instead of failing.

   Returns:
     {:expr Expr-with-real-mvars
      :meta-mctx MetavarContext
      :holes [{:id :expr :type :inst-implicit?}]
      :level-holes [{:id :level :name}]}"
  ([env sexpr]
   (elaborate-collecting env sexpr nil))
  ([env sexpr expected]
   (elaborate-collecting env sexpr expected {}))
  ([env sexpr expected opts]
   (elaborate* :collecting env nil sexpr expected opts)))

(defn elaborate-in-context
  "Elaborate an s-expression with a local context from a proof state.
   Local hypotheses are available as symbols.

   lctx is a map {fvar-id → {:name str :type Expr :tag :local/:let ...}}.
   The hypothesis names become available as symbols in the surface syntax.

   Example:
     ;; Inside a proof with hypothesis 'a : Nat' (fvar-id 42):
     (elaborate-in-context env lctx '(Eq a a))
     ;; => (Eq.{1} Nat (fvar 42) (fvar 42))"
  ([env lctx sexpr]
   (elaborate-in-context env lctx sexpr nil))
  ([env lctx sexpr expected]
   (elaborate* :strict env lctx sexpr expected)))

(defn elaborate-in-context-collecting
  "Contextual variant of `elaborate-collecting`."
  ([env lctx sexpr]
   (elaborate-in-context-collecting env lctx sexpr nil))
  ([env lctx sexpr expected]
   (elaborate-in-context-collecting env lctx sexpr expected {}))
  ([env lctx sexpr expected opts]
   (elaborate* :collecting env lctx sexpr expected opts)))

(defn elaborate-check
  "Elaborate and verify: elaborate the s-expression, then verify the result
   type-checks via the kernel type checker."
  ([env sexpr]
   (let [result (elaborate env sexpr)
         st (tc/mk-tc-state env)]
     (tc/infer-type st result)  ;; will throw on type error
     result))
  ([env sexpr expected]
   (let [result (elaborate env sexpr expected)
         st (tc/mk-tc-state env)
         inferred (tc/infer-type st result)]
     (when expected
       (when-not (tc/is-def-eq st inferred expected)
         (elab-error! "Elaborated term doesn't match expected type"
                      {:expected expected :inferred inferred})))
     result)))
