(ns ansatz.tactic.grind.split
  "Lean Grind/Split.lean checkDefaultSplitStatus/checkForallStatus/splitCore and
   Grind/Cases.lean cases/generalizeIndices', checkout v4.33.1."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.grind.action :as action]
            [ansatz.tactic.grind.egraph :as eg]
            [ansatz.tactic.grind.theorem :as theorem]
            [ansatz.tactic.grind.proof :as gp]))

(defn- c [n] (e/const' (name/from-string n) []))
(defn- whnf [st x] (#'tc/cached-whnf st x))
(defn- wrap [decls body]
  (reduce (fn [body [id type]] (e/lam "x" type (e/abstract1 body id) :default))
          body (reverse decls)))
(defn- local [branch type]
  (let [[ps id] (proof/alloc-id (:ps branch))
        st (tc/attach-lctx (tc/mk-tc-state (:env ps))
                           (red/lctx-add-local (:lctx (:tc branch)) id (str "split_" id) type))]
    [(assoc branch :ps ps :tc st) id]))
(defn- eq [st a b]
  (let [type (tc/infer-type st a) sort (whnf st (tc/infer-type st type))]
    (e/app* (e/const' (name/from-string "Eq") [(e/sort-level sort)]) type a b)))

(defn is-inductive-predicate? [st expr]
  (let [[head _] (e/get-app-fn-args expr)]
    (when (and (e/const? head)
               (not (contains? #{"Eq" "HEq" "True" "False" "And" "Or" "Exists"}
                               (name/->string (e/const-name head)))))
      (when-let [ci (env/lookup (:env st) (e/const-name head))]
        (when (and (= :induct (env/ci-tag ci)) (theorem/prop? st expr)) ci)))))

(defn- arithmetic-predicate? [info]
  ;; Nat.le is the built-in inductive arithmetic relation. It is owned by
  ;; arithmetic normalization/solvers, not the surface's implicit cases/intro
  ;; attributes for ordinary predicates (Internalize.checkAndAddSplitCandidate,
  ;; Init/Grind/Config.lean splitIndPred=false).
  (= "Nat.le" (name/->string (.name info))))

(defn- congr-to-prev-split? [branch expr]
  ;; Split.isCongrToPrevSplit compares application signatures, not truth classes:
  ;; every true proposition shares True, but can still require a separate split.
  (let [[head args] (e/get-app-fn-args expr)]
    (some (fn [prev]
            (let [[ph pa] (e/get-app-fn-args prev)]
              (and (= head ph) (= (count args) (count pa))
                   (every? true? (map #(eg/is-eqv (:graph branch) %1 %2) args pa)))))
          (:resolved branch))))

(defn check-default-split-status [branch truth]
  (some (fn [[expr node]]
          (when (and (not (contains? (:resolved branch) expr))
                     (not (congr-to-prev-split? branch expr))
                     (:yes (truth branch expr)))
            (when-let [ci (is-inductive-predicate? (:tc branch) expr)]
              (when (or (get-in branch [:config :split-ind-pred]) (not (arithmetic-predicate? ci)))
                {:kind :inductive :expr expr :proof (:yes (truth branch expr))
                 :info ci :gen (:gen node)}))))
        (get-in branch [:graph :enodes])))

(defn check-forall-status [branch truth]
  (some (fn [[p {:keys [gen]}]]
          (when (and (e/forall? p) (theorem/prop? (:tc branch) (e/forall-type p))
                     (not (contains? (:resolved branch) p))
                     (not (truth branch (e/forall-type p)))
                     (or (pos? (e/bvar-range (e/forall-body p)))
                         (not (truth branch (e/forall-body p)))))
            {:kind :imp :expr p :args [(e/forall-type p)] :gen gen})) (:facts branch)))

(defn activate-intro-theorems [branch]
  ;; Attr.lean's `intro` expands an inductive predicate into constructor rules.
  ;; The executable surface has no grind attribute command yet: activate these
  ;; checked rules by encountered predicate symbol, uniformly in goals and facts.
  ;; Match conclusions, avoiding unbounded forward construction of indices.
  (reduce (fn [branch [expr _]]
            (if-let [ci (is-inductive-predicate? (:tc branch) expr)]
              (let [nm (.name ci)]
                (if (or (arithmetic-predicate? ci) (contains? (:intro-theorems-active branch) nm)) branch
                    (-> branch (update :intro-theorems-active (fnil conj #{}) nm)
                        (update :theorems into
                                (keep #(theorem/mk-ematch-intro-theorem? (:tc branch) %) (.ctors ci)))))) branch))
          branch (get-in branch [:graph :enodes])))

(defn split-core
  "Eliminate a true predicate, generalizing indices with equalities. Graph terms
   are never substituted. Recursive recursor IHs are bound but deliberately ignored
   when an indexed casesOn wrapper is absent from the executable environment."
  [branch {:keys [expr proof info gen]} solve]
  (action/budget! (:config branch) :splits (:num-splits branch))
  (let [[head args] (e/get-app-fn-args expr)
        params (take (.numParams info) args) indices (vec (drop (.numParams info) args))
        env (:env (:tc branch))
        ;; Source-defined indexed predicates currently export rec but no casesOn.
        ;; Use its checked minors, ignoring IHs, to implement the same elimination.
        cases-name (name/mk-str (.name info) "casesOn")
        cases-ci (env/lookup env cases-name)
        rec-name (if cases-ci cases-name (name/mk-str (.name info) "rec"))
        rec-ci (env/lookup env rec-name)
        _ (when-not rec-ci (action/fail! "inductive predicate recursor unavailable" {:predicate expr}))
        levels (zipmap (.levelParams info) (e/const-levels head))
        rec (e/const' rec-name (mapv #(get levels % lvl/zero) (.levelParams rec-ci)))
        ind-type (reduce (fn [t p] (e/instantiate1 (e/forall-body t) p))
                         (e/instantiate-level-params (.type info) levels) params)
        [branch index-decls index-vars]
        (loop [b branch t ind-type decls [] vars []]
          (if (e/forall? t)
            (let [d (e/forall-type t) [b id] (local b d)]
              (recur b (e/instantiate1 (e/forall-body t) (e/fvar id))
                     (conj decls [id d]) (conj vars (e/fvar id)))) [b decls vars]))
        major-type (reduce e/app head (concat params index-vars))
        [branch major-id] (local branch major-type)
        equations (mapv #(eq (:tc branch) %1 %2) index-vars indices)
        motive (wrap (conj index-decls [major-id major-type])
                     (e/mk-arrows equations (c "False")))
        ;; Temporary motive locals have been abstracted; discard their context.
        branch (assoc branch :tc (tc/attach-lctx (tc/mk-tc-state env)
                                                 (apply dissoc (:lctx (:tc branch))
                                                        (conj (mapv first index-decls) major-id))))
        branch (-> branch (update :resolved conj expr) (assoc :rounds 0))
        rec (reduce e/app rec (concat params [motive]))
        ;; casesOn orders indices/major before minors; rec orders minors first.
        rec (if cases-ci (reduce e/app rec (concat indices [proof])) rec)
        ctors (vec (.ctors info))
        num-cases (count ctors)
        recursive? (.isRec info)
        gen-new (if (or (> num-cases 1) recursive?) (inc gen) gen)
        rec (reduce
             (fn [rec [i ctor]]
               (let [type (whnf (:tc branch) (tc/infer-type (:tc branch) rec))
                     minor-type (e/forall-type type)
                     field-count (.numFields (env/lookup env ctor))
                     b (update branch :num-splits + (if (or (pos? i) recursive?) 1 0))
                     ;; First open constructor fields, without reducing the motive.
                     [b t decls fields]
                     (loop [b b t minor-type ds [] fs [] j 0]
                       (if (< j field-count)
                         (let [d (e/forall-type t) [b id] (local b d)
                               fv (e/fvar id)
                               b (if (theorem/prop? (:tc b) d)
                                   (update b :raw-facts conj {:prop d :proof fv :gen gen-new}) b)]
                           (recur b (e/instantiate1 (e/forall-body t) fv)
                                  (conj ds [id d]) (conj fs fv) (inc j))) [b t ds fs]))
                     ;; The raw recursor adds IH binders before the motive app.
                     [b t decls]
                     (loop [b b t t ds decls]
                       (if (and (not cases-ci) (e/forall? t))
                         (let [d (e/forall-type t) [b id] (local b d)]
                           (recur b (e/instantiate1 (e/forall-body t) (e/fvar id)) (conj ds [id d])))
                         [b t ds]))
                     ctor-proof (reduce e/app (e/const' ctor (e/const-levels head)) (concat params fields))
                     b (update b :raw-facts conj {:prop (tc/infer-type (:tc b) ctor-proof)
                                                  :proof ctor-proof :gen gen-new})
                     ;; Generalized index equations become ordinary branch facts.
                     [b decls]
                     (loop [b b t (whnf (:tc b) t) ds decls]
                       (if (e/forall? t)
                         (let [d (e/forall-type t) [b id] (local b d)]
                           (recur (update b :raw-facts conj {:prop d :proof (e/fvar id) :gen gen-new})
                                  (whnf (:tc b) (e/instantiate1 (e/forall-body t) (e/fvar id)))
                                  (conj ds [id d])))
                         (do (when-not (= t (c "False"))
                               (action/fail! "unexpected predicate case target" {:target t})) [b ds])))
                     minor (wrap decls (solve b))]
                 (e/app rec minor))) rec (map-indexed vector ctors))
        rec (if cases-ci rec (reduce e/app rec (concat indices [proof])))]
    (reduce e/app rec (map #(gp/mk-eq-refl (:tc branch) %) indices))))
