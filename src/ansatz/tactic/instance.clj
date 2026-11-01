;; Follows Lean 4 (../lean4, checkout 55f80e10a3; behaviour checked against Lean 4.33.1):
;; Meta/SynthInstance.lean (tabled resolution, synthInstance?, synthPendingImp),
;; Meta/Instances.lean (instanceExtension, addInstance), Class.lean (out-params).

(ns ansatz.tactic.instance
  "Typeclass instance synthesis: a port of Lean 4's tabled resolution (Meta/SynthInstance.lean).

   - Candidates come from Lean's instance discrimination tree (`ansatz.tactic.instance-index`):
     `getUnify` on the goal, sorted by priority, local instances appended (tried first, newest
     first), consumed from the end.
   - `tryResolve` opens the goal's telescope, opens the candidate with metavariables
     (`getSubgoals`, each `?m : ∀ xs, A` applied to the goal's binders), unifies the conclusions
     (`ansatz.meta/is-def-eq` with synthPending and `isDefEqStuckEx`), and assigns the goal
     `fun xs => inst ?m…`. The instance-implicit binders are subgoals in the instance's
     precomputed synthesis order (`computeSynthOrder`).
   - Goals are tabled under normalized keys (`mkTableKey`: assignable metavariables become
     canonical names): a generator node per new goal, consumer nodes waiting on subgoals, answers
     abstracted over their metavariables (`abstractMVars`) and propagated to every waiter,
     `removeUnusedArguments?`, the canonical-instances cut, and Lean's result-size bound.
   - `synthInstance?`: out-params (and out-level-params) of the goal are replaced by fresh
     metavariables, the search runs one metacontext depth deeper, and the FIRST root answer is
     checked against the original goal (`assignOutParams`); results are cached per local-instance
     context, goal, synthPending depth, environment and registry.

   Unification inside the search runs at `.instances` transparency (`meta/*transparency*`),
   `assignOutParams` at default, as in Lean.

   Deviations: the resource bound counts resolution steps (`config/*synth-max-steps*`) where Lean
   counts heartbeats; metavariable-free comparisons go to the kernel, which unfolds at default
   transparency; Lean's reducibility attributes and class extension are not exported, so
   reducibility and class membership are recovered as `ansatz.meta/reducible-const?` and
   `ansatz.tactic.instance-index/mk-ctx` describe."
  (:require [ansatz.bundle :as bundle]
            [clojure.string :as str]
            [clojure.java.io :as io]
            [ansatz.meta :as meta]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.config :as config]
            [ansatz.tactic.instance-index :as ii])
  (:import [ansatz.kernel ConstantInfo Env]))

;; ============================================================
;; The registry: Lean's instanceExtension, class → entries
;; ============================================================
;; An entry is {:name Name :priority Nat :order n}, `:order` being the registration order (the
;; dump's line, Lean's DiscrTree insertion order). Within a class the entries are kept in Lean's
;; try order among equal keys: higher priority first, the most recent registration first among
;; equals. A store may add `:keys`/`:synth-order` (ansatz.tactic.instance-index/annotate-registry).

(defn- return-type-head
  "Strip foralls from a type to get the return type, then return its head constant name."
  [ty]
  (loop [t ty]
    (if (e/forall? t)
      (recur (e/forall-body t))
      (let [[head _] (e/get-app-fn-args t)]
        (when (e/const? head) (e/const-name head))))))

(defn- try-order
  "Lean's try order among entries of one class: priority descending, newest registration first."
  [entries]
  (vec (sort-by (juxt #(- (or (:priority %) 1000)) #(- (or (:order %) 0))) entries)))

(defn add-instance
  "Lean's `addInstance`: a NEW env whose instance table (the `:instances` extension) also
   holds the constant `inst-name`, keyed by the class its type concludes in, at `priority`
   (Lean's default 1000). A new registration is the most recent one; registering an instance
   again replaces its entry IN PLACE with the new priority (Lean's `insertVal`), so it keeps its
   registration order. An env with no registry starts with the empty table, as Lean's
   instanceExtension does."
  [^Env env inst-name & {:keys [priority] :or {priority 1000}}]
  (let [ci (or (env/lookup env inst-name)
               (throw (ex-info "add-instance: no such constant" {:name (name/->string inst-name)})))
        cls (or (return-type-head (.type ci))
                (throw (ex-info "add-instance: the type does not conclude in a class"
                                {:name (name/->string inst-name)})))
        idx (or (env/get-extension env :instances nil) {})
        next-order (inc (reduce max -1 (keep :order (mapcat val idx))))
        vs (get idx cls [])
        pos (first (keep-indexed (fn [i v] (when (= (:name v) inst-name) i)) vs))
        vs (if pos
             (update vs pos assoc :priority priority)
             (conj vs {:name inst-name :priority priority :order next-order}))]
    (env/with-extension env :instances (assoc idx cls (try-order vs)))))

(defn get-instances
  "The registry entries of a class, in Lean's try order among equal keys."
  [index class-name]
  (get index class-name []))

(defn parse-instance-tsv
  "Lean's @[instance] registry (scripts/dump_instances.lean: `class<TAB>instance<TAB>priority`
   lines, in registration order) → an instance index {class-Name → [{:name :priority :order} …]}.
   Within a class the candidates are in Lean's try order: HIGHER priority first (`instance
   (priority := low)` is tried last), the most recently registered first among equals.
   `present?` (name-string → bool) drops instances the env does not have, so a registry dumped
   from full Init serves a smaller bundled tier."
  ([lines] (parse-instance-tsv lines nil))
  ([lines present?]
   (let [seen (java.util.HashMap.)
         idx (reduce (fn [idx [line-no line]]
                       (let [parts (str/split line #"\t")]
                         (if (and (>= (count parts) 2)
                                  (or (nil? present?) (present? (nth parts 1))))
                           (let [cls (name/from-string (nth parts 0))
                                 prio (if (>= (count parts) 3) (Long/parseLong (nth parts 2)) 1000)
                                 k [(nth parts 0) (nth parts 1)]]
                             (if-let [pos (.get seen k)]
                               ;; an instance registered again (`attribute [instance 50] C.toX` after
                               ;; the structure-parent registration at 1000, or a re-exporting
                               ;; module) is ONE entry: Lean's DiscrTree.insertVal replaces the
                               ;; equal value in place, so it keeps its position and takes the
                               ;; LATER priority
                               (assoc-in idx [cls pos :priority] prio)
                               (do (.put seen k (count (get idx cls [])))
                                   (update idx cls (fnil conj [])
                                           {:name (name/from-string (nth parts 1)) :priority prio
                                            :order line-no}))))
                           idx)))
                     {} (map-indexed vector lines))]
     (into {} (map (fn [[k vs]] [k (try-order vs)])) idx))))

(defn load-instance-tsv
  "Load Lean's instance registry from a TSV file (see parse-instance-tsv)."
  [path]
  (with-open [rdr (io/reader path)]
    (parse-instance-tsv (doall (line-seq rdr)))))

(def ^:private bundled-instances-resource "ansatz/init-instances.tsv.gz")

(defn load-bundled-instances
  "The instance index of the BUNDLED Init registry (resources/ansatz/init-instances.tsv.gz, dumped
   by scripts/regen-bundled-attrs.sh), intersected with the env through `present?` — the zero-config
   `load-init!` tier's counterpart of the store's derived `:instances` blob. Missing or inconsistent resources fail
   before installation."
  [{:keys [present?]}]
  (let [payload (bundle/verified-bytes bundled-instances-resource)]
    (let [lines (with-open [in (java.util.zip.GZIPInputStream. (java.io.ByteArrayInputStream. payload))]
                  (str/split-lines (slurp in)))]
      (parse-instance-tsv lines present?))))

(defn index-for
  "The environment's registered instances (Lean Meta/Instances.lean:getGlobalInstancesIndex).
   An empty registry is valid; a missing registry is an environment setup error."
  [env]
  (or (env/get-extension env :instances nil)
      (throw (ex-info "Tactic error: no instance registry"
                      {:kind :tactic-error}))))

;; ============================================================
;; The discrimination tree of one (env, registry)
;; ============================================================

(deftype IdKey [o]
  Object
  (equals [_ x] (and (instance? IdKey x) (identical? o (.-o ^IdKey x))))
  (hashCode [_] (System/identityHashCode o)))

(def ^:private index-cache
  "{[IdKey env, IdKey registry] → index state}: the instance discrimination tree, entry data and
   class info derived from one registry over one environment. Session state (capture/restore);
   bounded, so a session that keeps extending its env does not retain every one of them."
  (atom {}))

(def ^:private max-index-states 8)

(defn reset-caches!
  "Forget every derived instance index."
  []
  (reset! index-cache {}))

(defn capture-caches
  "Capture the derived instance indexes for a proof session."
  []
  @index-cache)

(defn validate-caches! [snapshot]
  (when-not (map? snapshot)
    (throw (ex-info "Invalid instance cache snapshot" {})))
  snapshot)

(defn restore-caches! [snapshot]
  (reset! index-cache (validate-caches! snapshot)))

(defn- insertion-order
  "The registry's entries in registration (DiscrTree insertion) order: by `:order` when every
   entry has one, else class by class, each class's try order reversed (oldest first)."
  [registry]
  (let [all (for [[cls vs] registry v (rseq (vec vs))] (assoc v ::class cls))]
    (if (every? :order all) (sort-by :order all) all)))

(defn- class-root
  "The root key name of the instances of a non-inductive class `cls`: the head of the key of
   `cls ?args` (Lean reduces reducible aliases such as `DecidableEq` and `AddLeftMono` at the root)."
  [ctx ^ConstantInfo ci]
  (let [st (:st ctx)]
    (loop [t (.type ci) mctx meta/empty-context args []]
      (if (e/forall? t)
        (let [id (swap! (:next-id st) inc)
              mctx (meta/add-expr-mvar-decl mctx id (e/forall-type t) (:lctx st))]
          (recur (e/instantiate1 (e/forall-body t) (e/mvar id)) mctx (conj args (e/mvar id))))
        (let [goal (apply e/app* (e/const' (.name ci) (mapv lvl/param (.levelParams ci))) args)]
          (loop [g goal mctx mctx fuel 32]
            (let [g' (meta/whnf mctx st g)]
              (if (and (e/forall? g') (pos? fuel))
                (let [id (swap! (:next-id st) inc)
                      mctx (meta/add-expr-mvar-decl mctx id (e/forall-type g') (:lctx st))]
                  (recur (e/instantiate1 (e/forall-body g') (e/mvar id)) mctx (dec fuel)))
                (let [k (first (ii/mk-path ctx mctx st g))]
                  (when (= :const (nth k 0)) [:const (nth k 1)]))))))))))

(defn- make-index-state [^Env env registry]
  (let [ctx (ii/mk-ctx env registry)
        ordered (delay (vec (insertion-order registry)))
        unannotated-classes (delay (into #{} (comp (remove ii/annotated?) (map ::class)) @ordered))]
    {:ctx ctx
     :entry-data (atom {})
     :tries (atom {})
     :instance-names (delay (into #{} (map :name) @ordered))
     ;; annotated entries grouped by root key, in insertion order
     :annotated-roots (delay (group-by (comp first :keys)
                                       (filter #(and (ii/annotated? %) (seq (:keys %))) @ordered)))
     ;; the unannotated classes by the root key name their instances key under
     :class-roots (delay
                    (reduce (fn [m cls]
                              (let [ci (env/lookup env cls)]
                                (cond (nil? ci) m
                                      (or (env/induct? ci) (env/axiom? ci)) (update m [:const cls] (fnil conj []) cls)
                                      :else (if-let [k (try (class-root ctx ci) (catch clojure.lang.ExceptionInfo _ nil))]
                                              (update m k (fnil conj []) cls)
                                              m))))
                            {} @unannotated-classes))
     :ordered ordered}))

(defn- with-root-classes [state]
  (assoc state :root-classes
         (delay (into #{} (keep (fn [k] (when (= :const (nth k 0 nil)) (nth k 1))))
                      (concat (keys @(:class-roots state)) (keys @(:annotated-roots state)))))))

(def ^:private fully-annotated
  "registry → does every entry carry its keys and synthesis order? (weak in the registry)"
  (java.util.WeakHashMap.))

(defn- fully-annotated? [registry]
  (locking fully-annotated
    (let [hit (.get ^java.util.WeakHashMap fully-annotated registry)]
      (if (some? hit)
        hit
        (let [r (boolean (and (seq registry) (every? ii/annotated? (mapcat val registry))))]
          (.put ^java.util.WeakHashMap fully-annotated registry r)
          r)))))

(defn- index-state
  "The index state of `registry` over `env`. A fully annotated registry needs nothing from the
   env to build its tree, so its state is shared by every env it is used with (a session's env
   changes with every declaration it adds)."
  [^Env env registry]
  (let [k (if (fully-annotated? registry) [(IdKey. registry)] [(IdKey. env) (IdKey. registry)])]
    (or (get @index-cache k)
        (let [s (with-root-classes (make-index-state env registry))]
          (swap! index-cache (fn [m] (cond (contains? m k) m
                                           (>= (count m) max-index-states) {k s}
                                           :else (assoc m k s))))
          (get @index-cache k s)))))

(defn- entry-data
  "Keys and synthesis order of a registry entry: persisted, or computed once per index."
  [state entry]
  (if (ii/annotated? entry)
    entry
    (let [n (:name entry)]
      (or (get @(:entry-data state) n)
          (let [d (or (try (ii/entry-data (:ctx state) n) (catch clojure.lang.ExceptionInfo _ nil))
                      {:keys nil :synth-order nil})]
            (swap! (:entry-data state) assoc n d)
            d)))))

(defn- root-trie
  "The trie of instances whose key path starts with root key `k`."
  [state k]
  (if-let [hit (find @(:tries state) k)]
    (val hit)
    (let [classes (when (= :const (nth k 0)) (get @(:class-roots state) [:const (nth k 1)]))
          unannotated (when (seq classes)
                        (let [wanted (set classes)]
                          (filter #(and (wanted (::class %)) (not (ii/annotated? %))) @(:ordered state))))
          annotated (get @(:annotated-roots state) k)
          entries (let [es (concat annotated unannotated)]
                    (if (every? :order es) (sort-by :order es) es))
          roots (reduce (fn [roots en]
                          (let [{:keys [keys synth-order]} (entry-data state en)]
                            (if (= k (first keys))
                              (ii/trie-insert roots keys {:name (:name en) :priority (or (:priority en) 1000)
                                                          :synth-order synth-order})
                              roots)))
                        {} entries)
          t (get roots k)]
      (swap! (:tries state) assoc k t)
      t)))

;; ============================================================
;; Telescopes, binders, classes
;; ============================================================

(defn- whnf-i
  "whnf at Lean's `.instances` transparency (TC resolution's setting)."
  [ctx mctx st x]
  (meta/whnf-at mctx st x :instances (:instance-name? ctx)))

(defn- add-local [st fid nm type bi]
  (assoc st :lctx (assoc (:lctx st) fid {:tag :local :id fid :name nm :type type :binder-info bi})))

(defn- forall-telescope
  "Lean's `forallTelescope`/`forallTelescopeReducing` (at `.instances`): [st' fvar-ids body]."
  [ctx mctx st ty reducing?]
  (loop [t ty st st ids []]
    (let [t (meta/zonk-expr mctx t)]
      (if (e/forall? t)
        (let [fid (swap! (:next-id st) inc)]
          (recur (e/instantiate1 (e/forall-body t) (e/fvar fid))
                 (add-local st fid (e/forall-name t) (e/forall-type t) (e/forall-info t))
                 (conj ids fid)))
        (if reducing?
          (let [t' (whnf-i ctx mctx st t)]
            (if (e/forall? t') (recur t' st ids) [st ids t]))
          [st ids t])))))

(defn- mk-binding
  "Lean's `mkForallFVars`/`mkLambdaFVars` over the fvars `xs` of `st` (eta-reducing lambdas)."
  [st xs body lam?]
  (if (empty? xs)
    body
    (let [decls (mapv #(get (:lctx st) %) xs)]
      (reduce (fn [acc i]
                (let [{:keys [name type binder-info]} (nth decls i)
                      type (e/abstract-many type (subvec xs 0 i))]
                  (if lam?
                    (if (and (e/app? acc) (e/bvar? (e/app-arg acc)) (zero? (e/bvar-idx (e/app-arg acc)))
                             (not (#'ii/has-loose-bvar? (e/app-fn acc) 0)))
                      ;; etaReduce: `fun x => f x` ↦ `f`
                      (e/instantiate1 (e/app-fn acc) (e/bvar 0))
                      (e/lam name type acc (or binder-info :default)))
                    (e/forall' name type acc (or binder-info :default)))))
              (e/abstract-many body xs)
              (range (dec (count xs)) -1 -1)))))

(defn- class-of
  "Lean's `isClass?`: the class constant of a type, looking through its reducing telescope and
   `.instances` reduction (a class is an inductive or an axiom of the class extension)."
  [ctx mctx st ty]
  (let [[st _ body] (forall-telescope ctx mctx st ty true)]
    (loop [t body fuel 32]
      (let [h (e/get-app-fn t)]
        (cond
          (and (e/const? h) ((:class? ctx) (e/const-name h))
               (let [ci (env/lookup (:env ctx) (e/const-name h))]
                 (and ci (or (env/induct? ci) (env/axiom? ci)))))
          (e/const-name h)
          (zero? fuel) nil
          :else (let [t' (whnf-i ctx mctx st t)]
                  (when (not= t' t)
                    (let [[_ _ b] (forall-telescope ctx mctx st t' true)] (recur b (dec fuel))))))))))

(defn- local-instances
  "Lean's `getLocalInstances`: the local declarations whose type is a class, in declaration
   (fvar id) order: [[class fvar-id] …]."
  [ctx st]
  (let [lctx (:lctx st)
        memo (:synth-memo st)
        cached (when memo (get @memo ::local-instances))]
    (if (and cached (identical? (nth cached 0) lctx) (identical? (nth cached 1) (:index ctx)))
      (nth cached 2)
      (let [r (->> lctx
                   (filter (fn [[_ d]] (and (#{:local :let-decl} (:tag d)) (:type d))))
                   (sort-by key)
                   (keep (fn [[fid d]]
                           (when-let [c (try (class-of ctx meta/empty-context st (:type d))
                                             (catch clojure.lang.ExceptionInfo _ nil))]
                             [c fid])))
                   vec)]
        (when memo (swap! memo assoc ::local-instances [lctx (:index ctx) r]))
        r))))

;; ============================================================
;; getInstances, tryResolve
;; ============================================================

(defn- get-instances*
  "Lean's `getInstances`: the candidates for an instance goal of type `ty`, in Lean's array order
   (consumed from the END): global matches (`getUnify`) stably sorted by ascending priority, then
   the local instances of the goal's class, oldest first."
  [ctx mctx st ty]
  (let [linsts (local-instances ctx st)
        [st' _ body] (forall-telescope ctx mctx st ty true)]
    (when-let [cls (class-of ctx mctx st' body)]
      (let [globals (->> (ii/get-unify mctx st' #(root-trie (:state ctx) %) body)
                         (sort-by :priority)
                         (mapv (fn [v] {:global v})))
            locals (for [[c fid] linsts :when (= c cls)]
                     (let [[st'' xs _] (forall-telescope ctx meta/empty-context st (:type (get (:lctx st) fid)) true)]
                       {:local fid
                        :synth-order (vec (keep-indexed (fn [i x] (when (= :inst-implicit (:binder-info (get (:lctx st'') x))) i))
                                                        xs))}))]
        (into globals locals)))))

(defn- fresh-mvar [st mctx type]
  (let [id (swap! (:next-id st) inc)]
    [(meta/add-expr-mvar-decl mctx id type (:lctx st)) (e/mvar id)]))

(defn- def-eq
  "Unification inside synthesis. A mismatch is nil; an ExceptionInfo raised by the meta layer
   on an ill-typed speculative term is a mismatch too. isDefEqStuck and resource exhaustion
   propagate."
  [mctx st bound a b]
  (try (meta/is-def-eq mctx st bound a b)
       (catch clojure.lang.ExceptionInfo ex
         (if (or (meta/is-def-eq-stuck? ex) (= :synth-exhausted (:reason (ex-data ex))))
           (throw ex)
           nil))))

(defn- instance-value
  "The candidate's value, type and synthesis order: a global constant with fresh level mvars, or a
   local fvar. nil for a registry entry the env does not have."
  [ctx st mctx inst]
  (if-let [fid (:local inst)]
    [mctx (e/fvar fid) (:type (get (:lctx st) fid)) (:synth-order inst)]
    (let [{:keys [name synth-order]} (:global inst)]
      (when-let [^ConstantInfo ci (env/lookup (:env ctx) name)]
        (let [lps (vec (.levelParams ci))
              lids (vec (repeatedly (count lps) #(swap! (:next-id st) inc)))
              mctx (reduce meta/add-level-mvar-decl mctx lids)
              lvls (mapv lvl/mvar lids)]
          [mctx (e/const' name lvls)
           (cond-> (.type ci) (seq lps) (e/instantiate-level-params (zipmap lps lvls)))
           synth-order])))))

(defn- try-resolve
  "Lean's `tryResolve`: [mctx subgoals] or nil."
  [ctx st mctx mvar inst]
  (when-let [[mctx val itype synth-order] (instance-value ctx st mctx inst)]
    (let [mvar-type (meta/zonk-expr mctx (:type (meta/expr-decl! mctx (e/mvar-id mvar))))
          [st' xs body] (forall-telescope ctx mctx st mvar-type true)
          xs-args (mapv e/fvar xs)
          ;; getSubgoals: `?m : ∀ xs, A` in the goal's context, applied to xs
          [mctx val tbody mvars]
          (loop [t itype mctx mctx val val mvars []]
            (if (e/forall? t)
              (let [[mctx mv] (fresh-mvar st mctx (mk-binding st' xs (e/forall-type t) false))
                    arg (apply e/app* mv xs-args)]
                (recur (e/instantiate1 (e/forall-body t) arg) mctx (e/app val arg) (conj mvars mv)))
              (let [t' (whnf-i ctx mctx st' t)]
                (if (e/forall? t')
                  (recur t' mctx val mvars)
                  [mctx val t mvars]))))]
      (when-let [mctx (def-eq mctx st' (set xs) body tbody)]
        (let [val (mk-binding st' xs (meta/zonk-expr mctx val) true)]
          (when-let [mctx (def-eq mctx st #{} mvar val)]
            [mctx (into [] (comp (filter #(< % (count mvars))) (map #(nth mvars %))) synth-order)]))))))

;; ============================================================
;; Tabled resolution (SynthInstance.lean)
;; ============================================================

(defn- mk-table-key
  "Lean's `mkTableKey`: assignable expression mvars become `_tc.i` placeholders (here fvars with
   reserved negative ids), level mvars of the current depth `_tc.i` params."
  [mctx x]
  (let [x (meta/zonk-expr mctx x)
        depth (:depth mctx 0)
        emap (atom {})
        lstate (atom {:lmap {} :params []})
        x (meta/replace-mvars
           x (fn [m]
               (let [id (e/mvar-id m)
                     decl (meta/expr-decl mctx id)]
                 (when (and decl (= depth (:depth decl 0)))
                   (or (get @emap id)
                       (let [fv (e/fvar (- -1000000000 (count @emap)))]
                         (swap! emap assoc id fv)
                         fv))))))]
    (meta/map-levels x #(meta/level-mvars->params % (fn [id] (= depth (get-in mctx [:level-depth id]))) lstate "_tc"))))

(defn- mvar-type [mctx mvar]
  (meta/zonk-expr mctx (:type (meta/expr-decl! mctx (e/mvar-id mvar)))))

(defn- new-subgoal
  "Lean's `newSubgoal`: a generator node for `mvar` (unless it has no candidates) and a table
   entry waited on by `waiter`."
  [ctx st s mctx key mvar waiter]
  (let [ty (mvar-type mctx mvar)
        insts (get-instances* ctx mctx st ty)]
    (if (empty? insts)
      s
      (-> s
          (update :generators conj {:mvar mvar :key key :mctx mctx :instances insts
                                    :idx (count insts) :type-has-mvars? (meta/zonked-has-mvar? ty)})
          (assoc-in [:table key] {:waiters [waiter] :answers []})))))

(defn- unused-arguments?
  "Lean's `hasUnusedArguments` (syntactic)."
  [t]
  (loop [t t]
    (and (e/forall? t)
         (or (not (#'ii/has-loose-bvar? (e/forall-body t) 0))
             (recur (e/forall-body t))))))

(defn- remove-unused-arguments
  "Lean's `removeUnusedArguments?`: [type' transformer] for a goal `∀ xs, B` some of whose binders
   B does not use (directly or through the types of used ones), or nil."
  [ctx st mctx mvar]
  (let [ty (mvar-type mctx mvar)]
    (when (unused-arguments? ty)
      (let [[st' xs body] (forall-telescope ctx mctx st ty false)
            type-of #(:type (get (:lctx st') %))
            ys (vec (reduce (fn [ys x]
                              (if (or (contains? (#'ii/fvar-ids-in body) x)
                                      (some #(contains? (#'ii/fvar-ids-in (type-of %)) x) ys))
                                (cons x ys)
                                ys))
                            () (rseq xs)))
            ty' (mk-binding st' ys body false)
            fid (swap! (:next-id st) inc)
            st'' (add-local st' fid "redf" ty' :default)
            inner (mk-binding st'' xs (apply e/app* (e/fvar fid) (map e/fvar ys)) true)
            transformer (mk-binding st'' [fid] inner true)]
        [ty' transformer]))))

(defn- beta1 [f a]
  (if (e/lam? f) (e/instantiate1 (e/lam-body f) a) (e/app f a)))

(defn- push-resume [s cnode answers]
  (update s :resume into (map (fn [a] [cnode a]) answers)))

(defn- add-answer
  "Lean's `addAnswer`: a finished consumer is an answer of its goal's table entry (unless it is
   too large, or an equal answer is known), propagated to the entry's waiters."
  [st s cnode]
  (if (>= (:size cnode) config/*synth-max-result-size*)
    s
    (let [mctx (:mctx cnode)
          result (meta/abstract-mvars mctx st (meta/zonk-expr mctx (:mvar cnode)))
          answer {:result result
                  :result-type (meta/infer-type mctx st (:expr result))
                  :size (inc (:size cnode))}
          {:keys [waiters answers]} (get-in s [:table (:key cnode)])]
      (if (every? #(not= (:result-type %) (:result-type answer)) answers)
        (reduce (fn [s w]
                  (if (= w :root)
                    (if (zero? (:num-mvars result)) (assoc s :result result) s)
                    (update s :resume conj [w answer])))
                (assoc-in s [:table (:key cnode) :answers] (conj answers answer))
                waiters)
        s))))

(defn- consume
  "Lean's `consume`: drop the subgoals already assigned; with none left the node is an answer;
   else wait on the table entry of the next subgoal (a new generator when there is none)."
  [ctx st s cnode]
  (let [{:keys [mctx]} cnode
        subgoals (vec (remove #(meta/expr-assigned? mctx (e/mvar-id %)) (:subgoals cnode)))
        cnode (assoc cnode :subgoals subgoals)]
    (if (empty? subgoals)
      (add-answer st s cnode)
      (let [mvar (first subgoals)
            key (mk-table-key mctx (mvar-type mctx mvar))]
        (if-let [entry (get-in s [:table key])]
          (-> (push-resume s cnode (:answers entry))
              (update-in [:table key :waiters] conj cnode))
          (if-let [[ty' transformer] (remove-unused-arguments ctx st mctx mvar)]
            (let [key' (mk-table-key mctx ty')]
              (if-let [entry' (get-in s [:table key'])]
                (let [answers' (mapv (fn [a]
                                       (let [x (beta1 transformer (meta/zonk-expr mctx (:expr (:result a))))]
                                         (-> a (assoc-in [:result :expr] x)
                                             (assoc :result-type (meta/infer-type mctx st x)))))
                                     (:answers entry'))]
                  (-> (push-resume s cnode answers')
                      (update-in [:table key' :waiters] conj cnode)))
                (let [[mctx' mvar'] (fresh-mvar st mctx ty')]
                  (new-subgoal ctx st s mctx' key' mvar'
                               (assoc cnode :mctx mctx' :subgoals (into [mvar'] subgoals))))))
            (new-subgoal ctx st s mctx key mvar cnode)))))))

(defn- generate
  "Lean's `generate`: the next candidate of the top generator node."
  [ctx st s]
  (let [g (peek (:generators s))]
    (if (zero? (:idx g))
      (update s :generators pop)
      (if (and (not (:type-has-mvars? g))
               (some #(zero? (:num-mvars (:result %))) (get-in s [:table (:key g) :answers])))
        ;; canonical instances: a goal without metavariables needs one answer
        (update s :generators pop)
        (let [idx (dec (:idx g))
              inst (nth (:instances g) idx)
              s (update s :generators #(assoc-in % [(dec (count %)) :idx] idx))]
          (if-let [[mctx subgoals] (try-resolve ctx st (:mctx g) (:mvar g) inst)]
            (consume ctx st s {:key (:key g) :mvar (:mvar g) :subgoals subgoals :mctx mctx :size 0})
            s))))))

(defn- resume
  "Lean's `resume`: feed an answer to the next subgoal of a consumer."
  [ctx st s]
  (let [[cnode answer] (peek (:resume s))
        s (update s :resume pop)
        [mvar & rest] (:subgoals cnode)
        [mctx _ val] (meta/open-abstract-mvars-result (:mctx cnode) st (:result answer))]
    (if-let [mctx (def-eq mctx st #{} mvar val)]
      (consume ctx st s (assoc cnode :subgoals (vec rest) :mctx mctx :size (+ (:size cnode) (:size answer))))
      s)))

(declare synth-main*)

(defn- synth-main
  "Lean's `SynthInstance.main`: the first root answer (an abstract result without expression
   mvars) for `type` in `mctx` (already one depth deeper than the caller), or nil. Unification
   runs at `.instances` transparency, as Lean's `synthInstance?` configures it."
  [ctx st mctx type]
  (binding [meta/*transparency* :instances
            meta/*instance-name?* (:instance-name? ctx)]
    (synth-main* ctx st mctx type)))

(defn- synth-main*
  [ctx st mctx type]
  (let [[mctx mvar] (fresh-mvar st mctx type)
        key (mk-table-key mctx type)
        s0 (new-subgoal ctx st {:generators [] :resume [] :table {} :result nil} mctx key mvar :root)]
    (loop [s s0 steps 0]
      (cond
        (:result s) (:result s)
        (>= steps config/*synth-max-steps*)
        (throw (ex-info (str "Tactic error: instance synthesis exceeded its resource bound ("
                             "*synth-max-steps* " config/*synth-max-steps* ")")
                        {:kind :tactic-error :reason :synth-exhausted :goal type
                         :limit config/*synth-max-steps*}))
        (seq (:resume s)) (recur (resume ctx st s) (inc steps))
        (seq (:generators s)) (recur (generate ctx st s) (inc steps))
        :else nil))))

;; ============================================================
;; synthInstance? — out-params, the cache, the root answer
;; ============================================================

(def ^:private wildcard (e/fvar -1))
(def ^:private level-wildcard (lvl/param (name/from-string "__wild__")))

(defn- class-info [ctx cls] ((:class-info (:ictx ctx)) cls))

(defn- preprocess
  "Lean's `preprocess`: {:type :cache-key-type :kind}."
  [ctx mctx st type]
  (let [[st' xs body] (forall-telescope ctx mctx st type true)
        body (whnf-i ctx mctx st' body)
        type (mk-binding st' xs body false)
        [h args] (e/get-app-fn-args body)
        info (when (and (e/const? h) (seq args)) (class-info ctx (e/const-name h)))
        outs (:out-params info) louts (:out-level-params info)]
    (cond
      (not (meta/zonked-has-mvar? type)) {:type type :cache-key-type type :kind :no-mvars}
      (or (not (e/const? h)) (empty? args) (and (empty? outs) (empty? louts)))
      {:type type :cache-key-type type :kind :mvars-no-output-params}
      :else
      (let [c (if (empty? louts) h
                  (e/const' (e/const-name h) (vec (map-indexed (fn [i u] (if (contains? louts i) level-wildcard u))
                                                               (e/const-levels h)))))
            body' (apply e/app* c (map-indexed (fn [i a] (if (contains? outs i) wildcard a)) args))]
        {:type type :cache-key-type (mk-binding st' xs body' false) :kind :mvars-output-params}))))

(defn- preprocess-out-param
  "Lean's `preprocessOutParam`: the goal with its out-params (and out-level-params) replaced by
   fresh metavariables of `mctx`'s depth. [mctx type]."
  [ctx mctx st type]
  (let [[st' xs body] (forall-telescope ctx mctx st type false)
        [h args] (e/get-app-fn-args body)
        info (when (and (e/const? h) (seq args)) (class-info ctx (e/const-name h)))
        outs (:out-params info) louts (:out-level-params info)]
    (if (or (not (e/const? h)) (empty? args) (and (empty? outs) (empty? louts)))
      [mctx type]
      (let [[mctx c] (if (empty? louts)
                       [mctx h]
                       (let [[mctx us] (reduce (fn [[mctx us] [i u]]
                                                 (if (contains? louts i)
                                                   (let [id (swap! (:next-id st) inc)]
                                                     [(meta/add-level-mvar-decl mctx id) (conj us (lvl/mvar id))])
                                                   [mctx (conj us u)]))
                                               [mctx []] (map-indexed vector (e/const-levels h)))]
                         [mctx (e/const' (e/const-name h) us)]))
            [mctx args] (if (empty? outs)
                          [mctx args]
                          (loop [i 0 ty (meta/infer-type mctx st' c) mctx mctx acc []]
                            (if (< i (count args))
                              (let [ty (let [t (meta/zonk-expr mctx ty)] (if (e/forall? t) t (meta/whnf mctx st' t)))
                                    [mctx arg] (if (contains? outs i)
                                                 ;; created outside the telescope, applied to it
                                                 (let [[mctx mv] (fresh-mvar st mctx (mk-binding st' xs (e/forall-type ty) false))]
                                                   [mctx (apply e/app* mv (map e/fvar xs))])
                                                 [mctx (nth args i)])]
                                (recur (inc i) (e/instantiate1 (e/forall-body ty) arg) mctx (conj acc arg)))
                              [mctx acc])))]
        [mctx (mk-binding st' xs (apply e/app* c args) false)]))))

(defn- assign-out-params
  "Lean's `assignOutParams`: the result's type unified with the goal (`withDefault`)."
  [mctx st type result]
  (binding [meta/*transparency* :default]
    (some-> (def-eq (meta/with-synthetic-opaque-assignment mctx true) st #{} type (meta/infer-type mctx st result))
            (meta/with-synthetic-opaque-assignment false))))

(defn- check-result
  "Lean's `check` of a root answer: a metavariable-free answer to a metavariable-free goal is
   type-checked by the kernel checker."
  [mctx st type result]
  (let [type (meta/zonk-expr mctx type)]
    (or (meta/zonked-has-mvar? result) (meta/zonked-has-mvar? type)
        (try (tc/is-def-eq st (tc/infer-type st result) type)
             (catch clojure.lang.ExceptionInfo _ false)))))

(defn- apply-abstract-result
  "Lean's `applyAbstractResult?`: open the root answer in the caller's metacontext and check it
   against the goal. [mctx result] or nil."
  [mctx st type abst]
  (when abst
    (let [[mctx _ result] (meta/open-abstract-mvars-result mctx st abst)]
      (when-let [mctx (assign-out-params mctx st type result)]
        (let [result (meta/zonk-expr mctx result)]
          (when (check-result mctx st type result)
            [mctx result]))))))

(defn- apply-cached-abstract-result
  "Lean's `applyCachedAbstractResult?`."
  [mctx st type abst]
  (when abst
    (if (and (zero? (:num-mvars abst)) (empty? (:param-names abst)))
      (when-let [mctx (assign-out-params mctx st type (:expr abst))]
        [mctx (:expr abst)])
      (apply-abstract-result mctx st type abst))))

(defn- synth-instance*
  "Lean's `synthInstance?` for `type` in `mctx` (whose mvars it may assign through out-params):
   [mctx result] or nil. Throws isDefEqStuck when the goal cannot be decided yet."
  [ctx mctx st type]
  (binding [meta/*is-def-eq-stuck-ex* true]
    (let [linsts (local-instances ctx st)
          type (meta/zonk-expr mctx type)
          {:keys [type cache-key-type kind]} (preprocess ctx mctx st type)
          memo (:synth-memo st)
          cache-key [(IdKey. (:env ctx)) (IdKey. (:index ctx)) linsts cache-key-type meta/*synth-pending-depth*]
          hit (when memo (find @memo cache-key))]
      (if hit
        (apply-cached-abstract-result mctx st type (val hit))
        (let [nested (meta/inc-depth mctx true)
              [nested goal] (if (= kind :mvars-no-output-params)
                              [nested type]
                              (preprocess-out-param ctx nested st type))
              abst (synth-main ctx st nested goal)
              result (apply-abstract-result mctx st type abst)]
          (when memo
            (swap! memo assoc cache-key
                   (cond
                     (nil? abst) nil
                     (and (zero? (:num-mvars abst)) (empty? (:param-names abst))
                          (#{:no-mvars :mvars-no-output-params} kind))
                     (when result {:param-names [] :num-mvars 0 :expr (second result)})
                     :else abst)))
          result)))))

(defn- root-class?
  "Is `n` the class some registered instance concludes in after reduction (Lean only registers an
   instance whose type is a class, so this is class-extension knowledge the registry carries:
   the instances of `DecidableEq` make `Decidable` a class)?"
  [state n]
  (contains? @(:root-classes state) n))

(defn- synth-ctx [^Env env index]
  (let [state (index-state env index)
        class? (:class? (:ctx state))]
    {:env env :index index :state state :ictx (:ctx state)
     :class? (fn [n] (or (class? n) (root-class? state n)))
     :instance-name? (fn [n] (contains? @(:instance-names state) n))}))

(defn synth-instance
  "Lean's `synthInstance?` in a metacontext: [mctx result] or nil (also nil when the problem is
   stuck on metavariables of `mctx`). `st`'s local context supplies the local instances."
  ([mctx st goal] (synth-instance mctx st (index-for (:env st)) goal))
  ([mctx st index goal]
   (try (synth-instance* (synth-ctx (:env st) index) mctx st goal)
        (catch clojure.lang.ExceptionInfo ex
          (if (meta/is-def-eq-stuck? ex) nil (throw ex))))))

;; ============================================================
;; Public API
;; ============================================================

(defn synthesize*
  "Synthesize an instance of the metavariable-free `goal-type` in the local context of `st`
   against the registry `index` (the env must carry its instance extension even when that
   registry is empty). Returns the instance term, or nil when there is none. Throws when the
   search exceeds its resource bound, and when the answer leaves universe levels undetermined
   (Lean returns it with level metavariables, which a closed term cannot carry). `_depth` is
   accepted for compatibility and ignored."
  [st env index goal-type _depth]
  (index-for env)
  (when-let [[mctx r] (try (synth-instance* (synth-ctx env index) meta/empty-context st goal-type)
                           (catch clojure.lang.ExceptionInfo ex
                             (if (meta/is-def-eq-stuck? ex) nil (throw ex))))]
    (let [r (meta/zonk-expr mctx r)]
      (when (meta/zonked-has-mvar? r)
        (throw (ex-info "Tactic error: the instance leaves universe levels undetermined"
                        {:kind :tactic-error :reason :universe-mvars :goal goal-type :instance r})))
      r)))

(defn synthesize
  "Synthesize a typeclass instance for the given goal type.
   Returns the fully-applied instance term, or throws if not found."
  [env index goal-type]
  (or (synthesize* (tc/mk-tc-state env) env index goal-type 0)
      (throw (ex-info "Tactic error: instance resolution: no instance found"
                      {:kind :tactic-error :reason :no-instance :goal goal-type}))))

(defn candidates
  "The candidates for the goal `goal-type` in the local context of `st`, in Lean's try order (the
   reverse of `getInstances`' array): instance names, and [:local fvar-id] for local instances."
  ([env index goal-type] (candidates (tc/mk-tc-state env) env index goal-type))
  ([st env index goal-type]
   (mapv #(or (:name (:global %)) [:local (:local %)])
         (rseq (vec (get-instances* (synth-ctx env index) meta/empty-context st goal-type))))))

(defn resolve-decidable
  "Convenience: resolve a Decidable instance for a proposition, against the session's registry."
  [env prop]
  (let [index (index-for env)
        decidable-name (name/from-string "Decidable")
        goal (e/app (e/const' decidable-name []) prop)]
    (synthesize env index goal)))

(defn verify-instance
  "Verify that the resolved instance has the expected type `Decidable P`."
  [env prop instance]
  (let [st (tc/mk-tc-state env)
        decidable-name (name/from-string "Decidable")
        inferred (tc/infer-type st instance)
        expected (e/app (e/const' decidable-name []) prop)]
    (tc/is-def-eq st inferred expected)))

;; ============================================================
;; synthPending — instance synthesis from inside unification
;; ============================================================

(defn synth-pending-instance
  "`ansatz.meta/*synth-pending-fn*`, Lean's `synthPendingImp`: synthesize the instance
   metavariable `mvar-id` that unification is stuck on, in the metavariable's own local context,
   unless it is synthetic opaque, its type is not a class, or synthPending is nested deeper than
   `meta/max-synth-pending-depth`. Returns the metacontext with it assigned, or nil. Only
   isDefEqStuck counts as \"not yet\"; other failures propagate."
  [mctx st mvar-id]
  (let [decl (meta/expr-decl mctx mvar-id)
        env (:env st)
        index (env/get-extension env :instances nil)]
    (when (and decl index
               (not= :syntheticOpaque (:kind decl))
               (not (meta/expr-assigned-or-delayed? mctx mvar-id)))
      (let [st (if (:lctx decl) (assoc st :lctx (:lctx decl)) st)
            ctx (synth-ctx env index)
            type (meta/zonk-expr mctx (:type decl))]
        (when (and (<= meta/*synth-pending-depth* meta/max-synth-pending-depth)
                   (class-of ctx mctx st type))
          (binding [meta/*synth-pending-depth* (inc meta/*synth-pending-depth*)]
            (when-let [[mctx val] (try (synth-instance* ctx mctx st type)
                                       (catch clojure.lang.ExceptionInfo ex
                                         (if (meta/is-def-eq-stuck? ex) nil (throw ex))))]
              (when-not (meta/expr-assigned? mctx mvar-id)
                (meta/assign-expr mctx mvar-id val)))))))))

;; Loading this namespace is what makes instances synthesizable; installing the hook here
;; keeps `ansatz.meta` free of any dependency on the tactic layer.
(alter-var-root #'meta/*synth-pending-fn* (constantly synth-pending-instance))
