(ns ansatz.clj-model.callees
  "Calls from a modelled Clojure function to functions outside clojure.core (PR G3). A call
   `(g x …)` of a var `g`:

   - an `a/defmodel` function is modelled from its source. The a/defmodel functions reachable
     from `g` form a call graph; each strongly connected group is translated once, callees
     first, into definitions named after the var: `clj.<ns>.<name>.a<n>` per arity (`.v<n>` for
     a variadic one). A recursive group shares one functional `….F`, entered through
     `CljM.fix<k>` with the default fuel of each entry's arguments (ansatz.clj-model.translate).
     The env's :clj-model-vars extension records them, keyed by the source, so later models
     reuse them and a changed source is translated again.
   - an `a/defn` (or `a/foreign`) of the DSL whose parameters and result are Nat, Int, Bool,
     String or Float (their runtime values are the Clojure values): `dec_T` each argument, then
     `some (enc_R (g y …))`. For an `a/foreign ^:model` function its model `g.clj` stands in
     for `g`: a :tested `g` is the default d_R where its model makes no claim, its runtime is not.
   - any other function (outside `clojure.*`) is OPAQUE: the axiom
     `clj.<ns>.<name>.opaque<n> : CljM.V → … → Option CljM.V`. Its type is inhabited
     (`fun _ … => none`), so it cannot make the environment inconsistent; it assumes that `g`
     is a pure function of its arguments, and a model through it claims what Clojure returns
     whatever `g` returns. Its runtime calls `g` (a throw, or a result outside the model, is
     none), so the compiled model is checked against Clojure through the real `g`. The env's
     :clj-model-opaque extension maps each axiom to its var; `opaque-in` lists those a
     declaration reaches, which `a/trust-report` shows."
  (:require [clojure.string :as str]
            [ansatz.core :as a]
            [ansatz.config :as config]
            [ansatz.state :as state]
            [ansatz.clj-model :as m]
            [ansatz.clj-model.translate :as tr]
            [ansatz.codegen.decl :as decl]
            [ansatz.export.writer :as writer]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.surface.ingest :as ingest]))

(defn- qname [v] (str (ns-name (:ns (meta v))) "/" (:name (meta v))))

(defn- source-of [v] (get @ingest/model-source-registry (qname v)))

(defn- mangle [s] (str/replace (str s) #"[^A-Za-z0-9_]" "_"))

(defn- base-of [v] (str "clj." (mangle (ns-name (:ns (meta v)))) "." (mangle (:name (meta v)))))

(defn- defined? [kname] (some? (env/lookup (a/env) (name/from-string kname))))

(defn- define-forms! [forms]
  (binding [a/*verbose* false config/*clj-surface* false
            *ns* (or (find-ns 'ansatz.clj-model.kernel) (the-ns 'ansatz.clj-model.callees))]
    (doseq [f forms] (eval f))))

;; ── a/defmodel callees ──────────────────────────────────────────────────────────────────

(defn- callees-of
  "The a/defmodel vars `v`'s source mentions (a call graph's edges; over-approximated)."
  [v]
  (let [{:keys [form ns]} (source-of v)
        nsp (the-ns ns)]
    (into #{} (comp (filter symbol?)
                    (keep #(try (ns-resolve nsp %) (catch Exception _ nil)))
                    (filter #(and (var? %) (source-of %))))
          (tree-seq coll? #(if (map? %) (mapcat identity %) (seq %)) form))))

(defn- sccs
  "The strongly connected groups of the graph reachable from `root` (Tarjan), callees first."
  [root succ]
  (let [index (atom {}) low (atom {}) stack (atom []) on (atom #{}) out (atom [])]
    (letfn [(visit [v]
              (let [i (count @index)]
                (swap! index assoc v i) (swap! low assoc v i)
                (swap! stack conj v) (swap! on conj v)
                (doseq [w (succ v)]
                  (cond (not (contains? @index w)) (do (visit w) (swap! low update v min (@low w)))
                        (@on w) (swap! low update v min (@index w))))
                (when (= (@low v) (@index v))
                  (let [[pre scc] (split-with #(not= v %) (rseq @stack))
                        scc (conj (vec pre) v)]
                    (reset! stack (vec (drop-last (count scc) @stack)))
                    (swap! on #(apply disj % scc))
                    (swap! out conj scc)))))]
      (visit root))
    @out))

(defn- cached
  "The recorded model of a/defmodel var `v`, if it is of its current source."
  [v]
  (let [{:keys [form]} (source-of v)
        rec (get (env/get-extension @state/ansatz-env :clj-model-vars {}) (qname v))]
    (when (= (:form rec) form) rec)))

(defn- fresh-base
  "A name base for `v` not used by an earlier version of its source."
  [v]
  (let [used (set (map :base (vals (env/get-extension @state/ansatz-env :clj-model-vars {}))))
        b (base-of v)]
    (first (remove #(or (used %) (defined? (str % ".F"))) (cons b (map #(str b "_" %) (iterate inc 2)))))))

(defn- arity-name [base {:keys [params rest]}]
  (str base (if rest ".v" ".a") (count params)))

(defn- group-forms
  "The definitions of the a/defmodel group `fns` [{:var :form :ns :base}]: per arity an entry;
   a recursive group (`recursive?`) through one shared functional `<base₀>.F`."
  [fns recursive?]
  (let [parsed (mapv (fn [{:keys [form] :as f}] (merge f (tr/parse-fn form))) fns)
        OV '(Option CljM.V)
        defn* (fn [kname binders body] (list 'ansatz.core/defn (symbol kname) binders OV body))
        vbinders (fn [xs] (vec (mapcat (fn [x] [x :- 'CljM.V]) xs)))]
    (if-not recursive?
      (let [{:keys [var ns arities base]} (first parsed)]
        (for [ar arities]
          (let [{:keys [params body]} (tr/translate (list 'fn (tr/all-params ar) (:body ar)) ns nil {:arity (count (tr/all-params ar))})]
            (with-meta (defn* (arity-name base ar) (vbinders params) body) {:var var :arity ar}))))
      (let [{:keys [members names]} (tr/index-members (map (fn [{:keys [var arities ns self]}]
                                                             {:name var :arities arities :ns ns :fuel (:fuel (meta self))})
                                                           parsed))
            F (str (:base (first parsed)) ".F")
            lits (tr/int-weight (map :body members))]
        (tr/with-translation (:ns (first parsed))
          (fn []
            (let [{:keys [k binders body]} (tr/group-functional {} members {} names)]
              (cons (defn* F binders body)
                    (doall (for [{:keys [var base]} parsed, i (get names var)]
                             (let [mb (nth members i)
                                   xs (mapv tr/fresh (tr/all-params mb))
                                   fuel (or (tr/user-fuel {} mb xs) (tr/default-fuel xs lits))]
                               (with-meta (defn* (arity-name base mb) (vbinders xs) (tr/fix-entry (symbol F) k mb fuel xs))
                                 {:var var :arity mb}))))))))))))

(defn- define-group!
  "Translate and define the a/defmodel vars `vars` (one strongly connected group)."
  [vars]
  (let [fns (mapv (fn [v] (let [{:keys [form ns]} (source-of v)] {:var v :form form :ns ns :base (fresh-base v)}))
                  (sort-by qname vars))
        v0 (:var (first fns))
        recursive? (or (< 1 (count fns)) (contains? (callees-of v0) v0)
                       (tr/recursive? (tr/parse-fn (:form (first fns)))))
        forms (doall (group-forms fns recursive?))]
    (define-forms! forms)
    (swap! state/ansatz-env env/update-extension :clj-model-vars {} merge
           (into {} (for [{:keys [var form base]} fns]
                      [(qname var) {:form form :base base
                                    :arities (vec (for [f forms :when (= var (:var (meta f)))
                                                        :let [{:keys [params rest]} (:arity (meta f))]]
                                                    {:clj-model/fixed (count params) :clj-model/rest? (some? rest)
                                                     :kname (str (second f))}))}])))))

(def ^:private ^:dynamic *translating*
  "The a/defmodel vars whose groups are being translated."
  #{})

(defn ensure-var-model!
  "The model of a/defmodel var `v`: {:arities [{:clj-model/fixed n :clj-model/rest? r :kname k} …]},
   translating (bottom-up) the groups it reaches that are not yet modelled. A call back into a
   group being translated that the source scan did not see (a macro made it) is refused."
  [v]
  (or (cached v)
      (do (when (*translating* v)
            (tr/refuse! :recursion (symbol (qname v)) "a recursive call the source does not show (made by a macro)"))
          (doseq [scc (sccs v callees-of) :when (not-every? cached scc)]
            (binding [*translating* (into *translating* scc)]
              (define-group! scc)))
          (cached v))))

(defn- arity-call
  "A call of a modelled function with arities `as` on `atoms`, as Clojure picks the arity."
  [as atoms]
  (let [n (count atoms)]
    (if-let [a (or (first (filter #(and (not (:clj-model/rest? %)) (= n (:clj-model/fixed %))) as))
                   (first (filter #(and (:clj-model/rest? %) (<= (:clj-model/fixed %) n)) as)))]
      (list* (symbol (:kname a)) (tr/pack-args a atoms))
      (m/none-of 'CljM.V))))

;; ── DSL callees ─────────────────────────────────────────────────────────────────────────

(def scalar-types
  "The DSL types whose runtime values are the Clojure values a plain Clojure caller passes."
  '#{Nat Int Bool String Float})

(defn- type-sym [t]
  (when (e/const? t)
    (let [s (symbol (name/->string (e/const-name t)))] (when (scalar-types s) s))))

(defn- dsl-signature
  "{:kname :params [T …] :ret R :model name?} for a var holding a DSL function over
   `scalar-types`, or nil."
  [v]
  (when-let [kname (some-> v deref meta :ansatz.core/kernel-name)]
    (when-let [^ansatz.kernel.ConstantInfo ci (env/lookup (a/env) (name/from-string kname))]
      (let [[ts r] (loop [t (.type ci) ts []]
                     (if (e/forall? t)
                       (recur (e/forall-body t) (conj ts (when (= :default (e/forall-info t)) (type-sym (e/forall-type t)))))
                       [ts (when-not (e/has-loose-bvars? t) (type-sym t))]))]
        (when (and r (every? some? ts))
          {:kname kname :params ts :ret r
           :model (some-> (get @@(requiring-resolve 'ansatz.clj-model.boundary/registry) kname) :model-name)})))))

(defn- dsl-call
  "`(g a …)` for a DSL function: decode the arguments, call `g` (or its model), encode."
  [{:keys [kname params ret model]} atoms]
  (if (not= (count atoms) (count params))
    (m/none-of 'CljM.V)                       ;; a curried partial application or an ArityException
    (let [codec @(requiring-resolve 'ansatz.clj-model.boundary/codec)
          cs (mapv codec params) rc (codec ret)
          ys (mapv (fn [_] (tr/fresh "y")) params)
          inner (if model
                  (let [r (tr/fresh "r") z (tr/fresh "z")]
                    (list 'Option.bind (list* (symbol model) (map (fn [c y] (list (symbol (:enc c)) y)) cs ys))
                          (list 'fn [r :- 'CljM.V]
                                (list 'Option.bind (list (symbol (:dec rc)) r)
                                      (list 'fn [z :- ret] (list 'Option.some (list (symbol (:enc rc)) z)))))))
                  (list 'Option.some (list (symbol (:enc rc)) (list* (symbol kname) ys))))]
      (reduce (fn [body [a t c y]] (list 'Option.bind (list (symbol (:dec c)) a) (list 'fn [y :- t] body)))
              inner (reverse (map vector atoms params cs ys))))))

;; ── Opaque callees ──────────────────────────────────────────────────────────────────────

(defn- realized
  "`x` with every lazy part realized, or nil if it is larger than 100000 nodes."
  [x]
  (let [budget (volatile! 100000)]
    (letfn [(walk [x]
              (when (neg? (vswap! budget dec)) (throw (ex-info "clj-model: opaque result too large" {})))
              (cond (map? x) (run! (fn [[k v]] (walk k) (walk v)) x)
                    (coll? x) (run! walk x)))]
      (walk x)
      x)))

(defn- opaque-runtime
  "The runtime of an opaque axiom: `g` on the arguments' Clojure values; none when it throws or
   returns something the model cannot hold (a function, a small hash map, an endless seq)."
  [v]
  (fn [& xs]
    (try (let [r (realized (apply @v (map m/cljv->edn xs)))]
           (when-not ((requiring-resolve 'ansatz.clj-check/outside-domain?) r)
             (m/edn->cljv r)))
         (catch Throwable _ nil))))

(defn- opaque!
  "The opaque axiom for `n`-argument calls of var `v` (defined on first use)."
  [v n]
  (let [kname (str (base-of v) ".opaque" n)]
    (when-not (and (defined? kname) (:sym (get @ingest/arity-registry kname)))
      (let [xs (mapv #(symbol (str "x" %)) (range n))
            pairs (ingest/parse-params (vec (mapcat (fn [x] [x :- 'CljM.V]) xs)))
            env (a/env)
            {ty :type-ansatz} (a/elab-signature env pairs '(Option CljM.V))
            rt (opaque-runtime v)]
        (when-not (defined? kname)
          (swap! state/ansatz-env env/add-constant (env/mk-axiom (name/from-string kname) [] ty)))
        (decl/plan! env kname ty n)
        ;; codegen calls a constant's runtime through the var its arity entry names
        (let [f (decl/emit-foreign! kname (if (zero? n) (rt) rt))
              nsp (or (find-ns 'ansatz.clj-model.kernel) (the-ns 'ansatz.clj-model.callees))
              sym (decl/runtime-name kname)]
          (intern nsp sym f)
          (swap! ingest/arity-registry update kname assoc :sym (symbol (str (ns-name nsp)) (str sym))))
        (swap! state/ansatz-env env/update-extension :clj-model-opaque {} assoc kname (qname v))))
    kname))

(defn opaque-in
  "The functions (qualified names) whose opaque axioms the declaration `decl` reaches."
  ([decl] (opaque-in @state/ansatz-env decl))
  ([env decl]
   (let [opaque (env/get-extension env :clj-model-opaque {})]
     (vec (sort (distinct (keep #(get opaque (name/->string (.name ^ansatz.kernel.ConstantInfo %)))
                                (writer/closure-constants env [(str decl)]))))))))

;; ── The hook ────────────────────────────────────────────────────────────────────────────

(defn call-var
  "The builder (argument atoms → model term) of a call of var `v` in a model (see the namespace
   doc); `form` is the call, for refusals."
  [v form]
  (cond
    (source-of v) (let [{:keys [arities]} (ensure-var-model! v)] (fn [atoms] (arity-call arities atoms)))
    (dsl-signature v) (let [sig (dsl-signature v)]
                        ((requiring-resolve 'ansatz.clj-model.boundary/install-codecs!))
                        (fn [atoms] (dsl-call sig atoms)))
    (str/starts-with? (str (ns-name (:ns (meta v)))) "clojure.") (tr/refuse! :unmodelled-fn form)
    (some-> v deref meta :ansatz.core/kernel-name)
    (tr/refuse! :unmodelled-fn form "a DSL function whose parameters or result are not Nat, Int, Bool, String or Float")
    (not (fn? @v)) (tr/refuse! :unmodelled-form form)
    :else (fn [atoms] (list* (symbol (opaque! v (count atoms))) atoms))))
