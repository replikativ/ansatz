(ns ansatz.search
  "The REPL's view of the library as a DATABASE — queries over the catalogue (ansatz.catalogue)
   and a `suggest` that turns them into proof steps.

   Everything here is optional: tactics do not consult datahike unless asked. `enable!` installs
   `suggest` as the provider behind `exact?`/`apply?`; without it they stay as they are.

   The queries compose three things the catalogue holds per declaration: its SHAPE (the
   conclusion disc-tree key, served by the durable index `:idx/dt`), its VOCABULARY (`:decl/
   mentions`, the constants of the statement, as refs) and its PROVENANCE (module, attributes,
   dependencies). `suggest` uses them in that order — shape narrows the library to the few
   hundred lemmas whose conclusion could match, vocabulary ranks them by how much of the goal's
   language they share, and the kernel confirms the survivors by actually applying them."
  (:require [ansatz.catalogue :as cat]
            [ansatz.index.discr :as dti]
            [ansatz.recall :as recall]
            [ansatz.state :as state]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.proof :as proof]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.level :as lvl]
            [datahike.api :as d]
            [clojure.string :as str])
  (:import [ansatz.kernel Expr ConstantInfo]))

(defn db
  "The current store's catalogue DB (connected on first use), or nil."
  []
  (some-> (:store-path @state/ansatz-store) cat/current-db))

(defn- names [db eids] (when (seq eids) (map first (d/q '[:find ?n :in $ [?d ...] :where [?d :decl/name ?n]] db eids))))

;; ---- queries ----

(defn find-decls
  "Declarations by facts. Every key optional; all given ones must hold.
     :mentions [name …]   every listed constant occurs in the STATEMENT
     :head     name       head constant of the conclusion
     :kind     :thm|:def|:axiom|:induct|:ctor|:rec|:opaque|:quot
     :attr     \"simp\"|\"csimp\"|\"instance\"|\"extern\"|…
     :module   \"Mathlib.Data.List\"   (prefix)
     :limit    n (default 100)
   Returns names."
  [db {:keys [mentions head kind attr module limit] :or {limit 100}}]
  (let [where (cond-> []
                head (conj ['?d :decl/concl-head head])
                kind (conj ['?d :decl/kind kind])
                attr (conj ['?d :decl/attr attr])
                module (conj ['?d :decl/module '?mod] [(list 'clojure.string/starts-with? '?mod module)]))
        where (into where (mapcat (fn [i m] [['?d :decl/mentions (symbol (str "?m" i))]
                                              [(symbol (str "?m" i)) :decl/name m]])
                                  (range) mentions))
        where (conj where ['?d :decl/name '?n])]
    (take limit (map first (d/q {:find '[?n] :where where} db)))))

(defn describe
  "Everything the catalogue knows about a declaration."
  [db name-str]
  (some-> (d/pull db '[* {:decl/mentions [:decl/name]} {:decl/depends-on [:decl/name]}
                       {:decl/instance-of [:decl/name]}]
                  [:decl/name name-str])
          (update :decl/mentions #(mapv :decl/name %))
          (update :decl/depends-on #(mapv :decl/name %))
          (update :decl/instance-of :decl/name)))

(defn users-of
  "Declarations whose VALUE (proof/body) uses `name-str` directly."
  [db name-str]
  (map first (d/q '[:find ?n :in $ ?m :where [?x :decl/name ?m] [?d :decl/depends-on ?x] [?d :decl/name ?n]] db name-str)))

(defn mentioned-by
  "Declarations whose STATEMENT mentions `name-str`."
  [db name-str]
  (map first (d/q '[:find ?n :in $ ?m :where [?x :decl/name ?m] [?d :decl/mentions ?x] [?d :decl/name ?n]] db name-str)))

(def ^:private deps-rules
  '[[(dep ?a ?b) [?a :decl/depends-on ?b]]
    [(dep ?a ?b) [?a :decl/depends-on ?c] (dep ?c ?b)]])

(defn depends-on*
  "The TRANSITIVE dependencies of `name-str` (a datalog rule; large for a deep theorem)."
  [db name-str]
  (map first (d/q '[:find ?n :in $ % ?a :where [?x :decl/name ?a] (dep ?x ?y) [?y :decl/name ?n]] db deps-rules name-str)))

(defn simp-set
  "The @[simp] lemmas of a module prefix — `(simp [names…])` material."
  [db module-prefix]
  (find-decls db {:attr "simp" :module module-prefix :limit 100000}))

(defn instances-of
  "Instances of a class, by priority."
  [db class-name]
  (map first (d/q '[:find ?n ?p :in $ ?c :where [?cl :decl/name ?c] [?d :decl/instance-of ?cl] [?d :decl/name ?n] [(get-else $ ?d :decl/instance-prio 1000) ?p]] db class-name)))

;; ---- suggest: shape → vocabulary → kernel ----

(defn goal-consts
  "The constant names of a goal expression."
  [^Expr root]
  (let [seen (java.util.IdentityHashMap.) acc (java.util.LinkedHashSet.)]
    (loop [todo (list root)]
      (when-let [x (first todo)]
        (let [r (rest todo)]
          (if (or (not (instance? Expr x)) (.containsKey seen x))
            (recur r)
            (do (.put seen x true)
                (case (int (.tag ^Expr x))
                  2 (do (.add acc (nm/->string (.o0 ^Expr x))) (recur r))
                  3 (recur (conj r (.o0 ^Expr x) (.o1 ^Expr x)))
                  (4 5) (recur (conj r (.o1 ^Expr x) (.o2 ^Expr x)))
                  6 (recur (conj r (.o0 ^Expr x) (.o1 ^Expr x) (.o2 ^Expr x)))
                  (9 10) (recur (conj r (.o1 ^Expr x)))
                  (recur r)))))))
    (vec acc)))

(defn candidates
  "Shape + vocabulary, no kernel: the declarations whose conclusion structurally matches
   `goal-type`, ranked by the share of the goal's constants their statement mentions.
   Returns [{:name :score :kind} …], best first."
  [db goal-type & {:keys [limit] :or {limit 200}}]
  (let [ix (get (:secondary-indices db) :idx/dt)
        eids (vec (dti/search-eids ix (recall/query-key goal-type)))
        gc (set (goal-consts goal-type))
        rows (when (seq eids)
               (d/q '[:find ?d ?n ?k (distinct ?mn) :in $ [?d ...] :where
                      [?d :decl/name ?n] [?d :decl/kind ?k]
                      [(get-else $ ?d :decl/mentions :none) ?_]
                      [?d :decl/mentions ?m] [?m :decl/name ?mn]]
                    db eids))]
    (->> rows
         (map (fn [[_ n k ms]]
                {:name n :kind k
                 :score (if (seq gc) (/ (count (filter gc ms)) (double (count gc))) 0.0)}))
         (sort-by (juxt (comp - :score) (fn [{k :kind}] (case k :thm 0 :axiom 1 :def 2 3)) :name))
         (take limit))))

(defn- try-apply
  "Apply lemma `name-str` to a fresh goal `goal-type`; the resulting proof state, or nil."
  [env goal-type name-str]
  (when-let [^ConstantInfo ci (env/lookup env (nm/from-string name-str))]
    (let [[ps _] (proof/start-proof env goal-type)
          term (e/const' (nm/from-string name-str) (vec (repeat (count (.levelParams ci)) lvl/zero)))]
      (try (basic/apply-tac ps term) (catch Throwable _ nil)))))

(defn suggest
  "Lemmas that APPLY to `goal-type` (a closed kernel Prop), best first: shape-recalled from the
   index, ranked by shared vocabulary, confirmed by `apply`. Each hit carries the number of
   goals `apply` leaves (0 = `exact`). Options :limit (default 10), :try (candidates to
   confirm, default 60), :exclude #{names}."
  [goal-type & {:keys [limit try exclude] :or {limit 10 try 60 exclude #{}}}]
  (let [db (or (db) (throw (ex-info "no catalogue for the current store" {})))
        env @state/ansatz-env
        cands (remove #(contains? exclude (:name %)) (candidates db goal-type :limit try))]
    (->> cands
         (keep (fn [{:keys [name score kind]}]
                 (when-let [ps (try-apply env goal-type name)]
                   {:name name :score score :kind kind
                    :remaining (count (proof/goals ps))
                    :tactic (if (zero? (count (proof/goals ps))) [:exact name] [:apply name])})))
         (take limit)
         vec)))
