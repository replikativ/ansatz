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

(defn eid
  "The entity id of a declaration by name, or nil."
  [db name-str] (d/q '[:find ?e . :in $ ?n :where [?e :decl/name ?n]] db name-str))

;; EVERY query below resolves names to entity ids FIRST and passes them as `:in` arguments.
;; A name left in the pattern (`[?d :decl/mentions ?m] [?m :decl/name "Finset.sum"]`) leaves
;; the planner to join a 10M-datom attribute against an unbound variable: on Mathlib that
;; exhausted a 3.5 GB heap, where the same query with the id bound answers in ~2 s. It is the
;; shape the datahike spike already measured at 13 ms against 6 s (replikativ/datahike#1087).

(defn module-eids
  "Entity ids whose `:decl/module` starts with `prefix`, by SEEKING the AVET index to the
   prefix and reading while it holds — not `starts-with?` over every declaration's module,
   which no index can serve and which took 141 s on Mathlib."
  [db prefix]
  (into [] (comp (take-while #(and (= :decl/module (:a %)) (str/starts-with? (:v %) prefix)))
                 (map :e))
        (d/seek-datoms db :avet :decl/module prefix)))

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
  (let [eids (mapv #(eid db %) mentions)]
    (when (every? some? eids)
      (let [syms (mapv #(symbol (str "?m" %)) (range (count eids)))
            in (cond-> (into '[$] syms) module (conj '[?d ...]))
            args (cond-> (vec eids) module (conj (module-eids db module)))
            where (cond-> (vec (mapcat (fn [sym] [['?d :decl/mentions sym]]) syms))
                    head (conj ['?d :decl/concl-head head])
                    kind (conj ['?d :decl/kind kind])
                    attr (conj ['?d :decl/attr attr]))
            where (conj where ['?d :decl/name '?n])]
        (take limit (apply d/q {:find '[[?n ...]] :in in :where where} db args))))))

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
  (when-let [e (eid db name-str)]
    (d/q '[:find [?n ...] :in $ ?m :where [?d :decl/depends-on ?m] [?d :decl/name ?n]] db e)))

(defn mentioned-by
  "Declarations whose STATEMENT mentions `name-str`."
  [db name-str]
  (when-let [e (eid db name-str)]
    (d/q '[:find [?n ...] :in $ ?m :where [?d :decl/mentions ?m] [?d :decl/name ?n]] db e)))

(def ^:private deps-rules
  '[[(dep ?a ?b) [?a :decl/depends-on ?b]]
    [(dep ?a ?b) [?a :decl/depends-on ?c] (dep ?c ?b)]])

(defn depends-on*
  "The TRANSITIVE dependencies of `name-str` (a datalog rule; large for a deep theorem)."
  [db name-str]
  (when-let [e (eid db name-str)]
    (d/q '[:find [?n ...] :in $ % ?x :where (dep ?x ?y) [?y :decl/name ?n]] db deps-rules e)))

(defn simp-set
  "The @[simp] lemmas of a module prefix — `(simp [names…])` material."
  [db module-prefix]
  (find-decls db {:attr "simp" :module module-prefix :limit 100000}))

(defn instances-of
  "Instances of a class, by priority (lowest first — Lean tries those first)."
  [db class-name]
  (when-let [c (eid db class-name)]
    (->> (d/q '[:find ?n ?p :in $ ?cl :where [?d :decl/instance-of ?cl] [?d :decl/name ?n]
                [(get-else $ ?d :decl/instance-prio 1000) ?p]] db c)
         (sort-by second)
         (map first))))

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
   `goal-type`, ranked by how many of the goal's constants their statement also mentions.
   Returns [{:name :shared :score :kind} …], best first.

   The shape index OVER-APPROXIMATES by design — a star-headed stored key matches anything, so
   a Mathlib goal recalls ~5,500 declarations. Scoring therefore asks the database for a COUNT
   per candidate against the goal's constants (one bounded join), never for the candidates'
   mention lists: pulling every mention of every hit cost seconds and dominated the search."
  [db goal-type & {:keys [limit] :or {limit 200}}]
  (let [ix (get (:secondary-indices db) :idx/dt)
        eids (vec (dti/search-eids ix (recall/query-key goal-type)))
        gc (into [] (keep #(eid db %)) (goal-consts goal-type))
        shared (when (and (seq eids) (seq gc))
                 (into {} (d/q '[:find ?d (count ?c) :in $ [?d ...] [?c ...] :where [?d :decl/mentions ?c]]
                               db eids gc)))
        n-gc (max 1 (count gc))]
    (->> (d/q '[:find ?d ?n ?k :in $ [?d ...] :where [?d :decl/name ?n] [?d :decl/kind ?k]] db eids)
         (map (fn [[d n k]]
                (let [sh (get shared d 0)]
                  {:name n :kind k :shared sh :score (/ (double sh) n-gc)})))
         (sort-by (juxt (comp - :score) (fn [{k :kind}] (case k :thm 0 :axiom 1 :def 2 3)) :name))
         (take limit)
         vec)))

(def ^:dynamic *apply-timeout-ms*
  "How long one confirmation may take. `apply` against an arbitrary Mathlib lemma runs a real
   unification, and a few of them do not come back quickly — without a bound, one pathological
   candidate stalls the whole search. A candidate that times out is simply not suggested."
  1500)

(defn- try-apply
  "Apply lemma `name-str` to proof state `ps`; the resulting state, or nil (no such constant,
   the application failed, or it exceeded `*apply-timeout-ms*`)."
  [ps name-str]
  (when-let [^ConstantInfo ci (env/lookup (:env ps) (nm/from-string name-str))]
    (let [term (e/const' (nm/from-string name-str) (vec (repeat (count (.levelParams ci)) lvl/zero)))
          fut (future (try (basic/apply-tac ps term) (catch Throwable _ nil)))
          r (deref fut *apply-timeout-ms* ::timeout)]
      (when (= r ::timeout) (future-cancel fut))
      (when-not (= r ::timeout) r))))

(defn suggest
  "Lemmas that APPLY to the current goal of proof state `ps`, best first: shape-recalled from
   the catalogue's disc-tree index, ranked by shared vocabulary, confirmed by actually applying
   them. Each hit carries the number of goals `apply` leaves (0 = it closes the goal) and the
   tactic to write. Options :limit (default 10), :try (candidates to confirm, default 60),
   :exclude #{names}.

   A PROOF STATE, not a bare type: `apply` needs the goal's local context — a goal reached by
   `intros` has free variables that exist only there — and a caller that has a proof state is
   the caller that can use the answer."
  [ps & {:keys [limit try exclude] :or {limit 10 try 60 exclude #{}}}]
  (let [db (or (db) (throw (ex-info "no catalogue for the current store" {})))
        goal (proof/current-goal ps)
        _ (when-not goal (throw (ex-info "no goals" {})))
        cands (remove #(contains? exclude (:name %)) (candidates db (:type goal) :limit try))]
    (->> cands
         (keep (fn [{:keys [name score shared kind]}]
                 (when-let [ps' (try-apply ps name)]
                   (let [n (count (proof/goals ps'))]
                     {:name name :score score :shared shared :kind kind :remaining n
                      :tactic (if (zero? n) [:exact name] [:apply name])}))))
         ;; CONFIRMED first, then by how much is left to prove, then by vocabulary. A lemma
         ;; general enough to unify with anything (`BoxIntegral.Box.subbox_induction_on'` on a
         ;; Nat goal) applies and leaves two goals; one that closes the goal outright is the
         ;; answer. Candidate order is a prior, not a verdict.
         (sort-by (juxt :remaining (comp - :score)))
         (take limit)
         vec)))

(defn goal-state
  "A proof state whose current goal is the CONCLUSION of `name-str`'s statement, its binders
   introduced — the state a user is in when they set out to prove that theorem again. For
   re-find experiments and for trying `suggest` at the REPL."
  [name-str]
  (let [env @state/ansatz-env
        ^ConstantInfo ci (env/lookup env (nm/from-string name-str))
        _ (when-not ci (throw (ex-info "no such declaration" {:name name-str})))
        [ps _] (proof/start-proof env (.type ci))]
    (basic/intros ps)))
