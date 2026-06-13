(ns ansatz.wf
  "Well-Founded recursion — the lean4-faithful WellFounded.Nat.fix encoding, GuessLex measure
   inference, guard-aware decrease checking, and sizeOf derivation. Extracted from ansatz.core,
   which dispatches here (define-verified-wf) for non-structural recursion. Reads the live env from
   ansatz.state; the few core elaboration/API callbacks are resolved at runtime (core requires this
   ns, so a static require back would cycle)."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.omega :as omega]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.inductive :as inductive]
            [ansatz.surface.match :as surface-match]
            [ansatz.codegen :as codegen :refer [ansatz->clj]]
            [ansatz.config :as config]
            [ansatz.surface.elaborate :as elab]
            [ansatz.surface.ingest :as ingest
             :refer [parse-params binder-type metadata-params? arity-registry structure-registry codegen-registry]]
            [ansatz.state :refer [ansatz-env ansatz-instance-index]])
  (:import [ansatz.kernel ConstantInfo]))

;; ── core callbacks resolved at runtime (core requires this ns → no static require back) ──────────
(defn- run-tactic [ps tac] ((requiring-resolve 'ansatz.core/run-tactic) ps tac))
(defn- prove-theorem [& args] (apply (requiring-resolve 'ansatz.core/prove-theorem) args))
(defn- build-telescope-fvar [& args] (apply (requiring-resolve 'ansatz.core/build-telescope-fvar) args))
(defn- try-synthesize-instance [& args] (apply (requiring-resolve 'ansatz.core/try-synthesize-instance) args))
(defn- compute-arity [& args] (apply (requiring-resolve 'ansatz.core/compute-arity) args))

;; The live-env accessor (mirrors ansatz.core/env). `env` as a fn coexists with the `env/` ns
;; alias above — bare `(env)` reads the var, `env/lookup` uses the alias (the convention core uses).
(defn- env [] (or @ansatz-env (throw (ex-info "Call (ansatz/init!) or (ansatz/load-init!) first" {}))))

;; Verbosity flag stays interned in ansatz.core (the a/*verbose* public handle); read dynamically
;; so a caller's (binding [a/*verbose* …]) is honored across the core→wf call.
(defn- verbose? [] @(requiring-resolve 'ansatz.core/*verbose*))

(clojure.core/defn- replace-rec-calls
  "Walk expr, replacing calls to fn-name with IH applications.
   For fuel-based recursion: fn-name(arg) → ih(arg), no proof args.

   ih-depth: de Bruijn depth of the IH bvar relative to the current position.
   fn-name: Name of the function being defined.
   fn-arity: number of user-visible args the function takes.
   discr-expr: unused in fuel-based approach (kept for API compatibility)."
  [expr fn-name fn-arity ih-depth discr-expr]
  (let [walk
        (fn walk [e depth-offset discr]
          (cond
            ;; Application: check for recursive call or recursor
            (e/app? e)
            (let [[head args] (e/get-app-fn-args e)]
              (cond
                ;; Found a recursive call: replace with IH(arg, proof)
                (and (e/const? head)
                     (= (name/->string (e/const-name head))
                        (name/->string fn-name))
                     (= fn-arity (count args)))
                ;; Fuel-based: replace fn-name(args...) with ih(args...), no proof needed
                (let [walked-args (mapv #(walk % depth-offset discr) args)
                      ih-ref (e/bvar (+ ih-depth depth-offset))]
                  (reduce e/app ih-ref walked-args))

                ;; Detect Nat.rec application and specialize IH per branch
                ;; Generic application: walk children
                :else
                (reduce e/app (walk head depth-offset discr)
                        (mapv #(walk % depth-offset discr) args))))
            ;; Lambda: descend, incrementing depth
            (e/lam? e)
            (e/lam (e/lam-name e) (walk (e/lam-type e) depth-offset discr)
                   (walk (e/lam-body e) (inc depth-offset) discr)
                   (e/lam-info e))
            ;; Forall: descend
            (e/forall? e)
            (e/forall' (e/forall-name e) (walk (e/forall-type e) depth-offset discr)
                       (walk (e/forall-body e) (inc depth-offset) discr)
                       (e/forall-info e))
            ;; Let: descend
            (e/let? e)
            (e/let' (e/let-name e) (walk (e/let-type e) depth-offset discr)
                    (walk (e/let-value e) depth-offset discr)
                    (walk (e/let-body e) (inc depth-offset) discr))
            ;; Leaf nodes
            :else e))]
    (walk expr 0 discr-expr)))

(clojure.core/defn- build-invimage-type
  "Build InvImage (· < ·) measure y x as an Expr.
   y and x are Expr (typically bvars)."
  [env alpha-level alpha measure-lam y x]
  (let [nat (e/const' (name/from-string "Nat") [])
        lt-rel (e/lam "x1" nat
                      (e/lam "x2" nat
                             (e/app* (e/const' (name/from-string "LT.lt") [lvl/zero])
                                     nat (e/const' (name/from-string "instLTNat") [])
                                     (e/bvar 1) (e/bvar 0)) :default) :default)]
    (e/app* (e/const' (name/from-string "InvImage") [alpha-level (lvl/succ lvl/zero)])
            alpha nat lt-rel measure-lam y x)))

(clojure.core/defn- discharge-decreasing-proof
  "Build a proof of measure(rec-arg) < measure(current-arg).
   Uses omega to discharge the obligation.
   param-name, param-type: the function parameter (will be universally quantified).
   measure-form: the raw measure expression (in terms of bvar 0 = param).
   rec-arg-form: the argument to the recursive call (in terms of bvar 0 = param).
   Returns a lambda: λ (param : Type) => proof-of-lt."
  [env param-name param-type measure-ansatz rec-arg-ansatz]
  (let [nat (e/const' (name/from-string "Nat") [])
        ;; Build goal: ∀ (param : Type), measure(rec-arg) < measure(param)
        ;; measure-ansatz and rec-arg-ansatz are in terms of bvar 0 = param
        m-rec (e/app (e/lam (str param-name) param-type measure-ansatz :default) rec-arg-ansatz)
        m-cur measure-ansatz ;; measure(param) where param = bvar 0
        lt-goal (e/app* (e/const' (name/from-string "LT.lt") [lvl/zero])
                        nat (e/const' (name/from-string "instLTNat") [])
                        m-rec m-cur)
        ;; Wrap in forall: ∀ (param : Type), lt-goal
        full-goal (e/forall' (str param-name) param-type lt-goal :default)
        ;; Create proof state, intro param, then omega
        [ps _] (proof/start-proof env full-goal)
        ps (basic/intros ps [(str param-name)])
        ps (omega/omega ps)]
    (when-not (proof/solved? ps)
      (throw (ex-info (str "Cannot prove termination obligation."
                           "\nGoal: " (e/->string env full-goal))
                      {:goal full-goal})))
    ;; Extract gives us: λ (param) => proof-term
    (extract/extract ps)))

;; ============================================================
;; Guard-aware decrease checking (port of lean4's decreasing-goal generation)
;; ============================================================

(clojure.core/defn- wf-subst-syms
  "Replace symbols (and any form that is a key) in `form` per map `m`."
  [form m]
  (cond
    (contains? m form) (get m form)
    (seq? form)        (map #(wf-subst-syms % m) form)
    (vector? form)     (mapv #(wf-subst-syms % m) form)
    :else              form))

(clojure.core/defn- wf-guard-of
  "Map a surface boolean condition + polarity to a Prop guard usable by omega, or nil if the
   condition isn't an arithmetic comparison. Assumes Nat operands (WF measures are Nat).
   (== a b) → (= Nat a b);  (<= a b) → (<= Nat a b);  (< a b) → (< Nat a b);
   (>= a b) → (<= Nat b a);  (> a b) → (< Nat b a).  Negative polarity wraps in (Not …)."
  [cond-form pos?]
  (when (and (seq? cond-form) (= 3 (count cond-form)))
    (let [[op a b] cond-form
          prop (case op
                 == (list '= 'Nat a b)
                 <= (list '<= 'Nat a b)
                 <  (list '< 'Nat a b)
                 >= (list '<= 'Nat b a)
                 >  (list '< 'Nat b a)
                 nil)]
      (when prop (if pos? prop (list 'Not prop))))))

(clojure.core/defn- wf-ctor-pattern
  "Build the `(T.ctor typeargs… fields…)` discriminant pattern for a match branch guard.
   discr-type e.g. Nat or (List Nat); ctor-short e.g. succ; fields e.g. [pred]."
  [discr-type ctor-short fields]
  (let [[thead & targs] (if (seq? discr-type) discr-type [discr-type])
        ctor-full (symbol (str thead "." ctor-short))]
    (if (and (empty? targs) (empty? fields))
      ctor-full
      (cons ctor-full (concat targs fields)))))

(clojure.core/defn- collect-rec-calls-with-guards
  "Walk the surface body, collecting each self-call `(fn-name a0 … a_{n-1})` together with the
   path-condition guards (if/match) and match-bound field binders in scope at that call — the
   ansatz analogue of lean4's recursive-call context (Fix.lean). Returns a vector of
   {:args [arg-forms], :field-binders [[sym type-form] …], :guards [guard-form …]}.
   Match field types currently default to Nat (Stage-1 WF is over Nat measures)."
  [body fn-name n]
  (let [acc (atom [])]
    (letfn [(walk [form guards binders]
              (cond
                (and (seq? form) (= (first form) fn-name) (= n (count (rest form))))
                (do (swap! acc conj {:args (vec (rest form)) :field-binders binders :guards guards})
                    ;; nested self-calls inside this call's arguments carry their own obligations
                    (doseq [sub (rest form)] (walk sub guards binders)))

                (and (seq? form) (= 'if (first form)))
                (let [[_ c t e] form
                      gt (wf-guard-of c true)
                      ge (wf-guard-of c false)]
                  (walk t (if gt (conj guards gt) guards) binders)
                  (walk e (if ge (conj guards ge) guards) binders))

                (and (seq? form) (= 'match (first form)))
                (let [[_ discr discr-type _result & branches] form]
                  (doseq [br branches]
                    (let [[ctor-short x & more] br
                          [fields bbody] (if (vector? x) [x (first more)] [[] x])
                          field-bs (mapv (fn [f] [f 'Nat]) fields)
                          guard (list '= discr-type discr
                                      (wf-ctor-pattern discr-type ctor-short fields))]
                      (walk bbody (conj guards guard) (into binders field-bs)))))

                (and (seq? form) (= 'let (first form)))
                (let [[_ bnds bbody] form]
                  (doseq [v (take-nth 2 (rest bnds))] (walk v guards binders))
                  (walk bbody guards binders))

                (seq? form)
                (doseq [sub (rest form)] (walk sub guards binders))

                :else nil))]
      (walk body [] [])
      @acc)))

(clojure.core/defn- prove-decrease
  "Discharge one rec-call's decrease obligation:
     ∀ params field-binders, guards → measure[params := args] < measure[params]
   via omega (the goal that lean4's decreasing_tactic produces after `clean_wf`). Returns the
   proved theorem name on success; throws (omega) when the measure does not provably decrease."
  [pairs measure-form {:keys [args field-binders guards]}]
  (let [param-syms (mapv first pairs)
        subst (zipmap param-syms args)
        measure-at-args (wf-subst-syms measure-form subst)
        param-bs  (vec (mapcat (fn [[p t _]] [p :- t]) pairs))
        field-bs  (vec (mapcat (fn [[f t]] [f :- t]) field-binders))
        guard-bs  (vec (mapcat (fn [g i] [(symbol (str "hg" i)) :- g]) guards (range)))
        binders   (vec (concat param-bs field-bs guard-bs))
        goal      (list '< 'Nat measure-at-args measure-form)]
    (prove-theorem (gensym "decr") binders goal '[(omega)])))

(clojure.core/defn- prove-decrease-lex
  "Discharge one rec-call's LEXICOGRAPHIC decrease obligation for measure tuple [m1 m2]:
   m1 strictly decreases, or m1 is non-increasing and m2 strictly decreases — exactly the
   Prod.Lex.left / Prod.Lex.right' split the lex encoder will emit. Throws when neither holds."
  [pairs [m1 m2] {:keys [args field-binders guards]}]
  (let [param-syms (mapv first pairs)
        subst (zipmap param-syms args)
        param-bs  (vec (mapcat (fn [[p t _]] [p :- t]) pairs))
        field-bs  (vec (mapcat (fn [[f t]] [f :- t]) field-binders))
        guard-bs  (vec (mapcat (fn [g i] [(symbol (str "hg" i)) :- g]) guards (range)))
        binders   (vec (concat param-bs field-bs guard-bs))
        try-goal  (fn [goal] (try (prove-theorem (gensym "decr") binders goal '[(omega)]) true
                                  (catch Throwable _ false)))
        m1a (wf-subst-syms m1 subst)
        m2a (wf-subst-syms m2 subst)]
    (or (try-goal (list '< 'Nat m1a m1))
        (and (try-goal (list '<= 'Nat m1a m1))
             (try-goal (list '< 'Nat m2a m2)))
        (throw (ex-info "lexicographic measure does not decrease" {:call args :measure [m1 m2]})))))

(clojure.core/defn- wf-candidate-measures
  "GuessLex default measures restricted to a single Nat measure (lexicographic is Stage 3):
   each Nat parameter, then the sum of all Nat parameters."
  [pairs]
  (let [nat-ps (->> pairs (filter (fn [[_ t _]] (= t 'Nat))) (mapv first))]
    (concat (vec nat-ps)
            (when (> (count nat-ps) 1) [(cons '+ nat-ps)]))))

(clojure.core/defn- wf-candidate-lex-measures
  "Lexicographic candidates: ordered pairs of distinct Nat parameters (lean4 GuessLex's
   lexicographic combinations, restricted to 2-tuples)."
  [pairs]
  (let [nat-ps (->> pairs (filter (fn [[_ t _]] (= t 'Nat))) (mapv first))]
    (vec (for [a nat-ps b nat-ps :when (not= a b)] [a b]))))

(clojure.core/defn wf-guess-measure
  "Synthesize a terminating measure for an unannotated recursive function (lean4's GuessLex):
   the first candidate for which EVERY recursive call provably decreases (via omega) — single
   Nat measures first, then lexicographic pairs of parameters (e.g. Ackermann's [m n]).
   Returns the measure form (a vector for lex), or nil. The guess is vetted call-by-call here
   and then re-verified by the encoder's embedded kernel proofs, so a wrong guess cannot slip
   through."
  [pairs body-form fn-name n]
  (let [calls (collect-rec-calls-with-guards body-form fn-name n)
        passes? (fn [check m] (try (doseq [c calls] (check pairs m c)) true
                                   (catch Throwable _ false)))]
    (when (seq calls)
      (or (some (fn [m] (when (passes? prove-decrease m) m))
                (wf-candidate-measures pairs))
          (some (fn [mv] (when (passes? prove-decrease-lex mv) mv))
                (wf-candidate-lex-measures pairs))
          ;; data-typed params: sizeOf measures, unvetted here — the surface gate cannot
          ;; relate sizeOf-atoms through discriminant equalities; the encoder's embedded
          ;; kernel proofs accept or reject the guess. Single data param → (sizeOf p);
          ;; multi-param with every param Nat-or-sized → the parameter-order lexicographic
          ;; tuple (lean4 GuessLex's column order — covers merge-style two-list recursion)
          (let [sized? (fn [t] (and (not= t 'Nat)
                                    (or (and (seq? t) (= 'List (first t)))
                                        (and (symbol? t)
                                             (env/lookup @ansatz-env
                                                         (name/mk-str (name/from-string (str t))
                                                                      "_sizeOf_inst"))))))]
            (cond
              (and (= 1 (count pairs)) (sized? (second (first pairs))))
              (list 'sizeOf (ffirst pairs))

              (and (> (count pairs) 1)
                   (some (fn [[_ t _]] (sized? t)) pairs)
                   (every? (fn [[_ t _]] (or (= t 'Nat) (sized? t))) pairs))
              (mapv (fn [[p t _]] (if (sized? t) (list 'sizeOf p) p)) pairs)))))))

;; ── Stage 1b: lean4-faithful WellFounded.Nat.fix encoding (kernel-ENFORCED termination) ──
;; Port of lean4 mkFix Nat fast path (Fix.lean) + recursive motive refinement
;; (replaceRecApps/MatcherApp.addArg): the match discriminant reaches each decrease proof via the
;; dependent casesOn motive, so the proof is embedded in the term (not a side gate). Single Nat-arg
;; recursion over match/casesOn bodies; non-applicable shapes (if-guards, multi-arg) throw → caller
;; falls back to the (sound) fuel encoding. See memory wf-fix-encoding-mechanism.
(def ^:private wf-fix-counter (atom 9100000))
(defn- wf-fix-fresh [] (swap! wf-fix-counter inc))
(def ^:private wf-fix-NAT (e/const' (name/from-string "Nat") []))

(defn- wf-fix-mk-lt [a b]
  (e/app* (e/const' (name/from-string "LT.lt") [lvl/zero]) wf-fix-NAT
          (e/const' (name/from-string "instLTNat") []) a b))

;; IHType[xref] = (y:dom) → InvImage.{1,1} dom Nat (·<·) measure y xref → Ret
;; dom-ty = the fix's recursion domain (Nat, or Prod Nat Nat when multi-arg packed; both Sort 1).
(defn- wf-fix-ihtype [dom-ty measure-lam ret xref]
  (let [L1 (lvl/succ lvl/zero)
        ltfn (e/lam "n1" wf-fix-NAT (e/lam "n2" wf-fix-NAT (wf-fix-mk-lt (e/bvar 1) (e/bvar 0)) :default) :default)]
    (e/forall' "y" dom-ty
               (e/forall' "_"
                          (e/app* (e/const' (name/from-string "InvImage") [L1 L1]) (e/lift dom-ty 1 0) wf-fix-NAT ltfn measure-lam
                                  (e/bvar 0) (e/lift xref 1 0))
                          (e/lift ret 2 0) :default) :default)))

;; mkLambdaFVars: fvs=[[id name type] …] outer→inner; binder k's type may reference earlier ids.
(defn- wf-fix-mk-lambdas [fvs body]
  (let [ids (mapv first fvs) n (count fvs)]
    (loop [k (dec n) acc (e/abstract-many body ids)]
      (if (< k 0) acc
          (let [[_ nm ty] (nth fvs k)]
            (recur (dec k) (e/lam nm (e/abstract-many ty (subvec ids 0 k)) acc :default)))))))

;; telescope a Pi type to fvars, WHNF at each step (minor types are beta-redexes `motive (ctor …)`).
(defn- wf-fix-tele-open [ty reducer]
  (loop [t (.whnf reducer ty) bs []]
    (if (e/forall? t)
      (let [id (wf-fix-fresh)]
        (recur (.whnf reducer (e/instantiate1 (e/forall-body t) (e/fvar id)))
               (conj bs [id (e/forall-name t) (e/forall-type t)])))
      {:binders bs :body t})))

(defn- wf-fix-ty-of [scope id] (some (fn [[i t]] (when (= i id) t)) scope))

;; kernel-native decrease proof: ∀ scope, measure arg < measure P  (P fully pattern-substituted ⇒
;; closed and true), via omega; returned applied to the scope fvars.
(declare wf-sizeof-normalize)
(defn- wf-fix-decr-proof [env reducer scope measure-lam arg P]
  (let [ids (mapv first scope) tys (mapv second scope)
        ;; whnfCore the measure application: beta + iota, NO delta (lean4's clean_wf normalizes
        ;; the goal the same way; omega's reifier atomizes unreduced redexes, while full whnf
        ;; would delta-unfold Nat.add into recursors omega cannot read). iota is needed for the
        ;; packed multi-arg measure `Prod.rec … (Prod.mk a b)`. The proof still matches the call
        ;; site's `InvImage … arg P` obligation by defeq.
        m-of (fn [t] (wf-sizeof-normalize env (.whnfCore reducer (e/app measure-lam t))))
        prop (wf-fix-mk-lt (m-of arg) (m-of P))
        ;; mkForallFVars: binder i's type may reference earlier scope fvars (e.g. a dite guard
        ;; `h : ¬(x = 0)` mentions x) — abstract each type over ids[0..i), like wf-fix-mk-lambdas.
        gt (loop [i (dec (count ids)) body (e/abstract-many prop ids)]
             (if (< i 0) body
                 (recur (dec i) (e/forall' "s" (e/abstract-many (nth tys i) (subvec ids 0 i)) body :default))))
        [ps _] (proof/start-proof env gt)
        ps (basic/intros ps (mapv #(str "s" %) (range (count ids))))
        ps (reduce run-tactic ps '[(omega)])]
    (when-not (proof/solved? ps)
      (throw (ex-info "wf-fix: decrease not provable" {:goal (e/->string gt)})))
    (extract/verify ps)
    (apply e/app* (extract/extract ps) (mapv e/fvar ids))))

;; The Prod.Lex layer (Prod.Lex, Prod.lex, lexAccessible, Lex.right') panics through the standard
;; init export path only because of unrelated wfParam machinery — exported standalone it is clean,
;; bundled as resources/ansatz/lex-prelude.ndjson.gz. Loaded lazily (idempotent) when a
;; lexicographic :termination-by is first used: each missing declaration is kernel-VERIFIED on
;; admission (verify? true); declarations already in the env are skipped (the export carries its
;; full dependency closure).
(clojure.core/defn- wf-fix-ensure-prelude!
  "Ensure a bundled prelude export is loaded into the global env (idempotent via sentinel)."
  [sentinel resource label]
  (when-not (env/lookup @ansatz-env (name/from-string sentinel))
    (let [res (clojure.java.io/resource resource)
          _ (when-not res (throw (ex-info (str label " prelude not on classpath (" resource ")") {})))
          ndjson (with-open [in (java.util.zip.GZIPInputStream. (.openStream res))] (slurp in))
          decls (:decls (parser/parse-ndjson-string ndjson))
          env'
          (loop [ds (seq decls) env @ansatz-env]
            (if-let [ci (first ds)]
              (cond
                (env/lookup env (.name ^ansatz.kernel.ConstantInfo ci))
                (recur (next ds) env)
                (.isInduct ^ansatz.kernel.ConstantInfo ci)
                (let [{:keys [members rest]} (replay/collect-inductive-bundle ds)
                      [env2 rs] (replay/replay-inductive-bundle env members)]
                  (when-let [err (first (filter #(= :error (:status %)) rs))]
                    (throw (ex-info (str "lex prelude replay failed: " (:name err) " — " (:error err)) {})))
                  (recur rest env2))
                :else
                (let [[env2 r] (replay/replay-one env ci true)]
                  (when (= :error (:status r))
                    (throw (ex-info (str "lex prelude replay failed: " (:name r) " — " (:error r)) {})))
                  (recur (next ds) env2)))
              env))]
      (reset! ansatz-env env')
      (when (verbose?) (println (str "  ✓ " label " prelude loaded (kernel-verified)"))))))

(clojure.core/defn wf-fix-ensure-lex-prelude!
  "Ensure the Prod.Lex prelude is loaded (idempotent)."
  []
  (wf-fix-ensure-prelude! "Prod.Lex.right'" "ansatz/lex-prelude.ndjson.gz" "Prod.Lex"))

(clojure.core/defn wf-fix-ensure-sizeof-prelude!
  "Ensure the SizeOf prelude is loaded (idempotent): the SizeOf class, instSizeOfNat,
   List._sizeOf_inst and the per-constructor sizeOf_spec equations (exports cleanly standalone,
   like the lex prelude; absent from init-medium only due to unrelated export-path machinery)."
  []
  (wf-fix-ensure-prelude! "List._sizeOf_inst" "ansatz/sizeof-prelude.ndjson.gz" "SizeOf"))

;; ── N-ary packing + N-tuple lex helpers (lean4 mkProdElem right-association, GuessLex.lean:754) ──

;; right-nested Prod type over k Nat components: Nat × (Nat × (… × Nat)); k=1 → Nat
;; right-nested Prod of component types (lean4 PackDomain packs the ACTUAL domain types,
;; PackDomain.lean — non-dependent Type-0 telescopes here, so Prod instead of PSigma).
;; An integer k still means the Nat^k tuple (lex measure codomains).
(defn- wf-fix-pack-ty [tys-or-k]
  (let [tys (if (integer? tys-or-k) (vec (repeat tys-or-k wf-fix-NAT)) (vec tys-or-k))]
    (loop [i (- (count tys) 2) ty (peek tys)]
      (if (neg? i) ty
          (recur (dec i) (e/app* (e/const' (name/from-string "Prod") [lvl/zero lvl/zero])
                                 (nth tys i) ty))))))

;; right-nested Prod.mk: (v1, (v2, (…, vk))); 1-arity = Nat-valued components
(defn- wf-fix-pack-vals
  ([vals] (wf-fix-pack-vals (vec (repeat (count vals) wf-fix-NAT)) vals))
  ([tys vals]
   (let [k (count vals) tys (vec tys)]
     (loop [i (- k 2) acc (peek (vec vals))]
       (if (neg? i) acc
           (recur (dec i)
                  (e/app* (e/const' (name/from-string "Prod.mk") [lvl/zero lvl/zero])
                          (nth tys i) (wf-fix-pack-ty (subvec tys (inc i))) (nth vals i) acc)))))))

;; nested Prod.rec wrapper: takes body-n with the n params at bvars n-1..0 and returns a term
;; with ONE loose bvar 0 (the packed param) that destructures it back into the n binders.
;; cod = the motive codomain (closed), cod-lvl its sort level. n=1 → body-n unchanged.
;; Built with fvars + wf-fix-mk-lambdas so de Bruijn bookkeeping is automatic; the nested
;; wrappers are ordinary refinable recursors for the refinement machinery.
(defn- wf-fix-wrap-n
  ([n body-n cod cod-lvl] (wf-fix-wrap-n n (vec (repeat n wf-fix-NAT)) body-n cod cod-lvl))
  ([n tys body-n cod cod-lvl]
   (if (= n 1)
     body-n
     (let [L0 lvl/zero
           tys (vec tys)
           xids (vec (repeatedly n wf-fix-fresh))
           body-f (reduce (fn [b xid] (e/instantiate1 b (e/fvar xid))) body-n (rseq xids))
           build (fn build [p-expr xs tys]
                   (if (= 2 (count xs))
                     (e/app* (e/const' (name/from-string "Prod.rec") [cod-lvl L0 L0])
                             (nth tys 0) (nth tys 1)
                             (e/lam "_p" (wf-fix-pack-ty tys) (e/lift cod 1 0) :default)
                             (wf-fix-mk-lambdas [[(first xs) "a" (nth tys 0)]
                                                 [(second xs) "b" (nth tys 1)]] body-f)
                             p-expr)
                     (let [rest-ty (wf-fix-pack-ty (subvec tys 1))
                           pid (wf-fix-fresh)]
                       (e/app* (e/const' (name/from-string "Prod.rec") [cod-lvl L0 L0])
                               (nth tys 0) rest-ty
                               (e/lam "_p" (wf-fix-pack-ty tys) (e/lift cod 1 0) :default)
                               (wf-fix-mk-lambdas [[(first xs) "a" (nth tys 0)] [pid "_rest" rest-ty]]
                                                  (build (e/fvar pid) (rest xs) (subvec tys 1)))
                               p-expr))))]
       (build (e/bvar 0) xids tys)))))

;; the lexicographic relation over a right-nested k-tuple: Nat.lt for k=1, else
;; Prod.Lex Nat.lt (rel for k-1)
(defn- wf-fix-lex-rel [k]
  (if (= k 1)
    (e/const' (name/from-string "Nat.lt") [])
    (e/app* (e/const' (name/from-string "Prod.Lex") [lvl/zero lvl/zero])
            wf-fix-NAT (wf-fix-pack-ty (dec k))
            (e/const' (name/from-string "Nat.lt") []) (wf-fix-lex-rel (dec k)))))

;; the WellFoundedRelation instance for the k-tuple: Nat.lt_wfRel for k=1, else
;; Prod.lex Nat.lt_wfRel (instance for k-1)
(defn- wf-fix-lex-wfrel [k]
  (if (= k 1)
    (e/const' (name/from-string "Nat.lt_wfRel") [])
    (e/app* (e/const' (name/from-string "Prod.lex") [lvl/zero lvl/zero])
            wf-fix-NAT (wf-fix-pack-ty (dec k))
            (e/const' (name/from-string "Nat.lt_wfRel") []) (wf-fix-lex-wfrel (dec k)))))

;; one omega-proved arithmetic fact, ∀-closed over scope and applied back to the scope fvars
(defn- wf-fix-omega-fact [env scope prop]
  (let [ids (mapv first scope) tys (mapv second scope)
        gt (loop [i (dec (count ids)) body (e/abstract-many prop ids)]
             (if (< i 0) body
                 (recur (dec i) (e/forall' "s" (e/abstract-many (nth tys i) (subvec ids 0 i)) body :default))))
        [ps _] (proof/start-proof env gt)
        ps (basic/intros ps (mapv #(str "s" %) (range (count ids))))
        ps (run-tactic ps '(omega))]
    (when-not (proof/solved? ps)
      (throw (ex-info "wf-fix: omega fact not provable" {:goal (e/->string gt)})))
    (extract/verify ps)
    (apply e/app* (extract/extract ps) (mapv e/fvar ids))))

;; ── sizeOf-based termination over data structures (lean4's default WF measure) ──
;; The default measure for a data-typed parameter is `sizeOf p`, reducing data-structure
;; termination to the existing Nat machinery. Decrease goals contain sizeOf-of-constructor
;; terms that neither whnfCore (no delta) nor whnf (brecOn soup) normalize usefully; we rewrite
;; them via the auto-generated `<ctor>.sizeOf_spec` equations (e.g. sizeOf (cons h t) =
;; 1 + sizeOf h + sizeOf t) so omega sees linear arithmetic over sizeOf-atoms. The omega proof
;; is then DEFEQ to the raw obligation (spec equations hold by iota/beta — validated by
;; check-constant on the bridge), so no Eq transport is needed.

;; synthesize a SizeOf instance for supported types (Nat, List of sized)
(declare wf-fix-tele-open-plain)
(def ^:private wf-sizeof-inst
  "SizeOf instance synthesis — canonical implementation lives with the elaborator (P2)."
  elab/sizeof-inst)

(clojure.core/defn wf-derive-sizeof!
  "Derive the SizeOf machinery for a non-parameterized, non-indexed, Type-valued inductive
   (lean4 auto-derives this for every inductive): `<T>._sizeOf_1` (recursor-based size),
   `<T>._sizeOf_inst : SizeOf T`, and per-constructor `<ctor>.sizeOf_spec` rfl equations —
   the names the sizeOf measure machinery (wf-sizeof-inst / wf-sizeof-normalize) looks up.
   Field contributions: a recursive field uses the recursor's IH; a Nat field is its own
   size; other sized fields contribute SizeOf.sizeOf; unsized fields contribute nothing.
   Best-effort: silently a no-op for unsupported shapes."
  [ind-name-str]
  (try
    (let [ind-name (name/from-string ind-name-str)
          env0 @ansatz-env
          ind-ci (env/lookup env0 ind-name)]
      (when (and ind-ci (.isInduct ind-ci)
                 (zero? (.numParams ind-ci))
                 (let [t (.type ind-ci)]
                   (and (e/sort? t) (= (e/sort-level t) (lvl/succ lvl/zero))))
                 (not (env/lookup env0 (name/mk-str ind-name "_sizeOf_inst"))))
        (wf-fix-ensure-sizeof-prelude!)
        (let [env @ansatz-env
              L1 (lvl/succ lvl/zero)
              T (e/const' ind-name [])
              nat-c wf-fix-NAT
              ctor-names (vec (.ctors (env/lookup env ind-name)))
              rec? (fn [ty] (let [[h2 _] (e/get-app-fn-args ty)]
                              (and (e/const? h2) (= (e/const-name h2) ind-name))))
              nadd (fn [a b] (e/app* (e/const' (name/from-string "Nat.add") []) a b))
              ;; minor for one ctor: λ fields… ihs… => 1 + Σ contributions
              minor-of
              (fn [cn]
                (let [{bs :binders} (wf-fix-tele-open-plain (.type (env/lookup env cn)))
                      ftys (mapv second bs)
                      fids (mapv first bs)
                      rec-idx (vec (keep-indexed (fn [i ty] (when (rec? ty) i)) ftys))
                      ih-ids (mapv (fn [_] (wf-fix-fresh)) rec-idx)
                      contrib (fn [i]
                                (cond
                                  (rec? (nth ftys i))
                                  (e/fvar (nth ih-ids (.indexOf rec-idx i)))
                                  (let [[h2 a2] (e/get-app-fn-args (nth ftys i))]
                                    (and (e/const? h2) (empty? a2)
                                         (= "Nat" (name/->string (e/const-name h2)))))
                                  (e/fvar (nth fids i))
                                  :else
                                  (when-let [inst (wf-sizeof-inst env (nth ftys i))]
                                    (e/app* (e/const' (name/from-string "SizeOf.sizeOf") [L1])
                                            (nth ftys i) inst (e/fvar (nth fids i))))))
                      body (reduce nadd (e/lit-nat 1)
                                   (keep contrib (range (count ftys))))
                      tele (into (mapv (fn [[id ty]] [id "f" ty]) bs)
                                 (mapv (fn [iid] [iid "ih" nat-c]) ih-ids))]
                  (wf-fix-mk-lambdas tele body)))
              motive (e/lam "_t" T nat-c :default)
              sz1-val (apply e/app* (e/const' (name/mk-str ind-name "rec") [L1])
                             (into [motive] (mapv minor-of ctor-names)))
              sz1-name (name/mk-str ind-name "_sizeOf_1")
              sz1-ty (e/forall' "t" T nat-c :default)
              _ (swap! ansatz-env env/check-constant (env/mk-def sz1-name [] sz1-ty sz1-val))
              inst-name (name/mk-str ind-name "_sizeOf_inst")
              inst-ty (e/app (e/const' (name/from-string "SizeOf") [L1]) T)
              inst-val (e/app* (e/const' (name/from-string "SizeOf.mk") [L1]) T
                               (e/const' sz1-name []))
              _ (swap! ansatz-env env/check-constant (env/mk-def inst-name [] inst-ty inst-val))
              inst-c (e/const' inst-name [])
              szof (fn [x] (e/app* (e/const' (name/from-string "SizeOf.sizeOf") [L1]) T inst-c x))]
          ;; per-constructor rfl spec equations: sizeOf (ctor f…) = 1 + Σ contributions,
          ;; with recursive contributions spelled sizeOf (so the normalizer recurses)
          (doseq [cn ctor-names]
            (let [{bs :binders} (wf-fix-tele-open-plain (.type (env/lookup @ansatz-env cn)))
                  ftys (mapv second bs)
                  fids (mapv first bs)
                  contrib (fn [i]
                            (cond
                              (rec? (nth ftys i)) (szof (e/fvar (nth fids i)))
                              (let [[h2 a2] (e/get-app-fn-args (nth ftys i))]
                                (and (e/const? h2) (empty? a2)
                                     (= "Nat" (name/->string (e/const-name h2)))))
                              (e/fvar (nth fids i))
                              :else
                              (when-let [inst (wf-sizeof-inst @ansatz-env (nth ftys i))]
                                (e/app* (e/const' (name/from-string "SizeOf.sizeOf") [L1])
                                        (nth ftys i) inst (e/fvar (nth fids i))))))
                  rhs (reduce nadd (e/lit-nat 1) (keep contrib (range (count ftys))))
                  lhs (szof (apply e/app* (e/const' cn []) (mapv e/fvar fids)))
                  eq-core (e/app* (e/const' (name/from-string "Eq") [L1]) nat-c lhs rhs)
                  pf-core (e/app* (e/const' (name/from-string "Eq.refl") [L1]) nat-c lhs)
                  ids fids
                  wrap (fn [mk core]
                         (loop [k (dec (count bs)) acc (e/abstract-many core ids)]
                           (if (< k 0) acc
                               (recur (dec k) (mk (e/abstract-many (second (nth bs k)) (subvec ids 0 k)) acc)))))
                  eq-ty (wrap (fn [ty b] (e/forall' "f" ty b :default)) eq-core)
                  pf (wrap (fn [ty b] (e/lam "f" ty b :default)) pf-core)]
              (swap! ansatz-env env/check-constant
                     (env/mk-thm (name/mk-str cn "sizeOf_spec") [] eq-ty pf))))
          (when (verbose?)
            (println (str "  ✓ " ind-name-str " SizeOf derived (instance + "
                          (count ctor-names) " spec equations)"))))))
    (catch Throwable t
      (when (verbose?)
        (println (str "  sizeOf derivation skipped for " ind-name-str ": " (.getMessage t)))))))

;; plain (non-reducing) telescope opener — spec lemma types are syntactic foralls
(defn- wf-fix-tele-open-plain [ty]
  (loop [t ty bs []]
    (if (e/forall? t)
      (let [id (wf-fix-fresh)]
        (recur (e/instantiate1 (e/forall-body t) (e/fvar id)) (conj bs [id (e/forall-type t)])))
      {:binders bs :body t})))

;; first-order match of a pattern (holes = fvar ids) against a term; Expr equality is structural
(defn- wf-fo-match [pat term holes subst]
  (cond
    (and (e/fvar? pat) (contains? holes (e/fvar-id pat)))
    (let [id (e/fvar-id pat)]
      (if-let [prev (get subst id)]
        (when (= prev term) subst)
        (assoc subst id term)))
    (e/app? pat) (when (e/app? term)
                   (when-let [s (wf-fo-match (e/app-fn pat) (e/app-fn term) holes subst)]
                     (wf-fo-match (e/app-arg pat) (e/app-arg term) holes s)))
    :else (when (= pat term) subst)))

;; rewrite sizeOf-of-constructor subterms via the constructors' sizeOf_spec equations, and
;; collapse sizeOf over instSizeOfNat to its argument (defeq). Fixpoint over nesting.
(defn- wf-sizeof-normalize [env t]
  (letfn [(norm [t]
            (let [[h as] (e/get-app-fn-args t)]
              (or
               (when (and (e/const? h) (= "SizeOf.sizeOf" (name/->string (e/const-name h)))
                          (= 3 (count as)))
                 (let [[_T inst X] as
                       [xh _] (e/get-app-fn-args X)]
                   (cond
                     ;; sizeOf over the Nat instance is the identity (defeq)
                     (and (e/const? inst) (= "instSizeOfNat" (name/->string (e/const-name inst))))
                     (norm X)
                     ;; constructor-applied scrutinee: rewrite via <ctor>.sizeOf_spec
                     (e/const? xh)
                     (when-let [spec (env/lookup env (name/mk-str (e/const-name xh) "sizeOf_spec"))]
                       ;; instantiate the spec's universe params at level 0 (our data preludes are
                       ;; monomorphic at Sort 1) so first-order matching sees concrete levels
                       (let [lp (vec (.levelParams spec))
                             spec-ty (e/instantiate-level-params (.type spec)
                                                                 (zipmap lp (repeat lvl/zero)))
                             {bs :binders body :body} (wf-fix-tele-open-plain spec-ty)
                             holes (set (map first bs))
                             [eqh eqargs] (e/get-app-fn-args body)]
                         (when (and (e/const? eqh) (= "Eq" (name/->string (e/const-name eqh)))
                                    (= 3 (count eqargs)))
                           (when-let [subst (wf-fo-match (nth eqargs 1) t holes {})]
                             (when (= (count subst) (count bs))
                               (norm (reduce (fn [r [id v]] (e/instantiate1 (e/abstract1 r id) v))
                                             (nth eqargs 2) subst)))))))
                     :else nil)))
               ;; OfNat.ofNat Nat n inst → the literal (defeq) — the spec RHS spells its
               ;; constants this way and omega must see them as numerals, not atoms
               (when (and (e/const? h) (= "OfNat.ofNat" (name/->string (e/const-name h)))
                          (= 3 (count as))
                          (e/lit-nat? (nth as 1))
                          (let [[th _] (e/get-app-fn-args (nth as 0))]
                            (and (e/const? th) (= "Nat" (name/->string (e/const-name th))))))
                 (nth as 1))
               ;; default: rebuild with normalized subterms
               (cond
                 (seq as) (apply e/app* (norm h) (mapv norm as))
                 (e/lam? t) (e/lam (e/lam-name t) (norm (e/lam-type t)) (norm (e/lam-body t)) (e/lam-info t))
                 :else t))))]
    (norm t)))

;; lexicographic decrease proof (lean4 decreasing_tactic peel, WFTactics.lean:59), constructed
;; DIRECTLY and RECURSIVELY over the right-nested k-tuple: `Prod.Lex.left` when the head measure
;; strictly drops, else `Prod.Lex.right'` (the <=-variant of Lex.right, WF.lean:324 — subsumes the
;; equal-first-component case) wrapping the proof for the tail tuple. The omega base facts are
;; stated in the LT.lt/LE.le instance spelling (what omega certifies); the constructors expect
;; Nat.lt — defeq (instLTNat unfolds to Nat.lt), check-constant arbitrates.
(defn- wf-fix-decr-proof-lexn [env reducer scope k tup-lam arg P]
  (let [t-of (fn [t] (wf-sizeof-normalize env (.whnfCore reducer (e/app tup-lam t))))
        nat-le (fn [a b] (e/app* (e/const' (name/from-string "LE.le") [lvl/zero]) wf-fix-NAT
                                 (e/const' (name/from-string "instLENat") []) a b))
        unmk (fn [t] (let [[h as] (e/get-app-fn-args t)]
                       (when (and (e/const? h) (= "Prod.mk" (name/->string (e/const-name h)))
                                  (= 4 (count as)))
                         [(nth as 2) (nth as 3)])))
        dec-lex (fn dec-lex [j A Pt]
                  (if (= j 1)
                    ;; base: a single Nat measure — strict decrease via omega
                    (wf-fix-omega-fact env scope (wf-fix-mk-lt A Pt))
                    (let [[A1 Arest] (or (unmk A) (throw (ex-info "wf-fix: lex measure tuple did not reduce" {})))
                          [P1 Prest] (or (unmk Pt) (throw (ex-info "wf-fix: lex measure tuple did not reduce" {})))
                          rest-ty (wf-fix-pack-ty (dec j))
                          rest-rel (wf-fix-lex-rel (dec j))]
                      (try
                        ;; head component strictly decreases
                        (let [h (wf-fix-omega-fact env scope (wf-fix-mk-lt A1 P1))]
                          (e/app* (e/const' (name/from-string "Prod.Lex.left") [lvl/zero lvl/zero])
                                  wf-fix-NAT rest-ty (e/const' (name/from-string "Nat.lt") []) rest-rel
                                  A1 Arest P1 Prest h))
                        (catch Exception _
                          ;; head non-increasing, tail decreases lexicographically
                          (let [h1 (wf-fix-omega-fact env scope (nat-le A1 P1))
                                h2 (dec-lex (dec j) Arest Prest)]
                            (e/app* (e/const' (name/from-string "Prod.Lex.right'") [lvl/zero])
                                    rest-ty rest-rel P1 Prest A1 Arest h1 h2)))))))]
    (dec-lex k (t-of arg) (t-of P))))

;; is this app a recursor whose major is a free fvar occurring in P? → refinable.
(defn- wf-fix-refinable? [env h as P]
  (and (e/const? h)
       (.endsWith (name/->string (e/const-name h)) ".rec")
       (env/lookup env (e/const-name h))
       (let [rci (env/lookup env (e/const-name h))]
         (and (= (count as) (+ (.numParams rci) 1 (.numMinors rci) (.numIndices rci) 1))
              (e/fvar? (last as))
              (let [vid (e/fvar-id (last as))
                    fvids (atom #{})]
                ((fn go [x] (cond (e/fvar? x) (swap! fvids conj (e/fvar-id x))
                                  (e/app? x) (do (go (e/app-fn x)) (go (e/app-arg x)))
                                  (e/lam? x) (do (go (e/lam-type x)) (go (e/lam-body x)))
                                  (e/forall? x) (do (go (e/forall-type x)) (go (e/forall-body x)))
                                  :else nil)) P)
                (contains? @fvids vid))))))

(declare wf-fix-refine)

;; refine recursor (R.rec params motive minors… major) to thread ih-fvar, exposing each branch's
;; pattern via the dependent motive. Returns the refined recursor APPLIED to ih-fvar.
(defn- wf-fix-refine-rec [env callspec ret reducer rec-head call-args ih-fvar P scope]
  (let [rec-name (e/const-name rec-head)
        rci (env/lookup env rec-name) np (.numParams rci) nminors (.numMinors rci)
        params (vec (take np call-args))
        major (last call-args) v-id (e/fvar-id major)
        T (wf-fix-ty-of scope v-id)
        tc (ansatz.kernel.TypeChecker. env) _ (.setFuel tc (long config/*default-fuel*))
        ind-name (let [s (name/->string rec-name)] (name/from-string (subs s 0 (- (count s) 4))))
        ctor-names (vec (.ctors (env/lookup env ind-name)))
        P-abs (e/abstract-many P [v-id])
        inner-motive (e/lam "v" T (e/forall' "_" ((:ihtype callspec) P-abs) (e/lift ret 1 0) :default) :default)
        rec-applied (apply e/app* (e/const' rec-name (vec (e/const-levels rec-head))) (conj params inner-motive))
        tb (:binders (wf-fix-tele-open (.inferType tc rec-applied) reducer))
        minor-types (mapv (fn [i] (nth (mapv (fn [[_ _ t]] t) tb) i)) (range nminors))
        process (fn [mi]
                  (let [ctor-name (nth ctor-names mi) nf (.numFields (env/lookup env ctor-name))
                        bs (:binders (wf-fix-tele-open (nth minor-types mi) reducer)) bid (mapv first bs)
                        field-ids (vec (take nf bid))
                        field-tys (mapv (fn [i] (nth (mapv (fn [[_ _ t]] t) bs) i)) (range nf))
                        fs-id (last bid)
                        ctor-pat (apply e/app* (e/const' ctor-name (vec (rest (e/const-levels rec-head))))
                                        (into params (mapv e/fvar field-ids)))
                        Pc (e/instantiate1 (e/abstract-many P [v-id]) ctor-pat)
                        scope2 (into scope (mapv vector field-ids field-tys))
                        orig (nth call-args (+ np 1 mi)) nopen (dec (count bs))
                        obody (loop [b orig i 0] (if (and (< i nopen) (e/lam? b))
                                                   (recur (e/instantiate1 (e/lam-body b) (e/fvar (nth bid i))) (inc i)) b))
                        refined (wf-fix-refine env callspec ret reducer obody (e/fvar fs-id) Pc scope2)]
                    (wf-fix-mk-lambdas bs refined)))
        minors' (mapv process (range nminors))
        refined-rec (apply e/app* (e/const' rec-name (vec (e/const-levels rec-head))) (-> (into params [inner-motive]) (into minors') (conj major)))]
    (e/app refined-rec ih-fvar)))

;; descend a branch body: rewrite self-calls to (ih arg proof), refine nested recursors, open lambdas.
;; (The Bool.rec→dite WF conversion that lived here is gone: surface `if` over comparisons
;; now emits dite directly — P5b of the elaborator unification — so branch lambdas carry the
;; guard and the generic descent below collects it into the decrease-proof scope.)

(defn- wf-fix-refine [env callspec ret reducer body ih-fvar P scope]
  (let [[h as] (e/get-app-fn-args body)]
    (cond
      (and (e/const? h) (= (e/const-name h) (:cname callspec)) (= (:arity callspec) (count as)))
      (let [args' (mapv #(wf-fix-refine env callspec ret reducer % ih-fvar P scope) as)
            arg ((:pack callspec) args')]
        (e/app* ih-fvar arg ((:decr callspec) env reducer scope arg P)))
      (wf-fix-refinable? env h as P)
      (wf-fix-refine-rec env callspec ret reducer h as ih-fvar P scope)
      (seq as)
      (apply e/app* (wf-fix-refine env callspec ret reducer h ih-fvar P scope)
             (mapv #(wf-fix-refine env callspec ret reducer % ih-fvar P scope) as))
      (e/lam? body)
      (let [id (wf-fix-fresh) bt (e/lam-type body)
            inner (wf-fix-refine env callspec ret reducer
                                 (e/instantiate1 (e/lam-body body) (e/fvar id)) ih-fvar P (conj scope [id bt]))]
        (e/lam (e/lam-name body) bt (e/abstract-many inner [id]) (e/lam-info body)))
      :else body)))

;; ── Stage 1b-D: defining equations for wf-fix functions (lean4 WF/Unfold.lean rwFixEq) ──
;; A wf-fix definition does NOT unfold definitionally on a symbolic argument (WellFounded.fix is
;; stuck on the Acc proof), so simp needs explicit equations. Per lean4: one WellFounded.Nat.fix_eq
;; instance proves `f x = Ffn x (fun y _ => f y)`; we state per-LEAF equations (fully-composed
;; constructor patterns, e.g. `f (succ (succ k)) = succ (f k)`) so every discriminant in the
;; refined casesOn is constructor-headed and the stated RHS is defeq to fix_eq's RHS by iota/beta
;; alone (the decrease proofs are beta-dropped by `fun y _ => f y`). The bare fix_eq instance IS
;; the proof; check-constant carries the defeq burden. Leaf splitting is REQUIRED, not cosmetic:
;; a still-symbolic nested match is stuck with a refined motive on one side and the original on
;; the other — not defeq (this is why lean4 has eq_N splitting / the matcher arg_pusher).

;; rhs builder for the per-leaf equations: the original body already carries the surface
;; spelling (dite for comparison ifs since P5b), so this is a plain pass-through; kept as a
;; function for future spelling normalizations.
(defn- wf-fix-eq-rhs [_env body] body)

;; leaf enumerator: split each case-split-on-a-pattern-var per constructor, composing the
;; pattern; stop at dites/leaves. fields = the ∀-binders of the equation ([[id type] …]);
;; a split consumes the matched var and appends the constructor's fields.
(defn- wf-fix-eq-leaves [env tc reducer body pattern fields]
  (let [[h as] (e/get-app-fn-args body)]
    (if (wf-fix-refinable? env h as pattern)
      (let [rec-name (e/const-name h)
            rci (env/lookup env rec-name) np (.numParams rci) nminors (.numMinors rci)
            params (vec (take np as))
            major (last as) v-id (e/fvar-id major)
            ind-name (let [s (name/->string rec-name)] (name/from-string (subs s 0 (- (count s) 4))))
            ctor-names (vec (.ctors (env/lookup env ind-name)))
            rec-applied (apply e/app* (e/const' rec-name (vec (e/const-levels h))) (conj params (nth as np)))
            tb (:binders (wf-fix-tele-open (.inferType tc rec-applied) reducer))
            minor-types (mapv (fn [i] (nth (mapv (fn [[_ _ t]] t) tb) i)) (range nminors))]
        (vec (mapcat
              (fn [mi]
                (let [ctor-name (nth ctor-names mi) nf (.numFields (env/lookup env ctor-name))
                      bs (:binders (wf-fix-tele-open (nth minor-types mi) reducer)) bid (mapv first bs)
                      field-ids (vec (take nf bid))
                      field-tys (mapv (fn [i] (nth (mapv (fn [[_ _ t]] t) bs) i)) (range nf))
                      ctor-pat (apply e/app* (e/const' ctor-name (vec (rest (e/const-levels h))))
                                      (into params (mapv e/fvar field-ids)))
                      pattern' (e/instantiate1 (e/abstract-many pattern [v-id]) ctor-pat)
                      fields' (into (vec (remove (fn [[id _]] (= id v-id)) fields))
                                    (mapv vector field-ids field-tys))
                      ;; open the ORIGINAL minor: nf fields + structural-ih binders (unused in
                      ;; WF bodies — recursive calls reference the function constant)
                      orig (nth as (+ np 1 mi))
                      obody (loop [b orig i 0] (if (and (< i (count bs)) (e/lam? b))
                                                 (recur (e/instantiate1 (e/lam-body b) (e/fvar (nth bid i))) (inc i)) b))]
                  (wf-fix-eq-leaves env tc reducer obody pattern' fields')))
              (range nminors))))
      [{:fields fields :pattern pattern :rhs (wf-fix-eq-rhs env body)}])))

;; Build the (unapplied) fix term: param-type → ret. raw-body = the compiled body with the
;; (possibly packed) recursion param at bvar 0 (any shape: match/casesOn, if/Bool.rec, or mixed —
;; the general refine dispatcher routes each; for multi-arg the caller wraps the body in Prod.rec
;; and the callspec packs recursive-call args). The callspec carries the relation specifics:
;;   :ihtype  (fn [xref] IHType[xref])  — the IH function type over the recursion domain
;;   :decr    (fn [env reducer scope arg P] proof) — one decrease proof
;;   :fix     (fn [ret-level Ffn] fix-term) — wraps the refined functional in the fix combinator
;;            (WellFounded.Nat.fix for a single Nat measure, WellFounded.fix for lexicographic)
;; Throws if a decrease obligation is unprovable.
(defn- wf-fix-encode [env callspec raw-body ret param-type]
  (let [tc (doto (ansatz.kernel.TypeChecker. env) (.setFuel (long config/*default-fuel*)))
        reducer (.getReducer tc)
        ret-sort (.inferType tc ret)
        ret-level (if (e/sort? ret-sort) (e/sort-level ret-sort) (lvl/succ lvl/zero))
        Xid (wf-fix-fresh) Fvid (wf-fix-fresh) X (e/fvar Xid)
        Fty ((:ihtype callspec) X) Fv (e/fvar Fvid)
        rawX (e/instantiate1 raw-body X)
        body' (wf-fix-refine env callspec ret reducer rawX Fv X [[Xid param-type]])
        Ffn (wf-fix-mk-lambdas [[Xid "x" param-type] [Fvid "F" Fty]] body')]
    ((:fix callspec) ret-level Ffn)))

(clojure.core/defn elab-signature
  "fvar-first elaboration of an a/defn signature (P1 of the elaborator unification): each
   parameter type elaborates via surface/elaborate with the EARLIER params in scope as fvars
   (supporting dependent telescopes), the return type with all params in scope; the ∀-telescope
   is rebuilt by abstraction (mkForallFVars). Returns {:param-types [closed Expr …]
   :ret-ansatz Expr :type-ansatz Expr}. param-types/ret are fvar-free for the non-dependent
   signatures the embedding produces (same contract the bvar path had)."
  [env pairs ret-type-form]
  (let [n (count pairs)
        ids (vec (repeatedly n wf-fix-fresh))
        [lctx ptys]
        (loop [i 0 lctx {} acc []]
          (if (= i n) [lctx acc]
              (let [[pn pt _] (nth pairs i)
                    ty (elab/elaborate-in-context env lctx pt)
                    lctx' (assoc lctx (nth ids i) {:name (str pn) :type ty :tag :local})]
                (recur (inc i) lctx' (conj acc ty)))))
        ret (elab/elaborate-in-context env lctx ret-type-form)
        type-ansatz (loop [i (dec n) body (e/abstract-many ret ids)]
                      (if (< i 0) body
                          (let [[pn _ binfo] (nth pairs i)]
                            (recur (dec i)
                                   (e/forall' (str pn)
                                              (e/abstract-many (nth ptys i) (subvec ids 0 i))
                                              body (or binfo :default))))))]
    {:param-types ptys :ret-ansatz ret :type-ansatz type-ansatz}))

(clojure.core/defn define-verified-wf
  "Define a verified function with well-founded recursion.
   Uses WellFounded.Nat.fix from the environment.
   Returns compiled Clojure fn."
  [fn-name params ret-type-form body-form measure-form]
  (let [env (env)
        pairs (parse-params params)
        n (count pairs)
        ;; lean4's termination_by interprets a measure through its TYPE's
        ;; WellFoundedRelation — for a data-typed parameter that is sizeOf. So
        ;; `:termination-by m` with `m : Value` means `(sizeOf m)`; rewrite the
        ;; measure form (scalar or inside a lex vector) before the gate/encoder.
        sized-param? (fn [msym]
                       (some (fn [[p t _]]
                               (and (= p msym) (not= t 'Nat)
                                    (or (and (seq? t) (= 'List (first t)))
                                        (and (symbol? t)
                                             (env/lookup env (name/mk-str (name/from-string (str t))
                                                                          "_sizeOf_inst"))))))
                             pairs))
        lift-measure (fn [mf] (if (and (symbol? mf) (sized-param? mf)) (list 'sizeOf mf) mf))
        measure-form (if (vector? measure-form)
                       (mapv lift-measure measure-form)
                       (lift-measure measure-form))

        ;; Guard-aware termination check (lean4's decreasing goals; replaces fuel-trust): every
        ;; recursive call must provably decrease the measure under its path-condition guards.
        ;; The fuel encoding below is total either way; this gate is what makes :termination-by an
        ;; honest proof — a non-terminating definition (measure that doesn't decrease) is rejected.
        ;; A lexicographic (vector) measure skips this scalar gate: its only encoding is the
        ;; WellFounded.fix term below, whose embedded Prod.Lex proofs ARE the termination check.
        _ (when-not (or (vector? measure-form)
                        ((fn has-sz? [f] (cond (and (seq? f) (= 'sizeOf (first f))) true
                                               (or (seq? f) (vector? f)) (boolean (some has-sz? f))
                                               :else false))
                         measure-form))
            (doseq [c (collect-rec-calls-with-guards body-form fn-name n)]
              (try (prove-decrease pairs measure-form c)
                   (catch Throwable e
                     (throw (ex-info (str "Cannot prove `" fn-name "` terminates: measure `"
                                          measure-form "` is not provably decreasing on the recursive "
                                          "call with args " (:args c)
                                          (when (seq (:guards c)) (str " under guards " (:guards c)))
                                          ". Adjust :termination-by, or use ^:partial.")
                                     {:fn fn-name :kind :termination-decrease-failed :call c}))))))

        ;; Build the function type: ∀ params → ret-type (fvar-first, elab-signature)
        {:keys [param-types ret-ansatz type-ansatz]} (elab-signature env pairs ret-type-form)
        cname (name/from-string (str fn-name))

        ;; Fork env and add temporary axiom for self-reference
        tmp-ci (env/mk-axiom cname [] type-ansatz)
        tmp-env (env/add-constant (env/fork env) tmp-ci)

        ;; Compile body fvar-first (consistent with define-verified) on the forked env —
        ;; self-calls resolve to the axiom const; replace-rec-calls rewrites them to the IH below.
        body-ansatz (binding [surface-match/*use-cases-on?* true]
                      (build-telescope-fvar tmp-env pairs ret-type-form body-form))

        ;; Peel all outer lambdas to get the raw body
        raw-body (loop [e body-ansatz i 0]
                   (if (and (< i n) (e/lam? e))
                     (recur (e/lam-body e) (inc i))
                     e))

        ;; Compile measure expression(s) FVAR-FIRST (P2 of the elaborator unification): params
        ;; in scope as typed fvars, abstracted back to the bvar layout the encoders expect
        ;; (params at bvars n-1..0). A vector measure form is a LEXICOGRAPHIC tuple; the scalar
        ;; measure-ansatz is then only fuel-path scaffolding (unused — lex never takes fuel).
        ;; A sizeOf-mentioning measure needs the SizeOf prelude loaded BEFORE elaboration.
        nat (e/const' (name/from-string "Nat") [])
        has-sizeof? ((fn has-sz? [f] (cond (and (seq? f) (= 'sizeOf (first f))) true
                                           (or (seq? f) (vector? f)) (boolean (some has-sz? f))
                                           :else false))
                     measure-form)
        _ (when has-sizeof? (wf-fix-ensure-sizeof-prelude!))
        measure-env (if has-sizeof? @ansatz-env env)
        elab-measure (fn [mform]
                       (let [ids (vec (repeatedly n wf-fix-fresh))
                             lctx (into {} (map (fn [id [pn _ _] pt]
                                                  [id {:name (str pn) :type pt :tag :local}])
                                                ids pairs param-types))
                             m* (elab/elaborate-in-context measure-env lctx mform)]
                         (e/abstract-many m* ids)))
        lex-measures (when (vector? measure-form) (mapv elab-measure measure-form))
        measure-ansatz (elab-measure (if (vector? measure-form) (first measure-form) measure-form))

        ;; Universe level for return type
        tc-tmp (ansatz.kernel.TypeChecker. env)
        _ (.setFuel tc-tmp (long config/*default-fuel*))
        ret-sort (.inferType tc-tmp ret-ansatz)
        ret-level (if (e/sort? ret-sort) (e/sort-level ret-sort) (lvl/succ lvl/zero))

        ;; Fuel-based approach: Nat.rec on fuel (matching Lean 4's kernel-level pattern).
        ;; For n params: step = λ fuel ih p1 p2 ... pn => body[fn(a1..an) → ih(a1..an)]
        ;; raw-body has params at bvar 0..n-1 (p1=bvar 0, p2=bvar 1, etc.)
        ;; In the step body: pn=bvar 0, ..., p1=bvar n-1, ih=bvar n, fuel=bvar n+1
        ;; Since raw-body's bvar layout matches the step's param layout, no lifting needed.
        ;; ih is at depth n relative to the step body.
        replaced-body (replace-rec-calls raw-body cname n n nil)

        ;; Build multi-arg arrow type: p1 → p2 → ... → ret
        arrow-type (loop [i (dec n) ty ret-ansatz]
                     (if (< i 0) ty
                         (recur (dec i)
                                (e/forall' (str (first (nth pairs i)))
                                           (nth param-types i) ty :default))))

        ;; Build Nat.rec components
        nat-rec (e/const' (name/from-string "Nat.rec") [ret-level])
        motive-nr (e/lam "fuel" nat arrow-type :default)
        ;; base: λ p1 p2 ... pn => default (unreachable with correct fuel)
        ;; Use type-appropriate default value
        default-val (let [[rh ra] (e/get-app-fn-args ret-ansatz)]
                      (cond
                        ;; Nat → 0
                        (and (e/const? ret-ansatz)
                             (= "Nat" (name/->string (e/const-name ret-ansatz))))
                        (e/lit-nat 0)
                        ;; List α → List.nil α
                        (and (e/const? rh)
                             (= "List" (name/->string (e/const-name rh))))
                        (e/app (e/const' (name/from-string "List.nil") [lvl/zero])
                               (first ra))
                        ;; Bool → false
                        (and (e/const? ret-ansatz)
                             (= "Bool" (name/->string (e/const-name ret-ansatz))))
                        (e/const' (name/from-string "Bool.false") [])
                        ;; Fallback: try Inhabited.default
                        :else
                        (let [inh-inst (try-synthesize-instance
                                        env (e/app (e/const' (name/from-string "Inhabited") [(lvl/succ lvl/zero)])
                                                   ret-ansatz))]
                          (if inh-inst
                            (e/app* (e/const' (name/from-string "Inhabited.default") [(lvl/succ lvl/zero)])
                                    ret-ansatz inh-inst)
                            ;; Last resort: use lit-nat 0 (may cause type error if reached)
                            (e/lit-nat 0)))))
        base-nr (loop [i (dec n) body default-val]
                  (if (< i 0) body
                      (recur (dec i)
                             (e/lam (str (first (nth pairs i)))
                                    (nth param-types i) body :default))))
        ;; step: λ fuel ih p1 p2 ... pn => replaced-body
        step-nr (e/lam "fuel" nat
                       (e/lam "ih" arrow-type
                              (loop [i (dec n) body replaced-body]
                                (if (< i 0) body
                                    (recur (dec i)
                                           (e/lam (str (first (nth pairs i)))
                                                  (nth param-types i) body :default))))
                              :default) :default)
        ;; fuel = Nat.succ (measure(params)) where params are bvar 0..n-1 in the outer lambda
        fuel-expr (e/app (e/const' (name/from-string "Nat.succ") []) measure-ansatz)
        ;; Full: λ p1 ... pn => (Nat.rec motive base step fuel) p1 ... pn
        ;; Build inner: apply Nat.rec result to all params
        inner-app (reduce (fn [f i] (e/app f (e/bvar (- n 1 i))))
                          (e/app* nat-rec motive-nr base-nr step-nr fuel-expr)
                          (range n))
        ;; Wrap in outer lambdas
        final-body (loop [i (dec n) body inner-app]
                     (if (< i 0) body
                         (recur (dec i)
                                (e/lam (str (first (nth pairs i)))
                                       (nth param-types i) body :default))))

        ;; Stage 1b: prefer the lean4-faithful WellFounded.Nat.fix encoding (kernel-ENFORCED
        ;; termination — the decrease proof lives in the term). Single Nat arg directly; two Nat
        ;; args via Prod packing (lean4 packs through PSigma.casesOn, Fix.lean:183 — the packing
        ;; wrapper is just another refinable recursor for our refine-rec). Bodies may be
        ;; match/casesOn, if/Bool.rec (converted to dite, exposing the guard like lean4's
        ;; macro_inline ite), or mixed. On any unsupported shape or check failure, fall back to
        ;; the (sound, gate-checked) fuel encoding above.
        all-nat? (every? (fn [pt] (and (e/const? pt) (= "Nat" (name/->string (e/const-name pt)))))
                         param-types)
        nat-c (e/const' (name/from-string "Nat") [])
        L0 lvl/zero
        L1 (lvl/succ lvl/zero)
        ;; relation spec for a single Nat measure → WellFounded.Nat.fix
        mk-measure-relspec
        (fn [dom-ty m-lam]
          {:ihtype (fn [xref] (wf-fix-ihtype dom-ty m-lam ret-ansatz xref))
           :decr (fn [env2 reducer scope arg P] (wf-fix-decr-proof env2 reducer scope m-lam arg P))
           :fix (fn [ret-level Ffn]
                  (apply e/app* (e/const' (name/from-string "WellFounded.Nat.fix") [L1 ret-level])
                         [dom-ty (e/lam "x" dom-ty (e/lift ret-ansatz 1 0) :default) m-lam Ffn]))})
        ;; relation spec for a lexicographic k-tuple of Nat measures → general WellFounded.fix
        ;; with rel = fun y x => Prod.Lex Nat.lt (…) (tup y) (tup x) (right-nested for k>2) and
        ;; the wf proof projected from invImage tup (Prod.lex Nat.lt_wfRel (…)) — defeq to the
        ;; stated relation (lean4 Rel.lean:57 builds exactly this invImage; we state the relation
        ;; beta-expanded so each call-site obligation whnfs to a bare Prod.Lex goal).
        mk-lexn-relspec
        (fn [dom-ty tup-lam k]
          (let [tup-ty (wf-fix-pack-ty k)
                rel-k (wf-fix-lex-rel k)
                lexr (fn [a b] (e/app* rel-k a b))
                rel-lam (e/lam "y" dom-ty
                               (e/lam "x" (e/lift dom-ty 1 0)
                                      (lexr (e/app tup-lam (e/bvar 1)) (e/app tup-lam (e/bvar 0))) :default) :default)
                wfRel (e/app* (e/const' (name/from-string "invImage") [L1 L1]) dom-ty tup-ty tup-lam
                              (wf-fix-lex-wfrel k))
                hwf (e/proj (name/from-string "WellFoundedRelation") 1 wfRel)]
            {:ihtype (fn [xref]
                       (e/forall' "y" dom-ty
                                  (e/forall' "_"
                                             (lexr (e/app tup-lam (e/bvar 0)) (e/app tup-lam (e/lift xref 1 0)))
                                             (e/lift ret-ansatz 2 0) :default) :default))
             :decr (fn [env2 reducer scope arg P] (wf-fix-decr-proof-lexn env2 reducer scope k tup-lam arg P))
             :fix (fn [ret-level Ffn]
                    (apply e/app* (e/const' (name/from-string "WellFounded.fix") [L1 ret-level])
                           [dom-ty (e/lam "x" dom-ty (e/lift ret-ansatz 1 0) :default) rel-lam hwf Ffn]))}))
        lex? (vector? measure-form)
        ;; a sizeOf measure cannot be vetted by the surface gate (omega cannot relate
        ;; sizeOf-atoms through a discriminant equality) — like lex, the encoder's embedded
        ;; proofs ARE the termination check, and there is no honest fuel fallback.
        sizeof-measure? (boolean
                         ((fn has-sz? [f] (cond (and (seq? f) (= 'sizeOf (first f))) true
                                                (or (seq? f) (vector? f)) (boolean (some has-sz? f))
                                                :else false))
                          measure-form))
        sized1? (and (= n 1) (some? (wf-sizeof-inst env (nth param-types 0))))
        ;; n>=2 over sized (or Nat) domains: pack the ACTUAL param types (lean4 PackDomain) —
        ;; this is what admits merge-style two-list recursion with a sizeOf sum/lex measure
        sizedN? (and (> n 1)
                     (every? (fn [pt] (or (and (e/const? pt)
                                               (= "Nat" (name/->string (e/const-name pt))))
                                          (some? (wf-sizeof-inst @ansatz-env pt))))
                             param-types))
        fix-info
        (when (or all-nat? sized1? sizedN?)
          (try
            (let [packed-ty (if (= n 1) (nth param-types 0) (wf-fix-pack-ty param-types))
                  tc0 (doto (ansatz.kernel.TypeChecker. env) (.setFuel (long config/*default-fuel*)))
                  rs (.inferType tc0 ret-ansatz)
                  rv (if (e/sort? rs) (e/sort-level rs) L1)
                  ;; n=1: the body/measure already take the single param at bvar 0.
                  ;; n>=2: wrap in nested Prod.rec over the packed param (bvar 0 of the wrapper) —
                  ;; the minors restore the n-param bvar layout, and each nested wrapper is an
                  ;; ordinary refinable recursor for the refinement machinery.
                  wrapped (wf-fix-wrap-n n param-types raw-body ret-ansatz rv)
                  pack (fn [args] (wf-fix-pack-vals param-types (vec args)))
                  m-lam-of (fn [body] (if (= n 1)
                                        (e/lam (str (first (nth pairs 0))) (nth param-types 0) body :default)
                                        (e/lam "p" packed-ty (wf-fix-wrap-n n param-types body wf-fix-NAT L1) :default)))
                  relspec (if lex?
                            (let [_ (wf-fix-ensure-lex-prelude!)
                                  k (count lex-measures)
                                  tup-body (wf-fix-pack-vals lex-measures)
                                  tup-lam (if (= n 1)
                                            (e/lam (str (first (nth pairs 0))) (nth param-types 0) tup-body :default)
                                            (e/lam "p" packed-ty (wf-fix-wrap-n n param-types tup-body (wf-fix-pack-ty k) L1) :default))]
                              (mk-lexn-relspec packed-ty tup-lam k))
                            (mk-measure-relspec packed-ty (m-lam-of measure-ansatz)))
                  ;; a prelude load (lex / sizeOf) may have extended the global env during
                  ;; measure compilation — encode against the latest
                  env-l (if (or lex? sizeof-measure?) @ansatz-env env)
                  callspec (merge {:cname cname :arity n :pack (if (= n 1) first pack) :dom packed-ty}
                                  relspec)
                  fix-t (wf-fix-encode env-l callspec wrapped ret-ansatz packed-ty)
                  ;; user-facing n-ary value: fun x1 … xn => fix (pack x1 … xn)  (fix-t is closed)
                  v (if (= n 1)
                      fix-t
                      (loop [i (dec n)
                             body (e/app fix-t (wf-fix-pack-vals param-types
                                                                 (mapv #(e/bvar (- n 1 %)) (range n))))]
                        (if (< i 0) body
                            (recur (dec i) (e/lam (str (first (nth pairs i))) (nth param-types i) body :default)))))]
              (env/check-constant env-l (env/mk-def cname [] type-ansatz v))
              {:value v :fix fix-t :eqbody wrapped :packed-ty packed-ty :arity n})
            (catch Throwable t
              (when (verbose?)
                (println (str "  wf-fix encoding unavailable for " fn-name " ("
                              (.getMessage t) ") — using fuel encoding")))
              nil)))
        ;; a lexicographic measure has NO single-Nat fuel, and a sizeOf measure has no honest
        ;; gate-checked fuel — the encoder is the only sound path for either
        _ (when (and (or lex? sizeof-measure?) (nil? fix-info))
            (throw (ex-info (str "Cannot prove `" fn-name "` terminates: measure `"
                                 measure-form "` did not yield a verified WellFounded.fix encoding "
                                 "(each recursive call must decrease the measure"
                                 (when lex? " lexicographically") ").")
                            {:fn fn-name :kind :termination-wf-encode-failed})))
        encoding (if fix-info :wf-fix :fuel)
        chosen-body (or (:value fix-info) final-body)

        ;; Type-check on the real env
        tc (ansatz.kernel.TypeChecker. env)
        _ (.setFuel tc (long config/*default-fuel*))
        _ (.inferType tc chosen-body)

        ;; Add to environment (swap! to avoid stale env race)
        ci (env/mk-def cname [] type-ansatz chosen-body)
        _ (swap! ansatz-env env/check-constant ci)
        ;; Register arity for Clojure compilation (FAP/PAP dispatch)
        _ (swap! arity-registry assoc (str fn-name) (compute-arity type-ansatz))
        _ (when (verbose?) (println (str "✓ " fn-name " defined (well-founded recursion, "
                                         (case encoding
                                           :wf-fix (if lex? "kernel-enforced lexicographic WellFounded.fix"
                                                       "kernel-enforced WellFounded.Nat.fix")
                                           "fuel + termination gate") ")")))

        ;; Generate equation theorem: fn(args) = body[fn → fn]
        ;; For the fuel-based Nat.rec approach, this is true by computation:
        ;; Nat.rec motive base step (succ k) args = step k (Nat.rec ... k) args
        ;; which is = body[ih → fn] (the original body with recursive calls intact).
        ;; The proof is just Eq.refl (fn args).
        ;; For the wf-fix encoding, whnf of fn(args) is STUCK on the Acc proof, so the equations
        ;; come from WellFounded.Nat.fix_eq instead: per-leaf `<fn>.eq_N` theorems (the names simp's
        ;; find-eqn-theorems discovers), each proven by the bare fix_eq instance + kernel defeq.
        _ (if (= encoding :wf-fix)
            (try
              (let [env' @ansatz-env
                    [fixh fixargs] (e/get-app-fn-args (:fix fix-info))
                    tc-eq (doto (ansatz.kernel.TypeChecker. env') (.setFuel (long config/*default-fuel*)))
                    red-eq (.getReducer tc-eq)
                    eq-lvl (let [s (.inferType tc-eq ret-ansatz)]
                             (if (e/sort? s) (e/sort-level s) (lvl/succ lvl/zero)))
                    X2id (wf-fix-fresh) X2 (e/fvar X2id)
                    rawX2 (e/instantiate1 (:eqbody fix-info) X2)
                    ;; the equation LHS uses the user-facing n-ary application: unpack a
                    ;; Prod.mk-rooted pattern back into the argument list (defeq to the packed
                    ;; fix application by delta+beta)
                    unpack (fn [pattern]
                             ;; right-nested (Prod.mk a (Prod.mk b …)) → the n-ary argument list
                             (loop [t pattern acc [] left (:arity fix-info)]
                               (if (= 1 left)
                                 (conj acc t)
                                 (let [[ph pas] (e/get-app-fn-args t)]
                                   (if (and (e/const? ph) (= "Prod.mk" (name/->string (e/const-name ph)))
                                            (= 4 (count pas)))
                                     (recur (nth pas 3) (conj acc (nth pas 2)) (dec left))
                                     (throw (ex-info "wf-fix eq: unsplit packed pattern" {})))))))
                    leaves (wf-fix-eq-leaves env' tc-eq red-eq rawX2 X2 [[X2id (:packed-ty fix-info)]])]
                (doseq [[i {:keys [fields pattern rhs]}] (map-indexed vector leaves)]
                  (let [ids (mapv first fields)
                        eq-core (e/app* (e/const' (name/from-string "Eq") [eq-lvl])
                                        ret-ansatz (apply e/app* (e/const' cname []) (unpack pattern)) rhs)
                        eq-type (loop [k (dec (count fields)) acc (e/abstract-many eq-core ids)]
                                  (if (< k 0) acc
                                      (recur (dec k) (e/forall' "x" (e/abstract-many (second (nth fields k)) (subvec ids 0 k)) acc :default))))
                        ;; WellFounded.Nat.fix -> Nat.fix_eq; WellFounded.fix (lex) -> fix_eq --
                        ;; both take the fix's own args plus the scrutinee
                        pf-core (apply e/app* (e/const' (name/from-string
                                                         (str (name/->string (e/const-name fixh)) "_eq"))
                                                        (vec (e/const-levels fixh)))
                                       (conj (vec fixargs) pattern))
                        pf (loop [k (dec (count fields)) acc (e/abstract-many pf-core ids)]
                             (if (< k 0) acc
                                 (recur (dec k) (e/lam "x" (e/abstract-many (second (nth fields k)) (subvec ids 0 k)) acc :default))))
                        eq-name (name/from-string (str fn-name ".eq_" (inc i)))]
                    (swap! ansatz-env env/check-constant (env/mk-thm eq-name [] eq-type pf))))
                (when (verbose?)
                  (println (str "  ✓ " fn-name ".eq_1.." (count leaves) " equations (fix_eq)"))))
              (catch Exception e
                (when (verbose?)
                  (println (str "  ⚠ wf-fix equation generation failed: " (.getMessage e))))))
            (try
              (let [env' @ansatz-env
                    ;; Build: ∀ params, fn(params) = body-with-fn
                    ;; Create fvars for params
                    fv-base 8300000
                    param-fvids (mapv #(+ fv-base %) (range n))
                    param-fvars (mapv e/fvar param-fvids)
                    ;; fn(params) applied
                    fn-applied (reduce e/app (e/const' cname []) param-fvars)
                    ;; fn-applied WHNF-reduces to the step body (fuel encoding), so Eq.refl works.
                    tc-eq (ansatz.kernel.TypeChecker. env')
                    _ (.setFuel tc-eq (long config/*default-fuel*))
                    _ (doseq [i (range n)]
                        (.addLocal tc-eq (long (nth param-fvids i))
                                   (str (first (nth pairs i)))
                                   (nth param-types i)))
                    rhs (.whnf (.getReducer tc-eq) fn-applied)
                    ;; Eq type: fn(args) = rhs — abstract the param fvars (a theorem must be
                    ;; CLOSED; leaving them raw was the old "Unknown free variable" failure)
                    eq-type (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                                    ret-ansatz fn-applied rhs)
                    eq-type-abs (e/abstract-many eq-type param-fvids)
                    ;; Wrap in foralls
                    eq-full-type (loop [i (dec n) body eq-type-abs]
                                   (if (< i 0) body
                                       (recur (dec i)
                                              (e/forall' (str (first (nth pairs i)))
                                                         (nth param-types i) body :default))))
                    ;; Proof: Eq.refl (fn(args)) — works because fn(args) def-eq rhs
                    proof-core (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                                       ret-ansatz fn-applied)
                    ;; Abstract fvars back to bvars
                    proof-abs (e/abstract-many proof-core param-fvids)
                    ;; Wrap in lambdas
                    proof-full (loop [i (dec n) body proof-abs]
                                 (if (< i 0) body
                                     (recur (dec i)
                                            (e/lam (str (first (nth pairs i)))
                                                   (nth param-types i) body :default))))
                    eq-name (name/from-string (str fn-name ".eq_unfold"))
                    eq-ci (env/mk-thm eq-name [] eq-full-type proof-full)]
                (swap! ansatz-env env/check-constant eq-ci)
                (when (verbose?)
                  (println (str "  ✓ " fn-name ".eq_unfold equation theorem"))))
              (catch Exception e
                (when (verbose?)
                  (println (str "  ⚠ equation theorem generation failed: " (.getMessage e)))))))

        ;; Compile to Clojure — uncurry for multi-arg
        clj-form (ansatz->clj @ansatz-env final-body [])
        ;; The compiled form is curried: (fn [p1] (fn [p2] ... body ...))
        ;; Wrap in uncurried version: (fn [p1 p2 ...] ((curried p1) p2) ...)
        ;; For multi-arg: create a function that accepts both curried and uncurried calls.
        ;; Curried: ((f x) y) — needed when called from other compiled code
        ;; Uncurried: (f x y) — needed for ergonomic Clojure usage
        clj-fn (if (<= n 1)
                 (eval clj-form)
                 (let [param-syms (mapv (fn [[p _]] (gensym (str p "_"))) pairs)
                       curried-call (reduce (fn [f s] (list f s))
                                            (list clj-form (first param-syms))
                                            (rest param-syms))]
                   (eval
                     ;; Multi-arity: 1-arg returns curried, n-arg calls directly
                    `(fn
                       (~[(first param-syms)]
                         ;; Curried: return a fn that takes the remaining args
                        ~(if (= n 2)
                           `(fn [~(second param-syms)] ~curried-call)
                            ;; 3+ args: nested currying
                           (reduce (fn [body s] `(fn [~s] ~body))
                                   curried-call
                                   (reverse (rest param-syms)))))
                       (~param-syms ~curried-call)))))]
    clj-fn))

