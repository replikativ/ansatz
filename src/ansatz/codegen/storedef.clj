(ns ansatz.codegen.storedef
  "Runtime compilation of plain (non-abbrev) store definitions to Clojure.

   Lean's compiler never executes the kernel's brecOn/WellFounded.fix encoding of a
   recursive definition — it compiles the pre-encoding `f._unsafe_rec` body (direct
   self-calls; PreDefinition/Basic.lean:282), which lean4export does not carry. What the
   export DOES carry are the kernel-checked equation lemmas: `f.eq_def : ∀ params,
   f params = f.match_1 … (branch …)` whose branches contain direct self-calls. We compile
   THAT: the match aux unfolds through codegen's existing casesOn/.rec lowering into ctor
   dispatch, and the self-calls become `recur` when in tail position (Lean's *TR runtime
   re-implementations are tail-recursive by construction, so they become real loops).

   References: Lean v4.33.1 Elab/PreDefinition/Basic.lean and
   Compiler/LCNF/ToLCNF.lean (etaIfUnderApplied).

   Non-recursive plain defs (the `@[inline]` TR wrappers like List.lengthTR, instance
   literals) have no eq_def; their stored value compiles directly.

   Compiled fns are interned in `ansatz.storedef.runtime` under their UNMUNGED dotted Lean
   name (an unqualified dotted symbol resolves as a class, but a namespace-QUALIFIED dotted
   symbol resolves as a var) and registered in the arity-registry as
   {:arity n :erased k :sym qualified-sym}, which the codegen FAP path and the csimp
   lowerability guard consume. Any failure anywhere leaves the registries untouched and
   unsupported definitions raise a named codegen error before runtime emission."
  (:require [ansatz.eqns :as eqns]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.codegen.decl :as decl])
  (:import [ansatz.kernel ConstantInfo]))

(def ^:private runtime-ns (create-ns 'ansatz.storedef.runtime))

;; Only successful compilations are memoized. A failed dependency may become
;; available after installing a runtime lowering; failures must remain diagnostic.
(defonce ^:private compiled (atom {}))

;; Names currently being compiled (cycle guard). Self-references inside the body being
;; emitted hit this guard, fall through codegen as bare curried applications of the dotted
;; name, and are collapsed/rewritten by the post-processing below. Mutual recursion leaves
;; an unresolvable symbol in the sibling's form and fails cleanly at eval.
(def ^:private ^:dynamic *in-progress* #{})

(defn reset-cache!
  "Drop all memoized compilations (they are NOT unregistered from the arity-registry;
   test/debug helper)."
  []
  (reset! compiled {}))

;; ── eq_def parsing ────────────────────────────────────────────────────────────

(defn- strip-telescope
  "Split a ∀-telescope type into [[name type info] ...] binders and the conclusion."
  [t]
  (loop [t t binders []]
    (if (e/forall? t)
      (recur (e/forall-body t) (conj binders [(e/forall-name t) (e/forall-type t) (e/forall-info t)]))
      [binders t])))

(defn- parse-equation
  "From an equation theorem type `∀ tele, Eq T (f tele-bvars) rhs` return
   {:binders [[name type info] …] :rhs Expr}, or nil if the shape doesn't match
   (conditional equations carry extra hypothesis binders and fail the lhs check)."
  [env fname equation]
  (when-let [ci (env/lookup env equation)]
    (let [[binders concl] (strip-telescope (.type ^ConstantInfo ci))
          [h args] (e/get-app-fn-args concl)
          n (count binders)]
      (when (and (e/const? h) (= "Eq" (name/->string (e/const-name h))) (= 3 (count args)))
        (let [[_T lhs rhs] args
              [lh largs] (e/get-app-fn-args lhs)]
          (when (and (e/const? lh) (= fname (name/->string (e/const-name lh)))
                     (= n (count largs))
                     (every? identity
                             (map-indexed (fn [i a] (and (e/bvar? a) (= (- n 1 i) (e/bvar-idx a))))
                                          largs)))
            {:binders binders :rhs rhs :equation equation}))))))

(defn- parse-eq-def [env fname]
  ;; Meta/Eqns.lean getEqnsFor?: consume the recorded inventory in order.
  ;; The explicitly exported legacy eq_def remains usable without metadata.
  (some #(parse-equation env fname %)
        (distinct (concat (eqns/eqns-for env fname)
                          [(name/from-string (str fname ".eq_def"))]))))

(defn- const-refs
  "All constant names referenced in an Expr."
  [ex]
  (let [acc (java.util.HashSet.)]
    (letfn [(go [^ansatz.kernel.Expr x]
                (cond
                  (e/const? x) (.add acc (name/->string (e/const-name x)))
                  (e/app? x) (do (go (e/app-fn x)) (go (e/app-arg x)))
                  (e/lam? x) (do (go (e/lam-type x)) (go (e/lam-body x)))
                  (e/forall? x) (do (go (e/forall-type x)) (go (e/forall-body x)))
                  (e/let? x) (do (go (e/let-type x)) (go (e/let-value x)) (go (e/let-body x)))
                  (e/proj? x) (go (cast ansatz.kernel.Expr (.o1 x)))
                  :else nil))]
      (go ex))
    (set acc)))

(defn- unexecutable-ref?
  "Kernel recursion encodings that must never reach emission: their strict compile is
   exponential (brecOn below-tuples) or unresolvable."
  [n]
  (or (= n "WellFounded.fix")
      (.endsWith ^String n ".brecOn")
      (.endsWith ^String n ".fix")))

;; ── binder audit ──────────────────────────────────────────────────────────────

(defn- type-like?
  "Is this binder domain a Sort / type constructor (∀ … , Sort)? Such an EXPLICIT binder
   would become a runtime param whose call-site arg lowers to a bare type symbol — bail."
  [bt]
  (loop [t bt]
    (cond (e/sort? t) true
          (e/forall? t) (recur (e/forall-body t))
          :else false)))

(defn- audit-binders
  "Runtime shape of a binder telescope: {:erased k :arity n} with the non-default binders
   required to form a PREFIX (interleaved erased binders have no contiguous runtime
   parameter window), and no explicit type-like
   binder. Returns nil when the shape is unsupported."
  [binders]
  (let [infos (mapv (fn [[_ bt bi]] [bi bt]) binders)
        erased (count (take-while (fn [[bi _]] (not= :default bi)) infos))
        runtime (drop erased infos)]
    (when (and (every? (fn [[bi _]] (= :default bi)) runtime)
               (not-any? (fn [[_ bt]] (type-like? bt)) runtime)
               (<= 1 (count runtime) 20))
      {:erased erased :arity (count runtime)})))

;; ── Clojure-form post-processing ──────────────────────────────────────────────

(defn- form-beta
  "((fn [x] body) arg) → (let [x arg] body); ((let [b] f) arg) → (let [b] (f arg)).
   Bottom-up with local fixpoint: codegen's curried immediate applications otherwise hide
   the tail positions from the recur rewrite."
  [form]
  (let [step (fn step [f]
               (if (and (seq? f) (= 2 (count f)) (seq? (first f)))
                 (let [[h a] f]
                   (cond
                     (and (= 'fn (first h)) (vector? (second h)) (= 1 (count (second h))))
                     (step (list 'let [(first (second h)) a] (nth h 2)))
                     (= 'let (first h))
                     (list 'let (second h) (step (list (nth h 2) a)))
                     :else f))
                 f))
        w (fn w [f]
            (let [f (cond (seq? f) (apply list (map w f))
                          (vector? f) (mapv w f)
                          :else f)]
              (step f)))]
    (w form)))

(defn- occurs-sym? [form s]
  (boolean (some #(= s %) (tree-seq coll? seq form))))

(defn- inline-single-letfn
  "(letfn [(f [p] B)] (f arg)) → (let [p arg] B) when B has no self-occurrence — the
   one-level dispatch wrapper the casesOn lowering leaves behind. (codegen's has-rec
   refinement already avoids most of these; this catches the rest.)"
  [form]
  (let [w (fn w [f]
            (let [f (cond (seq? f) (apply list (map w f))
                          (vector? f) (mapv w f)
                          :else f)]
              (if (and (seq? f) (= 3 (count f)) (= 'letfn (first f))
                       (vector? (second f)) (= 1 (count (second f))))
                (let [[fname params body] (first (second f))
                      call (nth f 2)]
                  (if (and (seq? call) (= fname (first call)) (= 1 (count params))
                           (= 2 (count call)) (not (occurs-sym? body fname)))
                    (list 'let [(first params) (second call)] body)
                    f))
                f)))]
    (w form)))

(defn- collapse-head
  "Collapse curried application chains headed by symbol `dsym` into flat (dsym a…)."
  [form dsym]
  (let [w (fn w [f]
            (let [f (cond (seq? f) (apply list (map w f))
                          (vector? f) (mapv w f)
                          :else f)]
              (if (and (seq? f) (= 2 (count f)))
                (let [[h a] f]
                  (cond (= h dsym) (list dsym a)
                        (and (seq? h) (= dsym (first h))) (concat h [a])
                        :else f))
                f)))]
    (w form)))

(defn- peel-fns
  "Peel n nested 1-ary (fn [p] body) wrappers; nil if fewer are present."
  [form n]
  (loop [f form ps []]
    (if (= (count ps) n)
      [ps f]
      (when (and (seq? f) (= 'fn (first f)) (vector? (second f)) (= 1 (count (second f))))
        (recur (nth f 2) (conj ps (first (second f))))))))

(defn- rewrite-self
  "Rewrite flat self-calls: strip their erased arg prefix, then emit `(recur …)` in tail
   position (w.r.t. the named fn we build) and `local-name` calls elsewhere (inside nested
   fn/letfn/loop boundaries recur would silently target the WRONG recursion point, so those
   always take the named call). Returns nil if a self-call is under-applied."
  [form dsym local-name erased total]
  (let [fail (volatile! false)
        self-call?
        (fn [f] (and (seq? f) (= dsym (first f))))
        rw (fn rw [f tail? boundary?]
             (cond
               (self-call? f)
               (let [args (rest f)]
                 (if (< (count args) total)
                   (do (vreset! fail true) f)
                   ;; Lean WF/Fix.lean replaceRecApps.processRec preserves arguments
                   ;; applied to the returned function after the recursion telescope.
                   (let [rt-args (map #(rw % false boundary?) (take (- total erased) (drop erased args)))
                         extras (map #(rw % false boundary?) (drop total args))]
                     (if (and tail? (not boundary?) (empty? extras))
                       (apply list 'recur rt-args)
                       (reduce (fn [f a] (list f a)) (apply list local-name rt-args) extras)))))
               (seq? f)
               (let [[h & r] f]
                 (case h
                   if (let [[c t els] r]
                        (list 'if (rw c false boundary?) (rw t tail? boundary?)
                              (if (nil? els) els (rw els tail? boundary?))))
                   let (let [[bs body] r]
                         (list 'let (vec (map-indexed (fn [i x] (if (odd? i) (rw x false boundary?) x)) bs))
                               (rw body tail? boundary?)))
                   do (apply list 'do (concat (map #(rw % false boundary?) (butlast r))
                                              [(rw (last r) tail? boundary?)]))
                   case (let [[ce & br] r
                              n (count br)
                              paired (if (odd? n) (butlast br) br)
                              dflt (when (odd? n) (last br))]
                          (apply list 'case (rw ce false boundary?)
                                 (concat (map-indexed (fn [i x] (if (odd? i) (rw x tail? boundary?) x)) paired)
                                         (when dflt [(rw dflt tail? boundary?)]))))
                   (fn letfn loop)
                   ;; new recursion/closure boundary: self-calls inside must use the named call
                   (apply list (map (fn [x] (if (coll? x) (rw x false true) x)) f))
                   ;; ordinary application / other special form: args are non-tail
                   (apply list (map #(rw % false boundary?) f))))
               (vector? f) (mapv #(rw % false boundary?) f)
               :else f))
        out (rw form true false)]
    (when-not @fail out)))

;; ── the emitter (shared: store defs here, own a/defn via ansatz.core) ─────────

(defn- ansatz->clj* [env expr cname]
  (let [compile (requiring-resolve 'ansatz.codegen/ansatz->clj)
        raw (requiring-resolve 'ansatz.codegen/*raw-constants*)]
    (with-bindings {raw (conj @raw cname)}
      (compile env expr []))))

(defn emit-direct-recursion
  "Compile a DIRECT-RECURSION lambda term — self-calls appear as applications of the
   constant `cname` — into a flat named Clojure fn: full-arity method with `recur` at tail
   self-calls (named calls elsewhere), plus partial-arity methods returning closures so the
   fn also works curried in value position. This is the runtime's analogue of compiling
   Lean's `f._unsafe_rec` (the kernel keeps the recursor/brecOn encoding as the proven
   artifact; PreDefinition/Basic.lean:282).

   Returns {:fn-form form :fn compiled-fn} or nil when the shape is unsupported (arity
   mismatch on a self-call or an erased binder that turns out runtime-relevant).
   Emission/eval failures propagate. Callers own interning/registration."
  [env ^String cname term {:keys [erased arity]}]
  (let [total (+ erased arity)
        raw (binding [*in-progress* (conj *in-progress* cname)]
              (ansatz->clj* env term cname))
        dsym (symbol cname)
        simplified (-> raw form-beta inline-single-letfn (collapse-head dsym))]
    (when-let [[params body] (peel-fns simplified total)]
      (let [rt-params (subvec params erased)
            local-name (gensym "self_")
            body' (rewrite-self body dsym local-name erased total)]
        (when (and body'
                   ;; erased binders must be runtime-irrelevant in the final body
                   (not-any? #(occurs-sym? body' %) (subvec params 0 erased)))
          (let [emitted (decl/emit-wrapper rt-params body' {:erased erased :local-name local-name})]
            (assoc emitted :fn (eval (:fn-form emitted)))))))))

;; ── the store-def compiler ────────────────────────────────────────────────────

(defn- compilation-error [cname reason]
  (ex-info (str "Codegen error: cannot compile '" cname "': " reason)
           {:kind :codegen-error :declaration cname :reason reason}))

(defn- compile!*
  [env ^String cname ^ConstantInfo ci]
  (let [eqd (parse-eq-def env cname)
        ;; Lean Elab/PreDefinition/Basic.lean compiles the pre-encoding body.
        ;; Exports with eq_def provide the corresponding direct recursive RHS.
        [binders rhs]
        (if eqd
          [(:binders eqd) (:rhs eqd)]
          (loop [t (.getValue ci) bs []]
            (if (e/lam? t)
              (recur (e/lam-body t) (conj bs [(e/lam-name t) (e/lam-type t) (e/lam-info t)]))
              [bs t])))
        [type-binders _] (strip-telescope (.type ci))
        ;; Compiler/LCNF/ToLCNF.lean etaIfUnderApplied: expose the remaining
        ;; parameters of an eta-contracted value before fixing its convention.
        missing (- (count type-binders) (count binders))
        rhs (if (pos? missing)
              (reduce e/app (e/lift rhs missing 0) (map e/bvar (reverse (range missing))))
              rhs)
        binders (if (pos? missing) (into (vec binders) (drop (count binders) type-binders)) binders)
        refs (const-refs rhs)]
    (when-let [ref (first (sort (filter unexecutable-ref? refs)))]
      (throw (compilation-error cname
                               (str "kernel recursion encoding " ref
                                    "; exported direct equation body (.eq_def) is unavailable"))))
    (when (and (not eqd) (contains? refs cname))
      (throw (compilation-error cname "recursive value requires an exported direct equation body")))
    (when (not= (count binders) (count type-binders))
      (throw (compilation-error cname "eta-contracted value does not expose the declaration telescope")))
    (let [{:keys [erased arity] :as audit} (audit-binders binders)]
      (when-not audit
        (throw (compilation-error cname
                                  "unsupported runtime binder telescope: requires an erased prefix and 1..20 explicit non-type parameters (arity limit 20)")))
      (let [lam (reduce (fn [body [bn bt bi]] (e/lam bn bt body bi)) rhs (rseq (vec binders)))
            emitted (emit-direct-recursion env cname lam {:erased erased :arity arity})]
        (when-not emitted
          (throw (compilation-error cname "direct recursion emission cannot erase binders or match self-call arity")))
        (intern runtime-ns (symbol cname) (:fn emitted))
        (assoc (:convention emitted)
               :sym (symbol (str (ns-name runtime-ns)) cname)
               :provenance (cond (nil? eqd) :value
                                 (= (name/->string (:equation eqd)) (str cname ".eq_def")) :eq-def
                                 :else :equation)
               :equation (:equation eqd))))))

(defn compile-store-def!
  "Compile a plain store definition and register its runtime convention. Ineligible
   constants and active recursive references return nil. Unsupported definitions
   throw :codegen-error naming the declaration and cause; failures are not cached."
  [env ^String cname]
  ;; Ignore legacy negative entries retained by defonce during a hot reload.
  (let [memo (get @compiled cname)]
    (if (:sym memo)
      (do
        ;; A caller may have restored an isolated arity registry since this
        ;; compilation. Reinstall the convention before codegen redispatches.
        (swap! (deref (requiring-resolve 'ansatz.surface.ingest/arity-registry)) assoc cname memo)
        memo)
      (when-not (contains? *in-progress* cname)
        (when-let [^ConstantInfo ci (env/lookup env (name/from-string cname))]
          (when (and (<= 0 (.getHintsCode ci)) (some? (.getValue ci))
                     (not (contains? (env/get-extension env :extern #{}) cname)))
            (let [res (try
                        (compile!* env cname ci)
                        (catch clojure.lang.Compiler$CompilerException ex
                          (throw (ex-info (str "Codegen error: cannot compile '" cname "': "
                                               (.getMessage (.getCause ex)))
                                          {:kind :codegen-error :declaration cname
                                           :reason (.getMessage (.getCause ex))} ex))))]
              (swap! (deref (requiring-resolve 'ansatz.surface.ingest/arity-registry)) assoc cname res)
              (swap! compiled assoc cname res)
              res)))))))
