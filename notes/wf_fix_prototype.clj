;; ─────────────────────────────────────────────────────────────────────────────
;; WF-FIX ENCODING PROTOTYPE (Stage 1b) — VALIDATED, NOT WIRED INTO THE BUILD
;;
;; Lean4-faithful port of mkFix's Nat fast path (Fix.lean:300-301): a recursive
;; function is encoded as `WellFounded.Nat.fix` with a motive-refined `casesOn`
;; (MatcherApp.addArg, Fix.lean:140-151), so the recursive-call decrease proof is
;; embedded IN THE TERM (kernel-ENFORCED termination), not a side gate.
;;
;; STATUS (2026-06-11): SUPERSEDED — the production version (with recursive motive
;; refinement for nested matches) is now in src/ansatz/core.clj (`wf-fix-encode` +
;; `wf-fix-refine`/`wf-fix-refine-rec`), wired into `define-verified-wf` and covered by
;; test/ansatz/examples_test.clj `test-wf-fix-nonstructural-nested-match`. This file is
;; kept as the minimal single-level reference. The shipped version handles nested matches
;; (div2 on n-2, fib with two rec-calls) — kernel-enforced, suite green (442 tests). All of
;; if-guards (dite), multi-arg packing, and lexicographic measures have since shipped.
;;
;; To use: load ansatz.core + (a/load-init!), then paste these defs. Uses helpers
;; nm/cst/NAT/mk-lambdas/tele-open/decr-proof/mk-ihtype defined inline below.
;; ─────────────────────────────────────────────────────────────────────────────
(comment
  (require '[ansatz.core :as a] '[ansatz.kernel.env :as env] '[ansatz.kernel.name :as name]
           '[ansatz.kernel.expr :as e] '[ansatz.kernel.level :as lvl] '[ansatz.surface.match :as sm]
           '[ansatz.tactic.proof :as proof] '[ansatz.tactic.basic :as basic] '[ansatz.tactic.extract :as extract])
  (a/load-init!)

  (defn nm [s] (name/from-string s))
  (defn cst [s & ls] (e/const' (nm s) (vec ls)))
  (def NAT (cst "Nat"))
  (def run-tactic (resolve 'ansatz.core/run-tactic))
  (def gid (atom 8000000))
  (defn fresh [] (swap! gid inc))
  (defn mk-lt [a b] (e/app* (cst "LT.lt" lvl/zero) NAT (cst "instLTNat") a b))

  ;; mkLambdaFVars: fvs=[[id name type] ...] outer->inner; each type may ref earlier ids.
  ;; (Abstracting each binder type INDEPENDENTLY is the classic bug — lenient inferType
  ;;  misses it, check-constant catches it. Abstract binder k's type over (subvec ids 0 k).)
  (defn mk-lambdas [fvs body]
    (let [ids (mapv first fvs) n (count fvs)]
      (loop [k (dec n) acc (e/abstract-many body ids)]
        (if (< k 0) acc
            (let [[_ nm ty] (nth fvs k)]
              (recur (dec k) (e/lam nm (e/abstract-many ty (subvec ids 0 k)) acc :default)))))))

  ;; IHType[xref] = (y:Nat) -> InvImage.{1,1} Nat Nat ltfn measure y xref -> Ret
  (defn mk-ihtype [measure-lam ret xref]
    (let [ltfn (e/lam "n1" NAT (e/lam "n2" NAT (mk-lt (e/bvar 1) (e/bvar 0)) :default) :default)
          L1 (lvl/succ lvl/zero)]
      (e/forall' "y" NAT
        (e/forall' "_"
          (e/app* (cst "InvImage" L1 L1) NAT NAT ltfn measure-lam (e/bvar 0) (e/lift xref 1 0))
          (e/lift ret 2 0) :default) :default)))

  (def gtc (let [tc (ansatz.kernel.TypeChecker. (a/env))] (.setFuel tc 20000000) tc))
  ;; telescope-open a Pi type to fvars; WHNF at each step (minor types are beta-redexes
  ;; `motive' (ctor …)` — must whnf or you peel 0 binders).
  (defn tele-open
    ([ty] (tele-open ty (.getReducer gtc)))
    ([ty r]
     (loop [t (.whnf r ty) bs []]
       (if (e/forall? t)
         (let [id (fresh)]
           (recur (.whnf r (e/instantiate1 (e/forall-body t) (e/fvar id)))
                  (conj bs [id (e/forall-name t) (e/forall-type t)])))
         {:binders bs :body t}))))

  ;; kernel-native decrease proof: prove `∀ fields, m arg < m pattern` via omega, apply to field fvars.
  ;; The obligation type at the call is `InvImage … arg pattern` but this `<` proof is accepted by DEFEQ.
  (defn decr-proof [field-ids field-tys m arg pattern]
    (let [prop (mk-lt (e/app m arg) (e/app m pattern))
          gt (loop [i (dec (count field-ids)) body (e/abstract-many prop field-ids)]
               (if (< i 0) body (recur (dec i) (e/forall' "f" (nth field-tys i) body :default))))
          [ps _] (proof/start-proof (a/env) gt)
          ps (basic/intros ps (mapv #(str "f" %) (range (count field-ids))))
          ps (run-tactic ps '(omega))]
      (when-not (proof/solved? ps) (throw (ex-info "decrease not provable" {:goal (e/->string gt)})))
      (extract/verify ps)
      (apply e/app* (extract/extract ps) (mapv e/fvar field-ids))))

  ;; SINGLE-LEVEL encoder. raw-body = compiled `(R.rec params motive minors… major)`
  ;; (from build-telescope-fvar under sm/*use-cases-on?* true). measure-lam : T→Nat.
  ;; LIMITATION: only refines the TOP recursor; rec-calls must reference only top-level
  ;; fields (subsumed by structural recursion). Nested/if cases need recursive refinement
  ;; (see memory [[wf-fix-encoding-mechanism]] "NEXT-STEP RECIPE").
  (defn wf-fix-encode [wenv cname raw-body measure-lam ret param-type]
    (let [[rec-head args] (e/get-app-fn-args raw-body)
          rv (first (e/const-levels rec-head)) rec-name (e/const-name rec-head)
          rci (env/lookup wenv rec-name) np (.numParams rci) nminors (.numMinors rci)
          ind-params (vec (take np args))
          ind-name (let [s (name/->string rec-name)] (name/from-string (subs s 0 (- (count s) 4))))
          ctor-names (vec (.ctors (env/lookup wenv ind-name)))
          motive' (e/lam "x" param-type
                    (e/forall' "_" (mk-ihtype measure-lam ret (e/bvar 0)) (e/lift ret 1 0) :default) :default)
          rec-applied (apply e/app* (e/const' rec-name [rv]) (conj ind-params motive'))
          tc (ansatz.kernel.TypeChecker. wenv) _ (.setFuel tc 20000000)
          tb (:binders (tele-open (.inferType tc rec-applied)))
          minor-types (mapv (fn [i] (nth (mapv (fn [[_ _ t]] t) tb) i)) (range nminors))
          Xid (fresh) Fvid (fresh) X (e/fvar Xid) Fv (e/fvar Fvid)
          process (fn [mi]
                    (let [ctor-name (nth ctor-names mi) nf (.numFields (env/lookup wenv ctor-name))
                          bs (:binders (tele-open (nth minor-types mi))) bid (mapv first bs)
                          field-ids (vec (take nf bid))
                          field-tys (mapv (fn [i] (nth (mapv (fn [[_ _ t]] t) bs) i)) (range nf))
                          fs-id (last bid)
                          ctor-pat (apply e/app* (e/const' ctor-name (vec (e/const-levels (e/const' ctor-name []))))
                                          (into ind-params (mapv e/fvar field-ids)))
                          orig (nth args (+ np 1 mi)) nopen (dec (count bs))
                          obody (loop [b orig i 0] (if (and (< i nopen) (e/lam? b))
                                                     (recur (e/instantiate1 (e/lam-body b) (e/fvar (nth bid i))) (inc i)) b))
                          rw (fn rw [ex]
                               (let [[h as] (e/get-app-fn-args ex)]
                                 (cond
                                   (and (e/const? h) (= (e/const-name h) cname) (= 1 (count as)))
                                   (let [arg (rw (first as))]
                                     (e/app* (e/fvar fs-id) arg (decr-proof field-ids field-tys measure-lam arg ctor-pat)))
                                   (seq as) (apply e/app* (rw h) (mapv rw as))
                                   (e/lam? ex) (e/lam (e/lam-name ex) (rw (e/lam-type ex)) (rw (e/lam-body ex)) (e/lam-info ex))
                                   (e/forall? ex) (e/forall' (e/forall-name ex) (rw (e/forall-type ex)) (rw (e/forall-body ex)) (e/forall-info ex))
                                   :else ex)))]
                      (mk-lambdas bs (rw obody))))
          minors' (mapv process (range nminors))
          casesApp (e/app (apply e/app* (e/const' rec-name [rv])
                                 (-> (into ind-params [motive']) (into minors') (conj X))) Fv)
          Ffn (mk-lambdas [[Xid "x" param-type] [Fvid "F" (mk-ihtype measure-lam ret X)]] casesApp)
          Cmotive (e/lam "x" param-type (e/lift ret 1 0) :default)]
      (apply e/app* (cst "WellFounded.Nat.fix" (lvl/succ lvl/zero) rv) [param-type Cmotive measure-lam Ffn])))

  ;; ── validation ──
  (def bt (resolve 'ansatz.core/build-telescope-fvar))
  (def parse (resolve 'ansatz.core/parse-params))
  (def cnameCD (nm "ex-cd"))
  (def tenvCD (env/add-constant (env/fork (a/env)) (env/mk-axiom cnameCD [] (e/forall' "n" NAT NAT :default))))
  (def rawCD (binding [sm/*use-cases-on?* true]
               (let [b (bt tenvCD (parse '[^Nat n]) 'Nat '(match n Nat Nat (zero 0) (succ [pred] (ex-cd pred))))]
                 (loop [b b i 0] (if (and (< i 1) (e/lam? b)) (recur (e/lam-body b) (inc i)) b)))))
  (def mlam (e/lam "n" NAT (e/bvar 0) :default))
  (def termG (wf-fix-encode tenvCD cnameCD rawCD mlam NAT NAT))
  (env/check-constant (a/env) (env/mk-def (nm "ex_cd_g") [] (e/forall' "n" NAT NAT :default) termG)) ; => :OK
  )
