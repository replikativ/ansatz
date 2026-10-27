(ns ansatz.codegen
  "Codegen — compile a kernel Expr to a Clojure form for eval (`ansatz->clj`) plus the built-in
   lowering tables (`builtin-app`/`builtin-value`). Extracted from ansatz.core. Reads the shared
   registries in ansatz.surface.ingest (structure/codegen/arity) and the structural ctor/recursor/
   arity machinery; the runtime (wandler) augments lowering via `codegen-registry`."
  (:require [clojure.walk :as walk]
            [ansatz.codegen.numeric]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as level]
            [ansatz.inductive :as inductive]
            [ansatz.codegen.decl :as decl]
            [ansatz.codegen.types :as types]
            [ansatz.surface.ingest :as ingest :refer [structure-registry codegen-registry arity-registry]])
  (:import [ansatz.kernel ConstantInfo TypeChecker]))

(clojure.core/defn- nary-op
  "Emit `(op a b)` when a binary primitive is fully applied (>=2 compiled args), else a
   partial / the bare op — so an eta-reduced or VALUE-position op (a fold step `+`, a
   simp-produced partial `(Nat.ble k)`) still lowers to a runnable fn."
  [op ca]
  (cond
    (>= (count ca) 2) (list op (nth ca 0) (nth ca 1))
    (= (count ca) 1)  (list 'clojure.core/partial op (nth ca 0))
    :else op))

(clojure.core/defn- nary-op2
  "Like nary-op for ops whose saturated form isn't a bare symbol: `emit2` maps the two
   compiled args to a form; under-application eta-expands."
  [emit2 ca]
  (cond
    (>= (count ca) 2) (emit2 (nth ca 0) (nth ca 1))
    (= (count ca) 1)  (let [a (gensym "a") b (gensym "b")]
                        (list 'clojure.core/let [a (nth ca 0)]
                              (list 'clojure.core/fn [b] (emit2 a b))))
    :else (let [a (gensym "a") b (gensym "b")]
            (list 'clojure.core/fn
                  (list [a] (list 'clojure.core/fn [b] (emit2 a b)))
                  (list [a b] (emit2 a b))))))

(clojure.core/defn- tagged-inductive?
  "Tagged vectors distinguish fielded constructors that the native nil/vector rep cannot."
  [env ind-name-str]
  (and (not (#{"List" "Nat"} ind-name-str))
       (not (get @structure-registry ind-name-str))
       (when-let [ind-ci (env/lookup env (name/from-string ind-name-str))]
         (let [ctors (.ctors ^ConstantInfo ind-ci)
               fields (mapv #(.numFields ^ConstantInfo (env/lookup env %)) ctors)]
           (and (some pos? fields)
                (or (> (count fields) 2)
                    (and (= 2 (count fields)) (pos? (first fields)))))))))

(declare ansatz->clj beta-apply runtime-instance-op standard-real-approx)

;; ── built-in codegen tables (the Init/kernel lowerings) ──────────────────────────────────────────
;; head-name → lowering. `ansatz->clj` consults these BEFORE the `codegen-registry` extension seam
;; (so a runtime's registered vocabulary augments, never shadows, the kernel built-ins), then falls
;; through to the structural ctor / recursor / arity machinery. This mirrors Lean's compiler, which
;; lowers Nat/Int/Float/Bool primitives by table and `ite`/`dite`/recursors by dedicated handlers.
;;
;;   builtin-app   : head → (fn [env head args ca names] → clj-form)  — head APPLIED to args
;;   builtin-value : head → clj-form                                  — head in VALUE position (a
;;                                                                       fold step `+`, a comparator)
;; `ca` = already-compiled args; `args` = raw Ansatz Exprs (a few handlers peel lambdas).

(clojure.core/defn- bi-nary
  "App handler for a binary primitive that saturates to a bare symbol `op` (fold-step-safe via nary-op)."
  [op] (fn [_ _ _ ca _] (nary-op op ca)))

(clojure.core/defn- bi-nary2
  "App handler for a binary primitive whose saturated form `(emit2 a b)` isn't a bare symbol.
   `drop-prefix` (default 0) skips leading type/instance args (heterogeneous HAdd/HMul/… carry 4)."
  ([emit2] (bi-nary2 emit2 0))
  ([emit2 drop-prefix]
   (fn [_ _ _ ca _] (nary-op2 emit2 (if (pos? drop-prefix) (vec (drop drop-prefix ca)) ca)))))

(clojure.core/defn- hop-carrier
  "The head-constant name of the FIRST type argument (α), or nil. Used for
   numeric-literal representation; arithmetic dispatch follows the actual instance."
  [args]
  (when (seq args)
    (let [[h _] (e/get-app-fn-args (first args))]
      (when (e/const? h) (name/->string (e/const-name h))))))

(clojure.core/defn- hop
  "Compile an H-op's actual instance field. Carrier names never establish which
   implementation an instance contains. All H* classes here have one field."
  []
  (fn [env head args ca names]
    (when (< (count args) 4)
      (throw (ex-info "H-op lowering requires all type and instance arguments"
                      {:head (name/->string (e/const-name head))})))
    (if-let [emit2 (standard-real-approx env head args)]
      (nary-op2 emit2 (vec (drop 4 ca)))
      (let [hn (name/->string (e/const-name head))
            cls (subs hn 0 (.lastIndexOf ^String hn "."))
            field (e/proj (name/from-string cls) 0 (nth args 3))
            op (runtime-instance-op env field)]
        (ansatz->clj env (reduce e/app op (drop 4 args)) names)))))

(clojure.core/defn- bi-const "App handler for a nullary constant." [v] (fn [_ _ _ _ _] v))

;; One contract table drives saturated, partially applied and function-value lowering.
(def ^:private integer-binary
  {"Nat.sub" 'ansatz.codegen.numeric/nat-sub
   "Nat.pow" 'ansatz.codegen.numeric/pow "Int.pow" 'ansatz.codegen.numeric/pow
   "Nat.div" 'ansatz.codegen.numeric/tdiv "Nat.mod" 'ansatz.codegen.numeric/tmod
   "Int.tdiv" 'ansatz.codegen.numeric/tdiv "Int.tmod" 'ansatz.codegen.numeric/tmod
   "Int.ediv" 'ansatz.codegen.numeric/ediv "Int.emod" 'ansatz.codegen.numeric/emod
   "Int.fdiv" 'ansatz.codegen.numeric/fdiv "Int.fmod" 'ansatz.codegen.numeric/fmod})

;; Init/Prelude.lean List.foldl: foldl f a [] = a;
;; foldl f a (b :: l) = foldl f (f a b) l. The bundled export carries
;; only brecOn, without eq_def or a compiler replacement for this declaration.
;; Like List.length's native lowering, reduce executes these equations directly.
(def ^:private list-foldl
  (:fn-form (decl/emit-wrapper
             '[f_ init_ xs_]
             '(clojure.core/reduce (fn [acc_ x_] ((f_ acc_) x_)) init_ xs_)
             {})))

(def ^:private builtin-app
  (merge
   ;; n-ary arithmetic / comparison saturating to a bare op. Nat add/mul/succ use the
   ;; auto-promoting variants (+'/*'/inc'): with literals now emitted as longs, results
   ;; promote to bigint on overflow instead of throwing — full unbounded-Nat semantics at
   ;; ~3% over raw long ops (sub/div/mod/comparisons can't overflow from Nat inputs).
   {"Nat.add"  (bi-nary '+') "Nat.mul"  (bi-nary '*')
    "Nat.max"  (bi-nary 'max) "Nat.min" (bi-nary 'min)
    "Nat.blt"  (bi-nary '<)  "Nat.ble"  (bi-nary '<=) "Nat.beq" (bi-nary '==)
    "Float.add" (bi-nary '+) "Float.sub" (bi-nary '-) "Float.mul" (bi-nary '*) "Float.div" (bi-nary '/)
    ;; Lean's Int is unbounded, so its ops take the auto-promoting variants too. `Int.ofNat`
    ;; is the identity here: a Nat already runs as a long (promoting to bigint on overflow),
    ;; which is exactly what an Int is at runtime.
    "Int.add" (bi-nary '+') "Int.mul" (bi-nary '*') "Int.sub" (bi-nary '-')}
   ;; n-ary ops whose saturated form is a composite expr
   {"Bool.or"  (bi-nary2 (fn [x y] (list 'or x y)))
    "Bool.and" (bi-nary2 (fn [x y] (list 'and x y)))
    "Float.pow" (bi-nary2 (fn [x y] (list 'Math/pow x y)))
    ;; heterogeneous H* ops carry [α β γ inst …] — drop the 4-arg type/instance prefix
    "HAdd.hAdd" (hop) "HMul.hMul" (hop) "HSub.hSub" (hop)
    "HDiv.hDiv" (hop) "HMod.hMod" (hop) "HPow.hPow" (hop)}
   ;; nullary constants
   {"Bool.true" (bi-const true) "Bool.false" (bi-const false) "Nat.zero" (bi-const 0)
    "List.nil"  (bi-const nil)}
   ;; small structural lowerings + control flow + refinement erasure (bespoke handlers)
   {"List.foldl"    (fn [_ _ _ ca _]
                     (decl/apply-args {:arity 3 :erased 2} list-foldl ca))
    "Nat.succ"      (fn [_ _ _ ca _] (list 'inc' (nth ca 0)))
    "Int.ofNat"     (fn [_ _ _ ca _] (nth ca 0))
    "Int.neg"       (fn [_ _ _ ca _] (list '-' (nth ca 0)))
    "Int.natAbs"    (fn [_ _ _ ca _] (list 'ansatz.codegen.numeric/nat-abs (nth ca 0)))
    "Bool.not"      (fn [_ _ _ ca _] (list 'not (nth ca 0)))
    "ite"           (fn [_ _ _ ca _] (list 'if (nth ca 1) (nth ca 3) (nth ca 4)))
    "List.cons"     (fn [_ _ _ ca _] (list 'clojure.core/cons (nth ca 1) (nth ca 2)))
    "List.length"   (fn [_ _ _ ca _]              ; arity-tolerant: `List.length A` as a fn VALUE
                      (case (count ca)             ; (eta-reduced, e.g. fused into a comp) lowers to `count`
                        1 'clojure.core/count
                        (list 'count (nth ca 1))))
    ;; SizeOf.sizeOf T inst x → runtime size (mirrors sizeOf_spec; reached via the fuel scaffolding).
    "SizeOf.sizeOf" (fn [_ _ _ ca _] (list 'ansatz.core/rt-sizeof (nth ca 2)))
    ;; refinement erasure: a Subtype value IS its carrier at runtime (arity-tolerant for eta-reduced partials)
    "Subtype.val" (fn [_ _ _ ca _]
                    (case (count ca)
                      3 (nth ca 2)
                      2 'clojure.core/identity
                      1 (list 'fn '[_] 'clojure.core/identity)
                      (list 'fn '[_] (list 'fn '[_] 'clojure.core/identity))))
    "Subtype.mk" (fn [_ _ _ ca _]
                   (case (count ca)
                     4 (nth ca 2)
                     3 (list 'fn '[_] (nth ca 2))
                     2 (list 'fn '[v#] (list 'fn '[_] 'v#))
                     (list 'fn '[_] (list 'fn '[v#] (list 'fn '[_] 'v#)))))
    ;; OfNat.ofNat α n inst — a numeric literal AT a type (Lean's OfNat elaboration). The
    ;; literal is the second argument; on a real/float carrier it runs as a double.
    "OfNat.ofNat"
    (fn [_ _ args ca _]
      (let [lit (fn [n] (if (#{"Real" "Float"} (hop-carrier args))
                          (if (number? n) (double n) (list 'double n))
                          n))]
        (case (count ca)
          ;; arity-tolerant, as Subtype.val is: the instance argument erases to nothing
          0 (list 'fn '[_] (list 'fn '[n#] (list 'fn '[_] (lit 'n#))))
          1 (list 'fn '[n#] (list 'fn '[_] (lit 'n#)))
          (lit (nth ca 1)))))
    ;; Float literal: OfScientific.ofScientific Float inst m s e → m × 10^±e (type/inst erase)
    "OfScientific.ofScientific"
    (fn [_ _ _ ca _]
      (let [m (nth ca 2) sn (nth ca 3) ex (nth ca 4)]
        (if (and (number? m) (number? ex) (boolean? sn))
          (* (double m) (Math/pow 10.0 (double (if sn (- ex) ex))))
          (list '* (list 'double m) (list 'Math/pow 10.0 (list 'if sn (list '- ex) ex))))))
    ;; dite α cond dec then-fn else-fn → (if bool-cond then else); then/else peel their erased proof binder
    "dite"
    (fn [env _ args ca names]
      (let [then-fn (nth args 3)
            else-fn (nth args 4)
            then-body (if (e/lam? then-fn)
                        (ansatz->clj env (e/lam-body then-fn) (types/bind-type names "_h" (e/lam-type then-fn)))
                        (nth ca 3))
            else-body (if (e/lam? else-fn)
                        (ansatz->clj env (e/lam-body else-fn) (types/bind-type names "_h" (e/lam-type else-fn)))
                        (nth ca 4))
            dec-expr (nth args 2)
            [dec-head dec-args] (e/get-app-fn-args dec-expr)
            bool-cond (if (and (e/const? dec-head)
                               (#{"Nat.decEq" "Nat.decLt" "Nat.decLe"}
                                (name/->string (e/const-name dec-head))))
                        (list (case (name/->string (e/const-name dec-head))
                                "Nat.decEq" '== "Nat.decLt" '< "Nat.decLe" '<=)
                              (ansatz->clj env (nth dec-args 0) names)
                              (ansatz->clj env (nth dec-args 1) names))
                        (nth ca 2))]
        (list 'if bool-cond then-body else-body)))
    ;; WellFounded.Nat.fix α motive measure F x → letfn self-recursion; F = λ x. λ IH. body, IH calls drop the proof
    "WellFounded.Nat.fix"
    (fn [env head args ca names]
      (if (= 5 (count ca))
        (let [f-expr (nth args 3)
              x-arg (nth ca 4)
              self-sym (gensym "wf_")
              f-body-1 (when (e/lam? f-expr) (e/lam-body f-expr))
              f-body-2 (when (and f-body-1 (e/lam? f-body-1)) (e/lam-body f-body-1))
              x-name (when (e/lam? f-expr) (or (e/lam-name f-expr) "x"))
              ih-name (when (and f-body-1 (e/lam? f-body-1)) (or (e/lam-name f-body-1) "IH"))
              compiled-body (when f-body-2
                              (ansatz->clj env f-body-2
                                           (types/bind-type
                                            (types/bind-type names x-name (e/lam-type f-expr))
                                            ih-name (e/lam-type f-body-1))))
              ih-sym (symbol ih-name)
              replace-ih (fn replace-ih [form]
                           (cond
                             ;; ((IH y) proof) → (self y)
                             (and (seq? form) (= 2 (count form))
                                  (seq? (first form)) (= 2 (count (first form)))
                                  (= ih-sym (ffirst form)))
                             (list self-sym (second (first form)))
                             (seq? form) (apply list (map replace-ih form))
                             (vector? form) (mapv replace-ih form)
                             :else form))
              final-body (replace-ih compiled-body)]
          (list 'letfn [(list self-sym [(symbol x-name)] final-body)]
                (list self-sym x-arg)))
        ;; Partial application (shouldn't happen normally)
        (list 'apply (ansatz->clj env head names) ca)))}
   (into {} (map (fn [[n op]] [n (bi-nary op)]) integer-binary))))

(def ^:private builtin-value
  "head → clj-form for an op in VALUE position (a fold step `+`, a passed comparator)."
  (merge
   {"List.foldl" list-foldl
    "Nat.zero" 0 "Bool.true" true "Bool.false" false
    "Nat.succ" 'inc' "Int.ofNat" 'identity
    "Float.pow" (nary-op2 (fn [x y] (list 'Math/pow x y)) [])
    "Int.neg" '-' "Int.natAbs" 'ansatz.codegen.numeric/nat-abs
    ;; Unit/PUnit's single value → nil (the unit thunks a match auxiliary applies branches to).
    "Unit.unit" nil "PUnit.unit" nil}
   (into {} (map (fn [[n op]] [n (nary-op2 (fn [x y] (list op x y)) [])])
                 (merge {"Nat.add" '+' "Nat.mul" '*'
                         "Nat.min" 'min "Nat.max" 'max
                         "Nat.beq" '== "Nat.ble" '<= "Nat.blt" '<
                         "Int.add" '+' "Int.mul" '*' "Int.sub" '-'}
                        integer-binary)))))

(clojure.core/defn- extern-unhandled-form
  "Lean's @[extern] decls (inherited into the env's :extern extension by ansatz.attrs) are native
   primitives implemented in C — ansatz has no Lean body to lower. The common ones have builtins
   (Nat.add → +, Nat.mod → mod); the rest, on reaching the codegen fall-through with no
   builtin/registry/ctor lowering, would emit a bare symbol → an opaque ClassNotFoundException only
   if eval'd. Instead emit a form that THROWS a clear message when run, keeping codegen total (a
   dead-code occurrence never executes). Returns nil when `cn` is not an unhandled extern primitive."
  [env cn]
  (when (contains? (env/get-extension env :extern #{}) cn)
    (list 'throw (list 'ex-info
                       (str "ansatz: @[extern] native primitive '" cn "' has no Clojure runtime "
                            "lowering — register one via the codegen-registry to run it")
                       {:extern cn}))))

(def ^:dynamic *compile-store-defs*
  "Kill switch for equation-driven runtime compilation of plain store defs
   (ansatz.codegen.storedef). When false, plain non-abbrev store heads fall through to the
   pre-existing behavior (bare symbol / extern throw)."
  true)

(clojure.core/defn- storedef-compile!
  "Bridge to ansatz.codegen.storedef/compile-store-def! (requiring-resolve breaks the
   namespace cycle). Returns a successful {:arity :erased :sym} entry or nil
   for ineligible constants; unsupported definitions raise a named codegen error."
  [env ^String cname]
  ((requiring-resolve 'ansatz.codegen.storedef/compile-store-def!) env cname))

(clojure.core/defn- storedef-compile? [env cname]
  ((requiring-resolve 'ansatz.codegen.storedef/try-compile-store-def!) env cname))

(clojure.core/defn- csimp-target
  "Lean @[csimp] f→g: return g only when codegen can actually LOWER it as a head
   (builtin / registered / arity-registry / ctor / .rec recursor / :abbrev def — or, last
   resort, g compiles right now from its exported equation lemmas via storedef); else nil
   (keep f). The full Mathlib store exports compiler-internal targets (Nat.rec→Nat.recCompiled)
   as plain decls, which a bare env/lookup let through — emitting an unrunnable symbol.
   An f that already has a NATIVE lowering keeps it: a csimp swap must not hijack e.g.
   List.length → count into a compiled loop."
  [env h]
  ;; Compiler/CSimpAttr.lean replaceConstant? and LCNF/Simp/SimpValue.lean
  ;; applyImplementedBy? both replace the global constant, preserving arguments.
  (when-let [g (or (get (env/get-extension env :csimp {}) h)
                  (get (env/get-extension env :implemented-by {}) h))]
    (when-not (or (builtin-app h) (contains? builtin-value h) (contains? @codegen-registry h))
      (when (or (builtin-app g) (contains? builtin-value g) (contains? @codegen-registry g)
                (contains? @arity-registry g)
                (when-let [ci (env/lookup env (name/from-string g))]
                  (or (.isCtor ^ConstantInfo ci)
                      (and (.isRecursor ^ConstantInfo ci) (.endsWith ^String g ".rec"))
                      (= ConstantInfo/HINTS_ABBREV (.getHints ^ConstantInfo ci))))
                (when *compile-store-defs*
                  ;; An optional compiler replacement may use native machinery
                  ;; absent from this runtime. Keep the original definition then.
                  (some? (storedef-compile? env g))))
        g))))

(def ^:private match-aux-re #"\.match_\d+$")
(clojure.core/defn- match-aux?
  "A NON-recursive pattern-match auxiliary (`T.f.match_N`) or a `T.casesOn` — both are plain
   definitions whose body delegates to the inductive's `.rec`. The optimizer/simp can surface one
   when it reduces e.g. `List.filter p (a :: as)` a step; codegen unfolds them (below) so it bottoms
   out at the `.rec` path it already compiles, instead of emitting an unresolvable symbol."
  [^String h]
  (boolean (or (re-find match-aux-re h) (.endsWith h ".casesOn"))))

(clojure.core/defn- beta-apply
  "Apply lambda-telescope `value` to `args`, instantiating each leading binder (so a saturated
   match-aux call reduces to the `casesOn`/`rec` application its body denotes). Leftover args (over-
   application) are re-applied; a partial application returns the residual lambda."
  [value args]
  (loop [v value, as (seq args)]
    (if (and as (e/lam? v))
      (recur (e/instantiate1 (e/lam-body v) (first as)) (next as))
      ;; leftover args (over-application): apply left-assoc. (e/app* is variadic, so reduce e/app
      ;; over the residual args — NOT `(e/app* v (vec as))`, which would pass the vector as one arg.)
      (if as (reduce e/app v as) v))))

(clojure.core/defn- standard-real-approx
  "The existing trusted Real-as-double execution profile, restricted to dictionaries
   definitionally equal to pinned Mathlib standard instances. A Real carrier alone
   never authorizes substituting an operation for a custom instance. This is an
   approximation contract, not faithful execution of mathematical real numbers."
  [env head args]
  (when (= "Real" (hop-carrier args))
    (let [c (fn [s]
              (let [nm (name/from-string s)]
                (when-let [ci (env/lookup env nm)]
                  (e/const' nm (repeat (alength (.levelParams ^ConstantInfo ci)) level/zero)))))
          app (fn [f & as] (when (and f (every? some? as)) (reduce e/app f as)))
          real (c "Real") nat (c "Nat")
          hn (name/->string (e/const-name head))
          wrap (fn [generic dict] (app (c generic) real dict))
          pow (fn [dict] (app (c "instHPow") real nat dict))
          [op candidates]
          (case hn
            "HAdd.hAdd" ['+' [(wrap "instHAdd" (c "Real.instAdd"))]]
            "HMul.hMul" ['*' [(wrap "instHMul" (c "Real.instMul"))]]
            "HSub.hSub" ['-' [(wrap "instHSub" (c "Real.instSub"))]]
            "HDiv.hDiv" ['/ [(wrap "instHDiv" (c "Real.instDiv"))
                             (wrap "instHDiv" (app (c "DivInvMonoid.toDiv") real
                                                   (c "Real.instDivInvMonoid")))]]
            "HPow.hPow" ['Math/pow
                         [(pow (app (c "instPowNat") real
                                    (app (c "Monoid.toNatPow") real (c "Real.instMonoid"))))
                          (pow (app (c "NPow.toPow") real
                                    (app (c "Monoid.toNPow") real (c "Real.instMonoid"))))
                          (app (c "instHPow") real real (c "Real.instPow"))]]
            [nil nil])]
      (when (and op
                 (some (fn [candidate]
                         (when candidate
                           (try
                             (let [tc (TypeChecker. env)]
                               (.setFuel tc 50000)
                               (.isDefEq tc (nth args 3) candidate))
                             ;; Unknown/incompatible declarations and exhausted reduction
                             ;; cannot authorize approximation; ordinary instance dispatch follows.
                             (catch RuntimeException _ false))))
                       candidates))
        (fn [x y] (list op x y))))))

(clojure.core/defn- runtime-instance-op
  "Reduce a concrete instance projection, stopping at executable primitives and
   lambdas instead of unfolding their implementations. A symbolic instance stays
   a projection for ordinary runtime dispatch. Unsupported concrete instances and
   excessive unfolding fail explicitly, never select an operation by its carrier."
  [env expr]
  (let [fuel (volatile! 256)]
    (letfn [(step [expr]
              (when (neg? (vswap! fuel dec))
                (throw (ex-info "Runtime instance resolution exceeded its unfolding budget" {})))
              (let [[head args] (e/get-app-fn-args expr)]
                (cond
                  (e/let? head)
                  (step (reduce e/app
                                (e/instantiate1 (e/let-body head) (e/let-value head)) args))
                  (and (e/lam? head) (seq args)) (step (beta-apply head args))
                  (e/proj? head)
                  (let [struct (step (e/proj-struct head))
                        [sh sa] (e/get-app-fn-args struct)
                        ci (when (e/const? sh) (env/lookup env (e/const-name sh)))
                        idx (when (and ci (.isCtor ^ConstantInfo ci))
                              (+ (.numParams ^ConstantInfo ci) (e/proj-idx head)))]
                    (cond
                      (and idx (< idx (count sa)))
                      (step (reduce e/app (nth sa idx) args))
                      ;; Variable/nested symbolic instances use the existing representation-aware
                      ;; Expr.proj lowering (registered record field or constructor-vector slot).
                      (or (e/bvar? sh) (e/proj? sh))
                      (reduce e/app (e/proj (e/proj-type-name head) (e/proj-idx head) struct) args)
                      :else
                      (throw (ex-info "Cannot resolve concrete runtime instance projection"
                                      {:instance (e/->string struct)}))))
                  (e/const? head)
                  (let [hn (name/->string (e/const-name head))
                        ci (env/lookup env (e/const-name head))]
                    (if (and ci (.value ^ConstantInfo ci)
                             (not (contains? builtin-app hn))
                             (not (contains? @codegen-registry hn))
                             (not (contains? @arity-registry hn)))
                      (step (beta-apply (.value ^ConstantInfo ci) args))
                      expr))
                  :else expr)))
            (walk [expr]
              (cond
                (e/lam? expr)
                (e/lam (e/lam-name expr) (e/lam-type expr)
                       (walk (e/lam-body expr)) (e/lam-info expr))
                (e/proj? expr)
                (let [r (step expr)]
                  (if (e/proj? (e/get-app-fn r)) r (walk r)))
                (e/app? expr)
                (let [[h as] (e/get-app-fn-args expr)
                      ci (when (e/const? h) (env/lookup env (e/const-name h)))
                      v (when (and ci (.value ^ConstantInfo ci)
                                   (not (contains? builtin-app (name/->string (e/const-name h)))))
                          (beta-apply (.value ^ConstantInfo ci) as))]
                  ;; Generic instances often eta-wrap another class projection under
                  ;; lambdas (instHDiv -> fun x y => Div.div inst x y). Inline only
                  ;; projection accessors, leaving ordinary function bodies alone.
                  (if (and v (e/proj? (e/get-app-fn v)))
                    (walk (step v))
                    (reduce e/app (walk h) (map walk as))))
                (e/let? expr)
                (e/let' (e/let-name expr) (e/let-type expr)
                        (walk (e/let-value expr)) (walk (e/let-body expr)))
                :else expr))]
      (walk (step expr)))))

;; ── Instance-projection specialization (Lean-faithful monomorphization) ──────────────────────────
;; Collapse a structure OWN-field projection applied to a structure instance — a concrete `{Struct}.mk`
;; literal OR a named instance `def` that unfolds to one — down to the carrier op, so optimizer-emitted
;; `[inst : WSemiring S]`-parameterized terms stay executable whether the instance is inline or named.

(clojure.core/defn- own-proj-info
  "If const-name `h` is a structure OWN-field projection ({Struct}.{field}, field ∈ Struct's fields),
   return {:strukt :np :fidx} (np = the inductive's param count, fidx = field index); else nil."
  [env h]
  (let [dot (.lastIndexOf ^String h ".")
        strukt (when (pos? dot) (subs h 0 dot))
        field  (when (pos? dot) (subs h (inc dot)))
        sinfo  (when strukt (get @structure-registry strukt))
        fidx   (when sinfo (first (keep-indexed (fn [i f] (when (= field f) i)) (:fields sinfo))))]
    (when (and sinfo fidx)
      (when-let [ci (env/lookup env (name/from-string strukt))]
        {:strukt strukt :np (.numParams ^ConstantInfo ci) :fidx fidx}))))

(clojure.core/defn- mk-args
  "If `expr` is a `{strukt}.mk …` application, return its full arg vector; else nil."
  [strukt expr]
  (let [[h as] (e/get-app-fn-args expr)]
    (when (and (e/const? h) (= (str strukt ".mk") (name/->string (e/const-name h)))) (vec as))))

(clojure.core/defn- resolve-mk
  "Structurally reduce a projection's major premise to a `{Struct}.mk` literal, faithful to the kernel's
   `reduce_proj` (type_checker.cpp): whnf the major premise — INCLUDING delta-unfolding a named instance
   `def` — before matching the constructor. Two reduction steps, to a fixpoint:
     • own-field projection over a (resolved) mk literal:
       `WSemiring.toWAddMonoid (WSemiring.mk … parentInst …)` → parentInst → … → the carrier op term;
     • a named instance const whose value heads to a constructor:
       `instWSemiring_Nat` → its value `(WSemiring.mk …)` (delta). This is the `c = whnf(proj_expr(e))`
       step Lean does — it lets chains of PARENT instances referenced BY NAME resolve (algebra.clj builds
       `WSemiring.mk … instWAddMonoid_Nat …`, so `WSemiring.add` over the named instance reduces through
       both the WSemiring mk and the named WAddMonoid parent down to `Nat.add`).
   A non-instance def (e.g. `Nat.add`, whose value heads to a recursor, not a ctor) is left intact, so
   this terminates (it only recurses toward constructors, which carry no value) and never over-reduces."
  [env expr]
  (let [[h args] (e/get-app-fn-args expr)
        info (when (e/const? h) (own-proj-info env (name/->string (e/const-name h))))]
    (cond
      ;; own-field projection over a (resolved) mk literal → the field
      (and info (> (count args) (:np info)))
      (let [{:keys [strukt np fidx]} info
            self  (resolve-mk env (nth args np))
            margs (mk-args strukt self)]
        (if (and margs (> (count margs) (+ np fidx)))
          (resolve-mk env (nth margs (+ np fidx)))
          expr))
      ;; named instance const in major-premise position: delta-unfold iff its value heads to a
      ;; constructor (i.e. it IS a structure instance) — the kernel's whnf-of-major-premise step.
      (and (e/const? h) (nil? info))
      (let [ci (env/lookup env (e/const-name h))]
        (if (and ci (.value ^ConstantInfo ci))
          (let [v   (beta-apply (.value ^ConstantInfo ci) args)
                [vh _] (e/get-app-fn-args v)
                vci (when (e/const? vh) (env/lookup env (e/const-name vh)))]
            (if (and vci (.isCtor ^ConstantInfo vci))
              (resolve-mk env v)
              expr))
          expr))
      :else expr)))

(clojure.core/defn collapse-instance-projections
  "Deep, term-level instance monomorphization: everywhere in `expr`, collapse a structure OWN-field
   projection over a structure instance (a `{Struct}.mk` literal, or a named instance `def` that
   `resolve-mk` delta-unfolds to one) to the carrier op, and inline structure-prefixed
   reducible (:abbrev) accessors (e.g. an inherited `WSemiring.add`) so they too reduce to the op.
   Used to normalize an `[inst : WSemiring S]`-parameterized law's rhs (instantiated at a concrete
   instance) BEFORE the optimizer's structural pattern-matching — otherwise the projection wrapper
   shifts arg positions. Only structure projections/abbrevs reduce; regular defs (Nat.add) are left
   intact, so it terminates and never over-reduces."
  [env expr]
  (let [coll (fn [e] (collapse-instance-projections env e))
        [h args] (e/get-app-fn-args expr)]
    (if (e/const? h)
      (let [hn (name/->string (e/const-name h))
            dot (.lastIndexOf ^String hn ".")
            strukt (when (pos? dot) (subs hn 0 dot))
            info (own-proj-info env hn)
            ci (when (and strukt (contains? @structure-registry strukt))
                 (env/lookup env (e/const-name h)))]
        (cond
          ;; own-field projection over a (resolved) mk literal → the field, then recurse
          (and info (> (count args) (:np info))
               (mk-args (:strukt info) (resolve-mk env (nth args (:np info)))))
          (let [{:keys [strukt np fidx]} info
                margs (mk-args strukt (resolve-mk env (nth args np)))]
            (coll (reduce e/app (nth margs (+ np fidx)) (subvec (vec args) (inc np)))))
          ;; structure-prefixed reducible accessor (inherited field): inline + recurse
          (and ci (= ConstantInfo/HINTS_ABBREV (.getHints ^ConstantInfo ci)) (.value ^ConstantInfo ci))
          (coll (beta-apply (.value ^ConstantInfo ci) args))
          ;; ordinary const head: recurse into the args only
          :else (reduce e/app h (mapv coll args))))
      ;; non-const head: structural recursion
      (case (e/tag expr)
        :app    (e/app (coll (e/app-fn expr)) (coll (e/app-arg expr)))
        :lam    (e/lam (e/lam-name expr) (coll (e/lam-type expr)) (coll (e/lam-body expr)) (e/lam-info expr))
        :forall (e/forall' (e/forall-name expr) (coll (e/forall-type expr)) (coll (e/forall-body expr)) (e/forall-info expr))
        :let    (e/let' (e/let-name expr) (coll (e/let-type expr)) (coll (e/let-value expr)) (coll (e/let-body expr)))
        :proj   (e/proj (e/proj-type-name expr) (e/proj-idx expr) (coll (e/proj-struct expr)))
        expr))))

(clojure.core/defn- compile-minor [env minor names actuals]
  (let [n (count actuals)]
    ;; Apply in Expr space so eta-reduced builtins and flat-arity functions use
    ;; the same application lowering as explicitly written applications.
    (ansatz->clj env
                 (beta-apply (e/lift minor n 0)
                             (map #(e/bvar (- n % 1)) (range n)))
                 (loop [ctx names t (types/infer-type env minor names) xs actuals]
                   (if (empty? xs) ctx
                       (let [t (when t (.whnf (.getReducer (TypeChecker. env)) t))]
                         (recur (if (and t (e/forall? t))
                                  (types/bind-type ctx (str (first xs)) (e/forall-type t))
                                  (conj ctx (str (first xs))))
                                (when (and t (e/forall? t)) (e/forall-body t))
                                (rest xs))))))))

(clojure.core/defn- share-lazy-arguments [body replacements]
  (let [uses (frequencies (tree-seq coll? seq body))
        shared (filter #(and (> (get uses % 0) 1) (not (symbol? (replacements %))))
                       (keys replacements))
        result (walk/postwalk-replace
                (merge replacements (into {} (map #(vector % (list 'clojure.core/deref %)) shared)))
                body)]
    (if (seq shared)
      (list 'let (vec (mapcat #(vector % (list 'clojure.core/delay (replacements %))) shared)) result)
      result)))

(clojure.core/defn- validate-constructor-representation! [env rec-ci]
  ;; An override on a non-enum needs its own recursor lowering: generic codegen cannot
  ;; recover fields from an arbitrary runtime encoding. Enum overrides are decoded
  ;; by enum-dispatch using the very same lowering used for construction.
  (doseq [rule (.rules ^ConstantInfo rec-ci)
          :let [ctor-ci (env/lookup env (.ctor rule))
                ctor (name/->string (.ctor rule))
                ind-ci (env/lookup env (.inductName ^ConstantInfo ctor-ci))
                enum? (every? #(zero? (.numFields ^ConstantInfo (env/lookup env %)))
                              (.ctors ^ConstantInfo ind-ci))]
          :when (and (not enum?)
                     (contains? @codegen-registry ctor)
                     (not (contains? builtin-app ctor)))]
    (throw (ex-info "Codegen: constructor representation requires a matching recursor lowering"
                    {:kind :codegen-error :recursor (name/->string (.name ^ConstantInfo rec-ci))
                     :constructor ctor}))))

(clojure.core/defn- enum-dispatch [env rec-ci t bodies args names]
  (let [rules (.rules ^ConstantInfo rec-ci)
        values (mapv #(ansatz->clj env
                                   (reduce e/app (e/const' (.ctor %) [])
                                           (take (.numParams ^ConstantInfo rec-ci) args))
                                   names) rules)]
    ;; Const-position construction defines the representation, including builtin
    ;; precedence and registry overrides. Accept only distinct scalar literals;
    ;; arbitrary expressions require an explicitly registered eliminator.
    (when (or (not-every? #(or (nil? %) (boolean? %) (keyword? %) (string? %)
                               (number? %) (char? %)) values)
              (not= (count values) (count (distinct values))))
      (throw (ex-info "Codegen: enum representation requires distinct literal constructors or a matching recursor lowering"
                      {:kind :codegen-error :recursor (name/->string (.name ^ConstantInfo rec-ci))})))
    (list* 'cond
           (concat (mapcat (fn [v body] [(list 'clojure.core/= t v) body]) values bodies)
                   [:else (list 'throw (list 'ex-info "no matching enum constructor" {}))]))))

(def ^:dynamic *recursor-calls* {})

(clojure.core/defn- recursor-group->clj
  "Lower nested/mutual recursors from their kernel rules, with one local fn per recursor."
  [env head args names]
  (let [root (name/->string (e/const-name head))
        ci (env/lookup env (e/const-name head))
        prefix-count (+ (.numParams ci) (.numMotives ci) (.numMinors ci))
        major-idx (+ prefix-count (.numIndices ci))]
    (validate-constructor-representation! env ci)
    (when (< (count args) major-idx)
      (throw (ex-info "Codegen: unsupported recursor shape (missing minors or indices)"
                      {:kind :codegen-error :recursor root})))
    ;; Lean kernel inductive.h, inductive_reduce_rec: instantiate a rule with
    ;; params/motives/minors, then constructor fields. Discover auxiliary recursors
    ;; from those rules (nested types become a mutual group in inductive.cpp).
    (letfn [(children [x]
              (cond (e/app? x) [(e/app-fn x) (e/app-arg x)]
                    (e/lam? x) [(e/lam-body x)]
                    :else []))
            (references [ci]
              (for [rule (.rules ^ConstantInfo ci)
                    term (tree-seq #(seq (children %)) children (.rhs rule))
                    :when (e/const? term)
                    :let [c (env/lookup env (e/const-name term))]
                    :when (and c (.isRecursor ^ConstantInfo c))]
                (name/->string (.name ^ConstantInfo c))))]
      (let [group (loop [pending [root] found {}]
                    (if-let [n (peek pending)]
                      (if (contains? found n)
                        (recur (pop pending) found)
                        (let [c (env/lookup env (name/from-string n))]
                          (validate-constructor-representation! env c)
                          (recur (into (pop pending) (references c)) (assoc found n c))))
                      found))
            calls (into {} (map (fn [[n _]] [n (gensym "rec_")]) group))
            defs
            (binding [*recursor-calls*
                      (reduce-kv (fn [m n sym]
                                   (update m n (fnil conj [])
                                           {:sym sym :prefix (vec (take prefix-count args))
                                            :depth (count names)}))
                                 *recursor-calls* calls)]
              (mapv
               (fn [[n c]]
                 (let [t (gensym "t_")
                       clauses
                       (mapv
                        (fn [rule]
                          (let [ctor (env/lookup env (.ctor rule))
                                ind (name/->string (.inductName ^ConstantInfo ctor))
                                nf (.nfields rule)
                                fields (mapv (fn [_] (gensym "field_")) (range nf))
                                tagged? (tagged-inductive? env ind)
                                structure (get @structure-registry ind)
                                bindings (vec (mapcat
                                               (fn [i]
                                                 [(nth fields i)
                                                  (cond
                                                    (= ind "Nat") (list 'dec t)
                                                    (= ind "List") (list (if (zero? i) 'first 'rest) t)
                                                    structure (list (keyword (nth (:fields structure) i)) t)
                                                    :else (list 'nth t (+ i (if tagged? 1 0))))])
                                               (range nf)))
                                rhs (beta-apply (.rhs rule)
                                                (concat (map #(e/lift % nf 0) (take prefix-count args))
                                                        (map #(e/bvar (- nf % 1)) (range nf))))
                                [minor actuals] (e/get-app-fn-args rhs)
                                actual-syms (mapv (fn [_] (gensym "arg_")) actuals)
                                ctx (loop [ctx names
                                           t (reduce (fn [t arg]
                                                       (e/instantiate1 (e/forall-body t) arg))
                                                     (.type ctor) (take (.numParams ctor) args))
                                           fs fields]
                                      (if (empty? fs) ctx
                                          (recur (types/bind-type ctx (str (first fs)) (e/forall-type t))
                                                 (e/forall-body t) (rest fs))))
                                body (share-lazy-arguments
                                      (compile-minor env minor ctx actual-syms)
                                      (zipmap actual-syms (map #(ansatz->clj env % ctx) actuals)))]
                            {:cidx (.cidx ctor) :ind ind :tagged? tagged? :nf nf
                             :body (if (seq bindings) (list 'let bindings body) body)}))
                        (.rules ^ConstantInfo c))
                       {:keys [ind tagged?]} (first clauses)
                       body (cond
                              tagged? (list* 'case (list 'nth t 0)
                                             (mapcat #(vector (:cidx %) (:body %)) clauses))
                              (every? #(zero? (:nf %)) clauses)
                              (enum-dispatch env c t (mapv :body clauses) args names)
                              (= 1 (count clauses)) (:body (first clauses))
                              (and (= 2 (count clauses)) (zero? (:nf (first clauses))))
                              (list 'if (cond (= ind "Nat") (list 'zero? t)
                                              (= ind "List") (list 'not (list 'seq t))
                                              :else (list 'nil? t))
                                    (:body (first clauses)) (:body (second clauses)))
                              :else (throw (ex-info "Codegen: unsupported recursor shape"
                                                    {:kind :codegen-error :recursor n})))]
                   (list (calls n) [t] body)))
               group))
            eta? (<= (count args) major-idx)
            t (gensym "major_")
            result (list 'letfn defs
                         (list (calls root) (if eta? t (ansatz->clj env (nth args major-idx) names))))
            result (reduce (fn [f x] (list f (ansatz->clj env x names))) result
                           (drop (inc major-idx) args))]
        (if eta? (list 'fn [t] result) result)))))

(def ^:dynamic *raw-constants*
  "Direct-recursion lowering rewrites these kernel applications to local calls
   before emitting the declaration's runtime parameter list."
  #{})

(def ^:dynamic *local-conventions*
  "Compiled declaration conventions carried by let-bound function aliases."
  {})

(clojure.core/defn- record-value-head [head form]
  ;; Lean ToLCNF.visitLet binds the lowered value, including its csimp replacement.
  (if (instance? clojure.lang.IObj form)
    (with-meta form (assoc (meta form) ::resolved-head head))
    form))

(clojure.core/defn ansatz->clj
  "Compile Ansatz Expr to Clojure form for eval."
  [env expr names]
  (cond
    ;; ToLCNF.visit / visitAppArg erase before lowering the expression's body.
    (types/irrelevant? env expr names) nil
    ;; Nat literal: kernel Nats are BigInteger — emit a primitive long when it fits, so
    ;; literals don't seed accumulator chains with bigint arithmetic (~40% on hot loops).
    ;; The arithmetic builtins are auto-promoting (+'/*'/inc'), so unbounded-Nat semantics
    ;; are preserved: results overflow INTO bigint instead of starting there.
    (e/lit-nat? expr) (let [^java.math.BigInteger v (e/lit-nat-val expr)]
                        (if (< (.bitLength v) 63) (.longValue v) v))
    (e/lit-str? expr) (e/lit-str-val expr)
    (e/bvar? expr) (let [i (e/bvar-idx expr)]
                     (if (< i (count names))
                       (symbol (nth names (- (count names) i 1)))
                       (symbol (str "_" i))))
    ;; depth-unique binder name: bvars resolve positionally, so the name only needs to be
    ;; unique + a valid symbol — simp-instantiated binders may be kernel Name objects or
    ;; hygienic names that aren't, and duplicates would shadow incorrectly.
    (e/lam? expr) (let [n (str "v" (count names))]
                    (list 'fn [(symbol n)]
                          (ansatz->clj env (e/lam-body expr) (types/bind-type names n (e/lam-type expr)))))
    (e/app? expr)
    (let [[head args] (e/get-app-fn-args expr)]
      (if (e/const? head)
        (let [h0 (name/->string (e/const-name head))
              ;; @[csimp]: rewrite the head to its verified replacement g before any lowering, so
              ;; everything downstream (builtin/registry/ctor/recursor) dispatches on g.
              g (csimp-target env h0)
              head (if g (e/const' (name/from-string g) (e/const-levels head)) head)
              h (or g h0)
              cc (when-not (contains? *raw-constants* h) (get @arity-registry h))
              ;; The native Nat decision is lowered directly by dite's handler;
              ;; ordinary type, predicate and proof erasure uses visitAppArg below.
              native-decision? (when (and (= h "dite") (> (count args) 2))
                                 (let [[dh _] (e/get-app-fn-args (nth args 2))]
                                   (and (e/const? dh)
                                        (#{"Nat.decEq" "Nat.decLt" "Nat.decLe"}
                                         (name/->string (e/const-name dh))))))
              ;; Erased parameters never reach expression lowering or runtime calls.
              ca (mapv (fn [i arg]
                         (when-not (or (< i (or (:erased cc) 0))
                                       (and (= h "OfNat.ofNat") (#{0 2} i))
                                       (and (= h "OfScientific.ofScientific") (< i 2))
                                       ;; hop extracts the actual field from the
                                       ;; raw instance before emitting operands;
                                       ;; its type/dictionary prefix is not emitted.
                                       (and (#{"HAdd.hAdd" "HMul.hMul" "HSub.hSub"
                                               "HDiv.hDiv" "HMod.hMod" "HPow.hPow"} h)
                                            (< i 4))
                                       (and (= h "dite")
                                            (and (= i 2) native-decision?)))
                           (ansatz->clj env arg names))) (range) args)]
          (if-let [bi (or (when-let [entry
                                     (some (fn [{:keys [prefix depth] :as entry}]
                                             (when (and (>= (count names) depth)
                                                        (= (mapv #(e/lift % (- (count names) depth) 0) prefix)
                                                           (vec (take (count prefix) args))))
                                               entry))
                                           (get *recursor-calls* h))]
                            (fn [env head _ ca _]
                              (let [ci (env/lookup env (e/const-name head))
                                    idx (+ (.numParams ci) (.numMotives ci) (.numMinors ci) (.numIndices ci))]
                                (reduce (fn [f a] (list f a)) (list (:sym entry) (nth ca idx)) (drop (inc idx) ca)))))
                          (builtin-app h))]
            (bi env head args ca names)
            ;; Constructor application
            ;; For structures (defrecord): use ->RecordName constructor
            ;; For other inductives: tagged vector [field1 field2 ...]
            ;; Codegen seam FIRST: a runtime-registered lowering overrides the generic
            ;; representation (e.g. Option.some → nil-punning value, Prod.mk → [a b]) —
            ;; the runtime owns the representation of the vocabulary it installs.
            (if-let [cg (get @codegen-registry h)]
              (cg env expr names)
              (if-let [ctor-ci (when-let [ci (env/lookup env (e/const-name head))]
                                 (when (.isCtor ^ConstantInfo ci) ci))]
                (let [np (.numParams ctor-ci)
                      nf (.numFields ctor-ci)
                      fields (subvec ca np (+ np nf))
                    ;; Check if this is a structure with a defrecord
                      ind-name (subs h 0 (max 0 (- (count h) (count (name/->string (.name ctor-ci)))
                                                   -1 (count h))))
                    ;; Get the inductive name from the ctor name: T.mk → T
                      ctor-str (name/->string (.name ctor-ci))
                      dot-idx (.lastIndexOf ^String ctor-str ".")
                      struct-name (when (pos? dot-idx) (subs ctor-str 0 dot-idx))
                      struct-info (when struct-name (get @structure-registry struct-name))]
                  (cond
                  ;; Structure with defrecord: use ->RecordName constructor.
                  ;; :map? structures (malli [:map] records) construct plain Clojure maps.
                    (and struct-info (= nf (count (:fields struct-info))))
                    (if (:map? struct-info)
                      (apply list 'clojure.core/array-map
                             (mapcat (fn [f v] [(keyword f) v]) (:fields struct-info) fields))
                      (apply list (:ctor-sym struct-info) fields))
                  ;; General tagged inductive (e.g. Value): [cidx field…] — the tag in
                  ;; slot 0 lets the recursor dispatch and disambiguates same-arity ctors.
                  ;; 0-field tagged ctor → [cidx] (NOT nil — that's the enum rep).
                    (tagged-inductive? env struct-name)
                    (into [(.cidx ctor-ci)] fields)
                  ;; 0-field ctor: use index for enum dispatch
                    (zero? nf)
                    (let [cidx (.cidx ctor-ci)]
                      (if (zero? cidx) nil cidx))
                  ;; Default: tagged vector
                    :else (vec fields)))
              ;; Generic recursor compilation: *.rec → case dispatch with recursion
                (if-let [rec-ci (when (.endsWith ^String h ".rec")
                                  (env/lookup env (e/const-name head)))]
                  (when (.isRecursor ^ConstantInfo rec-ci)
                    ;; Lean inductive.cpp, is_reflexive/mk_rec_rules: functional
                    ;; recursive fields require the rule's lambda-wrapped IH.
                    ;; Route the whole family through rule instantiation, whatever
                    ;; its constructor representation (tagged, leaf/node or single).
                    (if (or (> (.numMotives ^ConstantInfo rec-ci) 1)
                            (pos? (.numIndices ^ConstantInfo rec-ci))
                            (when-let [rule (first (.rules ^ConstantInfo rec-ci))]
                              (let [ctor (env/lookup env (.ctor rule))
                                    ind (env/lookup env (.inductName ^ConstantInfo ctor))]
                                (.isReflexive ^ConstantInfo ind))))
                      (recursor-group->clj env head args names)
                      (let [_ (validate-constructor-representation! env rec-ci)
                            np (.numParams rec-ci)
                            nm (.numMotives rec-ci)
                            nmin (.numMinors rec-ci)
                            minor-start (+ np nm)
                            _ (when (or (not= nm 1) (< (count ca) (+ minor-start nmin)))
                                (throw (ex-info "Codegen: unsupported recursor shape (motives or missing minors)"
                                                {:kind :codegen-error :recursor h :motives nm
                                                 :minors nmin :arguments (count ca)})))
                          ;; Lean inductive.h, inductive_reduce_rec/get_major_idx:
                          ;; params, motives, minors, indices, then major.
                            major-idx (+ minor-start nmin (.numIndices rec-ci))
                          ;; Arity tolerance: a recursor used as a FUNCTION VALUE (e.g. an
                          ;; eta-reduced `R.rec motive minors` the optimizer passes to
                          ;; map/filterMap) lacks the major premise. Bind it to a fresh param
                          ;; and wrap the lowering in a fn supplying it (mirrors the
                          ;; Subtype.val / nary-op arity tolerance). Only the major may be
                          ;; missing (minors precede it and are present).
                            eta-major? (<= (count ca) major-idx)
                            eta-major-sym (gensym "etamaj_")
                            major (if eta-major? eta-major-sym (nth ca major-idx))
                            rules (.rules rec-ci)
                      ;; Determine which fields are recursive per constructor
                            ind-name-str (subs h 0 (- (count h) 4)) ;; remove ".rec"
                            ind-ci (env/lookup env (name/from-string ind-name-str))
                      ;; Build a letfn with self-recursive function
                            self-sym (gensym "rec_")
                        ;; Unique prefix for field names to avoid shadowing in nested matches
                            field-prefix (str "f" (gensym "") "_")
                            clauses
                            (map-indexed
                             (fn [i ^ansatz.kernel.ConstantInfo$RecursorRule rule]
                               (let [nf (.nfields rule)
                                     minor (nth ca (+ minor-start i))
                                     minor-ansatz-expr (nth args (+ minor-start i))
                                     ctor-name (.ctor rule)
                                     ctor-ci (env/lookup env ctor-name)
                                ;; Find recursive field indices
                                     rec-indices
                                     (when (.isRec ind-ci)
                                       (let [ct (.type ctor-ci)]
                                         (loop [ty ct skip (.numParams ctor-ci) j 0 acc []]
                                           (if (or (not (e/forall? ty)) (>= j nf))
                                             acc
                                             (if (pos? skip)
                                               (recur (e/forall-body ty) (dec skip) j acc)
                                               (let [ft (e/forall-type ty)
                                                     is-rec (ansatz.inductive/occurs-in?
                                                             ft (name/from-string ind-name-str))
                                                     _ (when (and is-rec (e/forall? ft))
                                                         (throw (ex-info "Codegen: functional recursive field requires kernel rule lowering"
                                                                         {:kind :codegen-error :recursor h
                                                                          :constructor (name/->string ctor-name)
                                                                          :field j})))]
                                                 (recur (e/forall-body ty) 0 (inc j)
                                                        (if is-rec (conj acc j) acc))))))))
                                     field-syms (mapv #(symbol (str field-prefix %)) (range nf))
                                     ih-syms (mapv #(symbol (str "ih" (gensym "") "_" %)) (or rec-indices []))]
                                 {:idx i :cidx (.cidx ^ConstantInfo ctor-ci)
                                  :nfields nf :minor minor :minor-ansatz minor-ansatz-expr
                                  :field-syms field-syms
                                  :rec-indices (or rec-indices []) :ih-syms ih-syms}))
                             rules)]
                  ;; Generate case dispatch
                        (let [t-sym (gensym "t_")
                              all-zero (every? #(zero? (:nfields %)) clauses)
                              has-rec (some #(seq (:rec-indices %)) clauses)
                            ;; Lean kernel inductive.h, inductive_reduce_rec: apply the
                            ;; rule to fields/IHs, beta-reducing only actual lambdas. A
                            ;; non-lambda remainder still lives in the consumed context.
                              apply-minor
                              (fn [{:keys [minor-ansatz field-syms ih-syms rec-indices]}]
                                (let [actuals (into field-syms ih-syms)
                                      compiled (compile-minor env minor-ansatz names actuals)
                                      calls (zipmap ih-syms
                                                    (map #(list self-sym (nth field-syms %)) rec-indices))]
                                ;; Share repeated IHs without forcing unused branches.
                                  (share-lazy-arguments compiled calls)))
                              field-bindings
                              (fn [{:keys [nfields field-syms]} offset]
                                (vec (mapcat
                                      (fn [i]
                                        [(nth field-syms i)
                                         (cond
                                           (= ind-name-str "List")
                                           (list (if (zero? i) 'first 'rest) t-sym)
                                           (get @structure-registry ind-name-str)
                                           (list (keyword (nth (:fields (get @structure-registry ind-name-str)) i)) t-sym)
                                           :else (list 'nth t-sym (+ offset i)))])
                                      (range nfields))))
                              branch (fn [clause offset]
                                       (let [bindings (field-bindings clause offset)
                                             result (apply-minor clause)]
                                         (if (seq bindings) (list 'let bindings result) result)))
                              body
                              (cond
                          ;; General tagged inductive (e.g. Value, 11 ctors mixed arity):
                          ;; dispatch on the cidx tag in slot 0; each branch binds its
                          ;; fields from (nth t (inc i)) and inlines IH as (self (nth t (inc ri))).
                          ;; The recursion (if any) rides the surrounding letfn self-sym.
                                (tagged-inductive? env ind-name-str)
                                (list* 'case (list 'nth t-sym 0)
                                       (concat (mapcat (fn [clause] [(:cidx clause) (branch clause 1)]) clauses)
                                               [(list 'throw (list 'ex-info "no matching ctor (tagged rep)"
                                                                   (list 'array-map :tag (list 'nth t-sym 0))))]))

                                all-zero
                                (enum-dispatch env rec-ci t-sym (mapv :minor clauses) args names)

                          ;; Nat.rec: Nat is native longs, not nil/vector
                                (and (= ind-name-str "Nat")
                                     (= 2 (count clauses))
                                     (zero? (:nfields (first clauses))))
                                (let [node-c (second clauses)
                                      pred-sym (first (:field-syms node-c))]
                                  (list 'if (list 'zero? t-sym)
                                        (apply-minor (first clauses))
                                        (list 'let [pred-sym (list 'dec t-sym)] (apply-minor node-c))))

                          ;; Leaf + node: first ctor 0 fields, others have fields
                                (and (= 2 (count clauses))
                                     (zero? (:nfields (first clauses))))
                                (list 'if (if (= ind-name-str "List")
                                            (list 'not (list 'seq t-sym))
                                            (list 'nil? t-sym))
                                      (apply-minor (first clauses))
                                      (branch (second clauses) 0))

                              ;; One constructor keeps the existing untagged field vector
                              ;; (or registered structure map/record).
                                (= 1 (count clauses))
                                (branch (first clauses) 0)

                                :else
                                (throw (ex-info "Codegen: unsupported recursor shape"
                                                {:kind :codegen-error :recursor h})))]

                    ;; Wrap in letfn only if the emitted body actually SELF-RECURSES (an IH
                    ;; landed in it) — a casesOn-derived dispatch never uses its IHs, and the
                    ;; `let` form keeps downstream self-calls (storedef recur) in tail position.
                          (let [rec-result
                                (if (and has-rec
                                         (some #(= self-sym %) (tree-seq coll? seq body)))
                                  (list 'letfn [(list self-sym [t-sym] body)]
                                        (list self-sym major))
                              ;; Non-recursive: just apply directly
                                  (list 'let [t-sym major] body))
                            ;; Extra args beyond major? Apply them (fuel-based WF pattern).
                                extra-args (if eta-major? [] (subvec ca (inc major-idx)))
                                applied (reduce (fn [f a] (list f a)) rec-result extra-args)]
                          ;; eta-wrap when the recursor was a bare function value
                            (if eta-major? (list 'fn [eta-major-sym] applied) applied))))))
            ;; @[extern] native primitive with no builtin/registry lowering: emit a clear throw
            ;; rather than a bare symbol applied to args (opaque ClassNotFoundException).
                  (or (extern-unhandled-form env h)
            ;; Unfold a match auxiliary / casesOn: beta-apply its definition to args and recurse,
            ;; so it lands on the `.rec` path codegen already compiles (instead of a bare symbol).
                      (when (match-aux? h)
                        (when-let [ci (env/lookup env (e/const-name head))]
                          (when-let [v (.value ^ConstantInfo ci)]
                            (ansatz->clj env (beta-apply v args) names))))
            ;; Structure OWN-field projection {Struct}.{field}: keyword access on the self argument,
            ;; applied FLAT to any extra args. This is the Lean-faithful instance-projection lowering
            ;; (mirrors the e/proj? path) — a binary op field like `add` lowers to `((:add rec) x y)`
            ;; = `(+ x y)`, NOT the broken curried `(((:add rec) x) y)`. With < self+1 args it lowers
            ;; the op as a VALUE (`(:add rec)` → the fn), so passing `add` as a fold step also works.
                      (when-let [{:keys [strukt np fidx]} (own-proj-info env h)]
                        (when (> (count args) np)                       ; self argument present
                          (let [self  (resolve-mk env (nth args np))    ; collapse projection chains
                                margs (mk-args strukt self)
                                op-code
                                (if (and margs (> (count margs) (+ np fidx)))
                                  ;; concrete instance literal: project the field DIRECTLY to the
                                  ;; carrier op — Lean-style monomorphization. NEVER builds the record,
                                  ;; so erased Prop/proof fields never reach the output.
                                  (ansatz->clj env (nth margs (+ np fidx)) names)
                                  ;; symbolic instance: keyword access on the lowered record.
                                  (list (keyword (subs h (inc (.lastIndexOf ^String h ".")))) (nth ca np)))
                                extra (subvec ca (inc np))]
                            (if (seq extra) (apply list op-code extra) op-code))))
            ;; Reducible (:abbrev) def with no runtime lowering — a structure projection or an
            ;; inherited instance accessor (a/structure generates these `:abbrev`). INLINE it
            ;; (Lean's compiler specializes reducible / instance-method defs): beta-apply the body
            ;; to args and recurse. This collapses a typeclass-method projection over a concrete
            ;; instance to the carrier op — `WAddMonoid.add S (mk … add …)` reduces to `proj … add`,
            ;; which the e/proj? path lowers to keyword access on the defrecord — WITHOUT unfolding
            ;; the op itself: abbrevs are height-0 (non-recursive), so recursion stops at the first
            ;; regular def (e.g. `Nat.add`, which lowers normally). Guarded `not arity-registry` so a
            ;; runtime-compiled fn is still CALLED, not inlined. Lets the optimizer emit
            ;; `[inst : WSemiring S]`-parameterized laws whose rhs stays executable.
                      (when-not (get @arity-registry h)
                        (when-let [ci (env/lookup env (e/const-name head))]
                          (when (and (= ConstantInfo/HINTS_ABBREV (.getHints ^ConstantInfo ci))
                                     (some? (.value ^ConstantInfo ci)))
                            (ansatz->clj env (beta-apply (.value ^ConstantInfo ci) args) names))))
            ;; Plain (non-abbrev) recursive/wrapper store def: compile it from its exported
            ;; equation lemma (f.eq_def) or non-recursive value (ansatz.codegen.storedef),
            ;; which interns + registers {:arity :erased :sym}, then re-dispatch (hits the
            ;; :sym-aware registry path below). All builtin/numeric/instance-field
            ;; lowerings above are exhausted here, so this is a terminal request;
            ;; optional replacement probes use storedef-compile? instead.
                      (when (and *compile-store-defs* (not (contains? @arity-registry h)))
                        (when (storedef-compile! env h)
                          (ansatz->clj env expr names)))
            ;; User-defined function: arity-aware compilation (Lean 4 FAP/PAP).
            ;; Check the arity registry to determine call style.
                      (if-let [cc (when-not (contains? *raw-constants* h) (get @arity-registry h))]
                        (decl/apply-args cc (or (:sym cc) (symbol h)) ca)
                        (reduce (fn [f a] (list f a)) (symbol h) ca))))))))

        (let [compiled (mapv #(ansatz->clj env % names) (cons head args))
              cc (when (e/bvar? head)
                   (get *local-conventions* (- (count names) (inc (e/bvar-idx head)))))]
          (if cc (decl/apply-args cc (first compiled) (vec (rest compiled)))
              (reduce (fn [f a] (list f a)) compiled)))))
    (e/const? expr) (let [cn0 (name/->string (e/const-name expr))
                          ;; @[csimp] also redirects an op in VALUE position to its verified replacement.
                          g (csimp-target env cn0)
                          expr (if g (e/const' (name/from-string g) (e/const-levels expr)) expr)
                          cn (or g cn0)]
                      ;; ops in VALUE position (a fold step, a passed comparator) lower to the
                      ;; runnable Clojure op, not a bare (unresolvable) symbol — `find` so a
                      ;; false/0 lowering isn't mistaken for "absent".
                      (record-value-head cn
                                         (cond
                                           (contains? builtin-value cn) (get builtin-value cn)
                                           (contains? @codegen-registry cn) ((get @codegen-registry cn) env expr names)
                                           :else
                        ;; Check if it's a constructor
                                           (if-let [ci (env/lookup env (e/const-name expr))]
                                             (if (.isCtor ^ConstantInfo ci)
                            ;; A 0-field ctor of a TAGGED inductive (e.g. Value.vnil) is
                            ;; [cidx], NOT the enum nil/index rep — must match the recursor's
                            ;; (nth t 0) dispatch and the edn->value encoding. (A bare
                            ;; MULTI-field tagged ctor is still a function → symbol.)
                                               (let [ind-nm (let [s cn, di (.lastIndexOf ^String s ".")]
                                                              (when (pos? di) (subs s 0 di)))]
                                                 (cond
                                                   (and (zero? (.numFields ci)) ind-nm (tagged-inductive? env ind-nm))
                                                   [(.cidx ci)]
                                                   (zero? (.numFields ci))
                                ;; 0-field ctor: use index for enum dispatch.
                                                   (let [cidx (.cidx ci)]
                                                     (if (zero? cidx) nil cidx))
                                                   :else (symbol cn)))
                                               (if-let [cg (get @codegen-registry cn)]
                                                 (cg env expr names)
                              ;; VALUE position (fold step, comparator): a storedef-compiled
                              ;; var supports curried application via its partial-arity
                              ;; methods — emit the qualified symbol. @[extern] primitives
                              ;; keep their explanatory throw BEFORE any compile attempt
                              ;; (native reps — String — may not match the Lean reference
                              ;; body), mirroring the app-position ordering.
                                                 (or (:sym (get @arity-registry cn))
                                                     (extern-unhandled-form env cn)
                                                     (when *compile-store-defs*
                                                       (:sym (storedef-compile! env cn)))
                                                     (symbol cn))))
                                             (if-let [cg (get @codegen-registry cn)]
                                               (cg env expr names)
                                               (or (:sym (get @arity-registry cn))
                                                   (extern-unhandled-form env cn) (symbol cn)))))))
    ;; Projection: Expr.proj type-name idx struct
    ;; For structures with defrecord: keyword access (:field-name struct)
    ;; For others: (nth struct idx)
    (e/proj? expr)
    (let [type-name-str (name/->string (e/proj-type-name expr))
          idx (e/proj-idx expr)
          struct-expr (ansatz->clj env (e/proj-struct expr) names)
          struct-info (get @structure-registry type-name-str)]
      (if (and struct-info (< idx (count (:fields struct-info))))
        ;; Structure with defrecord: keyword access
        (list (keyword (nth (:fields struct-info) idx)) struct-expr)
        ;; Fallback: nth on vector
        (list 'nth struct-expr idx)))
    (e/let? expr) (let [n (or (e/let-name expr) "x")
                        value (e/let-value expr)
                        compiled (ansatz->clj env value names)
                        cc (cond
                             (e/const? value) (get @arity-registry (::resolved-head (meta compiled)))
                             (e/bvar? value) (get *local-conventions*
                                                  (- (count names) (inc (e/bvar-idx value)))))]
                    (list 'let [(symbol n) compiled]
                          (binding [*local-conventions* (assoc *local-conventions* (count names) cc)]
                            (ansatz->clj env (e/let-body expr) (types/bind-type names n (e/let-type expr))))))
    :else expr))

