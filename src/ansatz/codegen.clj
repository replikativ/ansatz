(ns ansatz.codegen
  "Codegen — compile a kernel Expr to a Clojure form for eval (`ansatz->clj`) plus the built-in
   lowering tables (`builtin-app`/`builtin-value`). Extracted from ansatz.core. Reads the shared
   registries in ansatz.surface.ingest (structure/codegen/arity) and the structural ctor/recursor/
   arity machinery; the runtime (wandler) augments lowering via `codegen-registry`."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.inductive :as inductive]
            [ansatz.surface.ingest :as ingest :refer [structure-registry codegen-registry arity-registry]])
  (:import [ansatz.kernel ConstantInfo]))

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
    (= (count ca) 1)  (let [g (gensym "b")] (list 'clojure.core/fn [g] (emit2 (nth ca 0) g)))
    :else (let [g1 (gensym "a") g2 (gensym "b")] (list 'clojure.core/fn [g1 g2] (emit2 g1 g2)))))

(clojure.core/defn- tagged-inductive?
  "True when an inductive's runtime representation is the GENERAL tagged vector
   `[cidx field…]` (so both constructors and the recursor dispatch on the cidx in
   slot 0). Excludes the inductives that keep a NATIVE representation: List (cons
   seq), Nat (long), registered structures (defrecord/map), and all-zero enums
   (a bare index). The remaining shape — a multi-constructor inductive where at
   least one constructor carries fields (e.g. the EDN `Value` universe) — needs
   the tag to discriminate ctors that would otherwise collide (`vint i`/`vbool b`
   both being one-field). Mirrors `wandler.surface.edn/edn->value`'s encoding."
  [env ind-name-str]
  (and (not (#{"List" "Nat"} ind-name-str))
       (not (get @structure-registry ind-name-str))
       (when-let [ind-ci (env/lookup env (name/from-string ind-name-str))]
         (let [ctors (.ctors ^ConstantInfo ind-ci)]
           ;; >2 ctors with fields: needs the cidx tag to discriminate (e.g. Value's 11
           ;; ctors). Strictly ≤2-ctor shapes keep their NATIVE reps — Bool-like enums
           ;; (index) and leaf+node (nil / (vec fields), nil-dispatched by the leaf+node
           ;; recursor branch) — so a 2-ctor tree's hand-built [color l k r] rep is unchanged.
           (and ctors (> (alength ctors) 2)
                (boolean (some (fn [cn] (when-let [cci (env/lookup env cn)]
                                          (pos? (.numFields ^ConstantInfo cci))))
                               ctors)))))))

(declare ansatz->clj)

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

(clojure.core/defn- bi-const "App handler for a nullary constant." [v] (fn [_ _ _ _ _] v))

(def ^:private builtin-app
  (merge
   ;; n-ary arithmetic / comparison saturating to a bare op
   {"Nat.add"  (bi-nary '+)  "Nat.mul"  (bi-nary '*)  "Nat.div" (bi-nary 'quot)
    "Nat.max"  (bi-nary 'max) "Nat.min" (bi-nary 'min)
    "Nat.blt"  (bi-nary '<)  "Nat.ble"  (bi-nary '<=) "Nat.beq" (bi-nary '==)
    "Float.add" (bi-nary '+) "Float.sub" (bi-nary '-) "Float.mul" (bi-nary '*) "Float.div" (bi-nary '/)}
   ;; n-ary ops whose saturated form is a composite expr
   {"Nat.sub"  (bi-nary2 (fn [x y] (list 'max 0 (list '- x y))))   ; truncated Nat subtraction
    "Nat.pow"  (bi-nary2 (fn [x y] (list 'long (list 'Math/pow x y))))
    ;; Lean Nat.mod n 0 = n (total); Clojure (mod n 0) throws — guard faithfully.
    "Nat.mod"  (bi-nary2 (fn [x y] (list 'if (list 'zero? y) x (list 'mod x y))))
    "Bool.or"  (bi-nary2 (fn [x y] (list 'or x y)))
    "Bool.and" (bi-nary2 (fn [x y] (list 'and x y)))
    ;; heterogeneous H* ops carry [α β γ inst …] — drop the 4-arg type/instance prefix
    "HAdd.hAdd" (bi-nary2 (fn [x y] (list '+ x y)) 4)
    "HMul.hMul" (bi-nary2 (fn [x y] (list '* x y)) 4)
    "HSub.hSub" (bi-nary2 (fn [x y] (list 'max 0 (list '- x y))) 4)
    "HDiv.hDiv" (bi-nary2 (fn [x y] (list 'quot x y)) 4)
    "HPow.hPow" (bi-nary2 (fn [x y] (list 'long (list 'Math/pow x y))) 4)}
   ;; nullary constants
   {"Bool.true" (bi-const true) "Bool.false" (bi-const false) "Nat.zero" (bi-const 0)
    "List.nil"  (bi-const nil)}
   ;; small structural lowerings + control flow + refinement erasure (bespoke handlers)
   {"Nat.succ"      (fn [_ _ _ ca _] (list 'inc (nth ca 0)))
    "Bool.not"      (fn [_ _ _ ca _] (list 'not (nth ca 0)))
    "ite"           (fn [_ _ _ ca _] (list 'if (nth ca 1) (nth ca 3) (nth ca 4)))
    "List.cons"     (fn [_ _ _ ca _] (list 'clojure.core/cons (nth ca 1) (nth ca 2)))
    "List.length"   (fn [_ _ _ ca _] (list 'count (nth ca 1)))
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
                        (ansatz->clj env (e/lam-body then-fn) (conj names "_h"))
                        (nth ca 3))
            else-body (if (e/lam? else-fn)
                        (ansatz->clj env (e/lam-body else-fn) (conj names "_h"))
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
                              (ansatz->clj env f-body-2 (conj names x-name ih-name)))
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
        (list 'apply (ansatz->clj env head names) ca)))}))

(def ^:private builtin-value
  "head → clj-form for an op in VALUE position (a fold step `+`, a passed comparator)."
  {"Nat.zero" 0 "Bool.true" true "Bool.false" false
   "Nat.add" '+ "Nat.mul" '* "Nat.succ" 'inc "Nat.div" 'quot
   "Nat.beq" '== "Nat.ble" '<= "Nat.blt" '<
   "Nat.sub" '(fn [a b] (max 0 (- a b)))
   ;; Unit/PUnit's single value → nil (the unit thunks an unfolded match auxiliary applies its branches to).
   "Unit.unit" nil "PUnit.unit" nil})

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

(clojure.core/defn- csimp-target
  "Lean @[csimp]: a kernel-proven `f = g` registered as f→g in the :csimp env extension (by a/csimp,
   or inherited from Lean via ansatz.attrs) licenses the COMPILER to emit g wherever f appears — g is
   the faster/runnable equivalent, justified by the proof. Return g when head `h` has such a
   replacement AND g is lowerable here; else nil (fall back to f unchanged). The lowerability guard is
   essential: inherited compiler-internal targets (Nat.rec→Nat.recCompiled, List.length→List.lengthTR)
   are NOT in the store and must not replace a working head with an unrunnable one."
  [env h]
  (when-let [g (get (env/get-extension env :csimp {}) h)]
    (when (or (builtin-app g) (contains? builtin-value g) (contains? @codegen-registry g)
              (some? (env/lookup env (name/from-string g))))
      g)))

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
      (if as (e/app* v (vec as)) v))))

(clojure.core/defn ansatz->clj
  "Compile Ansatz Expr to Clojure form for eval."
  [env expr names]
  (cond
    (e/lit-nat? expr) (e/lit-nat-val expr)
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
                          (ansatz->clj env (e/lam-body expr) (conj names n))))
    (e/app? expr)
    (let [[head args] (e/get-app-fn-args expr)]
      (if (e/const? head)
        (let [h0 (name/->string (e/const-name head))
              ;; @[csimp]: rewrite the head to its verified replacement g before any lowering, so
              ;; everything downstream (builtin/registry/ctor/recursor) dispatches on g.
              g (csimp-target env h0)
              head (if g (e/const' (name/from-string g) (e/const-levels head)) head)
              h (or g h0)
              ca (mapv #(ansatz->clj env % names) args)]
          (if-let [bi (builtin-app h)]
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
                    (let [np (.numParams rec-ci)
                          nm (.numMotives rec-ci)
                          nmin (.numMinors rec-ci)
                          minor-start (+ np nm)
                          major-idx (+ minor-start nmin)
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
                                                           ft (name/from-string ind-name-str))]
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
                            apply-minor (fn [clause args]
                                          (reduce (fn [f a] (list f a))
                                                  (:minor clause) args))
                            body
                            (cond
                          ;; General tagged inductive (e.g. Value, 11 ctors mixed arity):
                          ;; dispatch on the cidx tag in slot 0; each branch binds its
                          ;; fields from (nth t (inc i)) and inlines IH as (self (nth t (inc ri))).
                          ;; The recursion (if any) rides the surrounding letfn self-sym.
                              (tagged-inductive? env ind-name-str)
                              (let [branches
                                    (mapcat
                                     (fn [{:keys [cidx nfields field-syms rec-indices ih-syms minor-ansatz]}]
                                       (let [bindings (vec (mapcat (fn [i] [(nth field-syms i)
                                                                            (list 'nth t-sym (inc i))])
                                                                   (range nfields)))
                                             n-ih (count rec-indices)
                                             all-names (into (mapv str field-syms) (mapv str ih-syms))
                                             minor-body (loop [e minor-ansatz n (+ nfields n-ih)]
                                                          (if (and (pos? n) (e/lam? e))
                                                            (recur (e/lam-body e) (dec n)) e))
                                             compiled-body (ansatz->clj env minor-body (into names all-names))
                                             ih-replacements
                                             (into {} (map (fn [j ri]
                                                             [(nth ih-syms j)
                                                              (list self-sym (list 'nth t-sym (inc ri)))])
                                                           (range n-ih) rec-indices))
                                             major-sym (when (symbol? major) major)
                                             inline-all (fn inline-all [form]
                                                          (cond
                                                            (and (symbol? form) (contains? ih-replacements form))
                                                            (get ih-replacements form)
                                                            (and major-sym (symbol? form) (= form major-sym)) t-sym
                                                            (seq? form) (apply list (map inline-all form))
                                                            (vector? form) (mapv inline-all form)
                                                            :else form))
                                             node-body (inline-all compiled-body)]
                                         [cidx (if (seq bindings) (list 'let bindings node-body) node-body)]))
                                     clauses)]
                                (list* 'case (list 'nth t-sym 0)
                                       (concat branches
                                               [(list 'throw (list 'ex-info "no matching ctor (tagged rep)"
                                                                   (list 'array-map :tag (list 'nth t-sym 0))))])))

                          ;; Enum: all ctors have 0 fields (Bool, Color, etc.)
                              (and all-zero (= 2 (count clauses)))
                          ;; Bool-like: (if value minor_1 minor_0)
                          ;; ctor 0 = falsy (nil/false), ctor 1 = truthy
                              (list 'if t-sym
                                    (:minor (second clauses))
                                    (:minor (first clauses)))

                              all-zero  ;; 3+ ctor enum
                              (list* 'case t-sym
                                     (mapcat (fn [{:keys [idx minor]}] [idx minor])
                                             clauses))

                          ;; Nat.rec: Nat is native longs, not nil/vector
                              (and (= ind-name-str "Nat")
                                   (= 2 (count clauses))
                                   (zero? (:nfields (first clauses))))
                              (let [leaf-c (first clauses)
                                    node-c (second clauses)
                                    pred-sym (first (:field-syms node-c))
                                ;; Nat.succ has 1 field: predecessor
                                    bindings [pred-sym (list 'dec t-sym)]
                                    minor-ansatz (:minor-ansatz node-c)
                                    n-ih (count (:rec-indices node-c))
                                    all-names (into (mapv str (:field-syms node-c))
                                                    (mapv str (:ih-syms node-c)))
                                    minor-body (loop [e minor-ansatz n (+ 1 n-ih)]
                                                 (if (and (pos? n) (e/lam? e))
                                                   (recur (e/lam-body e) (dec n))
                                                   e))
                                    compiled-body (ansatz->clj env minor-body
                                                               (into names all-names))
                                    ih-replacements
                                    (into {} (map (fn [j ri]
                                                    [(nth (:ih-syms node-c) j)
                                                     (list self-sym (nth (:field-syms node-c) ri))])
                                                  (range n-ih) (:rec-indices node-c)))
                                    major-sym (when (symbol? major) major)
                                    inline-all (fn inline-all [form]
                                                 (cond
                                                   (and (symbol? form) (contains? ih-replacements form))
                                                   (get ih-replacements form)
                                                   (and major-sym (symbol? form) (= form major-sym))
                                                   t-sym
                                                   (seq? form) (apply list (map inline-all form))
                                                   (vector? form) (mapv inline-all form)
                                                   :else form))
                                    node-body (inline-all compiled-body)]
                                (list 'if (list 'zero? t-sym)
                                      (:minor leaf-c)
                                      (list 'let bindings node-body)))

                          ;; Leaf + node: first ctor 0 fields, others have fields
                              (and (= 2 (count clauses))
                                   (zero? (:nfields (first clauses))))
                              (let [leaf-c (first clauses)
                                    node-c (second clauses)
                                    nf (:nfields node-c)
                                ;; Field bindings: [color (nth t 0) left (nth t 1) ...]
                                ;; For List: use first/rest instead of nth (native seq interop)
                                ;; Also bind the discriminant name to t-sym so that
                                ;; references to the matched value inside the body
                                ;; see the current node, not the outer parameter.
                                    is-list (= ind-name-str "List")
                                    bindings (vec (mapcat (fn [i]
                                                            [(nth (:field-syms node-c) i)
                                                             (if is-list
                                                               (case (int i)
                                                                 0 (list 'first t-sym)
                                                                 1 (list 'rest t-sym))
                                                               (list 'nth t-sym i))])
                                                          (range nf)))
                                ;; Unwrap minor Ansatz lambdas to get the body
                                ;; Then compile body with field names + IH inlined as (rec field)
                                    minor-ansatz (:minor-ansatz node-c)
                                ;; Unwrap nf + n-ih lambdas
                                    n-ih (count (:rec-indices node-c))
                                    all-names (into (mapv str (:field-syms node-c))
                                                    (mapv str (:ih-syms node-c)))
                                    minor-body (loop [e minor-ansatz n (+ nf n-ih)]
                                                 (if (and (pos? n) (e/lam? e))
                                                   (recur (e/lam-body e) (dec n))
                                                   e))
                                ;; Compile body with names for fields + IH symbols
                                    compiled-body (ansatz->clj env minor-body
                                                               (into names all-names))
                                ;; Replace IH symbols with inline recursive calls
                                ;; ih_sym → (self_fn field_sym) — lazy, only evaluated when needed
                                    ih-replacements
                                    (into {} (map (fn [j ri]
                                                    [(nth (:ih-syms node-c) j)
                                                     (list self-sym (nth (:field-syms node-c) ri))])
                                                  (range n-ih) (:rec-indices node-c)))
                                  ;; Replace major-premise references with t-sym.
                                  ;; When the body references the matched value (e.g., `l`
                                  ;; in `(cons x l)` inside a match on `l`), it should
                                  ;; refer to the current node in the recursion, not the
                                  ;; outer function parameter.
                                    major-sym (when (symbol? major) major)
                                    inline-all (fn inline-all [form]
                                                 (cond
                                                   (and (symbol? form) (contains? ih-replacements form))
                                                   (get ih-replacements form)
                                                   (and major-sym (symbol? form) (= form major-sym))
                                                   t-sym
                                                   (seq? form) (apply list (map inline-all form))
                                                   (vector? form) (mapv inline-all form)
                                                   :else form))
                                    node-body (inline-all compiled-body)]
                              ;; For List: use (not (seq t)) since (rest (cons x nil)) = ()
                                (list 'if (if is-list
                                            (list 'not (list 'seq t-sym))
                                            (list 'nil? t-sym))
                                      (:minor leaf-c)
                                      (list 'let bindings node-body)))

                              :else
                              (list 'throw (list 'ex-info "unsupported rec pattern" {})))]
                    ;; Wrap in letfn only if recursive, otherwise just inline
                        (let [rec-result
                              (if has-rec
                                (list 'letfn [(list self-sym [t-sym] body)]
                                      (list self-sym major))
                              ;; Non-recursive: just apply directly
                                (list 'let [t-sym major] body))
                            ;; Extra args beyond major? Apply them (fuel-based WF pattern).
                              extra-args (if eta-major? [] (subvec ca (inc major-idx)))
                              applied (reduce (fn [f a] (list f a)) rec-result extra-args)]
                          ;; eta-wrap when the recursor was a bare function value
                          (if eta-major? (list 'fn [eta-major-sym] applied) applied)))))
            ;; @[extern] native primitive with no builtin/registry lowering: emit a clear throw
            ;; rather than a bare symbol applied to args (opaque ClassNotFoundException).
                  (or (extern-unhandled-form env h)
            ;; Unfold a match auxiliary / casesOn: beta-apply its definition to args and recurse,
            ;; so it lands on the `.rec` path codegen already compiles (instead of a bare symbol).
                      (when (match-aux? h)
                        (when-let [ci (env/lookup env (e/const-name head))]
                          (when-let [v (.value ^ConstantInfo ci)]
                            (ansatz->clj env (beta-apply v args) names))))
            ;; User-defined function: arity-aware compilation (Lean 4 FAP/PAP).
            ;; Check the arity registry to determine call style.
                      (let [{:keys [arity erased]} (get @arity-registry h)]
                        (if (and arity (> arity 1) (>= (count ca) (+ arity erased)))
                    ;; FAP (full application): flat multi-arg call, skip erased prefix
                          (let [rt-args (subvec ca erased (+ erased arity))]
                            (apply list (symbol h) rt-args))
                    ;; Curried (unknown arity, single-arg, or partial application)
                          (reduce (fn [f a] (list f a)) (symbol h) ca)))))))))
        (let [compiled (mapv #(ansatz->clj env % names) (cons head args))]
          (reduce (fn [f a] (list f a)) compiled))))
    (e/const? expr) (let [cn0 (name/->string (e/const-name expr))
                          ;; @[csimp] also redirects an op in VALUE position to its verified replacement.
                          g (csimp-target env cn0)
                          expr (if g (e/const' (name/from-string g) (e/const-levels expr)) expr)
                          cn (or g cn0)]
                      ;; ops in VALUE position (a fold step, a passed comparator) lower to the
                      ;; runnable Clojure op, not a bare (unresolvable) symbol — `find` so a
                      ;; false/0 lowering isn't mistaken for "absent".
                      (if-let [e (find builtin-value cn)]
                        (val e)
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
                              (or (extern-unhandled-form env cn) (symbol cn))))
                          (if-let [cg (get @codegen-registry cn)]
                            (cg env expr names)
                            (or (extern-unhandled-form env cn) (symbol cn))))))
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
    (e/let? expr) (let [n (or (e/let-name expr) "x")]
                    (list 'let [(symbol n) (ansatz->clj env (e/let-value expr) names)]
                          (ansatz->clj env (e/let-body expr) (conj names n))))
    :else expr))

