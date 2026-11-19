(ns ansatz.clj-model.boundary
  "Where the DSL's types meet the Clojure model: codecs `enc_T : T → CljM.V`,
   `dec_T : CljM.V → Option T` and a default `d_T`, and `define-modelled`, the
   `a/foreign ^:model` branch that turns a foreign function's axiom into a definition:

     f.clj : CljM.V → … → Option CljM.V          the translated source (kernel-checked)
     f     : T → … → R := λ x…, Option.getD (Option.bind (f.clj (enc x)…) dec_R) d_R

   `f` is marked irreducible; its runtime is the user's function (Lean's @[implemented_by]).
   Status :tested (the default) stores the conformance statement
     f.conforms : ∀ x…, Option.isSome (Option.bind (f.clj (enc x)…) dec_R) = true
   (never as an axiom) and the runtime checks dec_R on every result; `(a/conforms f tactics…)`
   proves it (without tactics: ansatz.clj-model.proof/default-script), adds
   f.spec : ∀ x…, Option.bind (f.clj (enc x)…) dec_R = some (f x), and the status becomes :proved.
   `(a/port f g)` then proves `f x… = g x…` for an `a/defn g`, registers it as `a/csimp` and makes
   g the runtime: :ported. `^:paranoid` (or `paranoid!`) runs the model next to the impl on
   every call and throws where they differ (`paranoid-call`).

   The :tested gap. In :tested, `f` is a definition proofs can unfold (marking it irreducible
   stops Meta unfolding, but `rfl`, `decide` and `simp` reach the kernel), so a theorem about `f`
   holds of the MODEL, which answers the default d_R where it makes no claim: for
   `(fn [x] (+ x 1))` at Int, `f Long/MAX_VALUE = 0` is provable while the impl throws. The
   runtime never returns that d_R (it runs the impl, and rejects a result dec_R refuses).
   :proved closes the gap for inputs of the declared types: f.conforms says the model answers
   on all of them, and f.spec ties `f` to that answer.

   G1 codecs: Nat (dec requires 0 ≤ i), Int, Bool, String and the DSL `Value`
   (ansatz.surface.data; `CljM.ofValue` dedupes map entries first-wins like value->edn,
   `CljM.toValue?` maps list/vector/ordered seq to vvec like edn->value, and is none for a
   map over 8 entries or a set over 1 element, whose runtime order is the hash order).

   G2 codecs, generated per type as `CljM.enc_<T>` / `CljM.dec_<T>` over polymorphic helpers:
   `List T` (a vector; dec accepts nil, a list, a vector or an ordered seq), `Option T` (`none`
   is nil; refused when T's decoder accepts nil, Option Bool is fine), `Prod A B` (a 2-vector),
   Float (a double), an `a/structure` (a map with the field names as keywords; dec reads the
   fields and ignores other keys) and `Subtype T P` (a parameter only: its value, by T's codec). The runtime
   conversion of such an argument is its compiled enc_T then cljv->edn, so the impl receives
   exactly the value the model reads."
  (:require [ansatz.core :as a]
            [clojure.string :as str]
            [clojure.java.io :as io]
            [ansatz.config :as config]
            [ansatz.state :as state]
            [ansatz.clj-model :as m]
            [ansatz.clj-model.proof :as proof]
            [ansatz.clj-model.translate :as translate]
            [ansatz.codegen.decl :as decl]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.surface.elaborate :as elab]
            [ansatz.surface.ingest :as ingest]))

;; ── Kernel codecs ───────────────────────────────────────────────────────────────────────

(defn- defm [nm params ret body]
  (list 'ansatz.core/defn nm (vec (mapcat (fn [[p t]] [p :- t]) params)) ret body))

(defn- dec-form [nm ty ct body]
  (defm nm '[[v CljM.V]] (list 'Option ty)
    (list* 'match 'v 'CljM.V (list 'Option ty)
           (map (fn [[c fs]]
                  (if (= c ct) (list c '[i] body)
                      (let [none (list (symbol "@Option.none") ty)]
                        (if (empty? fs) (list c none) (list c (vec (repeatedly (count fs) #(gensym "_"))) none)))))
                m/ctors))))

(def ^:private scalar-forms
  [(defm 'CljM.encNat '[[n Nat]] 'CljM.V '(CljM.V.vlong (Int.ofNat n)))
   (dec-form 'CljM.decNat 'Nat 'vlong (list 'if '(<= 0 i) '(Option.some (Int.toNat i)) (list (symbol "@Option.none") 'Nat)))
   (defm 'CljM.encInt '[[n Int]] 'CljM.V '(CljM.V.vlong n))
   (dec-form 'CljM.decInt 'Int 'vlong '(Option.some i))
   (defm 'CljM.encBool '[[b Bool]] 'CljM.V '(CljM.V.vbool b))
   (dec-form 'CljM.decBool 'Bool 'vbool '(Option.some i))
   (defm 'CljM.encString '[[s String]] 'CljM.V '(CljM.V.vstr s))
   (dec-form 'CljM.decString 'String 'vstr '(Option.some i))
   ;; once, for f.spec: a conforming result is `some` of its getD
   '(ansatz.core/theorem CljM.some_getD [α :- Type, o :- (Option α), d :- α,
                                         h :- (= Bool (Option.isSome o) true)]
                         (= (Option α) o (Option.some (Option.getD o d)))
                         (cases o) (simp_all) (rfl))])

(def ^:private value-ctors
  '[[vnil 0] [vbool 1] [vint 1] [vstr 1] [vkw 1] [vcons 2] [vvec 1] [vmap 1] [ventry 3] [vfloat 1] [vset 1]])

(defn- value-match [disc ret arms]
  (list* 'match disc 'Value ret
         (map (fn [[c ar]] (let [[bs body] (get arms c)] (if (zero? ar) (list c body) (list c bs body))))
              value-ctors)))

(def ^:private value-forms
  (let [V (fn [c & xs] (let [s (symbol (str "CljM.V." c))] (if (seq xs) (list* s xs) s)))
        OVal '(Option Value)
        noneVal (list (symbol "@Option.none") 'Value)
        bindVal (fn [x v body] (list 'Option.bind x (list 'fn [v :- 'Value] body)))]
    [;; first-wins dedupe of a map chain / set chain (undecided key equality counts as distinct)
     (defm 'CljM.dropKey '[[k CljM.V] [c CljM.V]] 'CljM.V
       (m/vm 'c 'CljM.V 'c {'ventry [['k2 'w 'r] (list 'if '(Option.getD (CljM.keq k k2) false)
                                                       '(CljM.dropKey k r) (V 'ventry 'k2 'w '(CljM.dropKey k r)))]
                            'vcons [['h 't] (list 'if '(Option.getD (CljM.keq k h) false)
                                                  '(CljM.dropKey k t) (V 'vcons 'h '(CljM.dropKey k t)))]}))
     (defm 'CljM.dedupe '[[c CljM.V]] 'CljM.V
       (m/vm 'c 'CljM.V 'c {'ventry [['k 'w 'r] (V 'ventry 'k 'w '(CljM.dropKey k (CljM.dedupe r)))]
                            'vcons [['h 't] (V 'vcons 'h '(CljM.dropKey h (CljM.dedupe t)))]}))
     ;; chain? = the Value is a chain payload (cons/entry cells) rather than a value
     (defm 'CljM.ofV '[[chain Bool] [v Value]] 'CljM.V
       (value-match 'v 'CljM.V
                    {'vnil [[] (V 'vnil)]
                     'vbool [['b] (V 'vbool 'b)] 'vint [['i] (V 'vlong 'i)]
                     'vstr [['s] (V 'vstr 's)] 'vkw [['s] (V 'vkw 's)] 'vfloat [['f] (V 'vdouble 'f)]
                     'vcons [['h 't] (list 'if 'chain (V 'vcons '(CljM.ofV false h) '(CljM.ofV true t))
                                           (V 'vvec (V 'vcons '(CljM.ofV false h) '(CljM.ofV true t))))]
                     'ventry [['k 'w 'r] (list 'if 'chain (V 'ventry '(CljM.ofV false k) '(CljM.ofV false w) '(CljM.ofV true r))
                                               (V 'vnil))]
                     'vvec [['it] (V 'vvec '(CljM.ofV true it))]
                     'vmap [['e] (V 'vmap '(CljM.dedupe (CljM.ofV true e)))]
                     'vset [['it] (V 'vset '(CljM.dedupe (CljM.ofV true it)))]}))
     (defm 'CljM.ofValue '[[v Value]] 'CljM.V '(CljM.ofV false v))
     (defm 'CljM.toV '[[chain Bool] [v CljM.V]] OVal
       (let [seq-arm (fn [it] (bindVal (list 'CljM.toV true it) 'c '(Option.some (Value.vvec c))))]
         (m/vm 'v OVal noneVal
               {'vnil [[] '(Option.some Value.vnil)]
                'vbool [['b] '(Option.some (Value.vbool b))]
                'vlong [['i] (list 'if '(CljM.inLong i) '(Option.some (Value.vint i)) noneVal)]
                'vdouble [['f] '(Option.some (Value.vfloat f))]
                'vstr [['s] '(Option.some (Value.vstr s))]
                'vkw [['s] '(Option.some (Value.vkw s))]
                'vcons [['h 't] (list 'if 'chain (bindVal '(CljM.toV false h) 'h2
                                                          (bindVal '(CljM.toV true t) 't2 '(Option.some (Value.vcons h2 t2))))
                                      noneVal)]
                'ventry [['k 'w 'r] (list 'if 'chain
                                          (bindVal '(CljM.toV false k) 'k2
                                                   (bindVal '(CljM.toV false w) 'w2
                                                            (bindVal '(CljM.toV true r) 'r2 '(Option.some (Value.ventry k2 w2 r2)))))
                                          noneVal)]
                'vlist [['it] (seq-arm 'it)]
                'vvec [['it] (seq-arm 'it)]
                'vlseq [['o 'it] (list 'if 'o (seq-arm 'it) noneVal)]
                'vmap [['e] (list 'if '(<= (CljM.clen e) 8)
                                  (bindVal '(CljM.toV true e) 'c '(Option.some (Value.vmap c))) noneVal)]
                'vset [['e] (list 'if '(<= (CljM.clen e) 1)
                                  (bindVal '(CljM.toV true e) 'c '(Option.some (Value.vset c))) noneVal)]})))
     (defm 'CljM.toValue? '[[v CljM.V]] OVal '(CljM.toV false v))]))

(defn- installed-const? [n] (some? (env/lookup (a/env) (name/from-string n))))

(defn install-codecs!
  "Install the model (if needed) and the codecs; the `Value` codecs only when `Value` exists
   (ansatz.surface.data/install-core!)."
  []
  (m/install-model!)
  (locking #'install-codecs!
    (binding [a/*verbose* false config/*clj-surface* false *ns* (the-ns 'ansatz.clj-model.boundary)]
      (when-not (installed-const? "CljM.some_getD")
        (doseq [f scalar-forms] (eval f)))
      (when (and (installed-const? "Value") (not (installed-const? "CljM.toValue?")))
        (doseq [f value-forms] (eval f)))))
  :installed)

;; ── Per-type boundary ───────────────────────────────────────────────────────────────────

(defn- normalize-int [x] (if (and (instance? clojure.lang.BigInt x) (<= Long/MIN_VALUE x Long/MAX_VALUE)) (long x) x))

(defn codec
  "The boundary of a G1 type form: kernel enc/dec names, the default term, and the runtime
   conversion of a compiled argument to the Clojure value the user's function takes."
  [ty]
  (case ty
    Nat {:enc "CljM.encNat" :dec "CljM.decNat" :default 0 :->clj normalize-int}
    Int {:enc "CljM.encInt" :dec "CljM.decInt" :default 0 :->clj normalize-int}
    Bool {:enc "CljM.encBool" :dec "CljM.decBool" :default false :->clj identity}
    String {:enc "CljM.encString" :dec "CljM.decString" :default "" :->clj identity}
    Value (do (when-not (installed-const? "Value")
                (throw (ex-info (str "clj-model: the Value boundary needs the Value type "
                                     "(ansatz.surface.data/install-value-type! or install-core!)") {:type ty})))
              {:enc "CljM.ofValue" :dec "CljM.toValue?" :default 'Value.vnil
               :->clj @(requiring-resolve 'ansatz.surface.data/value->edn)})
    ((requiring-resolve 'ansatz.clj-model.boundary/compound-codec) ty)))

;; ── Compound codecs (G2) ────────────────────────────────────────────────────────────────

(defn- none-t [t] (list (symbol "@Option.none") t))
(defn- nil-list [t] (list (symbol "@List.nil") t))

(def ^:private poly-forms
  (let [A '[α :- Type :implicit] AB '[α :- Type :implicit, β :- Type :implicit]
        defn* (fn [nm params ret body] (list 'ansatz.core/defn nm params ret body))
        ;; an ordered sequential's items: a vector, a list, an ordered seq
        seq-arms (fn [ret k] {'vlist [['it] (k 'it)] 'vvec [['it] (k 'it)]
                              'vlseq [['o 'it] (list 'if 'o (k 'it) (none-t ret))]})
        pair (list 'if '(== (CljM.clen c) 2)
                   '(Option.bind (da (CljM.hd c))
                                 (fn [a :- α] (Option.bind (db (CljM.hd (CljM.tl c))) (fn [b :- β] (Option.some (Prod.mk a b))))))
                   (none-t '(Prod α β)))]
    [(defn* 'CljM.encListC (into A '[e :- (=> α CljM.V), xs :- (List α)]) 'CljM.V
       '(match xs (List α) CljM.V (nil CljM.V.vnil) (cons [h t] (CljM.V.vcons (e h) (CljM.encListC e t)))))
     (defn* 'CljM.encList (into A '[e :- (=> α CljM.V), xs :- (List α)]) 'CljM.V '(CljM.V.vvec (CljM.encListC e xs)))
     (defn* 'CljM.decListC (into A '[d :- (=> CljM.V (Option α)), c :- CljM.V]) '(Option (List α))
       (m/vm 'c '(Option (List α)) (none-t '(List α))
             {'vnil [[] (list 'Option.some (nil-list 'α))]
              'vcons [['h 't] '(Option.bind (d h) (fn [x :- α] (Option.bind (CljM.decListC d t)
                                                                            (fn [r :- (List α)] (Option.some (List.cons x r))))))]}))
     (defn* 'CljM.decList (into A '[d :- (=> CljM.V (Option α)), v :- CljM.V]) '(Option (List α))
       (m/vm 'v '(Option (List α)) (none-t '(List α))
             (assoc (seq-arms '(List α) (fn [it] (list 'CljM.decListC 'd it)))
                    'vnil [[] (list 'Option.some (nil-list 'α))])))
     (defn* 'CljM.encOption (into A '[e :- (=> α CljM.V), o :- (Option α)]) 'CljM.V
       '(match o (Option α) CljM.V (none CljM.V.vnil) (some [x] (e x))))
     (defn* 'CljM.decOption (into A '[d :- (=> CljM.V (Option α)), v :- CljM.V]) '(Option (Option α))
       (list 'if '(CljM.isNil v) (list 'Option.some (none-t 'α))
             '(Option.bind (d v) (fn [x :- α] (Option.some (Option.some x))))))
     (defn* 'CljM.encProd (into AB '[ea :- (=> α CljM.V), eb :- (=> β CljM.V), p :- (Prod α β)]) 'CljM.V
       '(CljM.V.vvec (CljM.V.vcons (ea (Prod.fst p)) (CljM.V.vcons (eb (Prod.snd p)) CljM.V.vnil))))
     (defn* 'CljM.decProd (into AB '[da :- (=> CljM.V (Option α)), db :- (=> CljM.V (Option β)), v :- CljM.V]) '(Option (Prod α β))
       (m/vm 'v '(Option (Prod α β)) (none-t '(Prod α β)) (seq-arms '(Prod α β) (fn [it] (list 'let ['c it] pair)))))
     '(ansatz.core/defn CljM.encFloat [f :- Float] CljM.V (CljM.V.vdouble f))
     (m/defm 'CljM.decFloat '[[v CljM.V]] '(Option Float) (m/vm 'v '(Option Float) (none-t 'Float) {'vdouble [['f] '(Option.some f)]}))]))

(defn- install-poly! []
  (when-not (installed-const? "CljM.decFloat")
    (binding [a/*verbose* false config/*clj-surface* false *ns* (the-ns 'ansatz.clj-model.boundary)]
      (doseq [f poly-forms] (eval f)))))

(defn- mangle [ty]
  (cond (seq? ty) (str/join "_" (map mangle ty))
        :else (str/replace (str ty) #"[^A-Za-z0-9]" "_")))

(defn- structure-fields
  "The constructor and fields [[name type-form] …] of a non-parametric a/structure `ty`, or nil."
  [ty]
  (when-let [{:keys [fields]} (and (symbol? ty) (get @ingest/structure-registry (str ty)))]
    (let [^ansatz.kernel.ConstantInfo ind (env/lookup (a/env) (name/from-string (str ty)))
          ^ansatz.kernel.ConstantInfo ctor (env/lookup (a/env) (aget (.ctors ind) 0))
          form (fn form [x] (cond (e/const? x) (symbol (name/->string (e/const-name x)))
                                  (e/app? x) (map form (cons (e/get-app-fn x) (e/get-app-args x)))
                                  :else (throw (ex-info "clj-model: a structure field type the boundary cannot name"
                                                        {:kind :clj-model/no-codec :type ty}))))]
      (when (zero? (.numParams ind))
        {:ctor (name/->string (.name ctor))
         :fields (loop [t (.type ctor) fs fields acc []]
                   (if (seq fs)
                     (do (when (e/has-loose-bvars? (e/forall-type t))
                           (throw (ex-info "clj-model: a dependent structure field" {:kind :clj-model/no-codec :type ty})))
                         (recur (e/forall-body t) (rest fs) (conj acc [(first fs) (form (e/forall-type t))])))
                     acc))}))))

(defn- define-codec! [enc forms]
  (when-not (installed-const? enc)
    (binding [a/*verbose* false config/*clj-surface* false *ns* (the-ns 'ansatz.clj-model.boundary)]
      (doseq [f forms] (eval f)))))

(defn compound-codec
  "The boundary of a compound type form (List, Option, Prod, Float, an a/structure, Subtype):
   monomorphic `CljM.enc_<T>`/`CljM.dec_<T>` defined on first use."
  [ty]
  (install-poly!)
  (let [head (if (seq? ty) (first ty) ty)
        enc (str "CljM.enc_" (mangle ty)) dec (str "CljM.dec_" (mangle ty))
        inner (when (and (seq? ty) (not= 'Subtype head)) (mapv codec (rest ty)))
        [c1 c2] inner
        sym symbol
        via-enc (fn [] (let [f (m/model-fn enc)] (fn [x] (m/cljv->edn (f x)))))
        mono (fn [enc-body dec-body]
               (define-codec! enc
                 [(list 'ansatz.core/defn (sym enc) ['x :- ty] 'CljM.V enc-body)
                  (list 'ansatz.core/defn (sym dec) ['v :- 'CljM.V] (list 'Option ty) dec-body)]))]
    (case head
      List (do (mono (list 'CljM.encList (sym (:enc c1)) 'x) (list 'CljM.decList (sym (:dec c1)) 'v))
               {:enc enc :dec dec :default (nil-list (second ty)) :nil? true :->clj (via-enc)})
      Option (do (when (:nil? c1)
                   (throw (ex-info (str "clj-model: no codec for " (pr-str ty) ": its element can be nil, so nil would be ambiguous")
                                   {:kind :clj-model/no-codec :type ty})))
                 (mono (list 'CljM.encOption (sym (:enc c1)) 'x) (list 'CljM.decOption (sym (:dec c1)) 'v))
                 {:enc enc :dec dec :default (none-t (second ty)) :nil? true :->clj (via-enc)})
      Prod (do (mono (list 'CljM.encProd (sym (:enc c1)) (sym (:enc c2)) 'x) (list 'CljM.decProd (sym (:dec c1)) (sym (:dec c2)) 'v))
               {:enc enc :dec dec :default (list 'Prod.mk (:default c1) (:default c2)) :->clj (via-enc)})
      Float {:enc "CljM.encFloat" :dec "CljM.decFloat" :default 0.0 :->clj identity}
      ;; a Subtype-typed parameter reads as its value (the elaborator's coercion), which is also
      ;; its runtime representation: the base type's codec applies
      Subtype (assoc (select-keys (codec (second ty)) [:enc :->clj]) :param-only true)
      (if-let [{:keys [ctor fields]} (structure-fields ty)]
        (let [fcs (mapv (comp codec second) fields)
              ys (mapv #(sym (str "y" %)) (range (count fields)))
              enc-body (list 'CljM.V.vmap
                             (reduce (fn [acc [[f _] fc]]
                                       (list 'CljM.V.ventry (list 'CljM.V.vkw f) (list (sym (:enc fc)) (list (sym (str ty "." f)) 'x)) acc))
                                     'CljM.V.vnil (reverse (map vector fields fcs))))
              dec-body (list 'if '(CljM.isMap v)
                             (reduce (fn [acc [[f t] fc y]]
                                       (list 'Option.bind (list 'Option.bind (list 'CljM.get 'v (list 'CljM.V.vkw f)) (sym (:dec fc)))
                                             (list 'fn [y :- t] acc)))
                                     (list 'Option.some (list* (sym ctor) ys))
                                     (reverse (map vector fields fcs ys)))
                             (none-t ty))]
          (mono enc-body dec-body)
          {:enc enc :dec dec :default (list* (sym ctor) (map :default fcs)) :->clj (via-enc)})
        (throw (ex-info (str "clj-model: no boundary codec for " (pr-str ty)
                             " (Nat, Int, Bool, String, Float, Value, List, Option, Prod, Subtype, an a/structure)")
                        {:kind :clj-model/no-codec :type ty}))))))

;; ── Where the source comes from ─────────────────────────────────────────────────────────

(defn- sha256 [^String s]
  (let [d (.digest (java.security.MessageDigest/getInstance "SHA-256") (.getBytes s "UTF-8"))]
    (apply str (map #(format "%02x" (bit-and % 0xff)) d))))

(defn model-source
  "The fn form to translate and the namespace to read it in: an inline fn literal; for a symbol
   naming a var, its a/defmodel source, else (best effort) clojure.repl/source-fn of the var
   with the SHA-256 of its file. A var defined at the REPL has no source: refused."
  [impl-form ns-sym]
  (if-not (symbol? impl-form)
    {:form impl-form :ns ns-sym :from :inline}
    (let [v (ns-resolve ns-sym impl-form)
          _ (when-not (var? v) (translate/refuse! :no-source impl-form))
          qname (symbol (str (ns-name (:ns (meta v)))) (str (:name (meta v))))]
      (or (get @ingest/model-source-registry (str qname))
          (let [file (:file (meta v))
                text (when (and file (not= "NO_SOURCE_PATH" file)) ((requiring-resolve 'clojure.repl/source-fn) qname))
                _ (when-not text (translate/refuse! :no-source impl-form))
                vns (ns-name (:ns (meta v)))
                form (binding [*ns* (the-ns vns) *read-eval* false] (read-string text))
                contents (some-> (or (io/resource file) (let [f (io/file file)] (when (.exists f) f))) slurp)]
            {:form (translate/defn->fn form) :ns vns :from :source-fn :file file
             :sha256 (some-> contents sha256)})))))

;; ── define-modelled ─────────────────────────────────────────────────────────────────────

(defonce ^{:doc "name → {:impl :params :ret :codecs :model-name :model-fn :statement :status}"}
  registry (atom {}))

(defn info [f] (or (get @registry (str f)) (throw (ex-info "clj-model: not a modelled function" {:fn f}))))

(defn- elab-closed [form]
  (elab/elaborate-in-context (a/env) {} form nil))

(defn paranoid-call
  "Run `impl` and the compiled model on the same arguments. Where the model answers (`some v`),
   the impl must return `v` (strict =); otherwise, or when it throws there, this throws
   :clj-model/model-disagrees: the model is unfaithful on these arguments. Where the model
   makes no claim, the impl's result stands."
  [cname impl model-fn args & [arity]]
  (let [claim (try (m/opt-value (apply model-fn (m/pack-args arity (map m/edn->cljv args))))
                   (catch StackOverflowError _ nil))   ;; the compiled fixpoint ran out of stack: no claim
        disagree (fn [data cause]
                   (ex-info (str "clj-model: the model of " cname " disagrees with its Clojure source")
                            (merge {:kind :clj-model/model-disagrees :fn cname :args (vec args)
                                    :model (m/cljv->edn (:some claim))} data)
                            cause))
        r (try (apply impl args)
               (catch Throwable t
                 (throw (if claim (disagree {:threw (.getName (class t))} t) t))))]
    (when (and claim (not (m/strict= (m/cljv->edn (:some claim)) r)))
      (throw (disagree {:result r} nil)))
    r))

(defn define-modelled
  "The `a/foreign ^:model` branch: translate `impl-form` (an inline fn literal, read in `ns-sym`)
   into `f.clj`, define `f` from it, and make `impl` its runtime. Returns the runtime fn.
   The status starts :tested, with the gap described in the namespace doc: theorems about `f`
   hold of the model, which answers d_R where it makes no claim (`succ-int Long/MAX_VALUE = 0`
   is provable while the impl throws); `prove-conforms!` (:proved) closes it on the declared types.
   `opts`: {:paranoid? true} runs the model next to the impl on every call (`paranoid-call`)."
  [fn-name params ret-type impl-form impl ns-sym & [opts]]
  (install-codecs!)
  (let [pairs (ingest/parse-params params)
        _ (when (some #(not= :default (nth % 2)) pairs)
            (throw (ex-info "clj-model: G1 boundary takes explicit parameters only" {:params params})))
        codecs (mapv (comp codec second) pairs)
        rc (codec ret-type)
        _ (when (:param-only rc)
            (throw (ex-info (str "clj-model: " (pr-str ret-type) " is a parameter type only (no default value)")
                            {:kind :clj-model/no-codec :type ret-type})))
        source (model-source impl-form ns-sym)
        model-name (str fn-name ".clj")
        model-form (translate/model-defn model-name (:form source) (:ns source) fn-name {:arity (count pairs)})
        arity (select-keys (meta model-form) [:clj-model/fixed :clj-model/rest?])
        _ (when-not (translate/accepts? arity (count pairs))
            (throw (ex-info "clj-model: the fn literal's arity differs from the declared parameters"
                            {:params params :impl impl-form})))
        model-fn (binding [a/*verbose* false config/*clj-surface* false *ns* (the-ns ns-sym)]
                   @(eval model-form))
        args (mapv first pairs)
        model-app (list* (symbol model-name)
                         (translate/pack-args arity (map (fn [p c] (list (symbol (:enc c)) p)) args codecs)))
        result (list 'Option.bind model-app (symbol (:dec rc)))
        body (list 'Option.getD result (:default rc))
        statement (list '= 'Bool (list 'Option.isSome result) true)
        cname (str fn-name)
        opaque ((requiring-resolve 'ansatz.clj-model.callees/opaque-in) model-name)]
    (binding [a/*verbose* false config/*clj-surface* false *ns* (the-ns ns-sym)]
      (a/define-verified fn-name params ret-type body))
    (swap! state/ansatz-env env/update-extension :reducibility-status {} assoc cname "irreducible")
    (swap! state/ansatz-env env/update-extension :clj-model {} assoc cname
           (cond-> {:status :tested :model model-name} (seq opaque) (assoc :opaque opaque)))
    (let [cell (atom :tested)
          paranoid (atom (boolean (:paranoid? opts)))
          ported (atom nil)
          ->clj (mapv :->clj codecs)
          dec-fn (m/model-fn (:dec rc))
          wrapper (fn [& xs]
                    (if-let [g @ported]
                      (apply g xs)
                      (let [args (map #(%1 %2) ->clj xs)
                            r (if @paranoid (paranoid-call cname impl model-fn args arity) (apply impl args))]
                        (if (and (= :proved @cell) (contains? '#{Nat Int Bool String} ret-type))
                          (normalize-int r)
                          (if-let [{v :some} (m/opt-value (dec-fn (m/edn->cljv r)))]
                            v
                            (throw (ex-info (str "clj-model: " fn-name " returned a value that does not decode as "
                                                 ret-type " (outside its asserted type)")
                                            {:kind :clj-model/nonconforming :fn cname :args (vec xs) :result r})))))))]
      (swap! registry assoc cname {:impl impl :params params :ret ret-type :pairs pairs :codecs codecs
                                   :ret-codec rc :model-name model-name :model-fn model-fn :ns ns-sym :arity arity
                                   :statement statement :status cell :paranoid paranoid :ported ported
                                   :source (:form source) :source-info (dissoc source :form) :opaque opaque})
      (println "⚠ modelled:" fn-name "— a definition from its Clojure source; conformance :tested, not proved"
               (if (seq opaque) (str "; opaque (assumed pure): " (str/join ", " opaque)) ""))
      (decl/emit-foreign! cname wrapper))))

(defn status [f] @(:status (info f)))

(defn statement
  "The conformance statement of `f` as [params prop]: prove it with `(a/conforms f tactics…)`."
  [f]
  (let [{:keys [params statement]} (info f)] [params statement]))

(defn prove-conforms!
  "Prove `f.conforms` with `tactics`, derive `f.spec`, and mark `f` :proved. Without tactics,
   the `clj_model` simp set is prepared for `f` and `proof/default-script` runs."
  [f tactics]
  (let [{:keys [params statement pairs ret ret-codec codecs model-name] :as i} (info f)
        cname (str f)
        args (mapv first pairs)
        result (nth (nth statement 2) 1)
        tactics (if (seq tactics)
                  tactics
                  (do (proof/prepare! model-name codecs ret-codec)
                      (if (proof/recursive-model? cname)
                        ;; prove the recursive groups first; the script then applies them
                        (proof/with-deep-stack
                          #((requiring-resolve 'ansatz.clj-model.recursion/recursive-script)
                            params statement
                            (proof/compute-script (mapv (fn [[p t]] [p t]) pairs) (proof/model-unfold cname) true)
                            (proof/model-unfold cname) cname))
                        (proof/default-script cname (mapv (fn [[p t]] [p t]) pairs)))))]
    (proof/with-deep-stack #(a/prove-theorem (symbol (str cname ".conforms")) params statement tactics))
    ;; f.spec by the generic lemma; the kernel unfolds the (irreducible) f to check it
    (let [spec-type (:type-ansatz (a/elab-signature (a/env) pairs
                                                    (list '= (list 'Option ret) result
                                                          (list 'Option.some (list* (symbol cname) args)))))
          spec-proof (elab-closed (list 'fn (vec (mapcat (fn [[p t]] [p :- t]) pairs))
                                        (list 'CljM.some_getD ret result (:default ret-codec)
                                              (list* (symbol (str cname ".conforms")) args))))]
      (swap! state/ansatz-env env/check-constant
             (env/mk-thm (name/from-string (str cname ".spec")) [] spec-type spec-proof)))
    (reset! (:status i) :proved)
    (swap! state/ansatz-env env/update-extension :clj-model {} assoc-in [cname :status] :proved)
    (when a/*verbose* (println "✓ modelled:" cname "— conformance proved"))
    :proved))

(defn paranoid!
  "Turn the paranoid runtime of `f` on or off: every call also runs the model and compares
   (`paranoid-call`). Returns `on?`."
  [f on?]
  (reset! (:paranoid (info f)) (boolean on?)))

(defn port!
  "The :ported path: `f` (:proved) is rewritten in the DSL as `g` (an `a/defn` of the same type).
   Proves `f.ported : ∀ x…, f x… = g x…` with `tactics` (default `proof/port-script`) and
   registers it as `a/csimp`, so compiled DSL code calls `g`; `g-fn`, g's compiled function,
   becomes `f`'s runtime. The trusted base for `f` is then the kernel and codegen only."
  [f g g-fn tactics]
  (let [{:keys [pairs ret status model-name codecs ret-codec] :as i} (info f)
        cname (str f)]
    (when-not (= :proved @status)
      (throw (ex-info (str "clj-model: port " cname " once it is :proved (a/conforms), not " @status)
                      {:kind :clj-model/not-proved :fn cname :status @status})))
    (let [args (map first pairs)
          tactics (if (seq tactics)
                    tactics
                    (do (proof/prepare! model-name codecs ret-codec)
                        (proof/port-script cname g (mapv (fn [[p t]] [p t]) pairs))))]
      (proof/with-deep-stack
        #(a/define-csimp (symbol (str cname ".ported")) (:params i)
           (list '= ret (list* (symbol cname) args) (list* (symbol (str g)) args)) tactics)))
    (reset! (:ported i) g-fn)
    (reset! status :ported)
    (swap! state/ansatz-env env/update-extension :clj-model {} assoc-in [cname :status] :ported)
    (when a/*verbose* (println "✓ modelled:" cname "— ported to" g))
    :ported))
