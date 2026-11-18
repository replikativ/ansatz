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
   proves it, adds f.spec : ∀ x…, Option.bind (f.clj (enc x)…) dec_R = some (f x), and the status
   becomes :proved.

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
   map over 8 entries or a set over 1 element, whose runtime order is the hash order)."
  (:require [ansatz.core :as a]
            [ansatz.config :as config]
            [ansatz.state :as state]
            [ansatz.clj-model :as m]
            [ansatz.clj-model.translate :as translate]
            [ansatz.codegen.decl :as decl]
            [ansatz.kernel.env :as env]
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
    (throw (ex-info (str "clj-model: no G1 boundary codec for " (pr-str ty)
                         " (G1: Nat, Int, Bool, String, Value)") {:kind :clj-model/no-codec :type ty}))))

;; ── define-modelled ─────────────────────────────────────────────────────────────────────

(defonce ^{:doc "name → {:impl :params :ret :codecs :model-name :model-fn :statement :status}"}
  registry (atom {}))

(defn info [f] (or (get @registry (str f)) (throw (ex-info "clj-model: not a modelled function" {:fn f}))))

(defn- elab-closed [form]
  (elab/elaborate-in-context (a/env) {} form nil))

(defn define-modelled
  "The `a/foreign ^:model` branch: translate `impl-form` (an inline fn literal, read in `ns-sym`)
   into `f.clj`, define `f` from it, and make `impl` its runtime. Returns the runtime fn.
   The status starts :tested, with the gap described in the namespace doc: theorems about `f`
   hold of the model, which answers d_R where it makes no claim (`succ-int Long/MAX_VALUE = 0`
   is provable while the impl throws); `prove-conforms!` (:proved) closes it on the declared types."
  [fn-name params ret-type impl-form impl ns-sym]
  (install-codecs!)
  (let [pairs (ingest/parse-params params)
        _ (when (some #(not= :default (nth % 2)) pairs)
            (throw (ex-info "clj-model: G1 boundary takes explicit parameters only" {:params params})))
        codecs (mapv (comp codec second) pairs)
        rc (codec ret-type)
        model-name (str fn-name ".clj")
        model-form (translate/model-defn model-name impl-form ns-sym fn-name)
        _ (when (not= (* 3 (count pairs)) (count (nth model-form 2)))
            (throw (ex-info "clj-model: the fn literal's arity differs from the declared parameters"
                            {:params params :impl impl-form})))
        model-fn (binding [a/*verbose* false config/*clj-surface* false *ns* (the-ns ns-sym)]
                   @(eval model-form))
        args (mapv first pairs)
        model-app (list* (symbol model-name) (map (fn [p c] (list (symbol (:enc c)) p)) args codecs))
        result (list 'Option.bind model-app (symbol (:dec rc)))
        body (list 'Option.getD result (:default rc))
        statement (list '= 'Bool (list 'Option.isSome result) true)
        cname (str fn-name)]
    (binding [a/*verbose* false config/*clj-surface* false *ns* (the-ns ns-sym)]
      (a/define-verified fn-name params ret-type body))
    (swap! state/ansatz-env env/update-extension :reducibility-status {} assoc cname "irreducible")
    (swap! state/ansatz-env env/update-extension :clj-model {} assoc cname {:status :tested :model model-name})
    (let [cell (atom :tested)
          ->clj (mapv :->clj codecs)
          dec-fn (m/model-fn (:dec rc))
          wrapper (fn [& xs]
                    (let [r (apply impl (map #(%1 %2) ->clj xs))]
                      (if (and (= :proved @cell) (not= 'Value ret-type))
                        (normalize-int r)
                        (if-let [{v :some} (m/opt-value (dec-fn (m/edn->cljv r)))]
                          v
                          (throw (ex-info (str "clj-model: " fn-name " returned a value that does not decode as "
                                               ret-type " (outside its asserted type)")
                                          {:kind :clj-model/nonconforming :fn cname :args (vec xs) :result r}))))))]
      (swap! registry assoc cname {:impl impl :params params :ret ret-type :pairs pairs :codecs codecs
                                   :ret-codec rc :model-name model-name :model-fn model-fn :ns ns-sym
                                   :statement statement :status cell :source impl-form})
      (println "⚠ modelled:" fn-name "— a definition from its Clojure source; conformance :tested, not proved")
      (decl/emit-foreign! cname wrapper))))

(defn status [f] @(:status (info f)))

(defn statement
  "The conformance statement of `f` as [params prop]: prove it with `(a/conforms f tactics…)`."
  [f]
  (let [{:keys [params statement]} (info f)] [params statement]))

(defn prove-conforms!
  "Prove `f.conforms` with `tactics`, derive `f.spec`, and mark `f` :proved."
  [f tactics]
  (let [{:keys [params statement pairs ret ret-codec] :as i} (info f)
        cname (str f)
        args (mapv first pairs)
        result (nth (nth statement 2) 1)]
    (a/prove-theorem (symbol (str cname ".conforms")) params statement tactics)
    ;; f.spec by the generic lemma; the kernel unfolds the (irreducible) f to check it
    (let [spec-type (:type-ansatz (a/elab-signature (a/env) pairs
                                                    (list '= (list 'Option ret) result
                                                          (list 'Option.some (list* (symbol cname) args)))))
          proof (elab-closed (list 'fn (vec (mapcat (fn [[p t]] [p :- t]) pairs))
                                   (list 'CljM.some_getD ret result (:default ret-codec)
                                         (list* (symbol (str cname ".conforms")) args))))]
      (swap! state/ansatz-env env/check-constant
             (env/mk-thm (name/from-string (str cname ".spec")) [] spec-type proof)))
    (reset! (:status i) :proved)
    (swap! state/ansatz-env env/update-extension :clj-model {} assoc-in [cname :status] :proved)
    (when a/*verbose* (println "✓ modelled:" cname "— conformance proved"))
    :proved))
