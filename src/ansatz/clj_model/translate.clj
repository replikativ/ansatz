(ns ansatz.clj-model.translate
  "Translate the source of a plain Clojure function into the kernel model (ansatz.clj-model):
   `(fn [x …] body)` becomes `(a/defn ^:lean f.clj [x :- CljM.V …] (Option CljM.V) …)` in
   A-normal form, where every call is an `Option.bind` and `none` (no claim) propagates.

   Special forms modelled: `if` (Clojure truthiness: `CljM.truthy`), `let*`, a single-form
   `do`, `quote`, `throw` (→ none), and `case` (intercepted before expansion: its `case*` is a
   hash dispatch; modelled as hashed-key equality tests, `CljM.caseIn`). Every other macro is
   expanded with `macroexpand-1` in the source namespace, so `when`, `cond`, `and`, `or`, `->`,
   `if-let`, `when-some`, `cond->`, `condp` … are faithful by construction. `let` and `fn` are
   intercepted before expansion to refuse destructuring.

   Functions are a second sort `CljM.V → … → Option CljM.V`, never a value: a fn literal, a
   let-bound function, a core function, `partial`, `comp`, `complement`, `constantly` or
   `juxt` may be called or passed to a modelled higher-order function (`map`, `reduce`,
   `update`, …), where it becomes a Lean lambda. A function anywhere else (returned, stored,
   compared) is refused (`:escaping-fn`). A value in function position (a keyword, map, set,
   vector, or a parameter) is invoked as Clojure does (`CljM.invoke`). A fn literal is inlined
   at each call: its arity is chosen per call, as Clojure does, and a variadic arity gets its
   extra arguments as a seq (or nil).

   Anything outside the model is refused with ex-info {:kind :clj/refused :reason r :form f},
   r from `refusal-reasons`."
  (:require [clojure.string :as str]))

(def refusal-reasons
  "reason → what it means. A closed set: the model contract lists it."
  (sorted-map
   :interop "Java interop (`.method`, `Class.`, `Class/static`, `new`): no model of Java objects."
   :side-effect "An effect (printing, I/O, `def`): the model is pure."
   :mutable-state "Atoms, volatiles, `deref`, `set!`: the model has no state."
   :dynamic-var "A dynamic var or `var`: its value depends on the binding in force."
   :try-catch "`try`: catching would turn a no-claim into a value."
   :dispatch "Protocols, multimethods and a raw `case*`: not modelled."
   :lazy-infinite "An infinite sequence (`iterate`, `cycle`, `repeat`/`range` without a bound)."
   :regex "Regular expressions: not modelled."
   :eval "`eval` and reading code at runtime."
   :escaping-fn "A function stored in data, returned or compared: the model's values are data; functions are only called or passed to a modelled higher-order function."
   :higher-order "A higher-order function the model does not cover yet (`apply`, `mapcat`, a comparator for `sort`, a transducer other than map/filter/remove/keep)."
   :destructuring "A destructuring binding form."
   :multi-form-body "A body with several forms: the earlier forms only run for effects."
   :multi-arity "A modelled function with several arities (a fn literal passed to a function may have several)."
   :recursion "Recursion, `loop`/`recur`, `letfn`."
   :unmodelled-fn "A call to a function the model does not cover."
   :unmodelled-form "A literal or form the model does not cover (char/BigInt/NaN literals, set or map literals with computed keys)."))

(defn refuse! [reason form & [hint]]
  (assert (contains? refusal-reasons reason) reason)
  (throw (ex-info (str "Refused Clojure model translation (" (name reason) "): "
                       (get refusal-reasons reason) "\n  form: " (pr-str form))
                  (cond-> {:kind :clj/refused :reason reason :form form}
                    hint (assoc :hint hint)))))

;; ── The clojure.core models ─────────────────────────────────────────────────────────────
;; symbol → how its call translates:
;;   :fixed {arity kernel-name}     a model op taking the arguments
;;   :fold / :chain                 a left fold of a binary op (+, *, -) / pairwise comparison
;;   :args kernel-name              a model op taking all arguments as one chain (variadic)
;;   :hof {arity {:op k :fns {i n}}} a model op whose argument i is a function of n arguments
;;                                  (:fn0 i: its 0-arity answer is passed first, for reduce)
;;   :negate                        the answer negated (not=, not-any?, not-every?)
;;   :build / :conj / :range / …    translated here (see op-call)

(def ^:private fixed1 (fn [k] {:fixed {1 k}}))

(def core-ops
  (merge
   {'+ {:fold "CljM.add" :zero 0 :one "CljM.num"}
    '* {:fold "CljM.mul" :zero 1 :one "CljM.num"}
    '- {:fold "CljM.sub" :one "CljM.neg"}
    '= {:chain "CljM.eq"}
    'not= {:chain "CljM.eq" :negate true}
    '< {:chain "CljM.lt"} '<= {:chain "CljM.le"} '> {:chain "CljM.gt"} '>= {:chain "CljM.ge"}
    'get {:fixed {2 "CljM.get" 3 "CljM.get3"}}
    'contains? {:fixed {2 "CljM.containsQ"}}
    'assoc {:assoc true} 'dissoc {:dissoc true}
    ;; G2: sequences, maps, strings
    'cons {:fixed {2 "CljM.cons"}} 'nth {:fixed {2 "CljM.nth" 3 "CljM.nth3"}}
    'take {:fixed {2 "CljM.take"}} 'drop {:fixed {2 "CljM.drop"}}
    'get-in {:fixed {2 "CljM.getIn" 3 "CljM.getIn3"}} 'assoc-in {:fixed {3 "CljM.assocIn"}}
    'select-keys {:fixed {2 "CljM.selectKeys"}}
    'subs {:fixed {2 "CljM.subs" 3 "CljM.subs3"}} 'keyword {:fixed {1 "CljM.keyword" 2 "CljM.keyword2"}}
    'merge {:args "CljM.merge"} 'concat {:args "CljM.concat"} 'str {:args "CljM.str"}
    'max {:args "CljM.max"} 'min {:args "CljM.min"} 'hash-set {:args "CljM.hashSet"}
    'list {:build "vlist"} 'vector {:build "vvec"} 'hash-map {:hash-map true}
    'conj {:conj true} 'range {:range true} 'into {:into true}
    ;; higher-order
    'map {:hof {2 {:op "CljM.map" :fns {0 1}} 3 {:op "CljM.map2" :fns {0 2}}}}
    'mapv {:hof {2 {:op "CljM.mapv" :fns {0 1}}}}
    'filter {:hof {2 {:op "CljM.filter" :fns {0 1}}}}
    'filterv {:hof {2 {:op "CljM.filterv" :fns {0 1}}}}
    'remove {:hof {2 {:op "CljM.remove" :fns {0 1}}}}
    'keep {:hof {2 {:op "CljM.keep" :fns {0 1}}}}
    'reduce {:hof {2 {:op "CljM.reduce" :fns {0 2} :fn0 0} 3 {:op "CljM.reduce3" :fns {0 2}}}}
    'some {:hof {2 {:op "CljM.some" :fns {0 1}}}}
    'every? {:hof {2 {:op "CljM.every" :fns {0 1}}}}
    'not-any? {:hof {2 {:op "CljM.some" :fns {0 1}}} :negate true}
    'not-every? {:hof {2 {:op "CljM.every" :fns {0 1}}} :negate true}
    'group-by {:hof {2 {:op "CljM.groupBy" :fns {0 1}}}}
    'sort-by {:hof {2 {:op "CljM.sortBy" :fns {0 1}}}}
    'update-vals {:hof {2 {:op "CljM.updateVals" :fns {1 1}}}}
    'update {:update true} 'update-in {:update-in true}}
   (update-vals
    '{nil? "CljM.nilQ" some? "CljM.someQ" not "CljM.not" identity "CljM.identity" inc "CljM.inc"
      dec "CljM.dec" zero? "CljM.zeroQ" pos? "CljM.posQ" neg? "CljM.negQ" count "CljM.count"
      string? "CljM.stringQ" keyword? "CljM.keywordQ" number? "CljM.numberQ" int? "CljM.intQ"
      map? "CljM.mapQ" vector? "CljM.vectorQ"
      seq "CljM.seq" first "CljM.first" rest "CljM.rest" next "CljM.next" second "CljM.second"
      last "CljM.last" empty? "CljM.emptyQ" vec "CljM.vec" set "CljM.set" reverse "CljM.reverse"
      keys "CljM.keys" vals "CljM.vals" frequencies "CljM.frequencies" distinct "CljM.distinct"
      sort "CljM.sort" name "CljM.name" seq? "CljM.seqQ" list? "CljM.listQ" set? "CljM.setQ"
      coll? "CljM.collQ" sequential? "CljM.sequentialQ" boolean? "CljM.booleanQ"
      symbol? "CljM.symbolQ" char? "CljM.charQ" true? "CljM.trueQ" false? "CljM.falseQ"
      boolean "CljM.boolean" even? "CljM.evenQ" odd? "CljM.oddQ"}
    fixed1)))

(def string-ops
  "clojure.string functions → their models (as core-ops)."
  {'join {:fixed {1 "CljM.join" 2 "CljM.join2"}} 'blank? (fixed1 "CljM.blankQ")
   'upper-case (fixed1 "CljM.upperCase") 'lower-case (fixed1 "CljM.lowerCase")
   'starts-with? {:fixed {2 "CljM.startsWithQ"}} 'ends-with? {:fixed {2 "CljM.endsWithQ"}}
   'includes? {:fixed {2 "CljM.includesQ"}}})

(def ^:private fn-makers
  "clojure.core functions that build functions: modelled in function position only."
  '#{partial comp complement constantly juxt})

(def ^:private classified
  "clojure.core functions refused with a specific reason."
  (merge (zipmap '[println print prn pr printf newline flush spit slurp tap> print-str
                   println-str prn-str pr-str with-out-str rand rand-int rand-nth shuffle
                   gensym random-uuid] (repeat :side-effect))
         (zipmap '[atom swap! reset! swap-vals! reset-vals! volatile! vswap! vreset! deref
                   ref ref-set alter commute agent send] (repeat :mutable-state))
         (zipmap '[eval load-string read-string load-file] (repeat :eval))
         (zipmap '[re-find re-matches re-pattern re-seq re-matcher re-groups] (repeat :regex))
         (zipmap '[iterate cycle repeatedly] (repeat :lazy-infinite))
         (zipmap '[apply mapcat run! transduce sequence eduction reduce-kv keep-indexed
                   map-indexed partition-by sort-by-key trampoline] (repeat :higher-order))))

;; ── Literals ────────────────────────────────────────────────────────────────────────────

(defn- vctor [ct & args] (let [s (symbol (str "CljM.V." ct))] (if (seq args) (list* s args) s)))

(defn- chain-of [xs] (reduce (fn [acc x] (vctor 'vcons x acc)) (vctor 'vnil) (reverse xs)))

(defn literal
  "A constant Clojure value → the surface term of its `CljM.V`."
  [x]
  (cond
    (nil? x) (vctor 'vnil)
    (boolean? x) (vctor 'vbool x)
    (instance? Long x) (vctor 'vlong x)
    (and (instance? Double x) (Double/isFinite x)) (vctor 'vdouble x)
    (string? x) (vctor 'vstr x)
    (keyword? x) (vctor 'vkw (subs (str x) 1))
    (symbol? x) (vctor 'vsym (str x))
    (char? x) (vctor 'vchar (list 'Char.ofNat (long (int x))))
    (map? x) (vctor 'vmap (reduce (fn [acc [k v]] (vctor 'ventry (literal k) (literal v) acc))
                                  (vctor 'vnil) (reverse (seq x))))
    (set? x) (vctor 'vset (chain-of (map literal x)))
    (vector? x) (vctor 'vvec (chain-of (map literal x)))
    (seq? x) (vctor 'vlist (chain-of (map literal x)))
    :else (refuse! :unmodelled-form x)))

(defn- constant? [x]
  (or (nil? x) (boolean? x) (instance? Long x) (string? x) (keyword? x)
      (and (instance? Double x) (Double/isFinite x))))

;; ── Translation ─────────────────────────────────────────────────────────────────────────
;; `tr` returns a surface term of type `Option CljM.V`; `with-atom` gives the continuation a
;; term of type `CljM.V` (a local or a literal), binding non-atomic forms first (ANF).
;; Locals map a symbol to its V term, or to {::fn builder} (a function: builder takes argument
;; atoms to a term of type `Option CljM.V`), or to ::self (the fn's own name: recursion).

(def ^:private ^:dynamic *ctx* nil)   ;; {:ns :self :counter (atom n)}

(defn- fresh [base]
  (symbol (str "cv_" (str/replace (str base) #"[^A-Za-z0-9]" "_") "_" (swap! (:counter *ctx*) inc))))

(declare tr with-fn)

(defn- fn-local? [x] (and (map? x) (contains? x ::fn)))

(defn- local-term
  "The V term of local `sym`; refuses a function or a self-reference used as a value."
  [locals sym form]
  (let [v (get locals sym)]
    (cond (= ::self v) (refuse! :recursion form)
          (fn-local? v) (refuse! :escaping-fn form)
          :else v)))

(defn- atom-of [locals form]
  (cond (and (symbol? form) (contains? locals form)) (local-term locals form form)
        (constant? form) (literal form)))

(defn- with-atom [locals form k]
  (if-let [a (atom-of locals form)]
    (k a)
    (let [t (fresh "t")]
      (list 'Option.bind (tr locals form) (list 'fn [t :- 'CljM.V] (k t))))))

(defn- with-atoms [locals forms k]
  (if (empty? forms) (k [])
      (with-atom locals (first forms)
        (fn [a] (with-atoms locals (rest forms) (fn [as] (k (cons a as))))))))

(defn- some-of [x] (list 'Option.some x))
(def ^:private none-term (list (symbol "@Option.none") 'CljM.V))

(defn- bind-result [x k]
  (let [t (fresh "r")] (list 'Option.bind x (list 'fn [t :- 'CljM.V] (k t)))))

(defn- negated [x] (bind-result x (fn [r] (list 'CljM.not r))))

(defn- lam
  "The Lean lambda `fun x₁ … xₙ => builder [x₁ … xₙ]` (the model's function sort)."
  [builder n]
  (let [xs (vec (repeatedly n #(fresh "x")))]
    (list 'fn (vec (mapcat (fn [x] [x :- 'CljM.V]) xs)) (builder xs))))

(defn- invoker
  "A value called as a function (Clojure's IFn on keywords, symbols, maps, sets, vectors)."
  [f]
  (fn [as] (case (count as)
             1 (list 'CljM.invoke f (first as))
             2 (list 'CljM.invoke3 f (first as) (second as))
             none-term)))

(defn- chain-call
  "Clojure's (< x y & more): compare pairwise, false at the first failing pair."
  [kname atoms negate]
  (if (= 1 (count atoms))
    (some-of (literal (not negate)))
    (cond-> (reduce (fn [acc [x y]]
                      (bind-result acc (fn [r] (list 'if (list 'CljM.truthy r) (list (symbol kname) x y)
                                                     (some-of (literal false))))))
                    (list (symbol kname) (first atoms) (second atoms))
                    (partition 2 1 (rest atoms)))
      negate negated)))

(defn- fold-call [op atoms]
  (reduce (fn [acc y] (bind-result acc (fn [r] (list op r y))))
          (list op (first atoms) (second atoms))
          (drop 2 atoms)))

(defn- op-call
  "The term of a call of a core function with spec `spec` on `args`: each {:a atom} (a value)
   or {:f builder} (a function)."
  [sym spec args]
  (let [n (count args)
        hof (get-in spec [:hof n])
        fn-pos (set (keys (:fns hof)))
        _ (doseq [[i d] (map-indexed vector args)]
            (when (and (:f d) (not (contains? fn-pos i)) (not (:update spec)) (not (:update-in spec)))
              (refuse! :escaping-fn sym)))
        atoms (mapv :a args)
        builder (fn [d] (or (:f d) (invoker (:a d))))]
    (cond
      hof (cond-> (list* (symbol (:op hof))
                         (into (if-let [i (:fn0 hof)] [((builder (nth args i)) [])] [])
                               (map-indexed (fn [i d] (if-let [k (get (:fns hof) i)] (lam (builder d) k) (:a d))))
                               args))
            (:negate spec) negated)
      (:hof spec) none-term                                ;; wrong arity: clojure.core throws
      (:fold spec) (case n
                     0 (if (contains? spec :zero) (some-of (literal (:zero spec))) none-term)
                     1 (list (symbol (:one spec)) (first atoms))
                     (fold-call (symbol (:fold spec)) atoms))
      (:chain spec) (if (zero? n) none-term (chain-call (:chain spec) atoms (:negate spec)))
      (:assoc spec) (if (or (< n 3) (even? n)) none-term
                        (reduce (fn [acc [k v]] (bind-result acc (fn [r] (list 'CljM.assoc r k v))))
                                (list 'CljM.assoc (first atoms) (second atoms) (nth atoms 2))
                                (partition 2 (drop 3 atoms))))
      (:dissoc spec) (case n
                       0 none-term
                       1 (some-of (first atoms))
                       (fold-call 'CljM.dissoc atoms))
      (:args spec) (list (symbol (:args spec)) (chain-of atoms))
      (:build spec) (some-of (vctor (symbol (:build spec)) (chain-of atoms)))
      (:hash-map spec) (cond (odd? n) none-term
                             (zero? n) (some-of (vctor 'vmap (vctor 'vnil)))
                             :else (bind-result (reduce (fn [acc [k v]] (bind-result acc (fn [r] (list 'CljM.assoc r k v))))
                                                        (some-of (vctor 'vmap (vctor 'vnil)))
                                                        (partition 2 atoms))
                                                (fn [m] (list 'CljM.hashMapOk m))))
      (:conj spec) (case n
                     0 (some-of (vctor 'vvec (vctor 'vnil)))
                     1 (some-of (first atoms))
                     (fold-call 'CljM.conj1 atoms))
      (:range spec) (case n
                      1 (list 'CljM.range (literal 0) (first atoms) (literal 1))
                      2 (list 'CljM.range (first atoms) (second atoms) (literal 1))
                      3 (list* 'CljM.range atoms)
                      none-term)
      (:into spec) (case n
                     0 (some-of (vctor 'vvec (vctor 'vnil)))
                     1 (some-of (first atoms))
                     2 (list 'CljM.into (first atoms) (second atoms))
                     none-term)
      (:update spec) (if (< n 3) none-term
                         (let [[m k f & more] args]
                           (when (or (:f m) (:f k) (some :f more)) (refuse! :escaping-fn sym))
                           (bind-result (list 'CljM.get (:a m) (:a k))
                                        (fn [old] (bind-result ((builder f) (cons old (map :a more)))
                                                               (fn [new] (list 'CljM.assoc (:a m) (:a k) new)))))))
      (:update-in spec) (if (< n 3) none-term
                            (let [[m ks f & more] args]
                              (when (or (:f m) (:f ks) (some :f more)) (refuse! :escaping-fn sym))
                              (list 'CljM.updateIn (:a m) (:a ks)
                                    (lam (fn [[x]] ((builder f) (cons x (map :a more)))) 1))))
      :else (if-let [k (get (:fixed spec) n)]
              (list* (symbol k) atoms)
              none-term))))   ;; wrong arity: clojure.core throws

(defn- check-binding-vector [form bv]
  (when-not (and (vector? bv) (even? (count bv)) (every? symbol? (take-nth 2 bv)))
    (refuse! :destructuring form))
  (when (some #(= '& %) (take-nth 2 bv)) (refuse! :destructuring form)))

(defn- single-body [form body]
  (cond (empty? body) nil
        (= 1 (count body)) (first body)
        :else (refuse! :multi-form-body form)))

(defn- resolve-var [sym]
  (try (ns-resolve (:ns *ctx*) sym) (catch Exception _ ::class)))

(defn- var-ns [v] (when (var? v) (str (:ns (meta v)))))

(defn- core-name
  "The clojure.core name a symbol resolves to in the source namespace (nil when it does not)."
  [locals sym]
  (when (and (symbol? sym) (not (contains? locals sym)))
    (let [v (resolve-var sym)]
      (when (= "clojure.core" (var-ns v)) (:name (meta v))))))

(defn- resolve-call [locals sym form]
  (cond
    (= sym (:self *ctx*)) (refuse! :recursion form)
    (str/starts-with? (name sym) ".") (refuse! :interop form)
    (and (str/ends-with? (name sym) ".") (not= sym '.)) (refuse! :interop form)
    :else
    (let [nsp (:ns *ctx*)
          v (resolve-var sym)]
      (cond
        (or (= ::class v) (class? v)) (refuse! :interop form)
        (and (namespace sym) (nil? v)
             (try (class? (ns-resolve nsp (symbol (namespace sym)))) (catch Exception _ false)))
        (refuse! :interop form)
        (nil? v) (refuse! :unmodelled-fn form)
        (.isDynamic ^clojure.lang.Var v) (refuse! :dynamic-var form)
        (instance? clojure.lang.MultiFn @v) (refuse! :dispatch form)
        (:protocol (meta v)) (refuse! :dispatch form)
        (= (var-ns v) "clojure.core") (or (get core-ops (:name (meta v)))
                                          (when (fn-makers (:name (meta v))) (refuse! :escaping-fn form))
                                          (when-let [r (classified (:name (meta v)))]
                                            (refuse! r form))
                                          (refuse! :unmodelled-fn form))
        (= (var-ns v) "clojure.string") (or (get string-ops (:name (meta v)))
                                            (when (#{'split 'split-lines 'replace 'replace-first 're-quote-replacement}
                                                   (:name (meta v)))
                                              (refuse! :regex form))
                                            (refuse! :unmodelled-fn form))
        :else (refuse! :unmodelled-fn form)))))

(def ^:private intercepted '#{let fn loop letfn case})

(defn- core-macro-name
  "`clojure.core/let` (as macroexpansions spell it) → `let`, for the macros intercepted
   before expansion; any other head unchanged."
  [head]
  (if (special-symbol? head)
    head
    (let [v (try (ns-resolve (:ns *ctx*) head) (catch Exception _ nil))]
      (if (and (var? v) (= "clojure.core" (str (:ns (meta v)))) (intercepted (:name (meta v))))
        (:name (meta v))
        head))))

(defn- class-qualified? [sym]
  (and (namespace sym)
       (try (class? (ns-resolve (:ns *ctx*) (symbol (namespace sym)))) (catch Exception _ false))))

;; ── Functions ───────────────────────────────────────────────────────────────────────────

(defn- fn-literal? [locals form]
  (and (seq? form) (symbol? (first form)) (not (contains? locals (first form)))
       (#{'fn* 'fn} (core-macro-name (first form)))))

(defn fn-form?
  "Is `form` a function (rather than a value) in the model's two sorts? A fn literal, a
   function-valued local, a call of a function maker (`partial` …), or a core function."
  [locals form]
  (cond
    (symbol? form) (if (contains? locals form)
                     (fn-local? (get locals form))
                     (let [v (resolve-var form)]
                       (and (var? v) (not (:macro (meta v))) (fn? @v))))
    (seq? form) (or (fn-literal? locals form)
                    (contains? fn-makers (core-name locals (first form))))
    :else false))

(defn- parse-arity
  "`([params] body…)` → {:params [sym …] :rest sym-or-nil :body form}."
  [form [params & body]]
  (when-not (vector? params) (refuse! :unmodelled-form form))
  (let [[fixed [amp rest-sym & extra]] (split-with #(not= '& %) params)]
    (when (or (not-every? symbol? fixed) (and amp (or (not (symbol? rest-sym)) (seq extra))))
      (refuse! :destructuring form))
    {:params (vec fixed) :rest (when amp rest-sym) :body (single-body form body)}))

(defn parse-fn
  "`(fn name? [params] body)` or `(fn name? ([params] body) …)` → {:self name :arities […]}."
  [form]
  (when-not (and (seq? form) (#{'fn 'fn* 'clojure.core/fn} (first form)))
    (refuse! :unmodelled-form form "the model translates a (fn [x …] body)"))
  (let [[_ & more] form
        self (when (symbol? (first more)) (first more))
        more (if self (rest more) more)
        arities (if (vector? (first more)) [more] more)]
    {:self self :arities (mapv #(parse-arity form %) arities)}))

(defn- pick-arity
  "Clojure's choice: the fixed arity of exactly n, else the variadic arity if n reaches it."
  [arities n]
  (or (first (filter #(and (nil? (:rest %)) (= n (count (:params %)))) arities))
      (first (filter #(and (:rest %) (<= (count (:params %)) n)) arities))))

(defn- rest-term
  "The value of a variadic parameter: nil, or the extra arguments as a seq."
  [extras]
  (if (empty? extras) (vctor 'vnil) (vctor 'vlseq true (chain-of extras))))

(defn- bind-params [locals {:keys [params rest]} atoms]
  (cond-> (merge locals (zipmap params atoms))
    rest (assoc rest (rest-term (drop (count params) atoms)))))

(defn- literal-builder
  "The builder of a fn literal: inlined at each call, closing over `locals`."
  [locals form]
  (let [{:keys [self arities]} (parse-fn form)
        locals (if self (assoc locals self ::self) locals)]
    (fn [atoms]
      (if-let [ar (pick-arity arities (count atoms))]
        (tr (bind-params locals ar atoms) (:body ar))
        none-term))))

(defn- core-builder [locals sym form]
  (let [spec (resolve-call locals sym form)]
    (fn [atoms] (op-call sym spec (mapv (fn [a] {:a a}) atoms)))))

(defn- with-fns [locals forms k]
  (if (empty? forms) (k [])
      (with-fn locals (first forms)
        (fn [b] (with-fns locals (rest forms) (fn [bs] (k (cons b bs))))))))

(defn- maker
  "A function built by partial / comp / complement / constantly / juxt."
  [locals mname [_ & args :as form] k]
  (case mname
    partial (if (empty? args) (refuse! :unmodelled-form form)
                (with-fn locals (first args)
                  (fn [f] (with-atoms locals (rest args)
                            (fn [as] (k (fn [atoms] (f (concat as atoms)))))))))
    comp (with-fns locals args
           (fn [fs]
             (k (if (empty? fs)
                  (fn [atoms] (if (= 1 (count atoms)) (some-of (first atoms)) none-term))
                  (fn [atoms]
                    (reduce (fn [acc g] (bind-result acc (fn [r] (g [r]))))
                            ((last fs) atoms) (rest (reverse fs))))))))
    complement (if (not= 1 (count args)) (refuse! :unmodelled-form form)
                   (with-fn locals (first args) (fn [f] (k (fn [atoms] (negated (f atoms)))))))
    constantly (if (not= 1 (count args)) (refuse! :unmodelled-form form)
                   (with-atom locals (first args) (fn [x] (k (fn [_] (some-of x))))))
    juxt (if (empty? args) (refuse! :unmodelled-form form)
             (with-fns locals args
               (fn [fs]
                 (k (fn [atoms]
                      (letfn [(go [fs acc]
                                  (if (empty? fs)
                                    (some-of (vctor 'vvec (chain-of acc)))
                                    (bind-result ((first fs) atoms) (fn [r] (go (rest fs) (conj acc r))))))]
                        (go fs [])))))))))

(defn- with-fn
  "Give `k` the builder of `form` in function position: a function, or a value invoked as one."
  [locals form k]
  (cond
    (and (symbol? form) (contains? locals form))
    (let [v (get locals form)]
      (cond (= ::self v) (refuse! :recursion form)
            (fn-local? v) (k (::fn v))
            :else (k (invoker v))))
    (and (symbol? form) (fn-form? locals form)) (k (core-builder locals form form))
    (fn-literal? locals form) (k (literal-builder locals form))
    (and (seq? form) (contains? fn-makers (core-name locals (first form))))
    (maker locals (core-name locals (first form)) form k)
    :else (with-atom locals form (fn [a] (k (invoker a))))))

;; ── Forms ───────────────────────────────────────────────────────────────────────────────

(defn- tr-let [locals form bindings body]
  (check-binding-vector form bindings)
  (let [body (single-body form body)]
    (letfn [(go [locals pairs]
                (if (empty? pairs)
                  (tr locals body)
                  (let [[sym init] (first pairs)]
                    (if (fn-form? locals init)
                      (with-fn locals init (fn [b] (go (assoc locals sym {::fn b}) (rest pairs))))
                      (if-let [a (atom-of locals init)]
                        (go (assoc locals sym a) (rest pairs))
                        (let [x (fresh sym)]
                          (list 'Option.bind (tr locals init)
                                (list 'fn [x :- 'CljM.V] (go (assoc locals sym x) (rest pairs))))))))))]
      (go locals (partition 2 bindings)))))

(defn- tr-case
  "`(case e test result … default?)`: hashed-key equality against the literal tests (a list
   groups alternatives); no match and no default is none (Clojure throws)."
  [locals form [e & clauses]]
  (let [default? (odd? (count clauses))
        pairs (partition 2 clauses)]
    (with-atom locals e
      (fn [x]
        (reduce (fn [else [test result]]
                  (let [alts (if (seq? test) test [test])]
                    (bind-result (list 'CljM.caseIn x (chain-of (map literal alts)))
                                 (fn [q] (list 'if (list 'CljM.truthy q) (tr locals result) else)))))
                (if default? (tr locals (last clauses)) none-term)
                (reverse pairs))))))

(defn- rewrite-into
  "`(into to xform from)` with a map/filter/remove/keep transducer (or a comp of them) →
   `(into to (… from))`: the strict model computes the same collection."
  [locals [head to xf from :as form]]
  (letfn [(as-seq [xf acc]
            (let [h (when (seq? xf) (core-name locals (first xf)))]
              (cond (and (#{'map 'filter 'remove 'keep} h) (= 2 (count xf))) (list (first xf) (second xf) acc)
                    (= 'comp h) (reduce (fn [a x] (as-seq x a)) acc (rest xf))
                    :else (refuse! :higher-order form "into with a transducer other than map/filter/remove/keep"))))]
    (list head to (as-seq xf from))))

(defn tr
  "Translate a Clojure form to a surface term of type `Option CljM.V`."
  [locals form]
  (cond
    (symbol? form)
    (cond (contains? locals form) (some-of (local-term locals form form))
          (class-qualified? form) (refuse! :interop form)
          :else (let [v (try (ns-resolve (:ns *ctx*) form) (catch Exception _ nil))]
                  (cond (and (var? v) (.isDynamic ^clojure.lang.Var v)) (refuse! :dynamic-var form)
                        (= form (:self *ctx*)) (refuse! :recursion form)
                        (class? v) (refuse! :interop form)
                        ;; a function as a value: returned, stored, or compared
                        (and (var? v) (fn? @v)) (refuse! :escaping-fn form)
                        :else (refuse! :unmodelled-form form))))
    (constant? form) (some-of (literal form))
    (char? form) (some-of (literal form))
    (instance? java.util.regex.Pattern form) (refuse! :regex form)
    (vector? form) (with-atoms locals form (fn [as] (some-of (vctor 'vvec (chain-of as)))))
    (map? form) (if (every? constant? (keys form))
                  (let [es (seq form)]
                    (with-atoms locals (map val es)
                      (fn [as] (some-of (vctor 'vmap (reduce (fn [acc [k a]] (vctor 'ventry (literal k) a acc))
                                                             (vctor 'vnil) (reverse (map vector (map key es) as))))))))
                  (refuse! :unmodelled-form form))
    (set? form) (if (every? constant? form) (some-of (literal form)) (refuse! :unmodelled-form form))
    (and (seq? form) (seq form))
    (let [[head & args] form]
      (cond
        (keyword? head)
        (case (count args)
          1 (with-atoms locals args (fn [[m]] (list 'CljM.get m (literal head))))
          2 (with-atoms locals args (fn [[m d]] (list 'CljM.get3 m (literal head) d)))
          none-term)
        ;; a function or a value in function position (head first, as Clojure evaluates it)
        (or (not (symbol? head)) (contains? locals head))
        (with-fn locals head (fn [f] (with-atoms locals args (fn [as] (f as)))))
        :else
        (case (core-macro-name head)
          if (let [[c t e] args]
               (when-not (<= 2 (count args) 3) (refuse! :unmodelled-form form))
               (with-atom locals c
                 (fn [ca] (list 'if (list 'CljM.truthy ca) (tr locals t) (tr locals e)))))
          (let* let) (tr-let locals form (first args) (rest args))
          do (if-let [b (single-body form args)] (tr locals b) (some-of (vctor 'vnil)))
          quote (some-of (literal (first args)))
          throw none-term
          ;; a fn literal in value position (calls and function arguments are handled above)
          (fn* fn) (refuse! :escaping-fn form)
          (loop* loop recur letfn* letfn) (refuse! :recursion form)
          try (refuse! :try-catch form)
          (new . reify* deftype* import* clojure.core/import*) (refuse! :interop form)
          set! (refuse! :mutable-state form)
          var (refuse! :dynamic-var form)
          (def monitor-enter monitor-exit) (refuse! :side-effect form)
          case (tr-case locals form args)
          case* (refuse! :dispatch form)
          (let [v (try (ns-resolve (:ns *ctx*) head) (catch Exception _ nil))]
            (if (and (var? v) (:macro (meta v)))
              (let [m (binding [*ns* (:ns *ctx*)] (macroexpand-1 form))]
                (if (identical? m form) (refuse! :unmodelled-form form) (tr locals m)))
              (let [spec (resolve-call locals head form)]
                (if (and (:into spec) (= 3 (count args)))
                  (tr locals (rewrite-into locals form))
                  (let [n (count args)
                        fn-pos (cond-> (set (keys (get-in spec [:hof n :fns])))
                                 (:update spec) (conj 2)
                                 (:update-in spec) (conj 2))]
                    (letfn [(go [i forms acc]
                                (if (empty? forms)
                                  (op-call head spec acc)
                                  (if (contains? fn-pos i)
                                    (with-fn locals (first forms) (fn [b] (go (inc i) (rest forms) (conj acc {:f b}))))
                                    (with-atom locals (first forms) (fn [a] (go (inc i) (rest forms) (conj acc {:a a})))))))]
                      (go 0 args []))))))))))
    (seq? form) (some-of (vctor 'vlist (vctor 'vnil)))    ;; ()
    :else (refuse! :unmodelled-form form)))

(defn translate
  "Translate `(fn [x … & rest?] body)` read in namespace `ns`. Returns {:params [binder …]
   :fixed n :rest? bool :body term}: the body a term of type `Option CljM.V` over binders of
   type `CljM.V` (a variadic parameter is one binder, the extra arguments as a seq or nil).
   `fn-name` (the foreign name) counts as a self-reference."
  [fn-form ns fn-name]
  (let [{:keys [self arities] :as parsed} (parse-fn fn-form)
        _ (when (not= 1 (count arities)) (refuse! :multi-arity fn-form))
        {:keys [params rest body]} (first arities)]
    (binding [*ctx* {:ns (the-ns ns) :self (or self fn-name) :counter (atom 0)}]
      (let [all (cond-> params rest (conj rest))
            binders (mapv fresh all)
            locals (zipmap all binders)]
        {:params binders :fixed (count params) :rest? (some? rest)
         :body (tr (if self (dissoc locals self) locals) body)}))))

(defn accepts?
  "Does a model of shape {:clj-model/fixed n :clj-model/rest? r} take `k` arguments?"
  [{:clj-model/keys [fixed rest?]} k]
  (if rest? (<= fixed k) (= fixed k)))

(defn pack-args
  "The model's argument terms for a call with argument terms `xs`: the fixed ones, then (for a
   variadic model) the extra ones as a seq, or nil."
  [{:clj-model/keys [fixed rest?]} xs]
  (if rest? (conj (vec (take fixed xs)) (rest-term (drop fixed xs))) (vec xs)))

(defn model-defn
  "The `a/defn ^:lean` form defining the model of `fn-form` as `kname`; its metadata carries
   :clj-model/fixed and :clj-model/rest? (the shape of its parameters)."
  [kname fn-form ns fn-name]
  (let [{:keys [params body fixed rest?]} (translate fn-form ns fn-name)]
    (with-meta
      (list 'ansatz.core/defn (symbol kname) (vec (mapcat (fn [p] [p :- 'CljM.V]) params))
            '(Option CljM.V) body)
      {:clj-model/fixed fixed :clj-model/rest? rest?})))
