(ns ansatz.clj-model.translate
  "Translate the source of a plain Clojure function into the kernel model (ansatz.clj-model):
   `(fn [x …] body)` becomes `(a/defn ^:lean f.clj [x :- CljM.V …] (Option CljM.V) …)` in
   A-normal form, where every call is an `Option.bind` and `none` (no claim) propagates.

   Special forms modelled: `if` (Clojure truthiness: `CljM.truthy`), `let*`, a single-form
   `do`, `quote`, the one `fn*` arity of the function itself, and `throw` (→ none). Every other
   macro is expanded with `macroexpand-1` in the source namespace, so `when`, `cond`, `and`,
   `or`, `->`, `if-let`, `when-some`, `cond->` … are faithful by construction. `let` and `fn`
   are intercepted before expansion to refuse destructuring.

   Anything outside the model is refused with ex-info {:kind :clj/refused :reason r :form f},
   r from `refusal-reasons` (G1: no recursion, varargs, higher-order functions, destructuring)."
  (:require [clojure.string :as str]))

(def refusal-reasons
  "reason → what it means. A closed set: the model contract lists it."
  (sorted-map
   :interop "Java interop (`.method`, `Class.`, `Class/static`, `new`): no model of Java objects."
   :side-effect "An effect (printing, I/O, `def`): the model is pure."
   :mutable-state "Atoms, volatiles, `deref`, `set!`: the model has no state."
   :dynamic-var "A dynamic var or `var`: its value depends on the binding in force."
   :try-catch "`try`: catching would turn a no-claim into a value."
   :dispatch "Protocols, multimethods and `case` (hash dispatch): not modelled yet."
   :lazy-infinite "An infinite sequence (`iterate`, `cycle`, `repeat`/`range` without a bound)."
   :regex "Regular expressions: not modelled."
   :eval "`eval` and reading code at runtime."
   :escaping-fn "A function stored in data or returned: the model's values are data."
   :higher-order "A higher-order function (`map`, `reduce`, …) or a call of a local (G1 has no function sort yet)."
   :destructuring "A destructuring binding form (G1 binds symbols only)."
   :multi-form-body "A body with several forms: the earlier forms only run for effects."
   :multi-arity "A function with several arities (G1 models one)."
   :recursion "Recursion, `loop`/`recur`, `letfn` (G1 translates non-recursive functions)."
   :varargs "A variadic parameter list `[x & more]` (G1)."
   :unmodelled-fn "A call to a function the model does not cover."
   :unmodelled-form "A literal or form the model does not cover (char/BigInt/NaN literals, set or map literals with computed keys)."))

(defn refuse! [reason form & [hint]]
  (assert (contains? refusal-reasons reason) reason)
  (throw (ex-info (str "Refused Clojure model translation (" (name reason) "): "
                       (get refusal-reasons reason) "\n  form: " (pr-str form))
                  (cond-> {:kind :clj/refused :reason reason :form form}
                    hint (assoc :hint hint)))))

;; ── The clojure.core models ─────────────────────────────────────────────────────────────
;; symbol → how its call translates. :fold = left fold of a binary op (+, *, -), :chain =
;; pairwise comparison with Clojure's short circuit, :fixed = {arity kernel-name}.

(def core-ops
  {'+ {:fold "CljM.add" :zero 0 :one "CljM.num"}
   '* {:fold "CljM.mul" :zero 1 :one "CljM.num"}
   '- {:fold "CljM.sub" :one "CljM.neg"}
   '= {:chain "CljM.eq"}
   'not= {:chain "CljM.eq" :negate true}
   '< {:chain "CljM.lt"} '<= {:chain "CljM.le"} '> {:chain "CljM.gt"} '>= {:chain "CljM.ge"}
   'nil? {:fixed {1 "CljM.nilQ"}} 'some? {:fixed {1 "CljM.someQ"}} 'not {:fixed {1 "CljM.not"}}
   'identity {:fixed {1 "CljM.identity"}}
   'inc {:fixed {1 "CljM.inc"}} 'dec {:fixed {1 "CljM.dec"}}
   'zero? {:fixed {1 "CljM.zeroQ"}} 'pos? {:fixed {1 "CljM.posQ"}} 'neg? {:fixed {1 "CljM.negQ"}}
   'get {:fixed {2 "CljM.get" 3 "CljM.get3"}}
   'contains? {:fixed {2 "CljM.containsQ"}}
   'assoc {:assoc true} 'dissoc {:dissoc true}
   'count {:fixed {1 "CljM.count"}}
   'string? {:fixed {1 "CljM.stringQ"}} 'keyword? {:fixed {1 "CljM.keywordQ"}}
   'number? {:fixed {1 "CljM.numberQ"}} 'int? {:fixed {1 "CljM.intQ"}}
   'map? {:fixed {1 "CljM.mapQ"}} 'vector? {:fixed {1 "CljM.vectorQ"}}})

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
         (zipmap '[map filter remove reduce mapv filterv keep some every? apply partial comp
                   juxt sort-by group-by mapcat into update update-in run!] (repeat :higher-order))))

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

(def ^:private ^:dynamic *ctx* nil)   ;; {:ns :self :counter (atom n)}

(defn- fresh [base]
  (symbol (str "cv_" (str/replace (str base) #"[^A-Za-z0-9]" "_") "_" (swap! (:counter *ctx*) inc))))

(declare tr)

(defn- atom-of [locals form]
  (cond (and (symbol? form) (contains? locals form)) (get locals form)
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

(defn- chain-call
  "Clojure's (< x y & more): compare pairwise, false at the first failing pair."
  [kname atoms negate]
  (let [ret (fn [x] (if negate (bind-result x (fn [r] (list 'CljM.not r))) x))]
    (if (= 1 (count atoms))
      (some-of (literal (not negate)))
      (ret (reduce (fn [acc [x y]]
                     (bind-result acc (fn [r] (list 'if (list 'CljM.truthy r) (list (symbol kname) x y)
                                                    (some-of (literal false))))))
                   (list (symbol kname) (first atoms) (second atoms))
                   (partition 2 1 (rest atoms)))))))

(defn- op-call [sym spec atoms]
  (let [n (count atoms)]
    (cond
      (:fold spec) (case n
                     0 (if (contains? spec :zero) (some-of (literal (:zero spec))) none-term)
                     1 (list (symbol (:one spec)) (first atoms))
                     (reduce (fn [acc y] (bind-result acc (fn [r] (list (symbol (:fold spec)) r y))))
                             (list (symbol (:fold spec)) (first atoms) (second atoms))
                             (drop 2 atoms)))
      (:chain spec) (if (zero? n) none-term (chain-call (:chain spec) atoms (:negate spec)))
      (:assoc spec) (if (or (< n 3) (even? n)) none-term
                        (reduce (fn [acc [k v]] (bind-result acc (fn [r] (list 'CljM.assoc r k v))))
                                (list 'CljM.assoc (first atoms) (second atoms) (nth atoms 2))
                                (partition 2 (drop 3 atoms))))
      (:dissoc spec) (case n
                       0 none-term
                       1 (some-of (first atoms))
                       (reduce (fn [acc k] (bind-result acc (fn [r] (list 'CljM.dissoc r k))))
                               (list 'CljM.dissoc (first atoms) (second atoms))
                               (drop 2 atoms)))
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

(defn- tr-let [locals form bindings body]
  (check-binding-vector form bindings)
  (let [body (single-body form body)]
    (letfn [(go [locals pairs]
              (if (empty? pairs)
                (tr locals body)
                (let [[sym init] (first pairs)]
                  (if-let [a (atom-of locals init)]
                    (go (assoc locals sym a) (rest pairs))
                    (let [x (fresh sym)]
                      (list 'Option.bind (tr locals init)
                            (list 'fn [x :- 'CljM.V] (go (assoc locals sym x) (rest pairs)))))))))]
      (go locals (partition 2 bindings)))))

(defn- resolve-call [locals sym form]
  (let [nsp (:ns *ctx*)]
    (cond
      (contains? locals sym) (refuse! :higher-order form)
      (= sym (:self *ctx*)) (refuse! :recursion form)
      (str/starts-with? (name sym) ".") (refuse! :interop form)
      (and (str/ends-with? (name sym) ".") (not= sym '.)) (refuse! :interop form)
      :else
      (let [v (try (ns-resolve nsp sym) (catch Exception _ ::class))]
        (cond
          (or (= ::class v) (class? v)) (refuse! :interop form)
          (and (namespace sym) (nil? v)
               (try (class? (ns-resolve nsp (symbol (namespace sym)))) (catch Exception _ false)))
          (refuse! :interop form)
          (nil? v) (refuse! :unmodelled-fn form)
          (.isDynamic ^clojure.lang.Var v) (refuse! :dynamic-var form)
          (= (str (:ns (meta v))) "clojure.core") (or (get core-ops (:name (meta v)))
                                                      (when-let [r (classified (:name (meta v)))]
                                                        (refuse! r form))
                                                      (refuse! :unmodelled-fn form))
          (instance? clojure.lang.MultiFn @v) (refuse! :dispatch form)
          (:protocol (meta v)) (refuse! :dispatch form)
          :else (refuse! :unmodelled-fn form))))))

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

(defn tr
  "Translate a Clojure form to a surface term of type `Option CljM.V`."
  [locals form]
  (cond
    (symbol? form)
    (cond (contains? locals form) (some-of (get locals form))
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
        (not (symbol? head)) (refuse! :higher-order form)
        (contains? locals head) (refuse! :higher-order form)
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
          ;; a fn literal outside a call to a higher-order function (those refuse first)
          (fn* fn) (refuse! :escaping-fn form)
          (loop* loop recur letfn* letfn) (refuse! :recursion form)
          try (refuse! :try-catch form)
          (new . reify* deftype* import* clojure.core/import*) (refuse! :interop form)
          set! (refuse! :mutable-state form)
          var (refuse! :dynamic-var form)
          (def monitor-enter monitor-exit) (refuse! :side-effect form)
          (case case*) (refuse! :dispatch form)
          (let [v (try (ns-resolve (:ns *ctx*) head) (catch Exception _ nil))]
            (if (and (var? v) (:macro (meta v)) (not (contains? locals head)))
              (let [m (binding [*ns* (:ns *ctx*)] (macroexpand-1 form))]
                (if (identical? m form) (refuse! :unmodelled-form form) (tr locals m)))
              (let [spec (resolve-call locals head form)]
                (with-atoms locals args (fn [as] (op-call head spec as)))))))))
    (seq? form) (some-of (vctor 'vlist (vctor 'vnil)))    ;; ()
    :else (refuse! :unmodelled-form form)))

(defn parse-fn
  "`(fn name? [params] body)` → {:params [sym …] :body form :self name}; refuses what G1 does
   not translate."
  [form]
  (when-not (and (seq? form) (#{'fn 'fn* 'clojure.core/fn} (first form)))
    (refuse! :unmodelled-form form "G1 translates an inline (fn [x …] body)"))
  (let [[_ & more] form
        self (when (symbol? (first more)) (first more))
        more (if self (rest more) more)
        arities (if (vector? (first more)) [more] more)]
    (when (not= 1 (count arities)) (refuse! :multi-arity form))
    (let [[params & body] (first arities)]
      (when-not (vector? params) (refuse! :unmodelled-form form))
      (when (some #{'&} params) (refuse! :varargs form))
      (when-not (every? symbol? params) (refuse! :destructuring form))
      {:params params :body (single-body form body) :self self})))

(defn translate
  "Translate `(fn [x …] body)` read in namespace `ns`. Returns {:params [model binder …] :body term},
   the body a term of type `Option CljM.V` over binders of type `CljM.V`. `fn-name` (the
   foreign name) counts as a self-reference."
  [fn-form ns fn-name]
  (let [{:keys [params body self]} (parse-fn fn-form)]
    (binding [*ctx* {:ns (the-ns ns) :self (or self fn-name) :counter (atom 0)}]
      (let [binders (mapv fresh params)
            locals (zipmap params binders)]
        {:params binders
         :body (tr (if self (dissoc locals self) locals) body)}))))

(defn model-defn
  "The `a/defn ^:lean` form defining the model of `fn-form` as `kname`."
  [kname fn-form ns fn-name]
  (let [{:keys [params body]} (translate fn-form ns fn-name)]
    (list 'ansatz.core/defn (symbol kname) (vec (mapcat (fn [p] [p :- 'CljM.V]) params))
          '(Option CljM.V) body)))
