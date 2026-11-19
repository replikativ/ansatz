(ns ansatz.clj-check
  "Differential checking of Ansatz elaboration against clojure.core.

   The kernel checks that a definition is well typed, and `ansatz.malli/check-verified!` checks
   that the compiled code computes what the kernel term computes. Neither can see an elaboration
   that gave a Clojure form a non-Clojure meaning: the proofs and the runtime then agree with each
   other and still disagree with the Clojure text. This namespace compares the compiled function
   with the CLOJURE READING of the same source — the form evaluated by clojure.core — on generated
   inputs.

   The pieces:
     type-desc      kernel parameter/result type → a small descriptor ([:nat], [:list [:int]], …)
     gen-inputs     seeded, edge-first argument tuples for a list of descriptors (no test.check)
     clj->runtime   Clojure value → the value the compiled function takes (an Option argument
     runtime->clj   passes unchanged; see `*option-rep*`) and back
     agree?         result equality: integers across Long/BigInt, NaN = NaN, sequences by element
     run-row        one row of the clojure.core contract table (ansatz.clj-contract)

   A call where clojure.core throws is outside the contract (Ansatz's total functions return
   something there); such calls are counted as :clj-throws, never as divergences.

   The Clojure model (ansatz.clj-model) is checked here too: `run-model-row` runs a row of the
   model contract (ansatz.clj-model.contract) on random EDN (`gen-edn-inputs`), and
   `check-model!` checks an `a/foreign ^:model` function's faithfulness and conformance."
  (:require [clojure.string :as str]
            [ansatz.core :as a]
            [ansatz.codegen.lean-runtime :as rt]
            [ansatz.config :as config]
            [ansatz.clj-model :as clj-model]
            [ansatz.clj-model.translate :as translate]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.surface.ingest :as ingest]))

;; ── Kernel types → descriptors ───────────────────────────────────────────────────────────

(defn- head-name [ty]
  (let [[h _] (e/get-app-fn-args ty)]
    (when (e/const? h) (name/->string (e/const-name h)))))

(declare type-desc)

(defn- struct-desc
  "A registered, non-parametric structure: its field names and field descriptors, read from the
   constructor's type."
  [environment tn sinfo]
  (when-let [ci (env/lookup environment (name/from-string (str tn ".mk")))]
    (let [field-types (loop [t (.type ^ansatz.kernel.ConstantInfo ci) acc []]
                        (if (e/forall? t)
                          (recur (e/forall-body t) (conj acc (e/forall-type t)))
                          acc))]
      (when (= (count field-types) (count (:fields sinfo)))
        [:struct tn (:ctor-sym sinfo)
         (mapv (fn [f t] [(keyword f) (type-desc environment t)]) (:fields sinfo) field-types)]))))

(defn type-desc
  "A descriptor for a closed kernel type, or [:unknown <printed type>]."
  [environment ty]
  (if (e/has-loose-bvars? ty)
    [:unknown (e/->string ty)]
    (let [[_ args] (e/get-app-fn-args ty)
          hn (head-name ty)
          sinfo (get @ingest/structure-registry hn)]
      (cond
        (and (empty? args) (#{"Nat" "Int" "Float" "Bool" "String"} hn))
        [(keyword (str/lower-case hn))]
        (and (= "List" hn) (= 1 (count args))) [:list (type-desc environment (first args))]
        (and (= "Option" hn) (= 1 (count args))) [:option (type-desc environment (first args))]
        (and (= "Prod" hn) (= 2 (count args)))
        [:prod (type-desc environment (first args)) (type-desc environment (second args))]
        (and sinfo (empty? args)) (or (struct-desc environment hn sinfo) [:unknown hn])
        :else [:unknown (e/->string ty)]))))

(defn- known? [d]
  (and (not= :unknown (first d))
       (case (first d)
         (:list :option) (known? (second d))
         :prod (and (known? (nth d 1)) (known? (nth d 2)))
         :struct (every? (comp known? second) (nth d 3))
         true)))

(defn signature
  "{:params [desc …] :ret desc} of a defined kernel constant, read from its type. Implicit and
   instance binders make a polymorphic signature, which this does not generate for: the
   descriptors then contain :unknown."
  [environment kname]
  (let [ci (env/lookup! environment (name/from-string (str kname)))]
    (loop [t (.type ^ansatz.kernel.ConstantInfo ci) ps []]
      (if (e/forall? t)
        (recur (e/forall-body t) (conj ps (type-desc environment (e/forall-type t))))
        {:params ps :ret (type-desc environment t)}))))

;; ── Generation: seeded, edge cases first ─────────────────────────────────────────────────

(def ^:private float-edges
  [0.0 -0.0 1.0 -1.0 2.0 -2.0 2.5 -7.5 7.0 0.1 Double/NaN Double/POSITIVE_INFINITY
   Double/NEGATIVE_INFINITY])

(defn edges
  "The edge values of a descriptor, the ones a divergence usually hides behind (0 and 1 for
   Nat, negatives for Int, ±0.0/NaN/±Infinity for Float, the empty list, nil for Option)."
  [d]
  (case (first d)
    :nat [0 1 2 3 7]
    :int [0 1 -1 2 -2 7 -7]
    :float float-edges
    :bool [false true]
    :string ["" "a" "ab" "b"]
    :list (let [es (edges (second d))]
            (into [[] [(first es)]]
                  (when (second es) [[(second es) (first es)] [(first es) (second es) (first es)]])))
    :option (into [nil] (take 3 (edges (second d))))
    :prod (vec (for [x (take 3 (edges (nth d 1))) y (take 3 (edges (nth d 2)))] [x y]))
    :struct (let [ctor @(resolve (nth d 2))
                  fields (nth d 3)]
              (->> (apply map vector (map (fn [[_ fd]] (take 3 (cycle (edges fd)))) fields))
                   (mapv #(apply ctor %))))
    []))

(defn- rand-nth-rng [^java.util.Random rng xs]
  (nth xs (.nextInt rng (count xs))))

(defn random-value
  "A random value of descriptor `d` drawn from `rng` (a java.util.Random)."
  [^java.util.Random rng d]
  (case (first d)
    :nat (long (.nextInt rng 41))
    :int (long (- (.nextInt rng 81) 40))
    :float (case (.nextInt rng 4)
             0 (double (- (.nextInt rng 41) 20))
             (* 100.0 (- (.nextDouble rng) 0.5)))
    :bool (.nextBoolean rng)
    :string (apply str (repeatedly (.nextInt rng 4) #(rand-nth-rng rng [\a \b \c])))
    :list (vec (repeatedly (.nextInt rng 5) #(random-value rng (second d))))
    :option (when (.nextBoolean rng) (random-value rng (second d)))
    :prod [(random-value rng (nth d 1)) (random-value rng (nth d 2))]
    :struct (apply @(resolve (nth d 2)) (map (fn [[_ fd]] (random-value rng fd)) (nth d 3)))))

(defn gen-inputs
  "Argument tuples for `descs`: the cartesian product of the edge values (at most `max-edges`
   tuples), then `n-random` random tuples from a generator seeded with `seed`."
  [descs & {:keys [seed n-random max-edges] :or {seed 42 n-random 40 max-edges 256}}]
  (let [rng (java.util.Random. (long seed))
        product (reduce (fn [acc d] (for [xs acc x (edges d)] (conj xs x))) [[]] descs)]
    (vec (concat (take max-edges product)
                 (repeatedly n-random (fn [] (mapv #(random-value rng %) descs)))))))

;; ── Representation: Clojure values ↔ compiled-runtime values ─────────────────────────────

(def ^:dynamic *option-rep*
  "How the compiled code represents `Option`. :nil-punning (the default; ansatz.codegen) —
   `none` is nil and `some x` is x, boxed in a `SomeBox` only when x is nil or a box
   (ansatz.codegen.lean-runtime/some-of), so a Clojure value crosses unchanged.
   :tagged (legacy, for code compiled when `some x` ran as `[x]`; to be removed) — `none` is
   nil and `some x` is `[x]`. The Clojure side always uses nil-punning."
  :nil-punning)

(defn clj->runtime
  "The value the compiled function expects for the Clojure value `v` of descriptor `d`."
  [d v]
  (case (first d)
    :option (cond (nil? v) nil
                  (= :tagged *option-rep*) [(clj->runtime (second d) v)]
                  :else (rt/some-of (clj->runtime (second d) v)))
    :list (mapv #(clj->runtime (second d) %) v)
    :prod [(clj->runtime (nth d 1) (first v)) (clj->runtime (nth d 2) (second v))]
    v))

(defn runtime->clj
  "The Clojure value of a compiled-runtime result `v` of descriptor `d`."
  [d v]
  (case (first d)
    :option (cond (nil? v) nil
                  (= :tagged *option-rep*)
                  (if (and (vector? v) (= 1 (count v)))
                    (runtime->clj (second d) (first v))
                    (throw (ex-info "not a tagged Option value" {:value v})))
                  :else (runtime->clj (second d) (rt/some-val v)))
    :list (some->> (seq v) (mapv #(runtime->clj (second d) %)))
    :prod [(runtime->clj (nth d 1) (first v)) (runtime->clj (nth d 2) (second v))]
    v))

(defn agree?
  "Do a Clojure result `c` and a (converted) Ansatz result `r` of descriptor `d` agree?
   Integers compare across Long/BigInt, doubles numerically with NaN equal to NaN, sequences
   element by element (nil and the empty sequence are the same value: Ansatz identifies
   `nil` with `()`, see the contract), Option by presence and then by value."
  [d c r]
  (case (first d)
    (:nat :int) (and (integer? c) (integer? r) (== c r))
    :float (and (instance? Double c) (instance? Double r)
                (or (and (Double/isNaN c) (Double/isNaN r)) (== c r)))
    :list (and (or (nil? c) (sequential? c)) (or (nil? r) (sequential? r))
               (= (count c) (count r))
               (every? true? (map #(agree? (second d) %1 %2) c r)))
    :option (if (or (nil? c) (nil? r)) (and (nil? c) (nil? r)) (agree? (second d) c r))
    :prod (and (sequential? c) (sequential? r) (= 2 (count c) (count r))
               (agree? (nth d 1) (first c) (first r))
               (agree? (nth d 2) (second c) (second r)))
    (= c r)))

;; ── Running a row ────────────────────────────────────────────────────────────────────────

(def ^:private scratch-ns 'ansatz.clj-check.rows)

(defn- the-scratch-ns []
  (or (find-ns scratch-ns)
      (let [n (create-ns scratch-ns)]
        (binding [*ns* n] (clojure.core/refer-clojure))
        n)))

(defonce ^:private row-counter (atom 0))

(defn- row-kernel-name [id]
  (symbol (str "ccrow-" (str/replace (str (namespace id) "-" (name id)) #"[^A-Za-z0-9-]" "-")
               "-" (swap! row-counter inc))))

(defn- eval-in [n form]
  (binding [*ns* n] (eval form)))

(defn- root-message [^Throwable t]
  (->> (iterate #(.getCause ^Throwable %) t)
       (take-while some?)
       (map #(.getMessage ^Throwable %))
       (remove nil?)
       (str/join " / ")))

(defn run-setup!
  "Evaluate declarations rows refer to (ansatz.clj-contract/setup-forms) in the rows'
   namespace. A declaration the session already has is kept."
  [forms]
  (doseq [f forms]
    (try (binding [a/*verbose* false] (eval-in (the-scratch-ns) f))
         (catch Throwable t
           (when-not (re-find #"already declared" (str (root-message t)))
             (throw t))))))

(defn missing-constants
  "The constants of `required` the current environment lacks."
  [required]
  (let [environment (a/env)]
    (vec (remove #(env/lookup environment (name/from-string %)) (sort required)))))

(defn reading
  "The Clojure reading of a row: `(fn [params…] form)` evaluated by clojure.core."
  [{:keys [params form]}]
  (eval-in (the-scratch-ns) (list 'fn (mapv first params) form)))

(defn define-row!
  "Define the row's form as an `a/defn` over its typed parameters. Returns the compiled fn."
  [{:keys [id params ret form lean?]}]
  (let [kname (row-kernel-name id)
        binders (mapv (fn [[p t]] (with-meta p {:- t})) params)]
    (binding [a/*verbose* false]
      (eval-in (the-scratch-ns)
               (list 'ansatz.core/defn (with-meta kname (cond-> {:- ret} lean? (assoc :lean true)))
                     binders form)))
    {:kname kname
     :fn @(ns-resolve (the-scratch-ns) kname)}))

(defn classify-call
  "Run one argument tuple (Clojure values) through the reading and the compiled fn."
  [clj-f rt-f sig args]
  (let [c (try {:v (apply clj-f args)} (catch Throwable t {:ex t}))
        r (when-not (:ex c)
            (try {:v (runtime->clj (:ret sig)
                                   (apply rt-f (map clj->runtime (:params sig) args)))}
                 (catch Throwable t {:ex t})))]
    (cond (:ex c) {:class :clj-throws}
          (:ex r) {:class :ansatz-throws :args args :clojure (:v c) :error (.getMessage ^Throwable (:ex r))}
          (agree? (:ret sig) (:v c) (:v r)) {:class :agree}
          :else {:class :diverge :args args :clojure (:v c) :ansatz (:v r)})))

(defn run-row
  "Run one contract row. Returns
     {:id … :status :skipped :missing [consts]}             a required constant is absent
     {:id … :status :refused :error msg :data ex-data}      the definition was not accepted
     {:id … :status :ran :counts {:agree n :diverge n …} :witnesses [first divergences]}
   `opts`: :seed, :n-random, :max-edges (see gen-inputs)."
  [row & {:as opts}]
  (let [missing (missing-constants (:requires row #{}))]
    (if (seq missing)
      {:id (:id row) :status :skipped :missing missing}
      (let [defined (try (define-row! row)
                         (catch Throwable t
                           {:refused t}))]
        (if-let [t (:refused defined)]
          {:id (:id row) :status :refused :error (root-message t)
           :data (let [datas (keep (fn [^Throwable x] (when (instance? clojure.lang.ExceptionInfo x) (ex-data x)))
                                   (take-while some? (iterate #(.getCause ^Throwable %) t)))]
                   (or (first (filter :reason datas)) (first datas)))}
          (let [sig (signature (a/env) (:kname defined))
                _ (when-not (every? known? (conj (:params sig) (:ret sig)))
                    (throw (ex-info "clj-check: no generator for a parameter or result type"
                                    {:row (:id row) :signature sig})))
                clj-f (reading row)
                domain (when-let [d (:domain row)] (eval-in (the-scratch-ns) d))
                inputs (cond->> (apply gen-inputs (:params sig)
                                       (mapcat identity (merge {:seed (hash (:id row))} opts)))
                         domain (filter #(apply domain %)))
                results (mapv #(classify-call clj-f (:fn defined) sig %) inputs)]
            {:id (:id row) :status :ran
             :counts (frequencies (map :class results))
             :witnesses (vec (take 3 (filter #(#{:diverge :ansatz-throws} (:class %)) results)))}))))))

(defn row-verdict
  "Does a run-row result meet the row's :expect? Returns {:ok? bool :why string}."
  [row result]
  (let [{:keys [status counts]} result
        bad (+ (get counts :diverge 0) (get counts :ansatz-throws 0))]
    (case status
      :skipped {:ok? true :why (str "skipped: missing " (:missing result))}
      :refused (if (= :refuse (:expect row))
                 (if-let [reason (:reason row)]
                   {:ok? (= reason (get-in result [:data :reason]))
                    :why (str "refused with " (pr-str (get-in result [:data :reason]))
                              ", expected reason " reason ": " (:error result))}
                   {:ok? true :why "refused"})
                 {:ok? false :why (str "expected " (:expect row) " but the definition was refused: "
                                       (:error result))})
      :ran (case (:expect row)
             (:agree :domain) {:ok? (and (zero? bad) (pos? (get counts :agree 0)))
                               :why (str "counts " counts " witnesses " (:witnesses result))}
             :diverges {:ok? (pos? (get counts :diverge 0))
                        :why (str "expected a divergence (a fix must flip this row), counts " counts)}
             :refuse {:ok? false :why (str "expected a refusal but the definition was accepted, counts "
                                           counts " witnesses " (:witnesses result))}))))

;; ── Per-definition check: check-clojure! ─────────────────────────────────────────────────
;; A row checks one operator; a definition composes them, and some divergences only appear in
;; the composition: `(if (== n 0) 0 (f (- n 2)))` over Nat verifies (truncating subtraction
;; makes every chain reach 0) while its Clojure reading never terminates for odd n.

(defn- fuel-exhausted [] (ex-info "clj-check: the Clojure reading ran out of fuel" {::fuel true}))

(defn- call-with-timeout
  "Run (f) on a daemon thread with a deeper stack; {:v value}, {:ex throwable} or {:timeout true}.
   A timed-out thread cannot be stopped on current JDKs; it is left to finish on its own (the
   Clojure reading is fuel-limited, so a recursive spin ends; a `loop` spin does not)."
  [f timeout-ms]
  (let [p (promise)
        t (Thread. nil
                   (fn [] (deliver p (try {:v (f)} (catch Throwable x {:ex x}))))
                   "clj-check-call" (* 64 1024 1024))]
    (.setDaemon t true)
    (.start t)
    (deref p timeout-ms {:timeout true})))

(defn- plain-param-names [params]
  (mapv first (ingest/parse-params params)))

(defn- clojure-reading
  "The Clojure reading of a recorded a/defn source: the body as a clojure.core function whose
   self-calls are fuel-counted. Returns {:f fn} or {:error msg} when the body has no Clojure
   reading (Ansatz-only forms such as `match` or typed `let`)."
  [{:keys [ns params body raw-name]} fuel]
  (let [pairs (ingest/parse-params params)]
    (if (some #(not= :default (nth % 2)) pairs)
      {:error "implicit or instance binders have no Clojure reading"}
      (let [self (symbol (str raw-name))
            ps (mapv first pairs)
            counter (gensym "fuel")
            form `(fn [~counter]
                    (letfn [(~self [~@ps]
                              (when (neg? (swap! ~counter dec))
                                (throw (#'ansatz.clj-check/fuel-exhausted)))
                              ~body)]
                      ~self))]
        (try (let [factory (binding [*ns* (the-ns ns)] (eval form))]
               ;; a fresh fuel budget per call
               {:make (fn [] (factory (atom fuel)))})
             (catch Throwable t {:error (root-message t)}))))))

(defn- fuel-exception? [^Throwable t]
  (some #(::fuel (ex-data %)) (take-while some? (iterate #(.getCause ^Throwable %) t))))

(defn check-clojure!
  "Compare an a/defn'd function with its Clojure reading — the same body evaluated by
   clojure.core — on inputs generated from the definition's kernel parameter types.

   `f` is the compiled function, its var or its symbol. Options: :runs (random inputs after the
   edge cases, default 40), :seed, :timeout-ms per Clojure call (default 2000), :fuel (self-calls
   per Clojure call, default 100000).

   Returns {:status :agree :runs n :agree n :clj-throws n} when every call agrees, or
   {:status :no-clojure-reading :cause msg} when the body is not Clojure (`match`, typed `let`,
   Lean names). Throws ex-info \"Clojure reading disagrees\" with {:args :clojure :ansatz} on the
   first divergence. A Clojure reading that overflows the stack, runs out of fuel or times out
   while the compiled function returned is a divergence (non-termination); any other Clojure
   exception is outside the contract (:clj-throws). Callees that are other verified functions run
   as their compiled versions."
  [f & {:keys [runs seed timeout-ms fuel] :or {runs 40 seed 42 timeout-ms 2000 fuel 100000}}]
  (let [v (cond (var? f) @f (symbol? f) @(resolve f) :else f)
        _ (when (nil? v) (throw (ex-info "check-clojure!: nothing to check" {:fn f})))
        kname (:ansatz.core/kernel-name (meta v))
        src (when kname (get @ingest/source-registry kname))]
    (when-not src
      (throw (ex-info "check-clojure!: not an a/defn function with a recorded source" {:fn f})))
    (let [{:keys [error make]} (clojure-reading src fuel)]
      (if error
        {:status :no-clojure-reading :cause error}
        (let [sig (signature (a/env) kname)]
          (when-not (every? known? (conj (:params sig) (:ret sig)))
            (throw (ex-info "check-clojure!: no generator for a parameter or result type"
                            {:fn kname :signature sig})))
          (let [inputs (gen-inputs (:params sig) :seed seed :n-random runs :max-edges 64)
                counts (atom {})]
            (doseq [args inputs]
              (let [r (call-with-timeout
                       #(runtime->clj (:ret sig) (apply v (map clj->runtime (:params sig) args)))
                       timeout-ms)
                    c (when (contains? r :v) (call-with-timeout #(apply (make) args) timeout-ms))
                    class (cond
                            (not (contains? r :v)) :ansatz-throws
                            (:timeout c) :diverge
                            (and (:ex c) (or (instance? StackOverflowError (:ex c))
                                             (fuel-exception? (:ex c)))) :diverge
                            (:ex c) :clj-throws
                            (agree? (:ret sig) (:v c) (:v r)) :agree
                            :else :diverge)]
                (swap! counts update class (fnil inc 0))
                (case class
                  :diverge
                  (throw (ex-info "Clojure reading disagrees"
                                  {:fn kname :args args
                                   :clojure (cond (:timeout c) :timeout
                                                  (:ex c) (if (fuel-exception? (:ex c)) :out-of-fuel
                                                              :stack-overflow)
                                                  :else (:v c))
                                   :ansatz (:v r)}))
                  :ansatz-throws
                  (throw (ex-info "check-clojure!: the compiled function failed"
                                  {:fn kname :args args
                                   :error (if (:timeout r) :timeout (root-message (:ex r)))}))
                  nil)))
            (merge {:status :agree :runs (count inputs) :agree 0 :clj-throws 0} @counts)))))))

(defmacro deftest-clojure
  "A clojure.test deftest that runs `check-clojure!` on the a/defn'd function named `f`
   (leanfran's defcheck). `f` is resolved when the test runs, in the namespace that uses the
   macro, so the definition may happen after the namespace is loaded."
  [test-name f & opts]
  `(clojure.test/deftest ~test-name
     (let [r# (check-clojure! (ns-resolve '~(ns-name *ns*) '~f) ~@opts)]
       (clojure.test/is (contains? #{:agree :no-clojure-reading} (:status r#)) (pr-str r#)))))

;; ── The Clojure model (ansatz.clj-model): faithfulness and conformance ───────────────────
;; Faithfulness: the compiled model against clojure.core on random EDN. Model `some v` must
;; equal clojure.core's value under clj-model/strict= (else :model-bug, a hard failure); model
;; `none` where clojure.core throws is :throws (right), where it returns is :no-claim (a gap,
;; counted against a row's :max-no-claim so a model answering none everywhere fails).
;; Conformance: on inputs from the declared types, dec_R of the model's result must be `some`.

(def ^:private long-edges [0 1 -1 2 7 -7 Long/MAX_VALUE Long/MIN_VALUE])
(def ^:private double-edges [0.0 -0.0 1.5 -2.0 Double/NaN Double/POSITIVE_INFINITY])
(def ^:private string-edges ["" "a" "ab" "😀" " \t" "Ab/c"])
(def ^:private keyword-edges [:a :b :c :ns/k])

(defn- big-map [] (zipmap (map #(keyword (str "k" %)) (range 10)) (range 10)))

(defn edn-edges
  "Edge values of an EDN generator kind: :any :int :nat :num :bool :string :key :map :coll :value,
   :ints (collections of integers), :kmap (keyword → integer maps), :mixmap (as :kmap, half of them
   hash maps of 9-12 entries), :seqable (collections and strings),
   :double; and for boundary types [:vec k] (vectors of k), [:pair a b], [:opt k] (nil or k)."
  [kind]
  (if (vector? kind)
    (let [[tag a b] kind]
      (case tag
        :vec (let [es (edn-edges a)] [[] [(first es)] (vec (take 3 es))])
        :pair (vec (for [x (take 3 (edn-edges a)) y (take 3 (edn-edges b))] [x y]))
        :opt (into [nil] (edn-edges a))))
    (case kind
      :double double-edges
      :ints [nil [] () [1 2 3] '(3 1 2) [2 2 1] [Long/MAX_VALUE 1] #{1 2 3} #{} (map inc [0 1 2]) (range 3) [-1]]
      :kmap [{} {:a 1} {:a 1 :b 2} {:b 2 :a 1 :c 3} {:a Long/MAX_VALUE :b 1} (big-map)]
      :mixmap [{} {:b 2 :a 1 :c 3} (zipmap [:i :h :g :f :e :d :c :b :a] (range 9)) (big-map)
               (zipmap (map #(keyword (str (char (+ 97 %)))) (range 12)) (range 12))]
      :seqable (into (edn-edges :coll) ["" "ab" "😀" [1 2 3] #{:a :b :c} (big-map)])
      :int long-edges
      :nat [0 1 2 7 Long/MAX_VALUE]
      :num (into long-edges double-edges)
      :bool [false true]
      :string string-edges
      :key (into keyword-edges [0 1 "a" nil])
      :map [{} {:a 1} {:a 1 :b 2} {:a Long/MAX_VALUE :b 1} {:a "x" :b 1} (hash-map :a 1 :b 2) (big-map)]
      :coll [nil [] () {} #{} [1 2] '(1 2) {:a 1} #{1 2} (map inc [0 1])]
      :value [nil {:a 1 :b 2} {:a 1} {:a Long/MAX_VALUE :b 1} {:a -3 :b 1.5} {:a "x" :b 1} {} [1 2]
              {:b 2 :a 1 :c [1]} true 3 "s" :k #{1}]
      :any [nil true false 0 1 -1 Long/MAX_VALUE Long/MIN_VALUE 0.0 -0.0 1.5 Double/NaN ""
            "😀" :a :ns/k 'sym \a () '(1 2) [] [1 2] {} {:a 1 :b 2} (hash-map :a 1 :b 2)
            (big-map) #{} #{1 2} (map inc [0 1])])))

(defn random-edn
  "A random EDN value of `kind` from `rng`, nested at most `depth` deep."
  [^java.util.Random rng kind depth]
  (let [pick (fn [xs] (nth xs (.nextInt rng (count xs))))
        small-int (fn [] (long (- (.nextInt rng 41) 20)))
        sub (fn [k] (random-edn rng k (dec depth)))]
    (if (vector? kind)
      (let [[tag a b] kind]
        (case tag
          :vec (vec (repeatedly (.nextInt rng 4) #(random-edn rng a 0)))
          :pair [(random-edn rng a 0) (random-edn rng b 0)]
          :opt (when (.nextBoolean rng) (random-edn rng a 0))))
      (case kind
        :double (random-edn rng :num 0)
        :int (if (zero? (.nextInt rng 5)) (pick long-edges) (small-int))
        :nat (if (zero? (.nextInt rng 5)) (pick [0 Long/MAX_VALUE]) (long (.nextInt rng 40)))
        :num (case (.nextInt rng 3) 0 (pick double-edges) 1 (* 10.0 (- (.nextDouble rng) 0.5)) (random-edn rng :int 0))
        :bool (.nextBoolean rng)
        :ints (let [xs (repeatedly (.nextInt rng 5) #(random-edn rng :int 0))]
                (case (.nextInt rng 5) 0 (vec xs) 1 (apply list xs) 2 (set xs) 3 (map identity xs) (vec (map #(mod % 5) xs))))
        :kmap (let [n (if (zero? (.nextInt rng 6)) (+ 9 (.nextInt rng 3)) (.nextInt rng 5))]
                (into {} (map (fn [i] [(keyword (str (char (+ 97 i)))) (random-edn rng :int 0)]) (range n))))
        ;; half small maps (array maps), half maps of 9-12 entries (hash maps)
        :mixmap (let [n (if (.nextBoolean rng) (.nextInt rng 5) (+ 9 (.nextInt rng 4)))]
                  (into {} (map (fn [i] [(keyword (str (char (+ 97 i)))) (random-edn rng :int 0)])
                                (take n (sort-by (fn [_] (.nextInt rng)) (range 14))))))
        :seqable (case (.nextInt rng 3) 0 (random-edn rng :string 0) 1 (random-edn rng :ints 0) (random-edn rng :coll depth))
        :string (pick (into string-edges ["b" "abc"]))
        :key (pick (into keyword-edges [0 1 2 "a"]))
        :map (let [n (if (zero? (.nextInt rng 8)) (+ 9 (.nextInt rng 3)) (.nextInt rng 4))
                   vk (if (pos? depth) :any :int)]
               (into {} (repeatedly n #(vector (random-edn rng :key 0) (sub vk)))))
        :value (case (.nextInt rng 6)
                 0 (pick [nil true false "s" :k 1.5])
                 1 (random-edn rng :int 0)
                 2 (vec (repeatedly (.nextInt rng 3) #(sub :value)))
               ;; records: each of :a :b :c present with p = 0.7, mostly integer-valued
                 (into {} (for [k [:a :b :c] :when (< (.nextInt rng 10) 7)]
                            [k (if (or (zero? depth) (< (.nextInt rng 10) 7)) (random-edn rng :int 0) (sub :value))])))
        :coll (case (.nextInt rng 5)
                0 nil
                1 (vec (repeatedly (.nextInt rng 4) #(sub :any)))
                2 (random-edn rng :map depth)
                3 (set (repeatedly (.nextInt rng 3) #(random-edn rng :key 0)))
                (apply list (repeatedly (.nextInt rng 3) #(sub :any))))
        :any (case (.nextInt rng 8)
               0 nil
               1 (.nextBoolean rng)
               2 (random-edn rng :num 0)
               3 (random-edn rng :string 0)
               4 (random-edn rng :key 0)
               5 (if (pos? depth) (random-edn rng :coll depth) (pick [[] {} #{}]))
               6 (random-edn rng :int 0)
               (pick [\a 'sym (map inc [0 1])]))))))

(defn gen-edn-inputs
  "Argument tuples for generator `kinds`: the product of the edges (at most `max-edges`), then
   `n-random` random tuples from a generator seeded with `seed`."
  [kinds & {:keys [seed n-random max-edges] :or {seed 42 n-random 60 max-edges 200}}]
  (let [rng (java.util.Random. (long seed))
        product (reduce (fn [acc k] (for [xs acc x (edn-edges k)] (conj xs x))) [[]] kinds)]
    (vec (concat (take max-edges product)
                 (repeatedly n-random (fn [] (mapv #(random-edn rng % 2) kinds)))))))

(defn- model-call
  "The compiled model's answer (a runtime CljM.V), or nil for none. The compiled fixpoint of a
   recursive model takes a frame per level where Clojure's `recur` takes none; running out of
   stack there is no claim."
  [model-fn arity args]
  (try (some-> (clj-model/opt-value (apply model-fn (clj-model/pack-args arity (map clj-model/edn->cljv args)))) :some)
       (catch StackOverflowError _ nil)))

(defn outside-domain?
  "Does an input contain a hash map of at most 8 entries? The model reads a small map as an
   array map (insertion order = iteration order, as for literals, assoc, into and every map
   the Value boundary passes); a small hash map (from `hash-map`, or `dissoc` on a large map)
   is outside its domain, so faithfulness checks skip such inputs."
  [x]
  (cond (instance? clojure.lang.PersistentHashMap x) (or (<= (count x) 8) (some outside-domain? (mapcat identity x)))
        (map? x) (some outside-domain? (mapcat identity x))
        (coll? x) (some outside-domain? x)
        :else false))

(defn model-verdict
  "Classify one call: the model's result (a runtime CljM.V, or nil for none) against the
   outcome of the Clojure call ({:v x} / {:ex t} / {:timeout true}). A StackOverflowError or
   OutOfMemoryError where the model answers is :resource: the model says what Clojure returns
   given enough stack and heap (a non-tail self-call takes a JVM frame per level; `recur` and
   `loop` take none), so running out of them is outside its claim, not a disagreement."
  [mv c]
  (cond (nil? mv) (if (contains? c :v) :no-claim :throws)
        (or (instance? StackOverflowError (:ex c)) (instance? OutOfMemoryError (:ex c))) :resource
        (and (contains? c :v) (clj-model/strict= (clj-model/cljv->edn mv) (:v c))) :agree
        :else :model-bug))

(defn- outcome-edn [c]
  (cond (contains? c :v) (:v c)
        (:timeout c) :timeout
        :else {:threw (.getName (class (:ex c))) :message (.getMessage ^Throwable (:ex c))}))

(defn- realize!
  "Realize a result (a lazy seq may throw when realized), refusing one over 100000 elements."
  [x]
  (let [budget (volatile! 100000)]
    (letfn [(walk [x]
              (when (neg? (vswap! budget dec)) (throw (ex-info "clj-check: result too large to compare" {})))
              (cond (map? x) (run! (fn [[k v]] (walk k) (walk v)) x)
                    (coll? x) (run! walk x)))]
      (walk x)
      x)))

(defn- faithfulness [model-fn arity clj-f inputs timeout-ms]
  (let [results (mapv (fn [args]
                        (let [mv (model-call model-fn arity args)
                              c (call-with-timeout #(realize! (apply clj-f args)) timeout-ms)]
                          {:verdict (model-verdict mv c) :args args
                           :model (if mv (clj-model/cljv->edn mv) :none) :clojure (outcome-edn c)}))
                      (remove outside-domain? inputs))]
    {:counts (merge {:agree 0 :throws 0 :no-claim 0 :model-bug 0 :resource 0} (frequencies (map :verdict results)))
     :model-bugs (vec (take 5 (filter #(= :model-bug (:verdict %)) results)))
     :no-claims (vec (take 3 (filter #(= :no-claim (:verdict %)) results)))}))

(defn run-model-row
  "Run one row of the model contract (ansatz.clj-model.contract): translate `(fn [params…] form)`
   into the model, then compare it with clojure.core on generated EDN."
  [{:keys [id params form]} & {:keys [seed n-random timeout-ms] :or {n-random 60 timeout-ms 2000}}]
  (clj-model/install-model!)
  (let [fn-form (list 'fn (mapv first params) form)
        kname (str (row-kernel-name id) ".clj")
        model-form (translate/model-defn kname fn-form (ns-name (the-scratch-ns)) nil)
        model-fn (binding [a/*verbose* false config/*clj-surface* false *ns* (the-scratch-ns)]
                   @(eval model-form))
        inputs (gen-edn-inputs (map second params) :seed (or seed (hash id)) :n-random n-random)]
    (assoc (faithfulness model-fn (meta model-form) (reading {:params params :form form}) inputs timeout-ms)
           :id id)))

(defn model-row-verdict
  "Does a model-row result pass? No model bug, at least one agreeing call, and no more
   no-claims than `:max-no-claim` (a fraction of the calls where clojure.core returned)."
  [row {:keys [counts] :as result}]
  (let [{:keys [agree no-claim model-bug]} counts
        returned (+ agree no-claim)
        frac (if (pos? returned) (/ no-claim (double returned)) 0.0)
        limit (:max-no-claim row 0.0)]
    {:ok? (and (zero? model-bug) (pos? agree) (<= frac limit))
     :why (str "counts " counts " no-claim fraction " (format "%.2f" frac) " (max " limit ")"
               (when (seq (:model-bugs result)) (str " model bugs " (pr-str (:model-bugs result))))
               (when (> frac limit) (str " no-claims " (pr-str (:no-claims result)))))}))

(defn- domain-kind
  "The EDN generator kind of a boundary type (:any for one it does not describe)."
  [t]
  (if (seq? t)
    (case (first t)
      List [:vec (domain-kind (second t))]
      Prod [:pair (domain-kind (nth t 1)) (domain-kind (nth t 2))]
      Option [:opt (domain-kind (second t))]
      :any)
    (get '{Nat :nat Int :int Bool :bool String :string Value :value Float :double} t :any)))

(defn check-model!
  "Check an `a/foreign ^:model` function: faithfulness of its model `f.clj` against its Clojure
   source (random EDN of any kind, plus inputs from the declared types), and conformance on
   inputs from the declared types: dec_R of the model's result must be `some`.

   Returns {:status :conforming | :nonconforming | :model-bug, :faithful {counts …},
   :conformance {:conforming n :nonconforming n}, :witnesses [{:args :model :clojure} …]}, the
   witnesses being the domain inputs where conformance fails, with what clojure.core did there.
   Options: :runs (random tuples, default 60), :seed, :timeout-ms (default 2000)."
  [f & {:keys [runs seed timeout-ms] :or {runs 60 seed 42 timeout-ms 2000}}]
  (let [{:keys [impl model-fn pairs ret-codec arity]} ((requiring-resolve 'ansatz.clj-model.boundary/info) f)
        dec-fn (clj-model/model-fn (:dec ret-codec))
        kinds (mapv (fn [[_ t]] (domain-kind t)) pairs)
        domain (gen-edn-inputs kinds :seed seed :n-random runs)
        anything (gen-edn-inputs (repeat (count pairs) :any) :seed (inc seed) :n-random runs :max-edges 64)
        faith (faithfulness model-fn arity impl (concat domain anything) timeout-ms)
        conf (mapv (fn [args]
                     (let [mv (model-call model-fn arity args)]
                       (if (and mv (clj-model/opt-value (dec-fn mv)))
                         {:ok true}
                         {:args args :model (if mv (clj-model/cljv->edn mv) :none)
                          :clojure (outcome-edn (call-with-timeout #(apply impl args) timeout-ms))})))
                   domain)
        bad (remove :ok conf)]
    {:status (cond (pos? (get-in faith [:counts :model-bug])) :model-bug
                   (seq bad) :nonconforming
                   :else :conforming)
     :faithful (:counts faith)
     :model-bugs (:model-bugs faith)
     :conformance {:conforming (count (filter :ok conf)) :nonconforming (count bad)}
     :witnesses (vec (take 5 bad))}))
