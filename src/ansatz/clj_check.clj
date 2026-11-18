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
     clj->runtime   Clojure value → the value the compiled function takes (Option is `[x]`/nil
     runtime->clj   when Ansatz runs alone; see `*option-rep*`) and back
     agree?         result equality: integers across Long/BigInt, NaN = NaN, sequences by element
     run-row        one row of the clojure.core contract table (ansatz.clj-contract)

   A call where clojure.core throws is outside the contract (Ansatz's total functions return
   something there); such calls are counted as :clj-throws, never as divergences."
  (:require [clojure.string :as str]
            [ansatz.core :as a]
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
  "How the compiled code represents `Option`: :tagged — `none` is nil and `some x` is `[x]`
   (Ansatz's own codegen, ansatz.codegen) — or :nil-punning — `some x` is `x` (wandler's
   runtime). The Clojure side always uses nil-punning."
  :tagged)

(defn clj->runtime
  "The value the compiled function expects for the Clojure value `v` of descriptor `d`."
  [d v]
  (case (first d)
    :option (cond (nil? v) nil
                  (= :tagged *option-rep*) [(clj->runtime (second d) v)]
                  :else (clj->runtime (second d) v))
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
                  :else (runtime->clj (second d) v))
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
