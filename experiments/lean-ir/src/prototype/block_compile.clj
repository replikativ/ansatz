(ns prototype.block-compile
  "Compile constructor/closure IR blocks to JVM code over the mutable runtime ABI.
   Control-transfer boundaries remain explicit. No native heap or general Lean ABI."
  (:refer-clojure :exclude [run!])
  (:require [prototype.machine :as m]
            [prototype.fingerprint :as fingerprint]
            [prototype.leaf-compile :as leaf]
            [prototype.mutable :as u])
  (:import [java.util IdentityHashMap]))

;; Reloading the compiler invalidates its in-memory block cache.
(def ^:private generation (Object.))

(def ^:private region-limit 128)
;; A path bound alone does not bound the JVM method: case arms duplicate lexical
;; state and every boundary materializes all pending join captures. Charge all
;; emitted paths, arguments and captures before constructing/evaluating the form.
(def ^:private emission-limit 4096)

(defn- entries [functions]
  (loop [pending (mapv #(vector (:body %) true 0) (vals functions)) found {}]
    (if (empty? pending) (vec (vals found))
      (let [[[op a b c d :as body] entry? distance] (peek pending)
            pending (pop pending)
            entry? (or entry? (>= distance region-limit))
            distance (if entry? 0 distance)
            found (if entry? (assoc found (fingerprint/key body) body) found)
            n (inc distance)
            children (case op
                       :let [[c false n]]
                       :call [[d true 0]]
                       :join [[c true 0] [d false n]]
                       :case (mapv #(vector (second %) false n) b)
                       (:inc :dec :set-tag) [[c false n]]
                       (:set :scalar-set) [[d false n]]
                       :del [[b false n]]
                       :suspend [[b true 0]]
                       :host [[d true 0]]
                       (:tail :return :jump :global :publish-global :unreachable :read-global :begin-init :publish-io-global :trap) []
                       (m/fail "Unsupported compiled instruction" {:op op}))]
        (recur (into pending children) found)))))

(defn- cost
  ([body] (cost body region-limit))
  ([[op _ b c d] remaining]
   (if (zero? remaining) (inc region-limit)
     (min (inc region-limit)
          (inc (case op
                 :del (cost b (dec remaining))
                 :let (cost c (dec remaining))
                 :join (cost d (dec remaining))
                 :case (reduce max 0 (map #(cost (second %) (dec remaining)) b))
                 (:inc :dec :set-tag) (cost c (dec remaining))
                 (:set :scalar-set) (cost d (dec remaining))
                 0))))))

(defn- realize-form! [form]
  ;; Syntax-quote splices can retain lazy capture/constant sequences. Realize
  ;; those before eval, so budget exhaustion cannot be wrapped by the compiler
  ;; after it has already started method emission. No recursive tree walking.
  (loop [todo [form]]
    (when (seq todo)
      (let [value (peek todo) todo (pop todo)]
        (recur (if (coll? value) (into todo value) todo)))))
  form)

(defn- emit-block [body functions lexical? leaf-calls? leaf-names path-limit]
  (let [machine (gensym "machine")
        registers (with-meta (gensym "registers") {:tag 'objects})
        pool (with-meta (gensym "pool") {:tag 'objects})
        constants (atom [])
        max-cost (atom 0)
        inlined-jumps (atom 0)
        leaf-sites (atom 0)
        emission-cost (volatile! 0)]
    (letfn [(spend! [units]
              (let [used (vswap! emission-cost + units)]
                (when (> used emission-limit)
                  (throw (ex-info "Compiled region emission budget" {::emission-budget true :units used})))))
            (constant [v]
              (spend! 4)
              (let [i (count @constants)]
                (swap! constants conj v)
                `(aget ~pool ~i)))
            (operand [[op x] env]
              (case op
                :var (get env x `(u/read-local ~registers ~x))
                :imm (constant x)
                (m/fail "Unsupported compiled operand" {:op op})))
            (arguments [xs env] (spend! (* 4 (count xs))) (mapv #(operand % env) xs))
            (target [[op x] env]
              (case op :direct [:direct (constant x)] :closure [:closure (operand x env)]
                    (m/fail "Unsupported compiled target" {:op op})))
            (expr [[op a b c] env]
              (spend! 12)
              (case op
                :literal (constant a)
                :ctor `(u/constructor! ~machine ~(constant a) ~(arguments b env))
                :closure `(u/closure! ~machine ~(constant a) ~(arguments b env))
                :project `(u/project ~machine ~(operand a env) ~b)
                :shared? `(u/shared? ~machine ~(operand a env))
                :scalar-ctor `(u/scalar-constructor! ~machine ~(constant a) ~(arguments b env) ~(constant c))
                :scalar-get `(u/scalar-get ~machine ~(operand a env) ~(constant b))
                :box `(u/box! ~machine ~(constant a) ~(operand b env))
                :unbox `(u/unbox ~machine ~(constant a) ~(operand b env))
                :runtime `(u/runtime-value! ~machine ~(constant a) ~(arguments b env))
                :prim (do (when-not (= (if (= a :add) 2 1) (count b))
                            (m/fail "Scalar primitive arity" {:op a}))
                          (let [v `(m/small-integer! ~(operand (first b) env))]
                            (case a
                              :add `(m/small-integer! (+ ~v (m/small-integer! ~(operand (second b) env))))
                              :inc `(m/small-integer! (inc ~v))
                              :dec `(m/small-integer! (dec ~v))
                              :zero? `(if (zero? ~v) 1 0)
                              (m/fail "Unsupported compiled scalar primitive" {:op a}))))
                (m/fail "Unsupported compiled expression" {:op op})))
            (materialize [env joins expression]
              (spend! (+ 16 (* 12 (count env))
                         (reduce + 0 (map (fn [[_ join]] (+ 24 (* 12 (count (:locals join))))) joins))))
              ;; The entry array stays unchanged until this boundary. Capture
              ;; every pending join BEFORE writing current locals into it: joins
              ;; can retain an older binding of the same register.
              `(do
                 ~@(for [[id {:keys [params body locals]}] joins
                         :let [saved (with-meta (gensym "capture") {:tag 'objects})]]
                     `(let [~saved (aclone ~registers)]
                        ~@(for [[id v] locals] `(aset ~saved ~id ~v))
                        (u/capture-join! ~machine ~id ~(constant params) ~(constant body) ~saved)))
                 ~@(for [[id v] env] `(aset ~registers ~id ~v))
                 ~expression))
            (finish [n instruction expression]
              (spend! 8)
              (swap! max-cost max n)
              `(do (u/add-steps! ~machine ~n) (u/set-body! ~machine ~(constant instruction)) ~expression))
            (emit [[op a b c d :as instruction] n env joins active]
              (spend! 12)
              (if (>= n path-limit)
                ;; End before this instruction. Materialize all lexical state;
                ;; the next dispatch compiles the remaining region on demand.
                (finish n instruction (materialize env joins `(u/set-body! ~machine ~(constant instruction))))
              (let [n (inc n)]
                (case op
                  :let (if lexical?
                         (let [v (gensym "value")]
                           `(let [~v ~(expr b env)] ~(emit c n (assoc env a v) joins active)))
                         `(do (aset ~registers ~a ~(expr b env)) ~(emit c n env joins active)))
                  :trap (finish n instruction `(m/fail "Reached unsupported guest declaration" {:declaration ~(constant a) :arguments ~(arguments b env)}))
                  :unreachable (finish n instruction `(m/fail "Reached Lean unreachable instruction" {}))
                  :del `(do (u/delete-shell! ~machine ~(operand a env)) ~(emit b n env joins active))
                  :set-tag `(do (u/set-constructor-tag! ~machine ~(operand a env) ~b) ~(emit c n env joins active))
                  :inc `(do (u/retain! ~machine ~(operand a env) ~b ~(boolean d)) ~(emit c n env joins active))
                  :dec `(do (u/release! ~machine ~(operand a env) ~b ~(boolean d)) ~(emit c n env joins active))
                  :set `(do (u/store! ~machine ~(operand a env) ~b ~(operand c env)) ~(emit d n env joins active))
                  :scalar-set `(do (u/scalar-store! ~machine ~(operand a env) ~(constant b) ~(operand c env)) ~(emit d n env joins active))
                  :join (if lexical?
                          (emit d n env (assoc joins a {:params b :body c :locals env}) active)
                          `(do (u/join! ~machine ~a ~(constant b) ~(constant c)) ~(emit d n env joins active)))
                  :call (if (and leaf-calls? (or (= :closure (first b)) (contains? leaf-names (second b)))
                                 (< @leaf-sites 4) (<= (+ n (cost d)) 256))
                          (let [call-target (gensym "target") args (gensym "args") result (gensym "result")]
                            (swap! leaf-sites inc)
                            `(let [~call-target ~(target b env) ~args ~(arguments c env)
                                   ~result (u/try-leaf! ~machine ~call-target ~args)]
                               (if (some? ~result)
                                 ~(emit d n (assoc env a result) joins active)
                                 ~(finish n instruction
                                          (materialize env joins `(u/call-values! ~machine ~call-target ~args ~a ~(constant d)))))))
                          (finish n instruction
                                  (materialize env joins `(u/call-values! ~machine ~(target b env) ~(arguments c env) ~a ~(constant d)))))
                  :tail (let [callee (when (= :direct (first a)) (get functions (second a)))
                              invoke `(u/call-values! ~machine ~(target a env) ~(arguments b env) nil nil)]
                          (finish n instruction
                                  (if (and lexical? callee (= (count (:params callee)) (count b)))
                                    invoke (materialize env joins invoke))))
                  :read-global (finish n instruction (materialize env joins `(u/deliver! ~machine (u/initialized-value ~machine ~(constant a)))))
                  :begin-init (finish n instruction (materialize env joins `(u/begin-init! ~machine ~(constant a) ~(constant b) ~(arguments c env) ~(constant d))))
                  :publish-io-global (finish n instruction (materialize env joins `(u/publish-io-global! ~machine ~(constant a) ~(constant b) ~(operand c env))))
                  :global (finish n instruction (materialize env joins `(u/global-enter! ~machine ~(constant a) ~(constant b))))
                  :publish-global (finish n instruction (materialize env joins `(u/publish-global! ~machine ~(constant a) ~(operand b env))))
                  :return (let [deliver `(u/deliver! ~machine ~(operand a env))]
                            (finish n instruction
                                    (if lexical?
                                      `(if (u/has-frames? ~machine) ~deliver ~(materialize env joins deliver))
                                      deliver)))
                  :jump (let [join (get joins a)]
                          (if (and lexical? join (= (count (:params join)) (count b))
                                   (not (contains? active a)) (<= (+ n (cost (:body join))) 256))
                            (let [args (mapv (fn [_] (gensym "arg")) b)
                                  jump-env (merge (:locals join) (zipmap (:params join) args))]
                              (swap! inlined-jumps inc)
                              `(let [~@(mapcat vector args (arguments b env))]
                                 ~(emit (:body join) n jump-env joins (conj active a))))
                            (finish n instruction (materialize env joins `(u/jump-values! ~machine ~a ~(arguments b env))))))
                  :suspend (finish n instruction (materialize env joins `(u/suspend! ~machine ~a ~(constant b))))
                  :host (finish n instruction (materialize env joins `(u/host! ~machine ~(constant a) ~(arguments b env) ~c ~(constant d))))
                  :case (let [_ (spend! (* 12 (count b)))
                              tag (gensym "tag")
                              fallback (if-let [[_ branch] (first (filter #(= :default (first %)) b))]
                                         (emit branch n env joins active) `(m/fail "Missing case" {:tag ~tag}))]
                          `(let [~tag (u/tag-of ~machine ~(operand a env))]
                             ~(reduce (fn [otherwise [key branch]]
                                        `(if (= ~tag ~(constant key)) ~(emit branch n env joins active) ~otherwise))
                                      fallback (reverse (remove #(= :default (first %)) b)))))
                  (m/fail "Unsupported compiled instruction" {:op op}))))) ]
      (let [limit (cost body path-limit)]
        (when (> limit 256) (m/fail "Compiled block instruction limit" {:cost limit}))
        (let [form (realize-form! `(fn [~machine ~pool]
                      (let [~registers (u/locals-array ~machine)] ~(emit body 0 {} {} #{}))))
              code (try (eval form)
                        (catch Throwable t
                          ;; Catch only a JVM method-size rejection here. Other
                          ;; syntax/type/compiler failures retain their evidence.
                          (if (some (fn [cause]
                                      (or (= "clojure.asm.MethodTooLargeException" (.getName (class cause)))
                                          (and (instance? IndexOutOfBoundsException cause)
                                               (= "Method code too large!" (.getMessage ^Throwable cause)))))
                                    (take-while some? (iterate ex-cause t)))
                            (throw (ex-info "Compiled JVM method size" {::method-size true} t))
                            (throw t))))
              constants (object-array @constants)]
          {:max-cost (+ @max-cost (* leaf/max-steps @leaf-sites))
           :emission-cost @emission-cost :region-limit path-limit
           :form form :inlined-jumps @inlined-jumps :leaf-sites @leaf-sites
           :execute! (fn [machine] (code machine constants))})))))

(defn- compile-block [body functions lexical? leaf-calls? leaf-names]
  (loop [path-limit region-limit attempts 1]
    (let [attempt (try {:block (emit-block body functions lexical? leaf-calls? leaf-names path-limit)}
                       (catch clojure.lang.ExceptionInfo e
                         (if (or (::emission-budget (ex-data e)) (::method-size (ex-data e)))
                           {:limit (if (::method-size (ex-data e)) :jvm-method-size :emission-budget)}
                           (throw e))))]
      (if-let [block (:block attempt)]
        (assoc block :compilation-attempts attempts)
        (if (> path-limit 1)
          (recur (max 1 (quot path-limit 2)) (inc attempts))
          ;; A root case may itself have too many alternatives even when every
          ;; arm is a boundary. Interpret EXACTLY this one instruction, including
          ;; its step charge, then demand-compile the selected continuation.
          {:max-cost 1 :form nil :inlined-jumps 0 :leaf-sites 0
           :region-limit 1 :compilation-attempts attempts :fallback (:limit attempt)
           :execute! (fn [machine] (u/step! machine))})))))

(defn compile-program
  ([functions] (compile-program functions nil))
  ([functions previous]
   (compile-program functions previous {}))
  ([functions previous {:keys [lexical-joins leaf-calls compact-registers]}]
   (when (and leaf-calls (not lexical-joins))
     (m/fail "Leaf calls require lexical regions" {}))
   (let [bodies (entries functions)
         options (cond-> {:direct-linking (boolean (:direct-linking *compiler-options*))
                          :lexical-joins (boolean lexical-joins)
                          :leaf-calls (boolean leaf-calls)
                          :compact-registers (boolean compact-registers)}
                   ;; Eliding a direct guest tail frame's materialization relies
                   ;; on callee existence and arity, never its implementation.
                   lexical-joins (assoc :tail-signatures (update-vals functions #(count (:params %)))))
         reuse? (and (identical? generation (:generation previous))
                     (= options (:compiler-options previous)))
         reusable (if reuse? (:blocks previous) {})
         reused (count (filter #(contains? reusable (fingerprint/key %)) bodies))
         plans (when leaf-calls (leaf/compile-plans functions (when reuse? (:leaf-plans previous))))
         leaf-names (set (keys plans))
         blocks (into {} (map (fn [body] [(fingerprint/key body) (or (get reusable (fingerprint/key body)) (compile-block body functions lexical-joins leaf-calls leaf-names))]) bodies))
         dispatch (IdentityHashMap.)]
     ;; Eager dispatch knows its entries. Fuel pauses inside a region must not
     ;; fingerprint every suffix merely to discover it is not an entry.
     (doseq [body bodies] (.put dispatch body (get blocks (fingerprint/key body))))
     ;; Reused executors retain old immutable continuation objects.
     (when reuse?
       (doseq [body (keys (:identity-blocks previous))]
         (when-let [block (get blocks (fingerprint/key body))]
           (.put dispatch body block))))
     {:functions functions :generation generation :compiler-options options
      :compiled-blocks (- (count bodies) reused) :reused-blocks reused
      :leaf-plans plans
      :register-layouts (when compact-registers (update-vals functions u/function-slots))
      ;; Reused callers resolve leaf plans through the current execution context.
      :blocks blocks :identity-blocks dispatch})))

(defn- execution-context [program machine]
  (assoc machine :leaf-plans (:leaf-plans program) :register-layouts (:register-layouts program)))

(defn compiler-token [] generation)

(defn- tail-targets [root]
  (loop [pending [root] found #{}]
    (if (empty? pending) found
      (let [[op a b c d] (peek pending) pending (pop pending)
            found (cond-> found
                    (and (= :tail op) (= :direct (first a))) (conj (second a))
                    (contains? #{:global :begin-init} op) (conj b))
            children (case op
                       :let [c] :call [d] :join [c d] :case (mapv second b)
                       (:inc :dec :set-tag) [c] (:set :scalar-set) [d]
                       (:del :suspend) [b] :host [d]
                       (:tail :global :begin-init :jump :return :publish-global :unreachable :read-global :publish-io-global :trap) []
                       (m/fail "Unsupported compiled instruction" {:op op}))]
        (recur (into pending children) found)))))

(defn runtime-block-key [functions body options]
  (when (or (:leaf-calls options) (:compact-registers options))
    (m/fail "Lazy prototype supports plain blocks and lexical regions" {:options options}))
  [generation (boolean (:lexical-joins options)) (boolean (:direct-linking options)) (fingerprint/key body)
   (when (:lexical-joins options)
     (into {} (map (fn [name] [name (when-let [f (get functions name)] (count (:params f)))])
                   (tail-targets body))))])

(defn compile-runtime-block [functions body options]
  (runtime-block-key functions body options)
  (binding [*compiler-options* (assoc *compiler-options* :direct-linking (boolean (:direct-linking options)))]
    (compile-block body functions (:lexical-joins options) false #{})))

(defn- check-program! [program machine]
  (when-not (= (:functions program) (:functions machine))
    (m/fail "Compiled program does not match machine code" {})))

(defn step-block! [program machine]
  (check-program! program machine)
  (when-not (= :running (u/status machine)) (m/fail "Machine is not running" {}))
  (if-let [block (.get ^IdentityHashMap (:identity-blocks program) (u/body-of machine))]
    ((:execute! block) (execution-context program machine))
    ;; A fuel pause can leave control in the middle of a compiled block.
    (u/step! (execution-context program machine)))
  machine)

(defn run!
  ([program machine] (run! program machine 10000000))
  ([program machine fuel]
   (check-program! program machine)
   (when-not (and (integer? fuel) (not (neg? fuel))) (m/fail "Invalid step budget" {:fuel fuel}))
   (loop [remaining fuel machine (execution-context program machine)]
     (cond
       (not= :running (u/status machine)) machine
       (zero? remaining) (u/pause! machine)
       :else
       (if-let [block (.get ^IdentityHashMap (:identity-blocks program) (u/body-of machine))]
         (if (>= remaining (:max-cost block))
           (let [before (u/steps machine)]
             ((:execute! block) machine)
             (recur (- remaining (- (u/steps machine) before)) machine))
           (u/run! machine remaining))
         (do (u/step! machine) (recur (dec remaining) machine)))))))
