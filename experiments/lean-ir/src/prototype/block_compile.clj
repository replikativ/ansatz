(ns prototype.block-compile
  "Compile constructor/closure IR blocks to JVM code over the mutable runtime ABI.
   Control-transfer boundaries remain explicit. No native heap or general Lean ABI."
  (:refer-clojure :exclude [run!])
  (:require [prototype.machine :as m]
            [prototype.leaf-compile :as leaf]
            [prototype.mutable :as u]))

;; Reloading the compiler invalidates its in-memory block cache.
(def ^:private generation (Object.))

(defn- entries [functions]
  (let [found (atom #{})]
    (letfn [(walk [[op a b c d :as body] entry?]
              (when entry? (swap! found conj body))
              (case op
                :let (walk c false)
                :call (walk d true)
                :join (do (walk c true) (walk d false))
                :case (doseq [[_ branch] b] (walk branch false))
                (:inc :dec) (walk c false)
                :set (walk d false)
                :suspend (walk b true)
                (:tail :return :jump) nil
                (m/fail "Unsupported compiled instruction" {:op op})))]
      (doseq [f (vals functions)] (walk (:body f) true))
      @found)))

(defn- cost [[op _ b c d]]
  (inc (case op
         :let (cost c)
         :join (cost d)
         :case (reduce max 0 (map #(cost (second %)) b))
         (:inc :dec) (cost c)
         :set (cost d)
         0)))

(defn- compile-block [body functions lexical? leaf-calls? leaf-names]
  (let [machine (gensym "machine")
        registers (with-meta (gensym "registers") {:tag 'objects})
        pool (with-meta (gensym "pool") {:tag 'objects})
        constants (atom [])
        max-cost (atom 0)
        inlined-jumps (atom 0)
        leaf-sites (atom 0)]
    (letfn [(constant [v]
              (let [i (count @constants)]
                (swap! constants conj v)
                `(aget ~pool ~i)))
            (operand [[op x] env]
              (case op
                :var (get env x `(u/read-local ~registers ~x))
                :imm (constant x)
                (m/fail "Unsupported compiled operand" {:op op})))
            (arguments [xs env] (mapv #(operand % env) xs))
            (target [[op x] env]
              (case op :direct [:direct (constant x)] :closure [:closure (operand x env)]
                    (m/fail "Unsupported compiled target" {:op op})))
            (expr [[op a b] env]
              (case op
                :literal (constant a)
                :ctor `(u/constructor! ~machine ~(constant a) ~(arguments b env))
                :closure `(u/closure! ~machine ~(constant a) ~(arguments b env))
                :project `(u/project ~machine ~(operand a env) ~b)
                :shared? `(u/shared? ~machine ~(operand a env))
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
              (swap! max-cost max n)
              `(do (u/add-steps! ~machine ~n) (u/set-body! ~machine ~(constant instruction)) ~expression))
            (emit [[op a b c d :as instruction] n env joins active]
              (let [n (inc n)]
                (case op
                  :let (if lexical?
                         (let [v (gensym "value")]
                           `(let [~v ~(expr b env)] ~(emit c n (assoc env a v) joins active)))
                         `(do (aset ~registers ~a ~(expr b env)) ~(emit c n env joins active)))
                  :inc `(do (u/retain! ~machine ~(operand a env) ~b) ~(emit c n env joins active))
                  :dec `(do (u/release! ~machine ~(operand a env) ~b) ~(emit c n env joins active))
                  :set `(do (u/store! ~machine ~(operand a env) ~b ~(operand c env)) ~(emit d n env joins active))
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
                  :case (let [tag (gensym "tag")
                              fallback (if-let [[_ branch] (first (filter #(= :default (first %)) b))]
                                         (emit branch n env joins active) `(m/fail "Missing case" {:tag ~tag}))]
                          `(let [~tag (u/tag-of ~machine ~(operand a env))]
                             ~(reduce (fn [otherwise [key branch]]
                                        `(if (= ~tag ~(constant key)) ~(emit branch n env joins active) ~otherwise))
                                      fallback (reverse (remove #(= :default (first %)) b)))))
                  (m/fail "Unsupported compiled instruction" {:op op}))))]
      (let [limit (cost body)]
        (when (> limit 256) (m/fail "Compiled block instruction limit" {:cost limit}))
        (let [form `(fn [~machine ~pool]
                      (let [~registers (u/locals-array ~machine)] ~(emit body 0 {} {} #{})))
              code (eval form)
              constants (object-array @constants)]
          {:max-cost (+ @max-cost (* leaf/max-steps @leaf-sites))
           :form form :inlined-jumps @inlined-jumps :leaf-sites @leaf-sites
           :execute! (fn [machine] (code machine constants))})))))

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
         reused (count (filter #(contains? reusable %) bodies))
         plans (when leaf-calls (leaf/compile-plans functions (when reuse? (:leaf-plans previous))))
         leaf-names (set (keys plans))]
     {:functions functions :generation generation :compiler-options options
      :compiled-blocks (- (count bodies) reused) :reused-blocks reused
      :leaf-plans plans
      :register-layouts (when compact-registers (update-vals functions u/function-slots))
      ;; Reused callers resolve leaf plans through the current execution context.
      :blocks (into {} (map (fn [body] [body (or (get reusable body) (compile-block body functions lexical-joins leaf-calls leaf-names))]) bodies))})))

(defn- execution-context [program machine]
  (assoc machine :leaf-plans (:leaf-plans program) :register-layouts (:register-layouts program)))

(defn compiler-token [] generation)

(defn- tail-targets [[op a b c d]]
  (case op
    :tail (if (= :direct (first a)) #{(second a)} #{})
    :let (tail-targets c)
    :call (tail-targets d)
    :join (into (tail-targets c) (tail-targets d))
    :case (into #{} (mapcat #(tail-targets (second %)) b))
    (:inc :dec) (tail-targets c)
    :set (tail-targets d)
    :suspend (tail-targets b)
    (:jump :return) #{}
    (m/fail "Unsupported compiled instruction" {:op op})))

(defn runtime-block-key [functions body options]
  (when (or (:leaf-calls options) (:compact-registers options))
    (m/fail "Lazy prototype supports plain blocks and lexical regions" {:options options}))
  [generation (boolean (:lexical-joins options)) (boolean (:direct-linking options)) body
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
  (if-let [block (get (:blocks program) (u/body-of machine))]
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
       (if-let [block (get (:blocks program) (u/body-of machine))]
         (if (>= remaining (:max-cost block))
           (let [before (u/steps machine)]
             ((:execute! block) machine)
             (recur (- remaining (- (u/steps machine) before)) machine))
           (u/run! machine remaining))
         (do (u/step! machine) (recur (dec remaining) machine)))))))
