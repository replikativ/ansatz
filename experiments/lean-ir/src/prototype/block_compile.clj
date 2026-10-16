(ns prototype.block-compile
  "Compile constructor/closure IR blocks to JVM code over the mutable runtime ABI.
   Control-transfer boundaries remain explicit. No native heap or general Lean ABI."
  (:refer-clojure :exclude [run!])
  (:require [prototype.machine :as m]
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

(defn- compile-block [body]
  (let [machine (gensym "machine")
        registers (with-meta (gensym "registers") {:tag 'objects})
        pool (with-meta (gensym "pool") {:tag 'objects})
        constants (atom [])]
    (letfn [(constant [v]
              (let [i (count @constants)]
                (swap! constants conj v)
                `(aget ~pool ~i)))
            (operand [[op x]]
              (case op
                :var `(u/read-local ~registers ~x)
                :imm (constant x)
                (m/fail "Unsupported compiled operand" {:op op})))
            (arguments [xs] (mapv operand xs))
            (target [[op x]]
              (case op :direct [:direct (constant x)] :closure [:closure (operand x)]
                    (m/fail "Unsupported compiled target" {:op op})))
            (expr [[op a b]]
              (case op
                :literal (constant a)
                :ctor `(u/constructor! ~machine ~(constant a) ~(arguments b))
                :closure `(u/closure! ~machine ~(constant a) ~(arguments b))
                :project `(u/project ~machine ~(operand a) ~b)
                :shared? `(u/shared? ~machine ~(operand a))
                :prim (do (when-not (= (if (= a :add) 2 1) (count b))
                            (m/fail "Scalar primitive arity" {:op a}))
                          (let [v `(m/small-integer! ~(operand (first b)))]
                            (case a
                              :add `(m/small-integer! (+ ~v (m/small-integer! ~(operand (second b)))))
                              :inc `(m/small-integer! (inc ~v))
                              :dec `(m/small-integer! (dec ~v))
                              :zero? `(if (zero? ~v) 1 0)
                              (m/fail "Unsupported compiled scalar primitive" {:op a}))))
                (m/fail "Unsupported compiled expression" {:op op})))
            (finish [n instruction expression]
              `(do (u/add-steps! ~machine ~n) (u/set-body! ~machine ~(constant instruction)) ~expression))
            (emit [[op a b c d :as instruction] n]
              (let [n (inc n)]
                (case op
                  :let `(do (aset ~registers ~a ~(expr b)) ~(emit c n))
                  :inc `(do (u/retain! ~machine ~(operand a) ~b) ~(emit c n))
                  :dec `(do (u/release! ~machine ~(operand a) ~b) ~(emit c n))
                  :set `(do (u/store! ~machine ~(operand a) ~b ~(operand c)) ~(emit d n))
                  :join `(do (u/join! ~machine ~a ~(constant b) ~(constant c)) ~(emit d n))
                  :call (finish n instruction `(u/call-values! ~machine ~(target b) ~(arguments c) ~a ~(constant d)))
                  :tail (finish n instruction `(u/call-values! ~machine ~(target a) ~(arguments b) nil nil))
                  :return (finish n instruction `(u/deliver! ~machine ~(operand a)))
                  :jump (finish n instruction `(u/jump-values! ~machine ~a ~(arguments b)))
                  :suspend (finish n instruction `(u/suspend! ~machine ~a ~(constant b)))
                  :case (let [tag (gensym "tag")
                              fallback (if-let [[_ branch] (first (filter #(= :default (first %)) b))]
                                         (emit branch n) `(m/fail "Missing case" {:tag ~tag}))]
                          `(let [~tag (u/tag-of ~machine ~(operand a))]
                             ~(reduce (fn [otherwise [key branch]]
                                        `(if (= ~tag ~(constant key)) ~(emit branch n) ~otherwise))
                                      fallback (reverse (remove #(= :default (first %)) b)))))
                  (m/fail "Unsupported compiled instruction" {:op op}))))]
      (let [limit (cost body)]
        (when (> limit 256) (m/fail "Compiled block instruction limit" {:cost limit}))
        (let [form `(fn [~machine ~pool]
                      (let [~registers (u/locals-array ~machine)] ~(emit body 0)))
              code (eval form)
              constants (object-array @constants)]
          {:max-cost limit :form form
           :execute! (fn [machine] (code machine constants))})))))

(defn compile-program
  ([functions] (compile-program functions nil))
  ([functions previous]
   (let [bodies (entries functions)
         options {:direct-linking (boolean (:direct-linking *compiler-options*))}
         reusable (if (and (identical? generation (:generation previous))
                           (= options (:compiler-options previous))) (:blocks previous) {})
         reused (count (filter #(contains? reusable %) bodies))]
     {:functions functions :generation generation :compiler-options options
      :compiled-blocks (- (count bodies) reused) :reused-blocks reused
      ;; Calls resolve against machine code at runtime; there is no callee inlining.
      :blocks (into {} (map (fn [body] [body (or (get reusable body) (compile-block body))]) bodies))})))

(defn- check-program! [program machine]
  (when-not (= (:functions program) (:functions machine))
    (m/fail "Compiled program does not match machine code" {})))

(defn step-block! [program machine]
  (check-program! program machine)
  (when-not (= :running (u/status machine)) (m/fail "Machine is not running" {}))
  (if-let [block (get (:blocks program) (u/body-of machine))]
    ((:execute! block) machine)
    ;; A fuel pause can leave control in the middle of a compiled block.
    (u/step! machine))
  machine)

(defn run!
  ([program machine] (run! program machine 10000000))
  ([program machine fuel]
   (check-program! program machine)
   (when-not (and (integer? fuel) (not (neg? fuel))) (m/fail "Invalid step budget" {:fuel fuel}))
   (loop [remaining fuel]
     (cond
       (not= :running (u/status machine)) machine
       (zero? remaining) (u/pause! machine)
       :else
       (if-let [block (get (:blocks program) (u/body-of machine))]
         (if (>= remaining (:max-cost block))
           (let [before (u/steps machine)]
             ((:execute! block) machine)
             (recur (- remaining (- (u/steps machine) before))))
           (u/run! machine remaining))
         (do (u/step! machine) (recur (dec remaining))))))))
