(ns prototype.numeric-compile
  "Small baseline compiler for numeric, tail-only guest functions.
   No heap, callbacks, joins, suspension or deoptimization; unsupported code rejects."
  (:require [prototype.machine :as m]))

(defn compile-program [functions]
  (let [targets (zipmap (keys functions) (range))
        slots (vec (sort (set (mapcat :params (vals functions)))))
        loop-regs (zipmap slots (repeatedly #(gensym "r")))
        pc (gensym "pc") entry (gensym "entry")
        initial (with-meta (gensym "initial") {:tag 'longs})]
    (letfn [(operand [[op x] env]
              (case op
                :var (or (get env x) (m/fail "Unbound compiled variable" {:variable x}))
                :imm (list 'clojure.core/long (m/small-integer! x))
                (m/fail "Unsupported compiled operand" {:op op})))
            (expr [[op a b] env]
              (case op
                :literal (list 'clojure.core/long (m/small-integer! a))
                :prim (do
                        (when-not (= 1 (count b)) (m/fail "Compiled primitive arity" {:op a}))
                        (let [v (operand (first b) env)]
                          (case a
                            :zero? `(if (zero? ~v) (long 1) (long 0))
                            (:inc :dec)
                            (let [result (gensym "checked")]
                              ;; Entry values and every result are bounded far inside
                              ;; long range, so this operation cannot wrap before its guard.
                              `(let [~result (~(if (= a :inc) 'clojure.core/unchecked-inc 'clojure.core/unchecked-dec) ~v)]
                                 (when-not (<= -9007199254740991 ~result 9007199254740991)
                                   (throw (ex-info "Prototype arithmetic requires an exact small integer" {})))
                                 ~result))
                            (m/fail "Unsupported compiled primitive" {:op a}))))
                (m/fail "Unsupported compiled expression" {:op op})))
            (body [[op a b c] env]
              (case op
                :let (let [local (gensym "local")]
                       `(let [~local ~(expr b env)] ~(body c (assoc env a local))))
                :return (operand a env)
                :case (let [v (gensym "case")]
                        `(let [~v ~(operand a env)]
                           ~(reduce (fn [fallback [tag branch]]
                                      (if (= :default tag) (body branch env)
                                        (do (m/small-integer! tag)
                                            `(if (= ~v (long ~tag)) ~(body branch env) ~fallback))))
                                    `(throw (ex-info "Missing case" {}))
                                    (reverse (sort-by #(= :default (first %)) b)))))
                :tail (let [[kind target] a
                            params (:params (get functions target))]
                        (when-not (and (= :direct kind) (contains? targets target)
                                       (= (count params) (count b)))
                          (m/fail "Unsupported compiled tail target/arity" {:target a}))
                        (let [args (zipmap params (map #(operand % env) b))]
                          `(recur (long ~(get targets target))
                                  ~@(map #(list 'clojure.core/long (get args % '(clojure.core/long 0))) slots))))
                (m/fail "Unsupported compiled instruction" {:op op})))]
      (let [form `(fn [~entry ~initial]
                    (loop [~pc (long ~entry)
                           ~@(mapcat (fn [i slot] [(get loop-regs slot) `(aget ~initial ~i)]) (range) slots)]
                      (case ~pc
                        ~@(mapcat (fn [[target {:keys [params] :as f}]]
                                    [(get targets target) (body (:body f) (select-keys loop-regs params))]) functions)
                        (throw (ex-info "Unresolved compiled function" {})))))
            code (eval form)]
        {:form form
         :invoke (fn [target args]
                   (let [f (get functions target)]
                     (when-not (and f (= (count args) (count (:params f))))
                       (m/fail "Compiled entry target/arity" {:target target}))
                     (let [args (zipmap (:params f) (map m/small-integer! args))
                           registers (long-array (map #(long (get args % 0)) slots))]
                       (code (get targets target) registers))))}))))
