(ns prototype.leaf-compile
  "Bounded, pure scalar leaves for guarded call specialization. No heap or effects."
  (:require [prototype.machine :as m]))

(def max-steps 8)

(defn small-integer? [x]
  (and (integer? x) (<= -9007199254740991 x 9007199254740991)))

(defn compile-leaf [function]
  (let [args (gensym "args")
        params (:params function)
        names (mapv (fn [_] (gensym "param")) params)]
    (letfn [(operand [[op x] env]
              (case op :imm (when (small-integer? x) x) :var (get env x) nil))
            (expression [[op a b] env]
              (case op
                :literal (when (small-integer? a) a)
                :prim (let [xs (mapv #(operand % env) b)
                            arity (case a :add 2 (:inc :dec :zero?) 1 nil)]
                        (when (and arity (= arity (count xs)) (every? some? xs))
                          (let [x `(m/small-integer! ~(first xs))]
                            (case a
                              :add `(m/small-integer! (+ ~x (m/small-integer! ~(second xs))))
                              :inc `(m/small-integer! (inc ~x))
                              :dec `(m/small-integer! (dec ~x))
                              :zero? `(if (zero? ~x) 1 0)))))
                nil))
            (walk [[op a b c] env n]
              (when (<= n max-steps)
                (case op
                  :return (when-let [value (operand a env)] {:form value :steps n})
                  :let (when-let [value (expression b env)]
                         (let [name (gensym "value")]
                           (when-let [rest (walk c (assoc env a name) (inc n))]
                             (update rest :form (fn [body] `(let [~name ~value] ~body))))))
                  nil)))]
      (when-let [leaf (walk (:body function) (zipmap params names) 1)]
        (assoc leaf :definition function
               :invoke (eval `(fn [~args]
                                (let [~@(mapcat (fn [i name] [name `(nth ~args ~i)]) (range) names)]
                                  ~(:form leaf)))))))))

(defn compile-plans [functions previous]
  (into {} (keep (fn [[name function]]
                   (if-let [old (get previous name)]
                     (if (= function (:definition old)) [name old]
                         (when-let [leaf (compile-leaf function)] [name leaf]))
                     (when-let [leaf (compile-leaf function)] [name leaf]))) functions)))
