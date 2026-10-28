(ns bulk-sparse-compiler
  "Research-only compiler variant. Load bulk-sparse-joins.clj first.
   Isolated compiler generation; no sparse Machine may escape its runtime scope."
  (:require [clojure.java.io :as io]
            [clojure.walk :as walk]
            [prototype.mutable :as u]
            [prototype.block-compile :as b]))

(defn materialize-form [machine registers constant spend! env joins expression]
  ;; Retain the existing conservative emitter budget and capture ordering.
  (spend! (+ 16 (* 12 (count env))
             (reduce + 0 (map (fn [[_ join]] (+ 24 (* 12 (count (:locals join))))) joins))))
  `(do
     ~@(for [[id {:keys [params body locals]}] joins
             :let [ids (vec (sort (keys locals)))]]
         `(bulk-sparse-joins/capture! ~machine ~id ~(constant params) ~(constant body)
                                    ~registers ~(constant ids) [~@(map locals ids)]))
     ~@(for [[id value] env] `(aset ~registers ~id ~value))
     ~expression))

(defn compiler []
  (let [definition
        (binding [*ns* (the-ns 'prototype.block-compile)]
        (with-open [reader (java.io.PushbackReader. (io/reader "src/prototype/block_compile.clj"))]
          (loop []
            (let [form (read {:eof ::eof} reader)]
              (when (= ::eof form) (throw (ex-info "Missing compiler definition" {})))
              (if (and (seq? form) (= 'defn- (first form)) (= 'emit-block (second form)))
                form (recur))))))
        replaced (atom 0)
        form (walk/postwalk
              (fn [form]
                (if (and (seq? form) (= 'materialize (first form))
                         (= '[env joins expression] (second form)))
                  (do (swap! replaced inc)
                      '(materialize [env joins expression]
                         (bulk-sparse-compiler/materialize-form machine registers constant spend! env joins expression)))
                  form))
              (cons 'fn (drop 2 definition)))]
    (assert (= 1 @replaced))
    (binding [*ns* (the-ns 'prototype.block-compile)] (eval form))))

(defn variant []
  (let [emit-var (ns-resolve 'prototype.block-compile 'emit-block)
        generation-var (ns-resolve 'prototype.block-compile 'generation)
        emit (compiler) generation (Object.)]
    (fn [thunk]
      ((ns-resolve 'bulk-sparse-joins 'run-with-runtime)
       #(with-redefs-fn {emit-var emit generation-var generation} thunk)))))

(defn benchmark [ordinary-context sizes]
  (let [with-variant (variant)
        context (with-variant runtime-feasibility/setup)
        ordinary (get-in ordinary-context [:workloads :jvm-private])
        sparse (get-in context [:workloads :jvm-private])]
    (doseq [_ (range 8)] (ordinary 100) (with-variant #(sparse 100)))
    {:scope "Research-only sparse join capture; separate compiler generation, same source. Each trial includes private build/fold and final freeze. Full World parity outside timing."
     :runs
     (vec (for [n sizes
                :let [expected ((get-in ordinary-context [:workloads :reference]) n)]
                trial (range 7)
                mode (if (even? trial) [:ordinary :sparse] [:sparse :ordinary])]
            (let [[actual metrics]
                  (prototype.unchanged-program-benchmark/measure
                   #(if (= :sparse mode) (with-variant (fn [] (sparse n))) (ordinary n)))]
              (assert (= expected actual))
              (assoc metrics :n n :trial trial :mode mode))))}))
