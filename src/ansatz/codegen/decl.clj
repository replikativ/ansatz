(ns ansatz.codegen.decl
  "Declaration parameter lists and application, following Lean's compiled Decl.params.
   Reference: lean4 55f80e10a3, Compiler/LCNF/Basic.lean Signature / Decl.getArity,
   Compiler/LCNF/ToLCNF.lean mkOverApplication /
   etaIfUnderApplied, Compiler/LCNF/Simp/Main.lean inlineApp?."
  (:require [clojure.walk :as walk]
            [ansatz.kernel.expr :as e]
            [ansatz.surface.ingest :refer [arity-registry]]))

(defn convention [params erased value?]
  {:params (vec params) :arity (count params) :erased erased :value? value?})

(defn plan!
  "Reserve the declaration's parameter list for recursive references. Emission
   replaces this reservation with the actual wrapper's convention."
  [cname type num-params]
  (let [erased (loop [t type i 0]
                 (if (and (< i num-params) (e/forall? t) (not= :default (e/forall-info t)))
                   (recur (e/forall-body t) (inc i)) i))
        cc (convention (vec (repeatedly (- num-params erased) #(gensym "p")))
                       erased (zero? num-params))]
    (let [kinds (loop [t type i 0 kinds []]
                  (if (= i erased) kinds
                      (recur (e/forall-body t) (inc i)
                             (conj kinds (if (e/sort? (e/forall-type t)) :type :implicit)))))]
      (swap! arity-registry assoc cname (assoc cc :erasure-kinds kinds)))
    cc))

(defn register! [cname emitted]
  (swap! arity-registry assoc cname (:convention emitted))
  (:fn emitted))

(defn emit-wrapper
  "The parameter vector used to emit the wrapper is also its recorded convention.
   A value has no invocation; an invoked nullary wrapper has a zero-argument method."
  [params body {:keys [erased value? local-name] :or {erased 0 value? false}}]
  (let [params (vec params)
        local-name (or local-name (gensym "decl"))
        cc (convention params erased value?)
        partials (for [k (range 1 (count params))]
                   (list (subvec params 0 k)
                         (reduce (fn [body p] (list 'fn [p] body))
                                 (apply list local-name params) (rseq (subvec params k)))))
        form (if value? body
                 (apply list 'fn local-name (concat partials [(list params body)])))]
    {:fn-form form :convention cc}))

(defn- peel-fns [form n]
  (loop [form form n n params []]
    (if (zero? n) [params form]
        (when (and (seq? form) (= 'fn (first form))
                   (vector? (second form)) (= 1 (count (second form))))
          (recur (nth form 2) (dec n) (conj params (first (second form))))))))

(defn- occurs? [p form]
  (boolean (some #{p} (tree-seq coll? seq form))))

(defn emit-classic!
  "Compile a curried term into the shared wrapper. Types and unused implicit-prefix
   binders erase. If a prefix binder is runtime-relevant, recompile self-calls with
   that retained parameter before recording and emitting the final convention."
  [cname compile-term]
  (let [{:keys [arity erased value? erasure-kinds]} (get @arity-registry cname)
        n (+ arity erased)
        raw (compile-term)
        [params body] (or (peel-fns raw n)
                          (let [ps (vec (repeatedly n #(gensym "p")))]
                            [ps (reduce (fn [f a] (list f a)) raw ps)]))
        erased' (count (take-while (fn [i] (or (= :type (nth erasure-kinds i nil))
                                               (not (occurs? (nth params i) body))))
                                   (range erased)))
        _ (when (not= erased erased')
            (swap! arity-registry assoc cname
                   (convention (subvec params erased') erased' value?)))
        [params body] (if (= erased erased') [params body]
                          (or (peel-fns (compile-term) n)
                              (throw (ex-info "Codegen error: cannot open declaration parameters"
                                              {:kind :codegen-error :name cname}))))
        ;; Lean erases types even if the kernel's fuel encoding threads them
        ;; through internal closures. Such uses receive the erased runtime value.
        body (walk/postwalk-replace (zipmap (take erased' params) (repeat nil)) body)
        emitted (emit-wrapper (subvec params erased') body {:erased erased' :value? value?})
        emitted (assoc emitted :fn (eval (:fn-form emitted)))]
    (register! cname emitted)))

(defn emit-foreign! [cname impl]
  (let [{:keys [params erased value?]} (get @arity-registry cname)
        impl-sym (gensym "impl")
        emitted (emit-wrapper params (if value? impl-sym (apply list impl-sym params))
                              {:erased erased :value? value?})
        factory (eval (list 'fn [impl-sym] (:fn-form emitted)))]
    (register! cname (assoc emitted :fn (factory impl)))))

(defn apply-args
  "ToLCNF.mkOverApplication / etaIfUnderApplied: drop erased arguments, call
   exactly Decl.params, apply extras to the result, or eta-expand missing params."
  [{:keys [arity erased value?]} f args]
  (let [args (vec (drop (min erased (count args)) args))]
    (if (>= (count args) arity)
      (reduce (fn [f a] (list f a))
              (if value? f (apply list f (take arity args))) (drop arity args))
      (let [fvar (gensym "f")
            supplied (mapv (fn [_] (gensym "a")) args)
            missing (vec (repeatedly (- arity (count args)) #(gensym "p")))]
        (list 'let (vec (concat [fvar f] (mapcat vector supplied args)))
              (reduce (fn [body p] (list 'fn [p] body))
                      (apply list fvar (concat supplied missing)) (rseq missing)))))))
