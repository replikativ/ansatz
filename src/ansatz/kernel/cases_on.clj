;; Algorithm adapted from Lean4 src/library/constructions/cases_on.cpp at819816b2.
;; Copyright(c)2014 Microsoft Corporation. Original author: Leonardo de Moura.
;; Apache-2.0; see LICENSE. This implementation does not perform admission.
(ns ansatz.kernel.cases-on
  "Pure casesOn definition construction, following Lean819816 cases_on.cpp.
   Returns a declaration only; no admission or changes to Env declarations.
   Existing lookup memo caches may be populated."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as level])
  (:import [ansatz.kernel ConstantInfo Env Expr Name Level]
           [java.util IdentityHashMap HashMap]))

(defn- fail [kind data]
  (throw (ex-info "Cannot construct casesOn declaration" (assoc data :type kind))))

(defn- get-constant [^Env env ^Name name]
  (or (.lookup env name) (fail :cases-on/unknown-constant {:name name})))

(defn- tick! [remaining]
  (when (neg? (vswap! remaining dec))
    (fail :cases-on/work-limit {})))

(defn- charge! [remaining amount]
  (when (neg? (vswap! remaining - amount)) (fail :cases-on/work-limit {})))

(defn- bounded-name! [value remaining]
  ;; Run before lookup/equality/interning: Name.equals recursively visits its
  ;; prefix, and scalar strings may be large despite a shallow Name spine.
  (loop [node value depth 0]
    (tick! remaining)
    (when-not (instance? Name node) (fail :cases-on/malformed-name {}))
    (when (> depth 256) (fail :cases-on/depth-limit {:kind :name}))
    (case (.tag ^Name node)
      0 (when-not (nil? (.prefix ^Name node)) (fail :cases-on/malformed-name {}))
      1 (do (when-not (string? (.str ^Name node)) (fail :cases-on/malformed-name {}))
            (charge! remaining (count (.str ^Name node)))
            (recur (.prefix ^Name node) (inc depth)))
      2 (recur (.prefix ^Name node) (inc depth))
      (fail :cases-on/malformed-name {})))
  value)

(defn- bounded-level! [value remaining]
  (let [seen (IdentityHashMap.)]
    (loop [pending [[value 0]]]
      (when-let [[node depth] (peek pending)]
        (let [pending (pop pending)]
          (when (> depth 256) (fail :cases-on/depth-limit {:kind :level}))
          (when-not (instance? Level node) (fail :cases-on/malformed-level {}))
          (if (and (.containsKey seen node) (>= (long (.get seen node)) depth))
            (recur pending)
            (do (tick! remaining) (.put seen node depth)
                (case (.tag ^Level node)
                  0 (recur pending)
                  1 (recur (conj pending [(.o0 ^Level node) (inc depth)]))
                  (2 3) (recur (conj pending [(.o0 ^Level node) (inc depth)]
                                             [(.o1 ^Level node) (inc depth)]))
                  4 (do (bounded-name! (.o0 ^Level node) remaining) (recur pending))
                  5 (fail :cases-on/open-expression {:kind :level-metavariable})
                  (fail :cases-on/malformed-level {})))))))))

(defn- bounded-levels! [values remaining]
  ;; Actual decoded Expr tables also use the two exact JDK list carriers
  ;; constructed by ExprStore; input arrays/lists must stay stable during call.
  ;; Refuse arbitrary lazy/custom collections before invoking iteration methods.
  (when-not (or (instance? (class (object-array 0)) values)
                (identical? clojure.lang.PersistentVector (class values))
                (identical? (class (java.util.Collections/emptyList)) (class values))
                (identical? (class (java.util.Arrays/asList (object-array 0))) (class values)))
    (fail :cases-on/malformed-levels {}))
  (when (> (count values) @remaining) (fail :cases-on/work-limit {}))
  (doseq [value values] (tick! remaining) (bounded-level! value remaining)))

(defn- children-at [^Expr expression depth]
  (when-not (instance? Expr expression) (fail :cases-on/malformed-expression {}))
  (case (e/tag expression)
    :app [[(e/app-fn expression) depth] [(e/app-arg expression) depth]]
    :lam [[(e/lam-type expression) depth] [(e/lam-body expression) (inc depth)]]
    :forall [[(e/forall-type expression) depth] [(e/forall-body expression) (inc depth)]]
    :let [[(e/let-type expression) depth] [(e/let-value expression) depth]
          [(e/let-body expression) (inc depth)]]
    :mdata [[(e/mdata-expr expression) depth]]
    :proj [[(e/proj-struct expression) depth]]
    (:bvar :sort :const :fvar :mvar :lit-nat :lit-str) []
    (fail :cases-on/malformed-expression {})))

(defn- children [expression] (mapv first (children-at expression 0)))

(defn- preflight-expression! [expression remaining]
  (let [seen (IdentityHashMap.)]
    (loop [pending [[expression 0]]]
      (when-let [[node depth] (peek pending)]
        (let [pending (pop pending)
              prior (.get seen node)]
          (when (> depth 256) (fail :cases-on/depth-limit {:kind :expression}))
          (when-not (instance? Expr node) (fail :cases-on/malformed-expression {}))
          ;; Revisit shared nodes reached more deeply: a shallow occurrence
          ;; cannot certify the maximum path depth of a later occurrence.
          (if (and prior (>= (long prior) depth))
            (recur pending)
            (do
              (tick! remaining) (.put seen node depth)
              (case (e/tag node)
                :sort (bounded-level! (e/sort-level node) remaining)
                :const (do (bounded-name! (e/const-name node) remaining)
                           (bounded-levels! (e/const-levels node) remaining))
                :lam (bounded-name! (e/lam-name node) remaining)
                :forall (bounded-name! (e/forall-name node) remaining)
                :let (bounded-name! (e/let-name node) remaining)
                :proj (bounded-name! (e/proj-type-name node) remaining)
                nil)
              (recur (into pending (map (fn [child] [child (inc depth)]) (children node)))))))))))

(defn- closed! [expression remaining]
  (preflight-expression! expression remaining)
  ;; Inspect actual binders/leaves rather than treating cached flags as proof.
  ;; Memoize identity+depth, since a DAG may occur at several binding depths.
  (let [seen (IdentityHashMap.)]
    (loop [pending [[expression 0]]]
      (when-let [[^Expr node depth] (peek pending)]
        (let [pending (pop pending) depths (or (.get seen node) (java.util.HashSet.))]
          (if (.contains ^java.util.Set depths depth)
            (recur pending)
            (do
              (tick! remaining)
              (when-not (instance? Expr node) (fail :cases-on/malformed-expression {}))
              (.add ^java.util.Set depths depth) (.put seen node depths)
              (when (or (e/fvar? node) (e/mvar? node)
                         (and (e/bvar? node) (or (neg? (e/bvar-idx node)) (>= (e/bvar-idx node) depth)))
                         ;; Public Expr/Level objects must remain stable during
                         ;; this operation; reflective/concurrent mutation is not
                         ;; a supported source of checking evidence.
                         (.hasMVar node))
                (fail :cases-on/open-expression {}))
              (recur (into pending (children-at node depth)))))))))
  expression)

(defn- rebuild [expression children]
  (let [[a b c] children]
    (case (e/tag expression)
      :app (e/app a b)
      :lam (e/lam (e/lam-name expression) a b (e/lam-info expression))
      :forall (e/forall' (e/forall-name expression) a b (e/forall-info expression))
      :let (e/let' (e/let-name expression) a b c)
      :mdata (e/mdata (e/mdata-data expression) a)
      :proj (e/proj (e/proj-type-name expression) (e/proj-idx expression) a)
      expression)))

(defn- rewrite [root operation argument remaining]
  ;; Iterative postorder and identity+depth memoization bound work on shared
  ;; open DAGs. In this algorithm instantiation substitutes only a fresh FVAR,
  ;; which has no loose bvars and therefore needs no lifting under binders.
  (let [cache (IdentityHashMap.) active (Object.)
        table (fn [node]
                (or (.get cache node)
                    (let [values (HashMap.)] (.put cache node values) values)))]
    (loop [pending [[false root 0]]]
      (if (empty? pending) (.get ^HashMap (table root) 0)
        (let [[finish? ^Expr node depth] (peek pending) pending (pop pending)
              _ (when (> depth 256) (fail :cases-on/depth-limit {:kind :binder}))
              ^HashMap values (table node) hit (.get values depth)]
          (cond
            finish?
            (let [edges (children-at node depth)
                  results (mapv (fn [[child d]] (.get ^HashMap (table child) d)) edges)
                  _ (when-not (every? #(instance? Expr %) results)
                      (fail :cases-on/malformed-expression {}))
                  result (if (every? true? (map (fn [[child _] value] (identical? child value)) edges results))
                           node (rebuild node results))]
              (.put values depth result) (recur pending))
            (identical? active hit) (fail :cases-on/cyclic-expression {})
            hit (recur pending)
            :else
            (do
              (tick! remaining)
              (let [edges (children-at node depth)]
                (if (empty? edges)
                  (let [value (cond
                                (and (= operation :instantiate) (e/bvar? node))
                                (let [index (e/bvar-idx node)]
                                  (cond (= index depth) argument (> index depth) (e/bvar (dec index)) :else node))
                                (and (= operation :abstract) (e/fvar? node) (= argument (e/fvar-id node)))
                                (e/bvar depth)
                                :else node)]
                    (.put values depth value) (recur pending))
                  (do (.put values depth active)
                      (recur (into (conj pending [true node depth])
                                   (map (fn [[child d]] [false child d]) edges)))))))))))))

(defn- head [expression remaining]
  (loop [expression expression]
    (tick! remaining)
    (if (e/app? expression) (recur (e/app-fn expression)) expression)))

(defn- uses-unsafe? [^Env env expressions remaining]
  ;; Native use_unsafe visits constants, including those in types, without
  ;; unfolding them. Only the explicit-hints overload's OR predicate applies.
  (let [seen (IdentityHashMap.)]
    (loop [pending (vec expressions) visited 0]
      (if (empty? pending) false
        (let [expression (peek pending) pending (pop pending)]
          (if (.containsKey seen expression)
            (recur pending visited)
            (do
              (tick! remaining)
              (.put seen expression true)
              (if (and (e/const? expression)
                       (when-let [^ConstantInfo ci (.lookup env (e/const-name expression))]
                         (.isUnsafeDeclaration ci)))
                true
                (recur (into pending (children expression)) (inc visited))))))))))

(defn- unit-telescope [kind expression unit remaining]
  ;; C++ mk_pi_unit/mk_fun_unit intentionally use DEFAULT binderInfo rather
  ;; than copying it. Domains/de Bruijn references otherwise remain unchanged.
  (let [binders (loop [expression expression out []]
                  (tick! remaining)
                  (if (e/forall? expression)
                    (recur (e/forall-body expression)
                           (conj out [(e/forall-name expression) (e/forall-type expression)]))
                    out))
        constructor (if (= :pi kind) e/forall' e/lam)]
    (reduce (fn [body [name type]] (constructor name type body :default))
            unit (rseq binders))))

(defn- close-over [kind locals body remaining]
  (let [constructor (if (= :pi kind) e/forall' e/lam)]
    (reduce (fn [body local]
              (constructor (:name local) (:type local)
                           (rewrite body :abstract (:id local) remaining) (:info local)))
            body (rseq (vec locals)))))

(defn make-declaration
  "Construct n.casesOn from the actual inductive/recursor entries in ENV.
   The result is a complete abbreviation definition, not an admission receipt.
   Consumed Name/Level/Expr paths and generated binder indices are capped at256;
   aggregate validation/transform work and Name text consume max-work. Standard
   Object[]/PersistentVector or exact ExprStore JDK level-table carriers required.
   ENV/CI/Expr data must remain stable during this call. Finite work/local
   limits are host bounds, not Lean heartbeat/depth accounting or a sandbox
   against reflective mutation of JVM data."
  ([env name] (make-declaration env name {}))
  ([^Env env ^Name name {:keys [max-locals max-work]
                        :or {max-locals 100000 max-work 10000000} :as limits}]
   (when-not (and (map? limits) (every? #{:max-locals :max-work} (keys limits))
                  (instance? Env env) (instance? Name name)
                  (integer? max-locals) (<= 1 max-locals Integer/MAX_VALUE)
                  (integer? max-work) (<= 1 max-work Long/MAX_VALUE))
     (fail :cases-on/invalid-input {}))
   (let [remaining (volatile! max-work)
         _ (bounded-name! name remaining)
         _ (when (loop [n name depth 0]
                   (if (= Name/ANONYMOUS (.tag ^Name n)) (>= depth 256)
                     (recur (.prefix ^Name n) (inc depth))))
             (fail :cases-on/depth-limit {:kind :generated-name}))
         ^ConstantInfo ind (get-constant env name)
         _ (when-not (.isInduct ind) (fail :cases-on/not-inductive {:name name}))
         rec-name (Name/mkStr name "rec")
         ^ConstantInfo recursor (get-constant env rec-name)
         _ (when-not (.isRecursor recursor) (fail :cases-on/invalid-recursor {:name rec-name}))
         _ (closed! (.type recursor) remaining)
         np (.numParams recursor) nm (.numMotives recursor)
         nn (.numMinors recursor) ni (.numIndices recursor)
         _ (when-not (and (.all recursor) (.levelParams recursor) (.levelParams ind)
                          (<= (count (.all recursor)) @remaining)
                          (<= (count (.levelParams recursor)) @remaining)
                          (<= (count (.levelParams ind)) @remaining))
             (fail :cases-on/invalid-recursor {:field :name-arrays}))
         ind-names (mapv (fn [n] (tick! remaining)
                          (when-not (instance? Name n) (fail :cases-on/invalid-recursor {:field :all}))
                          (bounded-name! n remaining)) (.all recursor))
         _ (doseq [n (concat (seq (.levelParams recursor)) (seq (.levelParams ind)))]
             (tick! remaining) (bounded-name! n remaining))
         _ (when-not (and (every? #(and (integer? %) (<= 0 %)) [np nm nn ni])
                          (pos? nm) (<= (count ind-names) nm)
                          (= (count ind-names) (count (set ind-names)))
                          (= 1 (count (filter #(= name %) ind-names))))
             (fail :cases-on/invalid-recursor {:name rec-name :field :counts}))
         next-id (volatile! 0)
         local! (fn [name type info]
                  (let [id @next-id]
                    (tick! remaining)
                    (when (>= id max-locals) (fail :cases-on/local-limit {:limit max-locals}))
                    (vswap! next-id inc)
                    {:id id :expr (e/fvar id) :name name :type type :info info}))
         [rec-locals result-type]
         (loop [type (.type recursor) out []]
           (if (e/forall? type)
             (let [local (local! (e/forall-name type) (e/forall-type type) (e/forall-info type))]
               (recur (rewrite (e/forall-body type) :instantiate (:expr local) remaining) (conj out local)))
             [out type]))
         _ (when-not (= (count rec-locals) (+ np nm nn ni 1))
             (fail :cases-on/invalid-recursor {:name rec-name :field :telescope}))
         levels (mapv (fn [n] (tick! remaining)
                        (when-not (instance? Name n) (fail :cases-on/invalid-recursor {:field :level-parameters}))
                        (level/param n)) (.levelParams recursor))
         elim-level (if (= (count (.levelParams recursor)) (count (.levelParams ind)))
                      level/zero (first levels))
         _ (when-not elim-level (fail :cases-on/invalid-recursor {:field :elimination-level}))
         unit (e/const' (Name/fromString "PUnit") [elim-level])
         star (e/const' (Name/fromString "PUnit.unit") [elim-level])
         motives (subvec rec-locals np (+ np nm))
         motive-ids (set (map :id motives))
         main-index (.indexOf ^java.util.List ind-names name)
         main-id (:id (nth motives main-index))
         params (subvec rec-locals 0 np)
         main-motive (nth motives main-index)
         indices-major (subvec rec-locals (+ np nm nn))
         initial-args (into (mapv :expr params)
                            (map-indexed (fn [j local]
                                           (if (= j main-index) (:expr local)
                                             (unit-telescope :lambda (:type local) unit remaining))) motives))
         process-minor
         (fn [local main?]
           (let [[minor-params nonrecursive conclusion]
                 (loop [type (:type local) minor-params [] nonrecursive []]
                   (if (e/forall? type)
                     (let [domain (e/forall-type type)
                           original (local! (e/forall-name type) domain (e/forall-info type))
                           terminal (loop [it domain]
                                      (tick! remaining)
                                      (if (e/forall? it) (recur (e/forall-body it)) it))
                           fn-head (head terminal remaining)
                           recursive? (and (e/fvar? fn-head) (contains? motive-ids (e/fvar-id fn-head)))
                           selected (if (and recursive? (not= main-id (e/fvar-id fn-head)))
                                      (local! (e/forall-name type) (unit-telescope :pi domain unit remaining)
                                              (e/forall-info type))
                                      original)]
                       ;; Instantiation uses ORIGINAL even when the lambda's
                       ;; eventual binder is the substituted PUnit local.
                       (recur (rewrite (e/forall-body type) :instantiate (:expr original) remaining)
                              (conj minor-params selected)
                              (cond-> nonrecursive (and main? (not recursive?)) (conj original))))
                     [minor-params nonrecursive type]))]
             (if main?
               (let [branch (local! (:name local) (close-over :pi nonrecursive conclusion remaining) (:info local))
                     application (reduce e/app (:expr branch) (map :expr nonrecursive))]
                 {:parameter branch :argument (close-over :lambda minor-params application remaining)})
               {:argument (close-over :lambda minor-params star remaining)})))
         groups (mapv (fn [n]
                        (let [^ConstantInfo info (get-constant env n)]
                          (tick! remaining)
                          (when-not (and (.isInduct info) (.ctors info)) (fail :cases-on/invalid-recursor {:name n :field :all}))
                          [n (count (.ctors info))])) ind-names)
         described (reduce + 0 (map second groups))
         _ (when (> described nn) (fail :cases-on/invalid-recursor {:field :minor-count}))
         minor-types (into (vec (mapcat (fn [[n count]] (repeat count (= n name))) groups))
                           (repeat (- nn described) false))
         minors (mapv (fn [index main?] (process-minor (nth rec-locals (+ np nm index)) main?))
                      (range nn) minor-types)
         parameters (into (into (conj params main-motive) indices-major) (keep :parameter minors))
         args (into (into initial-args (map :argument minors)) (map :expr indices-major))
         type (closed! (close-over :pi parameters result-type remaining) remaining)
         value (closed! (close-over :lambda parameters (reduce e/app (e/const' rec-name levels) args) remaining) remaining)
         unsafe? (uses-unsafe? env [type value] remaining)
         out-name (Name/mkStr name "casesOn")]
     (ConstantInfo/mkDefWithHints out-name (.levelParams recursor) type value
                                  ConstantInfo/REDUCIBILITY_ABBREV (byte (if unsafe? 1 0))
                                  (object-array [out-name])))))
