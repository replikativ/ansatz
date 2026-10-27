(ns ansatz.meta.match.basic
  "Pattern, AltLHS, Alt, Problem and Example operations from
   Lean/Meta/Match/Basic.lean (55f80e10a3). Patterns use :tag for Lean's
   constructors and kebab-cased structure fields. LocalDecl uses the kernel
   context's existing :id, :type and :value fields."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.meta :as meta]))

(defn inaccessible [expr] {:tag :inaccessible :e expr})
(defn var-pattern [fvar-id] {:tag :var :fvar-id fvar-id})
(defn ctor [ctor-name us params fields]
  {:tag :ctor :ctor-name ctor-name :us (vec us) :params (vec params) :fields (vec fields)})
(defn val-pattern [expr] {:tag :val :e expr})
(defn array-lit [type xs] {:tag :array-lit :type type :xs (vec xs)})
(defn as-pattern [var-id p h-id] {:tag :as :var-id var-id :p p :h-id h-id})
(defn alt-lhs [ref fvar-decls patterns]
  {:ref ref :fvar-decls (vec fvar-decls) :patterns (vec patterns)})
(defn alt [ref idx rhs fvar-decls patterns]
  (assoc (alt-lhs ref fvar-decls patterns) :idx idx :rhs rhs :cnstrs [] :not-alt-idxs []))
(defn problem [mvar-id vars alts examples]
  {:mvar-id mvar-id :vars (vec vars) :alts (vec alts) :examples (vec examples)})

(defn- map-expr-fvars
  "Lean FVarSubst.apply uses a simultaneous replacement, without visiting replacement terms."
  [f expr]
  (if-not (e/has-fvar-flag expr)
    expr
    (let [go #(map-expr-fvars f %)]
      (case (e/tag expr)
        :fvar (f (e/fvar-id expr))
        :app (e/app (go (e/app-fn expr)) (go (e/app-arg expr)))
        :lam (e/lam (e/lam-name expr) (go (e/lam-type expr)) (go (e/lam-body expr)) (e/lam-info expr))
        :forall (e/forall' (e/forall-name expr) (go (e/forall-type expr))
                            (go (e/forall-body expr)) (e/forall-info expr))
        :let (e/let' (e/let-name expr) (go (e/let-type expr))
                      (go (e/let-value expr)) (go (e/let-body expr)))
        :mdata (e/mdata (e/mdata-data expr) (go (e/mdata-expr expr)))
        :proj (e/proj (e/proj-type-name expr) (e/proj-idx expr) (go (e/proj-struct expr)))
        expr))))

(defn- subst-expr [s expr] (map-expr-fvars #(get s % (e/fvar %)) expr))
(defn- map-local-decl [f d]
  (cond-> d (:type d) (update :type f) (:value d) (update :value f)))

(defn pattern-apply-fvar-subst [s p]
  (let [subst #(subst-expr s %)
        go #(pattern-apply-fvar-subst s %)]
    (case (:tag p)
      (:inaccessible :val) (update p :e subst)
      :ctor (-> p (update :params #(mapv subst %)) (update :fields #(mapv go %)))
      :array-lit (-> p (update :type subst) (update :xs #(mapv go %)))
      :var (if-let [expr (get s (:fvar-id p))] (inaccessible expr) p)
      :as (if (contains? s (:var-id p)) (go (:p p)) (update p :p go)))))

(defn pattern-replace-fvar-id [fvar-id value p]
  (pattern-apply-fvar-subst {fvar-id value} p))

(defn pattern-has-expr-mvar [p]
  (boolean
   (case (:tag p)
     (:inaccessible :val) (seq (meta/collect-expr-mvars (:e p)))
     :ctor (or (some #(seq (meta/collect-expr-mvars %)) (:params p))
               (some pattern-has-expr-mvar (:fields p)))
     :array-lit (or (seq (meta/collect-expr-mvars (:type p)))
                    (some pattern-has-expr-mvar (:xs p)))
     :as (pattern-has-expr-mvar (:p p))
     :var false)))

(defn- expr-fvars [expr]
  (let [ids (volatile! #{})]
    (map-expr-fvars (fn [id] (vswap! ids conj id) (e/fvar id)) expr)
    @ids))

(defn pattern-collect-fvars [p]
  (case (:tag p)
    (:inaccessible :val) (expr-fvars (:e p))
    :ctor (into (reduce into #{} (map expr-fvars (:params p)))
                (mapcat pattern-collect-fvars (:fields p)))
    :array-lit (into (expr-fvars (:type p)) (mapcat pattern-collect-fvars (:xs p)))
    :as (conj (pattern-collect-fvars (:p p)) (:var-id p) (:h-id p))
    :var #{(:fvar-id p)}))

(defn alt-lhs-collect-fvars [lhs]
  (into (reduce (fn [ids d]
                  (into (into ids (expr-fvars (:type d)))
                        (when (:value d) (expr-fvars (:value d)))))
                #{} (:fvar-decls lhs))
        (mapcat pattern-collect-fvars (:patterns lhs))))

(defn instantiate-pattern-mvars [mctx p]
  (let [inst #(meta/instantiate-expr-mvars mctx %)
        go #(instantiate-pattern-mvars mctx %)]
    (case (:tag p)
      (:inaccessible :val) (update p :e inst)
      :ctor (-> p (update :params #(mapv inst %)) (update :fields #(mapv go %)))
      :array-lit (-> p (update :type inst) (update :xs #(mapv go %)))
      :as (update p :p go)
      :var p)))

(defn instantiate-alt-lhs-mvars [mctx lhs]
  (-> lhs
      (update :fvar-decls #(mapv (partial map-local-decl (partial meta/instantiate-expr-mvars mctx)) %))
      (update :patterns #(mapv (partial instantiate-pattern-mvars mctx) %))))

(defn alt-apply-fvar-subst [s alt]
  (let [subst #(subst-expr s %)]
    (-> alt
        (update :patterns #(mapv (partial pattern-apply-fvar-subst s) %))
        (update :fvar-decls #(mapv (partial map-local-decl subst) %))
        (update :rhs subst)
        (update :cnstrs #(mapv (fn [[lhs rhs]] [(subst lhs) (subst rhs)]) %)))))

(defn alt-replace-fvar-id [fvar-id value alt]
  (-> (alt-apply-fvar-subst {fvar-id value} alt)
      (update :fvar-decls #(filterv (fn [d] (not= fvar-id (:id d))) %))))

(defn alt-is-local-decl [fvar-id alt]
  (boolean (some #(= fvar-id (:id %)) (:fvar-decls alt))))

(defn example-replace-fvar-id [fvar-id ex p]
  (case (:tag p)
    :var (if (= fvar-id (:fvar-id p)) ex p)
    (:ctor :array-lit) (update p :xs #(mapv (partial example-replace-fvar-id fvar-id ex) %))
    p))

(defn example-apply-fvar-subst [s p]
  (case (:tag p)
    :var (let [expr (get s (:fvar-id p) (e/fvar (:fvar-id p)))]
           (if (e/fvar? expr) {:tag :var :fvar-id (e/fvar-id expr)} {:tag :underscore}))
    (:ctor :array-lit) (update p :xs #(mapv (partial example-apply-fvar-subst s) %))
    p))

(defn example-vars-to-underscore [p]
  (case (:tag p)
    :var {:tag :underscore}
    (:ctor :array-lit) (update p :xs #(mapv example-vars-to-underscore %))
    p))
