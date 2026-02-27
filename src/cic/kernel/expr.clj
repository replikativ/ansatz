;; Copyright (c) 2026 Simmis GmbH. All rights reserved.
;; CIC kernel for Clojure — Expression (term) representation.
;; Thin adapter over Java Expr class for ~64% memory reduction.

(ns cic.kernel.expr
  "Core expression type for the Calculus of Inductive Constructions.
   Uses compact Java Expr class with packed long metadata.

   Binder info: :default, :implicit, :strict-implicit, :inst-implicit

   Terms use de Bruijn indices for bound variables (bvar).
   Free variables (fvar) are used during type checking only.
   Metavariables (mvar) are not supported in the kernel.

   Each expression carries cached metadata (packed into Expr.data long):
   - bvar-range    — upper bound on loose de Bruijn indices
   - has-fvar      — does the expression contain any fvar?
   - has-lvl-param — does the expression contain any level parameter?
   These enable O(1) short-circuiting in instantiate1, lift, abstract1, etc."
  (:require [cic.kernel.level :as lvl]
            [cic.kernel.name :as name]
            [clojure.string :as str])
  (:import [cic.kernel Expr Level]))

;; ============================================================
;; Tag dispatch — keyword lookup for backward compatibility with case
;; ============================================================

(def ^:private tag-kws
  [:bvar :sort :const :app :lam :forall :let :lit-nat :lit-str :mdata :proj :fvar])

(defn tag [^Expr e] (nth tag-kws (.tag e)))

;; ============================================================
;; Expression constructors
;; ============================================================

(defn bvar
  "Bound variable (de Bruijn index)."
  [idx]
  (Expr/bvar (long idx)))

(defn sort'
  "Sort (universe). Prop = (sort zero), Type u = (sort (succ u))."
  [level]
  (Expr/sort level (lvl/has-param? level)))

(defn const'
  "Reference to a global constant with universe level arguments."
  [name levels]
  (Expr/mkConst name levels (boolean (some lvl/has-param? levels))))

(defn app
  "Function application (curried, left-associative)."
  [^Expr f ^Expr a]
  (Expr/app f a))

(defn lam
  "Lambda abstraction. binder-info is :default, :implicit, :strict-implicit, :inst-implicit."
  [name ^Expr binder-type ^Expr body binder-info]
  (Expr/lam name binder-type body binder-info))

(defn forall'
  "Pi type / dependent function type."
  [name ^Expr binder-type ^Expr body binder-info]
  (Expr/forall name binder-type body binder-info))

(defn let'
  "Let binding with type annotation."
  [name ^Expr type ^Expr value ^Expr body]
  (Expr/mkLet name type value body))

(defn lit-nat
  "Natural number literal."
  [n]
  (Expr/litNat n))

(defn lit-str
  "String literal."
  [s]
  (Expr/litStr s))

(defn mdata
  "Metadata annotation (definitionally transparent)."
  [data ^Expr expr]
  (Expr/mdata data expr))

(defn proj
  "Structure projection."
  [type-name idx ^Expr struct]
  (Expr/proj type-name (long idx) struct))

(defn fvar
  "Free variable with unique id."
  [id]
  (Expr/fvar (long id)))

;; ============================================================
;; Metadata — inline bit extraction from packed data long
;; ============================================================

(defn bvar-range
  "Get the loose bvar range of an expression.
   If bvar-range is 0, the expression has no loose bvars."
  ^long [^Expr e]
  (.bvarRange e))

(defn has-fvar-flag
  "Does this expression contain any fvar?"
  [^Expr e]
  (.hasFVar e))

(defn has-level-param-flag
  "Does this expression contain any level parameter?"
  [^Expr e]
  (.hasLevelParam e))

;; ============================================================
;; Predicates
;; ============================================================

(defn bvar? [^Expr e] (= Expr/BVAR (.tag e)))
(defn sort? [^Expr e] (= Expr/SORT (.tag e)))
(defn const? [^Expr e] (= Expr/CONST (.tag e)))
(defn app? [^Expr e] (= Expr/APP (.tag e)))
(defn lam? [^Expr e] (= Expr/LAM (.tag e)))
(defn forall? [^Expr e] (= Expr/FORALL (.tag e)))
(defn let? [^Expr e] (= Expr/LET (.tag e)))
(defn lit-nat? [^Expr e] (= Expr/LIT_NAT (.tag e)))
(defn lit-str? [^Expr e] (= Expr/LIT_STR (.tag e)))
(defn mdata? [^Expr e] (= Expr/MDATA (.tag e)))
(defn proj? [^Expr e] (= Expr/PROJ (.tag e)))
(defn fvar? [^Expr e] (= Expr/FVAR (.tag e)))

;; ============================================================
;; Field accessors — direct field access via type hints
;; ============================================================

;; bvar
(defn bvar-idx ^long [^Expr e] (.longVal e))

;; sort
(defn sort-level [^Expr e] (.o0 e))

;; const
(defn const-name [^Expr e] (.o0 e))
(defn const-levels [^Expr e] (.o1 e))

;; app
(defn app-fn ^Expr [^Expr e] (cast Expr (.o0 e)))
(defn app-arg ^Expr [^Expr e] (cast Expr (.o1 e)))

;; lam — o0=name, o1=type, o2=body, o3=binderInfo
(defn lam-name [^Expr e] (.o0 e))
(defn lam-type ^Expr [^Expr e] (cast Expr (.o1 e)))
(defn lam-body ^Expr [^Expr e] (cast Expr (.o2 e)))
(defn lam-info [^Expr e] (.o3 e))

;; forall — o0=name, o1=type, o2=body, o3=binderInfo
(defn forall-name [^Expr e] (.o0 e))
(defn forall-type ^Expr [^Expr e] (cast Expr (.o1 e)))
(defn forall-body ^Expr [^Expr e] (cast Expr (.o2 e)))
(defn forall-info [^Expr e] (.o3 e))

;; let — o0=name, o1=type, o2=value, o3=body
(defn let-name [^Expr e] (.o0 e))
(defn let-type ^Expr [^Expr e] (cast Expr (.o1 e)))
(defn let-value ^Expr [^Expr e] (cast Expr (.o2 e)))
(defn let-body ^Expr [^Expr e] (cast Expr (.o3 e)))

;; lit-nat
(defn lit-nat-val [^Expr e] (.o0 e))

;; lit-str
(defn lit-str-val [^Expr e] (.o0 e))

;; mdata — o0=data, o1=expr
(defn mdata-data [^Expr e] (.o0 e))
(defn mdata-expr ^Expr [^Expr e] (cast Expr (.o1 e)))

;; proj — o0=typeName, o1=struct, longVal=idx
(defn proj-type-name [^Expr e] (.o0 e))
(defn proj-idx ^long [^Expr e] (.longVal e))
(defn proj-struct ^Expr [^Expr e] (cast Expr (.o1 e)))

;; fvar
(defn fvar-id ^long [^Expr e] (.longVal e))

;; ============================================================
;; Convenience constructors
;; ============================================================

(defn app*
  "Left-associative multi-argument application."
  [f & args]
  (reduce app f args))

(defn arrow
  "Non-dependent function type: A → B."
  [a b]
  (forall' nil a b :default))

(defn lam-default
  "Lambda with default binder info."
  [name binder-type body]
  (lam name binder-type body :default))

(defn forall-default
  "Forall with default binder info."
  [name binder-type body]
  (forall' name binder-type body :default))

;; ============================================================
;; de Bruijn operations — with metadata-based short-circuiting
;; ============================================================

(defn has-loose-bvars?
  "Does e contain any bvar with index >= depth?"
  ([e] (pos? (bvar-range e)))
  ([e depth]
   (> (bvar-range e) depth)))

(defn- has-fvar?
  "Check if expression contains any fvar (used to short-circuit abstract1)."
  [e]
  (has-fvar-flag e))

(defn lift
  "Lift (shift) free de Bruijn indices in e by d, starting from cutoff c.
   Handles deeply nested apps iteratively."
  [e d c]
  (letfn [(go [e c]
            (if (<= (bvar-range e) c)
              e
              (case (tag e)
                :bvar (if (>= (bvar-idx e) c)
                        (bvar (+ (bvar-idx e) d))
                        e)
                :sort e
                :const e
                :app (let [^java.util.ArrayList args (java.util.ArrayList.)]
                       (loop [cur e]
                         (if (and (app? cur) (> (bvar-range cur) c))
                           (do (.add args (app-arg cur))
                               (recur (app-fn cur)))
                           (let [head' (go cur c)
                                 n (.size args)]
                             (loop [i (dec n) result head']
                               (if (neg? i)
                                 result
                                 (recur (dec i) (app result (go (.get args i) c)))))))))
                :lam (lam (lam-name e) (go (lam-type e) c) (go (lam-body e) (inc c)) (lam-info e))
                :forall (forall' (forall-name e) (go (forall-type e) c) (go (forall-body e) (inc c)) (forall-info e))
                :let (let' (let-name e) (go (let-type e) c) (go (let-value e) c) (go (let-body e) (inc c)))
                :lit-nat e
                :lit-str e
                :mdata (mdata (mdata-data e) (go (mdata-expr e) c))
                :proj (proj (proj-type-name e) (proj-idx e) (go (proj-struct e) c))
                :fvar e)))]
    (go e c)))

(defn instantiate1
  "Replace (bvar 0) with val in e, shifting remaining bvars down.
   This is the fundamental substitution for opening binders.
   Handles deeply nested apps iteratively."
  [e val]
  (letfn [(go [e depth]
            (if (<= (bvar-range e) depth)
              e
              (case (tag e)
                :bvar (let [idx (bvar-idx e)]
                        (cond
                          (= idx depth) (lift val depth 0)
                          (> idx depth) (bvar (dec idx))
                          :else e))
                :sort e
                :const e
                :app (let [^java.util.ArrayList args (java.util.ArrayList.)]
                       (loop [cur e]
                         (if (and (app? cur) (> (bvar-range cur) depth))
                           (do (.add args (app-arg cur))
                               (recur (app-fn cur)))
                           (let [head' (go cur depth)
                                 n (.size args)]
                             (loop [i (dec n) result head']
                               (if (neg? i)
                                 result
                                 (recur (dec i) (app result (go (.get args i) depth)))))))))
                :lam (lam (lam-name e) (go (lam-type e) depth) (go (lam-body e) (inc depth)) (lam-info e))
                :forall (forall' (forall-name e) (go (forall-type e) depth) (go (forall-body e) (inc depth)) (forall-info e))
                :let (let' (let-name e) (go (let-type e) depth) (go (let-value e) depth) (go (let-body e) (inc depth)))
                :lit-nat e
                :lit-str e
                :mdata (mdata (mdata-data e) (go (mdata-expr e) depth))
                :proj (proj (proj-type-name e) (proj-idx e) (go (proj-struct e) depth))
                :fvar e)))]
    (go e 0)))

(defn instantiate
  "Replace (bvar 0)..(bvar n-1) with vals[0]..vals[n-1]."
  [e vals]
  (reduce (fn [body v] (instantiate1 body v)) e (reverse vals)))

(defn abstract1
  "Replace free occurrences of fv (an fvar id) with (bvar depth) in e.
   Used to close binders after type checking.
   Handles deeply nested apps iteratively."
  [e fv]
  (if-not (has-fvar-flag e)
    e
    (letfn [(go [e depth]
              (if-not (has-fvar-flag e)
                e
                (case (tag e)
                  :bvar e
                  :sort e
                  :const e
                  :app (let [^java.util.ArrayList args (java.util.ArrayList.)]
                         (loop [cur e]
                           (if (and (app? cur) (has-fvar-flag cur))
                             (do (.add args (app-arg cur))
                                 (recur (app-fn cur)))
                             (let [head' (go cur depth)
                                   n (.size args)]
                               (loop [i (dec n) result head']
                                 (if (neg? i)
                                   result
                                   (recur (dec i) (app result (go (.get args i) depth)))))))))
                  :lam (lam (lam-name e) (go (lam-type e) depth) (go (lam-body e) (inc depth)) (lam-info e))
                  :forall (forall' (forall-name e) (go (forall-type e) depth) (go (forall-body e) (inc depth)) (forall-info e))
                  :let (let' (let-name e) (go (let-type e) depth) (go (let-value e) depth) (go (let-body e) (inc depth)))
                  :lit-nat e
                  :lit-str e
                  :mdata (mdata (mdata-data e) (go (mdata-expr e) depth))
                  :proj (proj (proj-type-name e) (proj-idx e) (go (proj-struct e) depth))
                  :fvar (if (= (fvar-id e) fv) (bvar depth) e))))]
      (go e 0))))

(defn instantiate-level-params
  "Replace universe level params in an expression using a substitution map.
   Uses identity-based memoization to handle DAG-structured expressions
   efficiently (avoids exponential blowup from shared sub-expressions).
   Handles deeply nested apps iteratively to avoid StackOverflow."
  [e subst]
  (if (or (empty? subst) (not (has-level-param-flag e)))
    e
    (let [^java.util.IdentityHashMap cache (java.util.IdentityHashMap.)]
      (letfn [(go [e]
                (if-not (has-level-param-flag e)
                  e
                  (or (.get cache e)
                      (let [r (case (tag e)
                                :bvar e
                                :sort (sort' (lvl/instantiate (sort-level e) subst))
                                :const (const' (const-name e) (mapv #(lvl/instantiate % subst) (const-levels e)))
                                ;; Handle app spine iteratively to avoid stack overflow
                                :app (let [;; Collect the app spine (list of args, innermost first)
                                           spine (loop [cur e acc (java.util.ArrayList.)]
                                                   (if (and (app? cur) (has-level-param-flag cur)
                                                            (not (.get cache cur)))
                                                     (do (.add acc (app-arg cur))
                                                         (recur (app-fn cur) acc))
                                                     [cur acc]))
                                           head-expr (first spine)
                                           ^java.util.ArrayList args-list (second spine)
                                           head' (go head-expr)
                                           n (.size args-list)]
                                       ;; Rebuild apps from head outward, processing args
                                       (loop [i (dec n) result head']
                                         (if (neg? i)
                                           result
                                           (let [orig-arg (.get args-list i)
                                                 arg' (go orig-arg)]
                                             (recur (dec i) (app result arg'))))))
                                :lam (lam (lam-name e) (go (lam-type e)) (go (lam-body e)) (lam-info e))
                                :forall (forall' (forall-name e) (go (forall-type e)) (go (forall-body e)) (forall-info e))
                                :let (let' (let-name e) (go (let-type e)) (go (let-value e)) (go (let-body e)))
                                :lit-nat e
                                :lit-str e
                                :mdata (mdata (mdata-data e) (go (mdata-expr e)))
                                :proj (proj (proj-type-name e) (proj-idx e) (go (proj-struct e)))
                                :fvar e)]
                        (.put cache e r)
                        r))))]
        (go e)))))

;; ============================================================
;; Utility: collect head + args from nested App
;; ============================================================

(defn get-app-fn
  "Get the head function of a nested application."
  [e]
  (if (app? e)
    (recur (app-fn e))
    e))

(defn get-app-args
  "Get all arguments of a nested application as a vector."
  [e]
  (loop [e e args (list)]
    (if (app? e)
      (recur (app-fn e) (cons (app-arg e) args))
      (vec args))))

(defn get-app-fn-args
  "Get [head-fn args-vec] from a nested application."
  [e]
  [(get-app-fn e) (get-app-args e)])

;; ============================================================
;; Display / pretty-print
;; ============================================================

(defn ->string
  "Display an expression as a human-readable string.
   Not intended for round-tripping, just for debugging."
  ([e] (->string e 0))
  ([e depth]
   (if (> depth 20)
     "..."
     (let [d (inc depth)]
       (case (tag e)
         :bvar (str "#" (bvar-idx e))
         :sort (str "(Sort " (lvl/->string (sort-level e)) ")")
         :const (let [n (name/->string (const-name e))
                      ls (const-levels e)]
                  (if (seq ls)
                    (str n ".{" (str/join ", " (map lvl/->string ls)) "}")
                    n))
         :app (let [[head args] (get-app-fn-args e)]
                (str "(" (->string head d) " " (str/join " " (map #(->string % d) args)) ")"))
         :lam (str "(fun : " (->string (lam-type e) d) " => " (->string (lam-body e) d) ")")
         :forall (str "(∀ : " (->string (forall-type e) d) ", " (->string (forall-body e) d) ")")
         :let (str "(let : " (->string (let-type e) d) " := " (->string (let-value e) d) " in " (->string (let-body e) d) ")")
         :lit-nat (str (lit-nat-val e))
         :lit-str (pr-str (lit-str-val e))
         :mdata (->string (mdata-expr e) d)
         :proj (str (name/->string (proj-type-name e)) "." (proj-idx e) "(" (->string (proj-struct e) d) ")")
         :fvar (str "?fv" (fvar-id e)))))))
