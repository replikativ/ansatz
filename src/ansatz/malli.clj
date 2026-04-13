;; Bridge between Ansatz verified functions and Malli runtime schemas.
;;
;; Converts CIC type expressions to Malli schema forms and registers
;; verified functions for instrumentation. Malli is an optional dependency —
;; this namespace requires it at runtime via requiring-resolve.
;;
;; Usage:
;;   (require '[ansatz.core :as a])
;;   (require '[ansatz.malli :as am])
;;
;;   ;; Auto-register on every a/defn:
;;   (binding [a/*malli?* true]
;;     (a/defn double [n :- Nat] Nat (+ n n)))
;;
;;   ;; Or manually:
;;   (am/register-from-defn! 'user 'double)
;;
;;   ;; Inspect the generated schema:
;;   (am/fn-schema-for "double")
;;   ;; => [:=> [:cat [:and :int [:>= 0]]] [:and :int [:>= 0]]]
;;
;;   ;; Instrument all registered functions:
;;   (am/instrument!)

(ns ansatz.malli
  "Bridge between Ansatz verified functions and Malli runtime schemas."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel ConstantInfo]))

;; ============================================================
;; Malli lazy loading
;; ============================================================

(defn- resolve-malli! [sym]
  (or (requiring-resolve sym)
      (throw (ex-info (str "Cannot resolve " sym
                           ". Is metosin/malli on the classpath?") {}))))

;; ============================================================
;; CIC Type → Malli Schema
;; ============================================================

(defn- const-name-str
  "Extract the string name from a Const expr."
  [expr]
  (when (e/const? expr)
    (name/->string (e/const-name expr))))

(defn type-expr->malli
  "Convert a CIC type Expr to a Malli schema form (plain Clojure data).

   opts map (optional):
     :env    - Ansatz environment, needed for structure types
     :struct-registry - atom of structure registry (defaults to ansatz.core/structure-registry)

   Returns Malli schema forms like :int, :string, [:sequential :int], etc.
   Unknown types map to :any."
  ([expr] (type-expr->malli expr nil))
  ([expr opts]
   (cond
     ;; Literal nat → the value itself as an enum (rare in types)
     (e/lit-nat? expr) :int

     ;; Const — base types
     (e/const? expr)
     (let [n (name/->string (e/const-name expr))]
       (case n
         "Nat"    [:and :int [:>= 0]]
         "Int"    :int
         "Bool"   :boolean
         "String" :string
         "Float"  :double
         "UInt8"  [:and :int [:>= 0] [:<= 255]]
         "UInt16" [:and :int [:>= 0] [:<= 65535]]
         "UInt32" [:and :int [:>= 0]]
         "UInt64" [:and :int [:>= 0]]
         "Unit"   :nil
         ;; Real/Float types → number?
         "Real"   number?
         ;; Prop/Type are not runtime values
         "Prop"   :any
         "True"   :boolean
         "False"  :boolean
         ;; Check if it's a known structure
         (if-let [struct-reg (:struct-registry opts)]
           (if-let [info (get @struct-reg n)]
             ;; Structure → :map with field schemas (simplified — fields as :any
             ;; since we'd need to peel the ctor type for precise schemas)
             (into [:map] (mapv (fn [f] [(keyword f) :any]) (:fields info)))
             :any)
           :any)))

     ;; App — applied type constructors (List Nat), (Option Int), etc.
     (e/app? expr)
     (let [[head args] (e/get-app-fn-args expr)]
       (if (e/const? head)
         (let [n (name/->string (e/const-name head))]
           (case n
             "List"   [:sequential (type-expr->malli (first args) opts)]
             "Array"  [:sequential (type-expr->malli (first args) opts)]
             "Option" [:maybe (type-expr->malli (first args) opts)]
             "Prod"   [:tuple (type-expr->malli (first args) opts)
                       (type-expr->malli (second args) opts)]
             "Sum"    [:or (type-expr->malli (first args) opts)
                       (type-expr->malli (second args) opts)]
             ;; Check for structure application (e.g. (Pair Nat Int))
             (if-let [struct-reg (:struct-registry opts)]
               (if-let [info (get @struct-reg n)]
                 (into [:map] (mapv (fn [f] [(keyword f) :any]) (:fields info)))
                 :any)
               :any)))
         ;; Non-const head (higher-kinded, etc.) → :any
         :any))

     ;; Forall — function type (when encountered as a standalone type, not peeled by fn-schema)
     (e/forall? expr) ifn?

     ;; Sort — Type/Prop as values
     (e/sort? expr) :any

     ;; Bvar — unresolved type variable
     (e/bvar? expr) :any

     ;; Everything else
     :else :any)))

;; ============================================================
;; Function Schema Extraction
;; ============================================================

(defn fn-schema
  "Extract a Malli function schema from a verified function's CIC type.
   Walks the forall telescope, collecting explicit (runtime) parameter types
   and the return type.

   Returns [:=> [:cat input1 input2 ...] output].

   Implicit and instance-implicit parameters are skipped — they don't exist
   at runtime (same logic as ansatz.core/compute-arity)."
  ([fn-type] (fn-schema fn-type nil))
  ([fn-type opts]
   (loop [t fn-type inputs []]
     (if (e/forall? t)
       (let [bi (e/forall-info t)]
         (if (= :default bi)
           ;; Explicit param → runtime argument, include in schema
           (recur (e/forall-body t)
                  (conj inputs (type-expr->malli (e/forall-type t) opts)))
           ;; Implicit/inst-implicit → erased at runtime, skip
           (recur (e/forall-body t) inputs)))
       ;; t is the return type
       [:=> (into [:cat] inputs) (type-expr->malli t opts)]))))

;; ============================================================
;; Registration
;; ============================================================

(defn register!
  "Register a Malli function schema for a verified function.
   ns-sym:      namespace symbol (e.g. 'user)
   fn-sym:      function name symbol (e.g. 'double)
   schema-form: Malli schema form (e.g. [:=> [:cat :int] :int])"
  [ns-sym fn-sym schema-form]
  (let [register-fn! (resolve-malli! 'malli.core/-register-function-schema!)]
    (register-fn! ns-sym fn-sym schema-form {})))

(defn register-from-defn!
  "Register a verified function with Malli by looking up its type in the
   Ansatz environment. Called automatically by a/defn when *malli?* is true."
  [ns-sym fn-name-sym]
  (let [env-atom (requiring-resolve 'ansatz.core/ansatz-env)
        env @env-atom
        struct-reg (requiring-resolve 'ansatz.core/structure-registry)
        cname (name/from-string (str fn-name-sym))
        ^ConstantInfo ci (env/lookup env cname)]
    (when ci
      (let [opts {:env env :struct-registry struct-reg}
            schema-form (fn-schema (.type ci) opts)]
        (register! ns-sym fn-name-sym schema-form)
        (when @(requiring-resolve 'ansatz.core/*verbose*)
          (println "  malli:" schema-form))))))

;; ============================================================
;; Instrumentation convenience
;; ============================================================

(defn instrument!
  "Instrument all registered verified functions with Malli runtime validation.
   Options are passed through to malli.instrument/instrument!.

   Common options:
     :scope  #{:input :output}  — which to validate (default: both)
     :report (fn [type data] …) — error handler"
  ([] (instrument! nil))
  ([opts]
   (let [mi-instrument! (resolve-malli! 'malli.instrument/instrument!)]
     (mi-instrument! opts))))

(defn unstrument!
  "Remove Malli instrumentation from all verified functions.
   Options are passed through to malli.instrument/unstrument!"
  ([] (unstrument! nil))
  ([opts]
   (let [mi-unstrument! (resolve-malli! 'malli.instrument/unstrument!)]
     (mi-unstrument! opts))))

;; ============================================================
;; Inspection
;; ============================================================

(defn fn-schema-for
  "Return the Malli function schema form for a named verified function.
   Looks up the function in the Ansatz environment by name string."
  [fn-name-str]
  (let [env-atom (requiring-resolve 'ansatz.core/ansatz-env)
        env @env-atom
        struct-reg (requiring-resolve 'ansatz.core/structure-registry)
        cname (name/from-string fn-name-str)
        ^ConstantInfo ci (env/lookup env cname)]
    (when ci
      (fn-schema (.type ci) {:env env :struct-registry struct-reg}))))
