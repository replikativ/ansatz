(ns engine-support.expr-context
  "Authentic Expr and MetavarContext fixture assembly for native worker contracts."
  (:refer-clojure :exclude [run!])
  (:require [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-header-checks :as header]
            [engine-support.expr :as expr] [java-ir-level-mvars-checks :as level]))

(def ^:dynamic *basis* nil)

(def directory "test/fixtures/java-expr-direct-runtime/")

(def helpers ["Lean.MetavarContext.getExprAssignmentExp" "Lean.MetavarContext.getDelayedMVarAssignmentExp"
              "Lean.DelayedMetavarAssignment.fvarsExp" "Lean.DelayedMetavarAssignment.mvarIdPendingExp" "Lean.assignExp"])

(defn originals [] (json/read-str (slurp (str directory "original-rows.json"))))

(defn records [] (json/read-str (slurp (str directory "execution-rows.json"))))

(defn copy-role [entry]
  (let [label (str "model-setup-" (get entry "label")) n ["str" ["anonymous"] label]]
    {"label" label "sha256" header/digest
     "row" (-> (get entry "row") (assoc "name" n) (assoc-in ["ir" "fdecl" "f"] n))}))

(defn context
  ([] (context {}))
  ([options]
   (let [extra (concat (records) (level/records) (map copy-role (take 19 (originals))))
         lab (binding [expr/*basis* *basis*]
               (expr/context (merge options {:extra-originals extra :rows (concat [(level/fresh-context-row)] (:rows options))})))
         policy (apply j/level-instantiation-policy (:ctx lab) (map (:headers lab) level/roles))]
     (assoc lab :level-policy policy))))

(defn engine [{:keys [ctx level-policy]}]
  (let [e (j/machine ctx)] (j/configure-level-instantiation! ctx e level-policy) e))

(defn mvar! [ctx e n] (expr/call ctx e "Lean.Expr.mvar._override" [n]))

(defn assign! [ctx e m n value] (expr/call ctx e "Lean.assignExp" [m n value]))

(defn fields [ctx value] (expr/fields ctx value))

(defn delayed-model-rows []
  ;; Explicit test adapter: copy the authenticated ten-field context and swap the
  ;; compiled assignment-map fields 8/9. Actual map operations/getters stay guest IR.
  ;; This is not claimed to be original assignDelayedMVar's monad implementation.
  [(let [order [0 1 2 3 4 5 6 7 9 8]
         tail (c/let-ir 12 "object" (c/ctor 0 (mapv #(c/v (+ 2 %)) order) 0)
                       ["dec" {:idx 1} 1 false false (c/ret 12)])]
     (c/decl "model-swap-expr-delayed-maps" [(c/p 1 "object")] "object"
       (reduce (fn [body i] (c/let-ir (+ i 2) "object" {:proj {:i i :x {:idx 1}}}
                             ["inc" {:idx (+ i 2)} 1 false false body])) tail (reverse (range 10)))))
   (c/decl "model-delayed-record" [(c/p 1 "object") (c/p 2 "object")] "object"
     (c/let-ir 3 "object" (c/ctor 0 [(c/v 1) (c/v 2)] 0) (c/ret 3)))])
