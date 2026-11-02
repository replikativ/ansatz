(ns engine-support.expr
  "Fixture constructors and bounded stepping for native Expr engine contracts."
  (:require [clojure.data.json :as json]
            [java-ir-baseline :as j]
            [java-ir-extern-checks :as x]
            [java-ir-header-checks :as header] [java-ir-expr-equality-checks :as eq]
            [java-ir-expr-find-checks :as find] [java-ir-sync-task-checks :as sync] [lean-compatibility-corpus :as corpus]))

(def ^:dynamic *basis* nil)

(def directory "test/fixtures/java-expr-machinery-runtime/")

(def roles ["Lean.Expr.bvar._override" "Lean.Expr.sort._override" "Lean.Expr.const._override"
            "Lean.Expr.app._override" "Lean.Expr.lam._override._boxed" "Lean.Expr.forallE._override._boxed"
            "Lean.Expr.letE._override._boxed" "Lean.Expr.mdata._override" "Lean.Expr.proj._override"])

(defn private-value [value field]
  ;; Typed job fields live partly on their private common superclass.
  (let [f (loop [cls (class value)]
            (when-not cls (throw (NoSuchFieldException. field)))
            (let [f (try (.getDeclaredField ^Class cls field) (catch NoSuchFieldException _ nil))]
              (if f f (recur (.getSuperclass ^Class cls)))))]
    (.setAccessible ^java.lang.reflect.Field f true) (.get ^java.lang.reflect.Field f value)))

(defn records [] (json/read-str (slurp (str directory "original-rows.json"))))

(defn setup-copy [entry]
  ;; Input preparation model: same original constructor algorithm, distinct Name.
  (let [label (str "model-setup-" (get entry "label")) n ["str" ["anonymous"] label]]
    {"label" label "sha256" header/digest
     "row" (-> (get entry "row") (assoc "name" n) (assoc-in ["ir" "fdecl" "f"] n))}))

(defn context
  ([] (context {}))
  ([{:keys [defer replacements rows host-specs inactive tasks extra-originals]}]
   (let [originals (filter #(not= "Lean.instantiateExprMVarsImp" (get % "label")) (records))
         entries (concat originals (eq/records) extra-originals (map setup-copy originals)
                   (when tasks (json/read-str (slurp "test/fixtures/java-task-sync-runtime/original-rows.json")))
                   (for [r (x/raw rows)] {"label" (last (get r "name")) "row" r "sha256" header/digest}))
         entries (vals (reduce (fn [m r] (let [n (get-in r ["row" "name"])]
                               (when-let [old (m n)] (assert (= (get old "row") (get r "row"))))
                               (assoc m n r))) {} entries))
         entries (mapv (fn [r] (if-let [body (get replacements (get r "label"))]
                                  (assoc-in r ["row" "ir" "fdecl" "body"] (json/read-str (json/write-str body))) r)) entries)
         base (j/prepare-host-program *basis* [] []) source (j/source-binding base {:expr-machinery-models true :fixture (corpus/sha256 (str directory "provenance.json"))})
         hm (into {} (for [r entries] [(get-in r ["row" "name"]) (j/declaration-header source (get r "row") (get r "sha256"))]))
         registered (j/register-headers base (vec (vals hm)) (or host-specs []))
         ctx (reduce (fn [ctx r] (if (and (get-in r ["row" "ir" "fdecl"]) (not (contains? (set defer) (get r "label"))))
                                   (j/materialize-body ctx (hm (get-in r ["row" "name"])) (get r "row") (mapv hm (find/direct (get r "row")))) ctx)) registered entries)
         ctx (if inactive (assoc ctx :explicit true) (sync/active ctx))]
     {:ctx ctx :source source :rows (into {} (map (juxt #(get % "label") #(get % "row")) entries))
      :headers (into {} (for [r entries] [(get r "label") (hm (get-in r ["row" "name"]))]))})))

(defn call [ctx e label args] (j/start! ctx e label args) (sync/finish! ctx e))

(defn setup! [ctx e role args] (call ctx e (str "model-setup-" (roles role)) args))

(defn fields [ctx value] (mapv identity (.get ^java.lang.reflect.Field (:fields ctx) value)))

(defn scalar-bytes [ctx value] (vec (.get ^java.lang.reflect.Field (:scalars ctx) value)))

(defn retain [ctx e value] (j/retain! ctx e value) value)

(defn bvar! [ctx e index] (setup! ctx e 0 [index]))

(defn sort! [ctx e] (setup! ctx e 1 [0]))

(defn app! [ctx e f a] (setup! ctx e 3 [f a]))

(defn lam! [ctx e body] (setup! ctx e 4 [0 (sort! ctx e) body 0]))

(defn fvar! [ctx e text]
  (call ctx e "Lean.Expr.fvar._override" [(call ctx e "Lean.Name.str._override" [0 text])]))

(defn finish-research! [ctx e]
  ;; Bound actual dispatches, not the number of single-step host round trips.
  ;; Dedicated pause/fork checks continue to advance exactly one instruction.
  (let [start (j/instructions ctx e) deadline (+ (System/nanoTime) 30000000000)]
    (loop []
      (let [phase (j/phase ctx e) elapsed (- (j/instructions ctx e) start)]
        (cond
          (= phase "complete") (j/take-result! ctx e)
          (or (not= phase "running") (>= elapsed 2000000) (> (System/nanoTime) deadline))
          (throw (ex-info "Bounded private Expr job reached a boundary"
                   {:phase phase :dispatches elapsed :instructions (j/instructions ctx e)
                    :code-header (some-> (j/code-request ctx e) (.header) (.name))
                    :host-symbol (some-> (j/host-request ctx e) (j/request-value "symbol"))}))
          :else (do (j/advance! ctx e (min 64 (- 2000000 elapsed))) (recur)))))))

(defn state [e] (some-> (sync/action e) (private-value "exprMachinery")))

(defn materialize [{:keys [ctx headers rows]} label]
  (let [row (rows label) by-name (into {} (for [[label h] headers] [(get (rows label) "name") h]))]
    (j/materialize-body ctx (headers label) row (mapv by-name (find/direct row)))))

(defn constructor-request! [ctx e]
  (loop [left 20000]
    (assert (pos? left) "No constructor CodeRequest within bounded progress")
    (or (j/code-request ctx e)
        (do (assert (not (j/advance! ctx e 1)) "Unexpected completion before constructor request")
            (recur (dec left))))))

(defn until! [ctx e predicate]
  (loop [left 20000]
    (assert (pos? left) "Private machinery test exceeded bounded progress")
    (when-not (predicate) (assert (not (j/advance! ctx e 1)) "Unexpected completion before target") (recur (dec left)))))
