(ns java-ir-expr-quick-order-control-checks
 "Ordering resource, metadata-kind and borrowed-entry boundaries."
 (:require [clojure.test :refer [deftest is run-tests]]
  [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
  [java-ir-expr-quick-order-checks :as order] [java-ir-expr-equality-checks :as eq]
  [java-ir-extern-checks :as x] [java-ir-host-checks :as h]
  [java-ir-generation-checks :as g] [java-ir-code-checks :as code]
  [java-ir-continuation-checks :as k]))
(def ^:dynamic *basis* nil)
(defn context [extra] (binding [order/*basis* *basis*] (order/context extra)))
(defn model-context [] (let [ctx (context [])] (assoc ctx :engine (j/machine ctx))))
(defn comparator [ctx]
 (let [cls (Class/forName "ansatz.research.ir.Interpreter$ExprOrder" true (:loader ctx))
       ctor (.getDeclaredConstructor cls (into-array Class [(:class ctx)]))]
  (.setAccessible ctor true) (.newInstance ctor (object-array [(:engine ctx)]))))
(defn compare! [cmp a b]
 (let [m (.getDeclaredMethod (class cmp) "apply" (into-array Class [Object Object]))]
  (.setAccessible m true) (.invoke m cmp (object-array [a b]))))

(deftest models-every-datavalue-domain-and-ordered-duplicate-tail
 (let [ctx (model-context) e (:engine ctx) b (eq/model-builder ctx) add (:add b) ex (:expr b) nm (:name b) ls (:list b)
       key (nm "k") other (nm "q") z (ex 0 [0])
       dv (fn [tag value] (if (= tag 1) (add tag [] 8 value 0) (add tag [value] 0 0 0)))
       md (fn [entries] (ex 10 [(ls (map #(add 0 % 0 0 0) entries)) z]))
       cases [[(md [[key (dv 0 "\uE000")]]) (md [[key (dv 0 "𐀀")]]) [1 0]]
              [(md [[key (dv 1 0)]]) (md [[key (dv 1 1)]]) [1 0]]
              [(md [[key (dv 2 key)]]) (md [[key (dv 2 other)]]) [1 0]]
              [(md [[key (dv 3 7)]]) (md [[key (dv 3 8)]]) [1 0]]
              [(md [[key (dv 4 (j/graph-int ctx -7))]]) (md [[key (dv 4 (j/graph-int ctx 8))]]) [0 0]]
              [(md [[key (dv 5 0)]]) (md [[key (dv 5 (add 2 [0 "x"] 0 0 0))]]) [0 0]]
              [(md [[key (dv 0 "x")]]) (md [[key (dv 1 0)]]) [1 0]]
              [(md [[key (dv 3 7)]]) (md [[key (dv 3 7)] [key (dv 3 7)]]) [1 0]]
              [(md [[key (dv 3 7)] [other (dv 3 1)]]) (md [[other (dv 3 1)] [key (dv 3 7)]]) [1 0]]]
       roots ((:finish b) (vec (mapcat #(take 2 %) cases))) before (k/counters ctx e)]
  (doseq [[i [_ _ expected]] (map-indexed vector cases)]
   (is (= expected (order/pair ctx (roots (* 2 i)) (roots (inc (* 2 i)))))))
  (is (= before (k/counters ctx e))) (j/close! ctx e)))

(deftest bounded-deep-shared-dag-and-independent-fork-results
 (let [ctx (model-context) e (:engine ctx) b (eq/model-builder ctx) ex (:expr b)
       a (loop [n 1000 child (ex 0 [0])] (if (zero? n) child (recur (dec n) (ex 5 [child child]))))
       c (loop [n 1000 child (ex 0 [0])] (if (zero? n) child (recur (dec n) (ex 5 [child child]))))
       [left right] ((:finish b) [a c]) before (k/counters ctx e)
       {child :engine roots :roots} (j/fork! ctx e [left right])]
  (is (= [0 0] (order/pair ctx left right))) (is (= before (k/counters ctx e)))
  (is (= [0 0] (order/pair (assoc ctx :engine child) (roots 0) (roots 1))))
  (j/close! ctx child) (j/close! ctx e)))

(deftest model-private-budget-is-shared-with-fresh-equality-and-interruption
 (doseq [interrupt? [false true]]
  (let [ctx (model-context) e (:engine ctx) b (eq/model-builder ctx)
        [a c] ((:finish b) [((:expr b) 0 [0]) ((:expr b) 0 [1])])
        cmp (comparator ctx) work-field (doto (.getDeclaredField (class cmp) "work") (.setAccessible true))
        before (k/counters ctx e)]
   ;; MODEL changes only invocation-local accounting. For the work case the
   ;; outer frame consumes the last unit; its fresh EQ probe must NOT reset it.
   (.setLong work-field cmp (long (if interrupt? 1023 999999)))
   (try
    (when interrupt? (.interrupt (Thread/currentThread)))
    (is (g/bad? #(compare! cmp a c)))
    (finally (when interrupt? (Thread/interrupted))))
   (when-not interrupt? (is (= 1000000 (.getLong work-field cmp))))
   (is (= before (k/counters ctx e))) (j/close! ctx e))))

(deftest borrowed-root-makeclosure-and-static-pap-fences
 (let [ctx (model-context) e (:engine ctx)
       a (j/call ctx e "Lean.Expr.bvar._override" [0]) b (j/call ctx e "Lean.Expr.bvar._override" [1])
       before (k/counters ctx e)]
  (is (g/bad? #(j/call ctx e "Lean.Expr.quickLt" [a b])))
  (is (= "idle" (j/phase ctx e)))
  (is (g/bad? #(j/make-closure! ctx e "Lean.Expr.quickLt" [])))
  (is (= before (k/counters ctx e))) (is (= 1 (c/rc ctx a) (c/rc ctx b)))
  (j/release! ctx e a) (j/release! ctx e b) (j/close! ctx e))
 (is (g/bad? #(context [(c/decl "invalid-order-pap" [] "object"
    (c/let-ir 1 "object" {:pap {:c (order/raw-name) :ys []}} (c/ret 1)))]))))

(deftest borrowed-import-and-hostreply-closure-fences-before-claim
 (let [rs (order/records) base (j/prepare-host-program *basis* [] []) source (j/source-binding base (Object.))
       raw (j/declaration-header source (get-in rs [0 "row"]) (get-in rs [0 "sha256"]))
       ctx (j/register-headers base [raw]) e (j/machine ctx) before (k/counters ctx e)]
  (is (g/bad? #(j/install-graph! ctx e (j/prepared-graph ctx source (Object.)
     [(j/graph-node ctx {:kind :closure :id 1 :target raw})] [] [] [(j/graph-ref ctx 1)]))))
  (is (= before (k/counters ctx e))) (is (false? (h/private-value e "graphInstalled"))) (j/close! ctx e))
 (let [;; Prepare actual Host registration separately; context helper rows retain
       ;; their original source contents, no fabricated native callable admitted.
       rows (concat (map #(get % "row") (eq/records)) (map #(get % "row") (order/records)) [(h/ext "order-host" h/owned)])
       ctx (j/prepare-host-program (assoc *basis* :explicit true) (x/raw rows) [h/owned]) e (j/machine ctx)
       forged (eq/forged-raw-closure ctx "Lean.Expr.quickLt")]
  (j/start! ctx e "order-host" [0])
  (let [request (j/host-request ctx e) before (k/counters ctx e)]
   (is (g/bad? #(j/resume-host! ctx e request forged)))
   (is (identical? request (j/host-request ctx e))) (is (= before (k/counters ctx e)))
   (is (= 1 (c/rc ctx forged)))
   (j/resume-host! ctx e request 0) (is (= 0 (j/take-result! ctx e))))
  (j/release! ctx e forged) (j/close! ctx e)))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-quick-order-control-checks)))
