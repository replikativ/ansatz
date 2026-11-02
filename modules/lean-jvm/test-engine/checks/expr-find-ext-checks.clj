(ns java-ir-expr-find-ext-checks
  "Pinned FindStep traversal and resumable borrowed callback protocol."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-expr-find-checks :as f] [java-ir-extern-checks :as x]
            [java-ir-host-checks :as h] [java-ir-generation-checks :as g]
            [java-ir-code-checks :as code] [java-ir-continuation-checks :as k]
            [java-ir-sync-task-checks :as sync] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-expr-find-ext-runtime/")
(def base-records f/records)
(defn records [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn actual-name [] (get-in (first (records)) ["row" "name"]))
(def apply-row
  (c/decl "model-apply-find-ext" (mapv #(c/p % "object") [1 2 3]) "object"
    (c/let-ir 4 "object" {:ap {:x {:idx 1} :ys [(c/v 2) (c/v 3)]}} (c/ret 4))))
(defn context
  ([] (context {}))
  ([options]
   (binding [f/*basis* *basis*]
     (with-redefs [f/records #(concat (base-records) (records))]
       (f/context (update options :rows #(concat [apply-row (f/pred-row "model-done" 2 "object")] %)))))))
(defn host-lab [] (context {:rows [(h/ext "model-host-predicate" f/host-predicate)] :host-specs [f/host-predicate]}))
(defn start! [ctx e root]
  (let [p (f/predicate ctx e "model-host-predicate")]
    (j/start! ctx e "Lean.Expr.findExtImpl?._boxed" [p root]) p))
(defn run! [ctx e p root] (f/invoke ctx e "Lean.Expr.findExtImpl?._boxed" [p root]))
(defn trace! [ctx e root reply]
  (let [seen (atom []) p (start! ctx e root)
        result (f/drive ctx e (fn [r] (let [current (first (h/args r))]
                                (swap! seen conj current) (j/resume-host! ctx e r (reply current)))))]
    {:seen @seen :result result :predicate p}))

(deftest exact-original-abi-and-source-receipt
  (let [rows (records) p (json/read-str (slurp (str directory "provenance.json")))
        raw (get-in (first rows) ["row" "ir" "extern"])]
    (is (= 2 (count rows)))
    (is (= (get p "original-rows-sha256") (corpus/sha256 (str directory "original-rows.json"))))
    (is (= [] (get p "initialized-dependencies")))
    (is (= [["object" "object"] [true true] "tobject"]
           [(mapv #(get % "ty") (get raw "xs")) (mapv #(get % "borrow") (get raw "xs")) (get raw "type")]))
    (is (= [false false] (mapv #(get % "borrow") (get-in (second rows) ["row" "ir" "fdecl" "xs"]))))))

(deftest three-findsteps-owned-wrapper-and-owning-ap
  (doseq [[label found?] [["model-false" true] ["model-true" false] ["model-done" false]] route [:root :ap]]
    (let [{:keys [ctx]} (context) e (j/machine ctx) root (f/mk ctx e 0 7)
          p (f/predicate ctx e label) before (h/private-value e "allocations")
          result (if (= route :root) (run! ctx e p root)
                   (f/invoke ctx e "model-apply-find-ext"
                     [(j/make-closure! ctx e "Lean.Expr.findExtImpl?._boxed" []) p root]))]
      ;; AP allocates its closure before start; only the root route isolates Some.
      (when (= route :root) (is (= (if found? 1 0) (- (h/private-value e "allocations") before))))
      (is (h/private-value p "dead"))
      (if found?
        (do (is (identical? root (aget ^objects (f/fields ctx result) 0)))
            (is (= 1 (c/rc ctx root))) (sync/release! ctx e result))
        (is (= 0 result)))
      (is (h/private-value root "dead")) (sync/close! ctx e))))

(deftest preorder-skips-only-function-spine-apps-and-covers-all-child-kinds
  (let [{:keys [ctx]} (host-lab) e (j/machine ctx)
        bf (f/mk ctx e 0 11) br (f/mk ctx e 0 12) fv (f/mk ctx e 1 0) mv (f/mk ctx e 2 0)
        sort (f/mk ctx e 3 0) con (f/mk ctx e 4 0 0)
        lit (f/mk ctx e 9 (f/invoke ctx e "model-literal" [17]))
        proj (f/mk ctx e 11 0 0 bf) md (f/mk ctx e 10 0 proj)
        forall (f/mk ctx e 7 0 mv md) app (f/mk ctx e 5 con sort)
        lam (f/mk ctx e 6 0 app forall) let-node (f/mk ctx e 8 0 fv lit lam)
        partial (f/mk ctx e 5 let-node br) tail (f/mk ctx e 0 13) root (f/mk ctx e 5 partial tail)
        expected [root let-node fv lit lam app con sort forall mv md proj bf br tail]
        {:keys [seen result predicate]} (trace! ctx e root (constantly 1))]
    (is (= 0 result)) (is (= (count expected) (count seen)))
    (is (every? true? (map identical? expected seen)))
    (is (not-any? #(identical? partial %) seen))
    (is (every? #(h/private-value % "dead") (conj expected partial predicate))) (sync/close! ctx e)))

(deftest done-prunes-one-subtree-while-found-stops-all-later-predicates
  (doseq [stop? [false true]]
    (let [{:keys [ctx]} (host-lab) e (j/machine ctx) a (f/mk ctx e 0 1) b (f/mk ctx e 0 2)
          subtree (f/mk ctx e 6 0 a b) last (f/mk ctx e 0 3) root (f/mk ctx e 8 0 subtree last (f/mk ctx e 0 4))
          {:keys [seen result]} (trace! ctx e root #(cond (identical? % subtree) (if stop? 0 2) :else 1))]
      (is (= (if stop? 2 4) (count seen)))
      (is (not-any? #(or (identical? a %) (identical? b %)) seen))
      (if stop?
        (do (is (identical? subtree (aget ^objects (f/fields ctx result) 0))) (sync/release! ctx e result))
        (is (= 0 result)))
      (sync/close! ctx e))))

(deftest skipped-shared-partial-app-does-not-populate-cache-and-ordinary-find-is-unchanged
  (doseq [extended? [false true]]
    (let [{:keys [ctx]} (host-lab) e (j/machine ctx) head (f/mk ctx e 0 1) arg (f/mk ctx e 0 2)
          inner (f/mk ctx e 5 head arg) _ (j/retain! ctx e inner) root (f/mk ctx e 5 inner inner)
          seen (atom []) p (f/predicate ctx e "model-host-predicate")
          _ (j/start! ctx e (if extended? "Lean.Expr.findExtImpl?._boxed" "Lean.Expr.findImpl?._boxed") [p root])
          result (f/drive ctx e (fn [r] (swap! seen conj (first (h/args r)))
                                 (j/resume-host! ctx e r (if extended? 1 0))))
          expected (if extended? [root head arg inner head arg] [root inner head arg])]
      (is (= 0 result)) (is (= (count expected) (count @seen)))
      (is (every? true? (map identical? expected @seen))) (sync/close! ctx e))))

(deftest sharing-cache-exclusions-remain-native-order-before-callback-retains
  (doseq [tag [0 1 2 3 4 9]]
    (let [{:keys [ctx]} (host-lab) e (j/machine ctx)
          leaf (case tag 0 (f/mk ctx e 0 0) 1 (f/mk ctx e 1 0) 2 (f/mk ctx e 2 0)
                 3 (f/mk ctx e 3 0) 4 (f/mk ctx e 4 0 0)
                 9 (f/mk ctx e 9 (f/invoke ctx e "model-literal" [0])))
          _ (j/retain! ctx e leaf) root (f/mk ctx e 5 leaf leaf)
          {:keys [seen result]} (trace! ctx e root (constantly 1))
          expected (if (contains? #{0 3 4} tag) [root leaf leaf] [root leaf])]
      (is (= 0 result)) (is (= (count expected) (count seen)))
      (is (every? true? (map identical? expected seen))) (sync/close! ctx e))))

(deftest raw-borrowed-and-inactive-entry-fences-are-preclaim
  (let [{:keys [ctx source headers]} (context) e (j/machine ctx) root (f/mk ctx e 0 0)
        p (f/predicate ctx e "model-true") before (k/counters ctx e)]
    (is (g/bad? #(j/start! ctx e "Lean.Expr.findExtImpl?" [p root])))
    (is (= "idle" (j/phase ctx e))) (is (= before (k/counters ctx e)))
    (is (g/bad? #(j/make-closure! ctx e "Lean.Expr.findExtImpl?" [])))
    (is (g/bad? #(context {:rows [(c/decl "model-find-ext-pap" [] "object"
                       (c/let-ir 1 "object" {:pap {:c (actual-name) :ys []}} (c/ret 1)))]})))
    (is (g/bad? #(j/install-graph! ctx e (j/prepared-graph ctx source (Object.)
                 [(j/graph-node ctx {:kind :closure :id 1 :target (headers "Lean.Expr.findExtImpl?")})]
                 [] [] [(j/graph-ref ctx 1)]))))
    (is (false? (h/private-value e "graphInstalled")))
    (sync/release! ctx e p) (sync/release! ctx e root) (sync/close! ctx e))
  (doseq [mode [:recursive :explicit]]
    (let [{:keys [ctx]} (context {:inactive mode}) e (j/machine ctx) root (j/call ctx e "model-expr-0" [0])
          p (f/predicate ctx e "model-true") before (k/counters ctx e)]
      (is (re-find #"active explicit runtime" (c/failure #(j/call ctx e "Lean.Expr.findExtImpl?._boxed" [p root]))))
      (is (= before (k/counters ctx e))) (is (= 1 (c/rc ctx p) (c/rc ctx root))))))

(deftest invalid-findstep-keeps-owned-receiver-and-failure-diagnostics
  (doseq [object? [false true]]
    (let [{:keys [ctx]} (host-lab) e (j/machine ctx) root (f/mk ctx e 0 0)
          invalid (if object? (f/mk ctx e 0 9) 3) _ (start! ctx e root) request (h/request! ctx e)]
      (j/resume-host! ctx e request invalid)
      (is (re-find #"canonical FindStep" (c/failure #(sync/finish! ctx e))))
      (let [a (f/find-action e) state (f/find-state e) slot (h/private-value a "slot")]
        (is ((if object? identical? =) invalid (aget ^objects (h/private-value e "objects") slot)))
        (is (true? (h/private-value state "receiverOwned")))
        (when object? (is (= 1 (c/rc ctx invalid))))
        (is (= "failed" (j/phase ctx e)))))))

(deftest code-demand-host-pause-and-fork-preserve-extended-mode-and-acquisitions
  (let [callback (c/decl "model-code-ext-pred" [(c/p 1 "object")] "object"
                   (c/let-ir 2 "object" (c/fap "model-host-predicate" [(c/v 1)])
                     ["dec" {:idx 1} 1 false false (c/ret 2)]))
        {:keys [ctx headers rows]} (context {:rows [(h/ext "model-host-predicate" f/host-predicate) callback]
                                           :host-specs [f/host-predicate] :defer #{"model-code-ext-pred"}})
        parent (j/machine ctx) root (f/mk ctx parent 0 0) p (f/predicate ctx parent "model-code-ext-pred")]
    (j/start! ctx parent "Lean.Expr.findExtImpl?._boxed" [p root])
    (let [_ (code/request! ctx parent) state (f/find-state parent)
          {:keys [engine roots]} (j/fork! ctx parent [root p]) child engine [cr cp] roots
          ready (j/materialize-body ctx (headers "model-code-ext-pred") (rows "model-code-ext-pred") [(headers "model-host-predicate")])]
      (is (true? (h/private-value state "extended")))
      (is (true? (h/private-value (f/find-state child) "extended")))
      (is (= 2 (c/rc ctx root) (c/rc ctx cr))) (is (= 1 (c/rc ctx p) (c/rc ctx cp)))
      (doseq [[e er reply] [[parent root 0] [child cr 2]]]
        (j/resume-code! ready e (j/code-request ready e))
        (let [r (h/request! ready e)]
          (is (identical? er (first (h/args r)))) (is (= 2 (c/rc ready er)))
          (j/resume-host! ready e r reply)
          (let [result (sync/finish! ready e)]
            (if (zero? reply)
              (do (is (identical? er (aget ^objects (f/fields ready result) 0))) (sync/release! ready e result))
              (is (= 0 result)))))
        (is (h/private-value er "dead")) (sync/close! ready e)))))

(deftest forked-function-spine-modes-survive-a-nonempty-pending-stack
  (let [{:keys [ctx]} (host-lab) parent (j/machine ctx) a (f/mk ctx parent 0 1) b (f/mk ctx parent 0 2)
        root (f/mk ctx parent 5 a b) _ (start! ctx parent root) request (h/request! ctx parent)]
    (j/resume-host! ctx parent request 1)
    ;; Pause after root's result is consumed and children are enqueued, before
    ;; the function-spine entry is popped (one budgeted Find dispatch at a time).
    (loop [left 1000]
      (assert (pos? left))
      (if (seq (h/private-value (f/find-state parent) "pending"))
        nil (do (j/advance! ctx parent 1) (recur (dec left)))))
    (let [{:keys [engine roots]} (j/fork! ctx parent [root a b]) child engine [cr ca cb] roots
          state (f/find-state parent) copy (f/find-state child)]
      (is (= [true false] (vec (h/private-value state "functionSpines"))))
      (is (= [true false] (vec (h/private-value copy "functionSpines"))))
      (is (identical? ca (.peek ^java.util.Deque (h/private-value copy "pending"))))
      (doseq [[e expected] [[parent [a b]] [child [ca cb]]]]
        (let [seen (atom []) result (f/drive ctx e (fn [r] (swap! seen conj (first (h/args r))) (j/resume-host! ctx e r 1)))]
          (is (= 0 result)) (is (= 2 (count @seen)))
          (is (every? true? (map identical? expected @seen))))
        (sync/close! ctx e)))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-find-ext-checks)))
