(ns java-ir-kernel-projection-checks
  "Borrowed checking projection from actual Java Nodes, not a frontend result."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [prototype.kernel-bridge :as bridge] [prototype.imported-kernel :as imported] [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name] [java-ir-baseline :as j]
            [java-ir-baseline-checks :as c] [java-ir-extern-checks :as x] [java-ir-host-checks :as h]
            [ansatz.research.ir.kernel-projection :as projection]
            [lean-compatibility-corpus :as corpus])
  (:import [ansatz.kernel Env Expr Level]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-kernel-projection/")
(defn descriptors []
  [{:kind :ctor :id 1 :rc 1 :tag 1 :fields [0 "HostedSort"] :scalars (vec (repeat 8 0))}
   {:kind :ctor :id 2 :rc 1 :tag 1 :fields [0] :scalars (vec (repeat 8 0))}
   {:kind :ctor :id 3 :rc 1 :tag 3 :fields [{:ref 2}] :scalars (vec (repeat 8 0))}
   {:kind :ctor :id 4 :rc 1 :tag 0 :fields [{:ref 1} 0 {:ref 3}]}
   {:kind :ctor :id 5 :rc 1 :tag 0 :fields [{:ref 4}] :scalars [0]}
   {:kind :ctor :id 6 :rc 1 :tag 0 :fields [{:ref 5}]}])
(defn context
  ([] (context (descriptors) 6))
  ([descriptors root-id]
   (let [ctx (j/prepare-host-program *basis* [] []) engine (j/machine ctx)
         source (j/source-binding ctx {:test-only-raw-layout-model true})
         nodes (mapv (fn [node] (j/graph-node ctx
                            (if (contains? node :fields)
                              (update node :fields #(mapv (fn [v] (if (map? v) (j/graph-ref ctx (:ref v)) v)) %)) node))) descriptors)
         [root] (j/install-graph! ctx engine (j/selected-owner-graph ctx source (Object.) nodes [] [] [(j/graph-ref ctx root-id)]))]
     {:ctx ctx :engine engine :root root})))
(defn open [ctx engine & [max-nodes]]
  (projection/open-projector ctx engine {:max-nodes (or max-nodes 100) :deadline-nanos (+ (System/nanoTime) 10000000000)}))
(defn projected [scope root] (bridge/project-with-stats (:world scope) :axiom-declaration root (:projector scope)))
(defn counters [engine] (into {} (for [key ["allocations" "stores" "retains" "releases" "shellDeletes"]] [key (h/private-value engine key)])))

(deftest raw-source-constructor-layout-evidence-is-pinned
  (let [manifest (json/read-str (slurp (str directory "provenance.json")))
        records (json/read-str (slurp (str directory "original-rows.json")))
        ctors (for [r records node (tree-seq coll? seq (get-in r ["row" "ir"]))
                    :when (and (map? node) (get node "ctor"))] (get-in node ["ctor" "i"]))
        layouts (set (map #(select-keys % ["cidx" "size" "ssize" "usize"]) ctors))]
    (is (= 5 (count records)))
    (is (= (get manifest "fixture-sha256") (corpus/sha256 (str directory "original-rows.json"))))
    (doseq [[tag fields scalar] [[1 2 8] [1 1 8] [3 1 8] [0 3 0] [0 1 1] [0 1 0]]]
      (is (contains? layouts {"cidx" tag "size" fields "ssize" scalar "usize" 0})))))

(deftest genuine-java-node-borrow-projects-and-checks-safe-sort1-axiom
  (let [{:keys [ctx engine root]} (context) before (j/java-value ctx root) counts (counters engine)
        scope (open ctx engine) empty (env/empty-env)]
    (try
      (let [result (bridge/admit-axiom (:world scope) empty root 10000 (:projector scope))
            constant (:constant result) type (.type constant)]
        (is (= (name/from-string "HostedSort") (.name constant)))
        (is (= Expr/SORT (.tag ^Expr type)))
        (is (= (Level/succ Level/ZERO_LEVEL) (.o0 ^Expr type)))
        (is (identical? root (:guest-declaration result)))
        (is (nil? (.lookup ^Env empty (.name constant))))
        (is (some? (.lookup ^Env (:env result) (.name constant))))
        (is (= before (j/java-value ctx root))) (is (= counts (counters engine)))
        (is (identical? constant (:value (projected scope root)))))
      (finally ((:close! scope)) (j/release! ctx engine root) (j/close! ctx engine)))))

(deftest closed-scope-clears-both-memos-and-rejects-cached-values
  (let [{:keys [ctx engine root]} (context) scope (open ctx engine)]
    (projected scope root)
    (is (pos? (:borrowed-views ((:stats scope)))))
    (is (pos? (:projected-values ((:stats scope)))))
    (is (not (identical? engine (:world scope))))
    ((:close! scope)) ((:close! scope))
    (is (= {:open? false :borrowed-views 0 :projected-values 0} ((:stats scope))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"closed" (projected scope root)))
    (j/release! ctx engine root) (j/close! ctx engine)))

(deftest progress-thread-deadline-and-node-budget-reject-without-projector-owner-effects
  (let [{:keys [ctx engine root]} (context) scope (open ctx engine)]
    (projected scope root)
    (j/retain! ctx engine root)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"progressed" (projected scope root)))
    ((:close! scope)) (j/release! ctx engine root)
    (let [scope (open ctx engine 2) counts (counters engine)]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"source-node limit" (projected scope root)))
      (is (= counts (counters engine))) ((:close! scope)))
    (let [scope (open ctx engine)
          clock (ns-resolve 'ansatz.research.ir.kernel-projection 'nano-time)]
      (with-redefs-fn {clock (constantly Long/MAX_VALUE)}
        #(is (thrown-with-msg? clojure.lang.ExceptionInfo #"deadline" (projected scope root))))
      ((:close! scope)))
    (let [scope (open ctx engine)
          error (atom nil) thread (Thread. (fn [] (try (projected scope root) (catch Throwable e (reset! error e)))))]
      (.start thread) (.join thread 1000)
      (is (some? @error)) (is (re-find #"another thread" (.getMessage ^Throwable @error)))
      ((:close! scope)))
    (j/release! ctx engine root) (j/close! ctx engine)))

(deftest malformed-unsafe-open-and-nontype-declarations-reject
  (doseq [mode [:short-cache :unsafe :open :not-type]]
    (let [nodes (case mode
                  :short-cache (assoc-in (descriptors) [2 :scalars] (vec (repeat 7 0)))
                  :unsafe (assoc-in (descriptors) [4 :scalars] [1])
                  :open (assoc (descriptors) 2 {:kind :ctor :id 3 :rc 1 :tag 0 :fields [0] :scalars (vec (repeat 8 0))})
                  :not-type (into (assoc (descriptors) 2 {:kind :ctor :id 3 :rc 1 :tag 9 :fields [{:ref 7}] :scalars (vec (repeat 8 0))})
                                  [{:kind :ctor :id 7 :rc 1 :tag 0 :fields [4]}]))
          ;; Remove now-unreachable Level node; importer requires closed reachability.
          nodes (if (contains? #{:open :not-type} mode) (vec (remove #(= 2 (:id %)) nodes)) nodes)
          {:keys [ctx engine root]} (context nodes 6) scope (open ctx engine) counts (counters engine)]
      (try
        (is (thrown? Exception (bridge/admit-axiom (:world scope) (env/empty-env) root 10000 (:projector scope))))
        (is (= counts (counters engine)))
        (finally ((:close! scope)) (j/release! ctx engine root) (j/close! ctx engine))))))

(deftest cycle-and-nonconstructor-carriers-are-not-checking-nodes
  (let [nodes [{:kind :ctor :id 1 :tag 5 :fields [{:ref 1} {:ref 1}] :scalars (vec (repeat 8 0))}]
        {:keys [ctx engine root]} (context nodes 1) scope (open ctx engine)]
    (try (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Cyclic" (bridge/project-expr (:world scope) root (:projector scope))))
         (finally ((:close! scope)) (j/close! ctx engine))))
  (doseq [node [{:kind :array :id 1 :fields [0]} {:kind :ref :id 1 :fields [0]} {:kind :byte-array :id 1 :bytes [0]}]]
    (let [{:keys [ctx engine root]} (context [node] 1) scope (open ctx engine)]
      (try (is (thrown? Exception (bridge/project-expr (:world scope) root (:projector scope))))
           (finally ((:close! scope)) (j/close! ctx engine))))))

(deftest aligned-physical-padding-and-semantic-binder-storage-share-rules
  (doseq [size [9 16 10]]
    (let [nodes (into (subvec (descriptors) 0 3)
                  [{:kind :ctor :id 7 :rc 1 :tag 0 :fields [0] :scalars (vec (repeat 8 0))}
                   {:kind :ctor :id 8 :rc 1 :tag 6 :fields [{:ref 1} {:ref 3} {:ref 7}]
                    :scalars (vec (repeat size 0))}])
          {:keys [ctx engine root]} (context nodes 8) scope (open ctx engine)]
      (try
        (if (= size 10)
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"layout" (bridge/project-expr (:world scope) root (:projector scope))))
          (let [value (bridge/project-expr (:world scope) root (:projector scope))]
            (is (= Expr/LAM (.tag ^Expr value)))
            (is (= 0 (.bvarRange ^Expr value)))))
        (finally ((:close! scope)) (j/release! ctx engine root) (j/close! ctx engine))))))

(deftest dead-and-closure-nodes-cannot-be-projector-constructors
  (let [{:keys [ctx engine root]} (context)]
    (j/release! ctx engine root)
    (let [scope (open ctx engine)]
      (try (is (thrown? Exception (projected scope root)))
           (finally ((:close! scope)) (j/close! ctx engine)))))
  (let [ctx (j/prepare-host-program *basis*
              (x/raw [(c/decl "identity" [(c/p 1 "object")] "object" (c/ret 1))]) [])
        engine (j/machine ctx) closure (j/make-closure! ctx engine "identity" []) scope (open ctx engine)]
    (try (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Closure" (bridge/project-expr (:world scope) closure (:projector scope))))
         (finally ((:close! scope)) (j/release! ctx engine closure) (j/close! ctx engine)))))

(deftest closed-failed-idle-and-disposed-flags-reject-initial-open-and-memo-hits
  (doseq [flag [:closed :failed-idle :disposed-model]]
    (let [{:keys [ctx engine root]} (context (mapv #(dissoc % :rc) (descriptors)) 6)
          ctx (if (= flag :failed-idle)
                (j/extend-program ctx [((x/originals) "Nat.add")]) ctx)
          _ (when (= flag :failed-idle) (j/install-program! ctx engine))
          scope (open ctx engine)]
      (projected scope root)
      (let [before (counters engine)]
        (case flag
          :closed (j/close! ctx engine)
          :failed-idle (is (not= "NO ERROR" (c/failure #(j/call ctx engine "Nat.add" ["bad" 0]))))
          ;; A controlled no-counter-change disposed state models the lifecycle
          ;; bit independently; actual disposal normally also advances counters.
          :disposed-model (let [field (doto (.getDeclaredField ^Class (:class ctx) "disposed") (.setAccessible true))]
                            (.setBoolean field engine true)))
        (is (= "idle" (j/phase ctx engine)))
        (is (= before (counters engine)))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"close/failure/disposal" (projected scope root)))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"close/failure/disposal" (open ctx engine)))
        ((:close! scope))
        (is (= {:open? false :borrowed-views 0 :projected-values 0} ((:stats scope))))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-kernel-projection-checks)))


(deftest imported-ci-carrier-reuses-actual-node-scope-and-rejects-closed-memo-hits
  (let [{:keys [ctx engine root]} (context) scope (open ctx engine)
        project (imported/make-constant-projector (:world scope) (:carrier-ops scope)
                  {:max-visits 10000 :max-rule-nodes 100})
        counts (counters engine)]
    (try
      (let [ci (project (:world scope) root)
            inventory (imported/project-constant-name-kind (:world scope) root
                        {:max-nodes 20 :max-chars 100} (:carrier-ops scope))]
        (is (= (name/from-string "HostedSort") (.name ci)))
        (is (= {:name (.name ci) :kind 0} inventory))
        (is (= counts (counters engine))))
      ((:prototype.kernel-bridge/clear-memo! (meta project)))
      ((:close! scope))
      (is (thrown-with-msg? Exception #"closed" (project (:world scope) root)))
      (finally
        ((:prototype.kernel-bridge/clear-memo! (meta project)))
        ((:close! scope)) (j/release! ctx engine root) (j/close! ctx engine)))))

(deftest imported-ci-carrier-cannot-bypass-node-or-total-visit-limits
  (let [{:keys [ctx engine root]} (context)]
    (try
      (doseq [[max-nodes max-visits message] [[1 10000 #"source-node limit"]
                                            [100 1 #"total visit limit"]]]
        (let [scope (open ctx engine max-nodes)
              project (imported/make-constant-projector (:world scope) (:carrier-ops scope)
                        {:max-visits max-visits :max-rule-nodes 100})]
          (try
            (is (thrown-with-msg? Exception message (project (:world scope) root)))
            (finally ((:prototype.kernel-bridge/clear-memo! (meta project))) ((:close! scope))))))
      (finally (j/release! ctx engine root) (j/close! ctx engine)))))
