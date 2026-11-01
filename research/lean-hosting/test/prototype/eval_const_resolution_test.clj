(ns prototype.eval-const-resolution-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [prototype.eval-const :as eval]
            [prototype.eval-const-test :as fixtures]
            [prototype.program-install :as install]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.runtime-prim :as prim]))

(def answer (fixtures/n "answer"))
(def witness-helper (fixtures/n "actualInterpreterWitness"))
(def fixture (install/bundle-catalogue (slurp "fixtures/runtime-compiled-identity.jsonl")))
(defn witness [local?]
  {:schema "lean-eval-const-witness/1" :producer "RuntimeCompileShim.exportEvalConstWitness"
   :leanCommit (get prim/pinned-build "lean_get_githash")
   :runtimeProfile {:target "x86_64-unknown-linux-gnu" :wordBits 64}
   :name answer :boxedTarget (get-in fixture [:manifests 0 :entryPoints 0 :boxedTarget]) :sorryDep nil :missingDependencies []
   :declarations (mapv #(assoc (select-keys % [:name :ir]) :sourceLocal local?) (vals (:declarations fixture)))})
(defn bundle-text [candidate]
  (apply str (map #(str (json/write-str %) "\n")
                  (concat (:manifests candidate) (vals (:declarations candidate))))))
(defn helper [text]
  {:params [1 2 3] :body [:dec [:var 1] 1 [:dec [:var 2] 1
                         [:let 4 [:ctor 0 [[:imm text]]] [:return [:var 4]]]]]})
(def ^:dynamic *backing-catalogue* nil)
(defn setup [backend local? change-witness]
  (let [preinstalled (:world (install/install (m/world {}) fixture))
        code (if local? {} (:functions preinstalled))
        witness (change-witness (witness local?))
        helpers {fixtures/exporter {:params [1 2 3]
                                   :body [:let 4 [:project [:var 1] 1]
                                          [:dec [:var 1] 1 [:dec [:var 2] 1
                                           [:let 5 [:ctor 0 [[:var 4]]] [:return [:var 5]]]]]]}
                 witness-helper {:params [1 2 3]
                                 :body [:let 4 [:project [:var 1] 0]
                                        [:dec [:var 1] 1 [:dec [:var 2] 1
                                         [:let 5 [:ctor 0 [[:var 4]]] [:return [:var 5]]]]]]}
                 fixtures/apply-answer {:params [1 2] :body [:tail [:closure [:var 1]] [[:imm 0] [:var 2]]]}}
        binding (eval/make-binding fixtures/exporter
                                   (cond-> {:witness witness-helper :trusted-functions (merge code helpers)}
                                     (not local?) (assoc :catalogue (or *backing-catalogue* fixture))))
        params (get-in binding [:signature :params])
        row {:kind "decl" :name fixtures/root
             :ir {:extern {:f fixtures/root :xs (mapv (fn [i p] (assoc p :x {:idx i})) (range 1 5) params)
                           :type "object" :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"] :fn "lean_eval_const"}}]}}}}
        functions (assoc (merge code helpers) fixtures/root (second (raw/lower {"lean_eval_const" binding} row)))
        session (raw/open-functions functions {"lean_eval_const" binding} {:backend backend})
        [world environment] (m/allocate (m/world functions) :ctor 0 [(json/write-str witness) (bundle-text fixture)])
        [world name] (m/scalar-constructor world 1 [0 "answer"] {:objects 2 :usize 0 :ssize 8})
        world (assoc-in world [:heap (:id name) :scalar-bytes] (zipmap (range 16 24) (repeat 0)))]
    {:session session :world world :environment environment :name name :witness witness}))
(defn evaluate [{:keys [session world environment name]}]
  (raw/call session world fixtures/root [m/erased environment 0 name]))
(defn continue-from [context result] (assoc context :session (:session result) :world (:state result)))
(defn unwrap [result]
  (let [world (:state result) value (:value result) node (m/node world value)
        closure (first (:fields node))]
    (is (= 1 (:tag node)))
    [(m/release (m/retain world closure 1) value 1) closure]))

(deftest imported-code-resolves-before-a-kernel-environment-is-associated
  (doseq [backend [:reference :mutable :jvm]]
    (let [context (setup backend false identity) result (evaluate context)
          [world closure] (unwrap result)
          called (raw/call (:session result) world fixtures/apply-answer [closure 42])]
      (is (= 42 (:value called)))
      (is (empty? (:kernel-environments (:state result))))
      (is (identical? (get-in context [:world :functions answer])
                      (get-in result [:state :functions answer]))))))

(deftest successful-local-units-can-be-evaluated-repeatedly-in-independent-forks
  (doseq [backend [:reference :mutable :jvm]]
    (let [context (setup backend true identity) first-result (evaluate context)
          saved (continue-from context first-result)
          a (evaluate saved) b (evaluate saved)]
      (is (= (:next-id (:state a)) (:next-id (:state b))))
      (is (= (:eval-const-authorizations (:state a)) (:eval-const-authorizations (:state b))))
      (is (seq (get-in a [:state :eval-const-authorizations :functions])))
      (let [digest (get-in a [:state :eval-const-authorizations :unit-digests answer])]
        (is (boolean (re-matches #"[0-9a-f]{64}" digest)))
        (is (seq (get-in a [:state :eval-const-authorizations :units digest :declarations]))))
      (doseq [result [a b]]
        (let [[world closure] (unwrap result)
              called (raw/call (:session result) world fixtures/apply-answer [closure 42])]
          (is (= 42 (:value called)))))
      (is (= 1 (:rc (m/node (:state a) (:environment context)))))
      (is (= 1 (:rc (m/node (:state a) (:name context))))))))

(deftest changed-selected-ir-and-borrow-abi-are-rejected-despite-identical-kernel-root
  (doseq [change [(fn [w] (assoc-in w [:declarations 0 :ir :fdecl :xs 0 :borrow] true))
                  (fn [w] (assoc-in w [:declarations 0 :ir :fdecl :body] ["ret" {:irrelevant nil}]))]]
    (doseq [backend [:reference :mutable :jvm]]
      (let [context (setup backend false change)]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"(selected IR differs|boxed ABI)"
              (evaluate (assoc-in context [:world :kernel-environments] {0 {:anchor (:environment context)}}))))))))

(deftest executable-dependency-replacement-is-rejected-even-when-selected-ir-is-unchanged
  (doseq [backend [:reference :mutable :jvm]]
    (let [context (setup backend false identity)
          ;; Existing boxed wrapper calls answer. Replace the dependency body,
          ;; while keeping the same names, params, ABI and witness.
          changed (with-meta (assoc (get-in context [:world :functions answer]) :body [:return [:imm 99]])
                             (meta (get-in context [:world :functions answer])))
          functions (assoc (get-in context [:world :functions]) answer changed)
          context (-> context (assoc-in [:world :functions] functions)
                      (assoc :session (raw/open-functions functions (get-in context [:session :bindings]) {:backend backend})))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"executable differs" (evaluate context))))))

(deftest witness-must-provide-the-actual-complete-static-closure
  (doseq [change [#(assoc % :sorryDep answer)
                  #(assoc % :missingDependencies [answer])
                  #(update % :declarations (fn [rows] (filterv (fn [r] (not= answer (:name r))) rows)))]]
    (is (thrown? clojure.lang.ExceptionInfo (evaluate (setup :reference false change))))))

(deftest structural-comparison-is-stack-safe-and-preserves-deep-differences
  (let [deep (reduce (fn [b i] ["vdecl" {:idx i} "object" {:irrelevant nil} b]) ["ret" {:irrelevant nil}] (range 5000))
        other (reduce (fn [b i] ["vdecl" {:idx i} "object" {:irrelevant nil} b]) ["ret" {:lit 7}] (range 5000))]
    (is (eval/ir-equal? deep deep))
    (is (not (eval/ir-equal? deep other)))))

(deftest fork-with-same-kernel-anchor-but-changed-dependent-ir-cannot-reuse-code
  (doseq [backend [:reference :mutable :jvm]]
    (let [context (setup backend true identity)
          first-result (evaluate context)
          saved (continue-from context first-result)
          before (get-in saved [:world :eval-const-authorizations])
          changed (update (:witness context) :declarations
                          (fn [rows] (mapv (fn [r] (if (= answer (:name r))
                                                    (assoc-in r [:ir :fdecl :body] ["ret" {:irrelevant nil}]) r)) rows)))
          fork (-> saved
                   (assoc-in [:world :kernel-environments] {999 {:anchor (:environment saved)}})
                   (assoc-in [:world :heap (:id (:environment saved)) :fields] [(json/write-str changed) (second (:fields (m/node (:world saved) (:environment saved))))]))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected IR differs" (evaluate fork)))
      (is (= before (get-in saved [:world :eval-const-authorizations])))
      (is (= 1 (:tag (m/node (:state (evaluate saved)) (:value (evaluate saved)))))))))

(deftest mixed-unit-reuses-admitted-local-dependencies-and-completed-initializers
  (let [nullary (install/bundle-catalogue (slurp "fixtures/runtime-compiled-nullary.jsonl"))
        next-name (fixtures/n "answer2")
        next-row {:kind "decl" :name next-name :sourceLocal true
                  :runtime {:role "value" :initializer nil}
                  :ir {:fdecl {:f next-name :xs [] :type "tobject" :info {}
                               :body ["vdecl" {:idx 1} "tobject" {:fap {:c answer :ys []}}
                                      ["ret" {:var {:id {:idx 1}}}]]}}}
        old-action (get-in nullary [:manifests 0 :initializationPlan :actions 0])
        next-action {:action {:kind "value" :name next-name :target next-name} :meta false}
        candidate (-> nullary
                      (assoc-in [:declarations next-name] next-row)
                      (assoc-in [:manifests 0 :requestedRoots] [next-name])
                      (assoc-in [:manifests 0 :entryPoints] [{:name next-name :boxedTarget next-name}])
                      (assoc-in [:manifests 0 :initializationPlan :actions] [old-action next-action]))
        next-witness (assoc (with-redefs [fixture candidate] (witness true)) :name next-name)]
    (doseq [backend [:reference :mutable :jvm]]
      (let [context (with-redefs [fixture nullary] (setup backend true identity))
            first-result (evaluate context)
            old-function (get-in first-result [:state :functions answer])
            saved (continue-from context first-result)
            changed (-> saved
                        (assoc-in [:world :heap (:id (:environment saved)) :fields]
                                  [(json/write-str next-witness) (bundle-text candidate)])
                        (assoc-in [:world :heap (:id (:name saved)) :fields 1] "answer2"))
            result (evaluate changed)]
        (is (= [42] (:fields (m/node (:state result) (:value result)))))
        (is (identical? old-function (get-in result [:state :functions answer])))
        (is (= :ready (get-in result [:state :globals answer :status])))
        (is (= :ready (get-in result [:state :globals next-name :status])))
        (is (= #{old-action next-action} (get-in result [:state :eval-const-authorizations :actions])))
        (let [bad (assoc-in candidate [:manifests 0 :initializationPlan :actions 0 :meta] true)
              bad-world (assoc-in changed [:world :heap (:id (:environment saved)) :fields 1] (bundle-text bad))]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"initialization action differs" (evaluate bad-world))))))))

(deftest changing-the-witness-helper-cannot-forge-environment-code-selection
  (let [context (setup :reference false identity)
        functions (assoc (get-in context [:world :functions]) witness-helper (helper (json/write-str (witness false))))
        changed (-> context (assoc-in [:world :functions] functions)
                    (assoc :session (raw/open-functions functions (get-in context [:session :bindings]) {:backend :reference})))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"executable differs" (evaluate changed)))))

(deftest original-catalogue-schema-does-not-invent-commit-provenance
  (doseq [backend [:reference :mutable :jvm]]
    (binding [*backing-catalogue* (update fixture :manifests #(mapv (fn [manifest] (dissoc manifest :leanCommit)) %))]
      (let [result (evaluate (setup backend false identity))
            [world closure] (unwrap result)]
        (is (= 42 (:value (raw/call (:session result) world fixtures/apply-answer [closure 42])))))))
  (doseq [change [(fn [m] (assoc m :leanCommit "wrong-commit"))
                  (fn [m] (assoc m :leanCommit nil))
                  (fn [m] (assoc m :leanVersion "4.33.0"))
                  (fn [m] (assoc-in m [:runtimeProfile :wordBits] 32))
                  (fn [m] (dissoc m :runtimeProfile))]]
    (binding [*backing-catalogue* (update fixture :manifests #(mapv change %))]
      (is (thrown? clojure.lang.ExceptionInfo (evaluate (setup :reference false identity))))))
  (doseq [change [(fn [w] (dissoc w :leanCommit))
                  (fn [w] (assoc w :leanCommit "wrong-commit"))]]
    (binding [*backing-catalogue* (update fixture :manifests #(mapv (fn [m] (dissoc m :leanCommit)) %))]
      (is (thrown? clojure.lang.ExceptionInfo (evaluate (setup :reference false change)))))))

(def imported-closed (fixtures/n "importedClosed"))
(defn imported-catalogue []
  (let [closed {:kind "decl" :name imported-closed :sourceLocal true :sourceModule (fixtures/n "OriginalModule")
                :runtime {:role "closed" :initializer nil}
                :ir {:fdecl {:f imported-closed :xs [] :type "tobject" :info {}
                             :body ["vdecl" {:idx 1} "tobject" {:lit {:v {:str {:v "cached"}}}}
                                    ["ret" {:var {:id {:idx 1}}}]]}}}
        original (get-in fixture [:declarations answer :ir :fdecl :body])]
    (-> fixture
        (assoc-in [:declarations imported-closed] closed)
        (assoc-in [:declarations answer :ir :fdecl :body]
                  ["vdecl" {:idx 3} "tobject" {:fap {:c imported-closed :ys []}}
                   ["dec" {:idx 3} 1 true false original]]))))
(defn missing-import-context [backend catalogue]
  (binding [*backing-catalogue* catalogue]
    (let [context (setup backend false
                         #(assoc % :declarations (mapv (fn [r] (assoc (select-keys r [:name :ir]) :sourceLocal false))
                                                       (vals (:declarations catalogue)))))
          functions (apply dissoc (get-in context [:world :functions]) (keys (:declarations fixture)))
          ;; Exporting this environment as a fresh compilation unit must never
          ;; occur: imported metadata is not source-unit admission evidence.
          world (-> (:world context) (assoc :functions functions)
                    (assoc-in [:heap (:id (:environment context)) :fields 1] "not a compiler bundle"))]
      (assoc context :world world :session (raw/open-functions functions (get-in context [:session :bindings]) {:backend backend})))))

(deftest missing-imports-link-from-canonical-catalogue-without-source-unit-receipts
  (doseq [backend [:reference :mutable :jvm]]
    (let [catalogue (imported-catalogue) context (missing-import-context backend catalogue)
          result (evaluate context) fork (evaluate context)
          [world closure] (unwrap result)
          called (raw/call (:session result) world fixtures/apply-answer [closure 42])
          authority (get-in called [:state :eval-const-authorizations])]
      (is (= 42 (:value called)))
      (is (= :ready (get-in called [:state :globals imported-closed :status])))
      (is (= "closed" (get-in authority [:imported-declarations imported-closed :runtime :role])))
      (is (empty? (:units authority)))
      (is (empty? (:declarations authority)))
      (is (empty? (:kernel-environments (:state called))))
      (is (= (set (keys (get-in result [:state :functions]))) (set (keys (get-in fork [:state :functions])))))
      (doseq [[name function] (get-in context [:world :functions])]
        (is (identical? function (get-in result [:state :functions name]))))
      (is (not (contains? (get-in context [:world :functions]) answer)))
      (is (empty? (get-in context [:world :eval-const-authorizations]))))))

(deftest imported-extension-rejects-selected-ir-drift-before-publishing-code
  (doseq [backend [:reference :mutable :jvm]]
    (let [context (missing-import-context backend (imported-catalogue))
          text (get-in context [:world :heap (:id (:environment context)) :fields 0])
          witness (json/read-str text :key-fn keyword)
          changed (update witness :declarations
                          #(mapv (fn [r] (if (= imported-closed (:name r))
                                           (assoc-in r [:ir :fdecl :body] ["ret" {:irrelevant nil}]) r)) %))
          context (assoc-in context [:world :heap (:id (:environment context)) :fields 0] (json/write-str changed))]
      (try (evaluate context) (is false "must reject")
           (catch clojure.lang.ExceptionInfo error
             (is (re-find #"selected IR differs" (.getMessage error)))
             (is (identical? (get-in context [:world :functions])
                             (get-in (ex-data error) [:checkpoint :functions])))
             (is (empty? (get-in (ex-data error) [:checkpoint :eval-const-authorizations]))))))))

(deftest failed-import-link-preserves-old-program-and-recovery-checkpoint
  (doseq [backend [:reference :mutable :jvm]]
    (let [context (missing-import-context backend (imported-catalogue))
          collision ["str" imported-closed "_ansatz_global_initializer"]
          functions (assoc (get-in context [:world :functions]) collision {:params [] :body [:return [:imm 99]]})
          changed (-> context (assoc-in [:world :functions] functions)
                      (assoc :session (raw/open-functions functions (get-in context [:session :bindings]) {:backend backend})))]
      ;; Wrapper collision is discovered inside actual catalogue lowering, after
      ;; witness validation. It must not publish a partially linked program.
      (try (evaluate changed) (is false "must reject")
           (catch clojure.lang.ExceptionInfo error
             (is (re-find #"Global initializer name collision" (.getMessage error)))
             (is (identical? functions (get-in (ex-data error) [:checkpoint :functions])))
             (is (empty? (get-in (ex-data error) [:checkpoint :eval-const-authorizations])))))
      (is (some? (:value (evaluate context)))))))

(deftest imported-link-validates-existing-dependency-identities-before-adoption
  (doseq [backend [:reference :mutable :jvm]]
    (let [context (missing-import-context backend (imported-catalogue))
          boxed (get-in fixture [:manifests 0 :entryPoints 0 :boxedTarget])
          functions (assoc (get-in context [:world :functions]) boxed {:params [1 2] :body [:return [:imm 99]]})
          context (-> context (assoc-in [:world :functions] functions)
                      (assoc :session (raw/open-functions functions (get-in context [:session :bindings]) {:backend backend})))]
      (try (evaluate context) (is false "must reject")
           (catch clojure.lang.ExceptionInfo error
             (is (re-find #"executable differs" (.getMessage error)))
             (is (identical? functions (get-in (ex-data error) [:checkpoint :functions])))
             (is (empty? (get-in (ex-data error) [:checkpoint :eval-const-authorizations]))))))))

(deftest local-source-runtime-classification-and-initializer-mapping-remain-strict
  (let [result (evaluate (setup :reference true identity))]
    (doseq [change [#(assoc-in % [:declarations answer :runtime :role] "value")
                    #(assoc-in % [:declarations answer :runtime :initializer] (fixtures/n "differentInitializer"))
                    #(assoc-in % [:declarations answer :sourceLocal] false)]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected IR differs"
            (eval/install-bundle (:state result) (change fixture)))))))

(deftest missing-initialized-import-does-not-run-its-module-initializer
  (let [initializer (fixtures/n "importedInitializer")
        base {:kind "decl" :name answer :sourceLocal true :sourceModule (fixtures/n "OriginalModule")
              :runtime {:role "initialized" :initializer initializer}
              :ir {:fdecl {:f answer :xs [] :type "object" :info {} :body ["vdecl" {:idx 1} "object" {:lit {:v {:str {:v "initializer-must-not-run"}}}} ["ret" {:var {:id {:idx 1}}}]]}}}
        catalogue (assoc fixture :declarations
                         {answer base initializer
                          {:kind "decl" :name initializer :sourceLocal true :runtime {:role "ordinary" :initializer nil}
                           :ir {:fdecl {:f initializer :xs [] :type "object" :info {} :body ["vdecl" {:idx 1} "object" {:lit {:v {:str {:v "initializer-must-not-run"}}}} ["ret" {:var {:id {:idx 1}}}]]}}}})]
    (doseq [backend [:reference :mutable :jvm]]
      (let [context (missing-import-context backend catalogue)
            text (json/read-str (get-in context [:world :heap (:id (:environment context)) :fields 0]) :key-fn keyword)
            context (assoc-in context [:world :heap (:id (:environment context)) :fields 0]
                              (json/write-str (assoc text :boxedTarget answer)))]
        (try (evaluate context) (is false "must reject uninitialized imported value")
             (catch clojure.lang.ExceptionInfo error
               (is (re-find #"initialized declaration is not ready" (.getMessage error)))
               (is (identical? (get-in context [:world :functions])
                               (get-in (ex-data error) [:checkpoint :functions])))
               (is (empty? (get-in (ex-data error) [:checkpoint :globals])))))
        (let [ready (assoc-in context [:world :globals answer] {:status :ready :value "imported-value"})
              result (evaluate ready)]
          (is (= ["imported-value"] (:fields (m/node (:state result) (:value result)))))
          (is (empty? (get-in result [:state :eval-const-authorizations :actions])))
          (is (empty? (get-in result [:state :eval-const-authorizations :units]))))))))

(defn source-import-context [backend callback change]
  (let [initial (setup backend true identity)
        admitted (evaluate initial)
        saved (continue-from initial admitted)
        module (get-in saved [:world :eval-const-authorizations :units
                              (get-in saved [:world :eval-const-authorizations :unit-digests answer])
                              :manifest :initializationPlan :module])
        selected (change (update (witness false) :declarations
                                 #(mapv (fn [r] (assoc r :sourceModule module)) %)))
        binding (eval/make-binding fixtures/exporter
                  (cond-> {:witness witness-helper :trusted-functions (get-in saved [:world :functions])}
                    callback (assoc :authorize-source-import callback)))
        world (assoc-in (:world saved) [:heap (:id (:environment saved)) :fields]
                        [(json/write-str selected) (bundle-text fixture)])
        session (raw/open-functions (:functions world) {"lean_eval_const" binding} {:backend backend})]
    (assoc saved :world world :session session)))

(deftest source-import-transitions-require-explicit-checked-authority-for-each-row
  ;; This callback MODELS installation authority. Actual source module and kernel
  ;; association checks are exercised by source-import-test, not this fixture.
  (doseq [backend [:reference :mutable :jvm]]
    (let [calls (atom [])
          callback (fn [world _ environment selected local unit]
                     (swap! calls conj (:name selected))
                     (is (m/ref? environment))
                     (is (true? (:sourceLocal local)))
                     (is (false? (:sourceLocal selected)))
                     (is (some #{(:name selected)} (:declarations unit)))
                     [(assoc world :heartbeat-allocation-offset 77) true])
          context (source-import-context backend callback identity)
          before (:eval-const-authorizations (:world context))
          result (evaluate context)
          [world closure] (unwrap result)
          called (raw/call (:session result) world fixtures/apply-answer [closure 42])]
      (is (= 42 (:value called)))
      (is (= 77 (:heartbeat-allocation-offset (:state result))))
      (is (= (count (:declarations fixture)) (count @calls)))
      (is (identical? before (:eval-const-authorizations (:state result))))
      (is (nil? (:heartbeat-allocation-offset (:world context)))))))

(deftest source-import-transition-does-not-admit-missing-or-changed-module-and-code
  (doseq [backend [:reference :mutable :jvm]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"selected IR differs"
          (evaluate (source-import-context backend nil identity))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"installation authority"
          (evaluate (source-import-context backend (fn [w & _] [w false]) identity))))
    (doseq [change [#(update % :declarations (fn [rows] (mapv (fn [r] (dissoc r :sourceModule)) rows)))
                    #(assoc-in % [:declarations 0 :sourceModule] (fixtures/n "OtherModule"))
                    #(assoc-in % [:declarations 0 :ir :fdecl :body] ["ret" {:irrelevant nil}])]]
      (let [called (atom false)]
        (is (thrown? clojure.lang.ExceptionInfo
              (evaluate (source-import-context backend
                          (fn [w & _] (reset! called true) [w true]) change))))
        (is (false? @called))))))

(defn file-import-installation [backend change-candidate change-options empty-roots?]
  (let [callback (fn [world _ _ _ _ _] [world true])
        context (source-import-context backend callback identity)
        candidate (change-candidate
                    (update fixture :declarations
                      (fn [rows] (into {} (map (fn [[n r]] [n (assoc r :sourceLocal false :sourceModule nil)])) rows))))
        [world roots] (m/allocate (if empty-roots? (:world context)
                                   (m/retain (:world context) (:name context) 1))
                                 :array 246 (if empty-roots? [] [(:name context)]))
        active (atom (:session context))
        invoke (fn [world target args]
                 (let [result (raw/call @active world target args)]
                   (reset! active (:session result)) [(:state result) (:value result)]))
        options (change-options {:witness witness-helper :trusted-functions (:functions world)
                                 :authorize-source-import callback})]
    {:before world :context context :roots roots
     :run #(eval/install-file-bundle {:invoke invoke} world (:environment context) roots
                                     (bundle-text candidate) options)}))

(deftest final-file-installation-uses-actual-root-witnesses-for-imported-source-code
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [before context roots run]} (file-import-installation backend identity identity false)
          installed (run) world (:world installed)]
      (is (= (:functions before) (:functions world)))
      (is (identical? (get-in before [:eval-const-authorizations :declarations answer])
                      (get-in world [:eval-const-authorizations :declarations answer])))
      (is (= 1 (:rc (m/node world (:environment context)))))
      (is (= 2 (:rc (m/node world (:name context)))))
      (is (= 1 (:rc (m/node world roots))))
      (is (empty? (:pending-local-initializers installed))))))

(deftest final-file-installation-cannot-infer-missing-or-contradictory-witness-authority
  (doseq [[candidate options empty-roots?]
          [[identity #(dissoc % :witness) false]
           [identity identity true]
           [#(assoc-in % [:declarations answer :ir :fdecl :body] ["ret" {:irrelevant nil}]) identity false]
           [#(assoc-in % [:declarations answer :sourceModule] (fixtures/n "OtherModule")) identity false]
           [identity #(dissoc % :authorize-source-import) false]]]
    (let [{:keys [run]} (file-import-installation :reference candidate options empty-roots?)]
      (is (thrown? clojure.lang.ExceptionInfo (run))))))
