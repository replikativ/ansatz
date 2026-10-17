(ns prototype.eval-const
  "Pinned evalConstCore bridge. Actual guest interpreter lookup witnesses, exact
   IR comparison and immutable function identities authorize existing code.
   Kernel-map identity and declaration names alone are never code authority."
  (:require [clojure.data.json :as json]
            [clojure.string :as str]
            [prototype.machine :as m]
            [prototype.kernel-bridge :as bridge]
            [prototype.interop-codec :as codec]
            [prototype.guest-json :as guest-json]
            [prototype.ir-value :as ir-value]
            [prototype.import-ir :as ir]
            [prototype.program-install :as install]
            [prototype.initialization :as initialization]
            [prototype.runtime-prim :as prim]
            [prototype.walk :as walk])
  (:import [ansatz.kernel Name]
           [java.nio.charset StandardCharsets]
           [java.security MessageDigest]))

(def signature
  {:params [{:ty "erased" :borrow false} {:ty "object" :borrow true}
            {:ty "object" :borrow true} {:ty "tobject" :borrow true}]
   :return-type "object"})

(defn- structured-name [^Name name]
  (loop [name name parts []]
    (if (.isAnonymous name)
      (reduce (fn [prefix [kind payload]] [kind prefix payload]) ["anonymous"] (rseq parts))
      (recur (.-prefix name) (conj parts (if (.isStr name) ["str" (.-str name)]
                                           ["num" (str (.-num name))]))))))

(defn ir-equal?
  "Stack-safe exact JSON structural equality, including ABI/borrow annotations."
  [a b]
  (loop [pending [[a b]]]
    (if (empty? pending) true
      (let [[a b] (peek pending) pending (pop pending)]
        (cond
          (identical? a b) (recur pending)
          (map? a) (if (and (map? b) (= (set (keys a)) (set (keys b))))
                     (recur (into pending (map (fn [[k v]] [v (get b k)]) a))) false)
          (vector? a) (if (and (vector? b) (= (count a) (count b)))
                        (recur (into pending (map vector a b))) false)
          (or (map? b) (vector? b)) false
          (= a b) (recur pending)
          :else false)))))

(defn- row [catalogue name]
  (if-let [read-declaration (:read-declaration catalogue)] (read-declaration name)
    (get-in catalogue [:declarations name])))
(defn- decl [row] (or (get-in row [:ir :fdecl]) (get-in row [:ir :extern])))
(defn- raw-dependencies [row]
  (into #{} (keep (fn [x] (when (map? x) (or (get-in x [:fap :c]) (get-in x [:pap :c])))))
        (walk/forms (get-in row [:ir :fdecl :body]))))
(defn- executable-dependencies [f]
  (into (set (:runtime-dependencies f))
        (keep (fn [x]
                (when (vector? x)
                  (case (first x)
                    :direct (second x)
                    :closure (when (= 3 (count x)) (second x))
                    (:global :begin-init) (nth x 2)
                    nil))))
        (walk/forms (:body f))))

(defn- validate-witness [w target]
    (when-not (and (= "lean-eval-const-witness/1" (:schema w))
                   (= "RuntimeCompileShim.exportEvalConstWitness" (:producer w))
                   (= (get prim/pinned-build "lean_get_githash") (:leanCommit w))
                   (= {:target "x86_64-unknown-linux-gnu" :wordBits 64} (:runtimeProfile w))
                   (= target (:name w)) (vector? (:declarations w))
                   (vector? (:missingDependencies w)) (empty? (:missingDependencies w))
                   (nil? (:sorryDep w)))
      (m/fail "Invalid, missing or sorry-dependent evalConst interpreter witness" {:name target}))
    (let [rows (:declarations w) by-name (into {} (map (juxt :name identity)) rows)]
      (when-not (and (= (count rows) (count by-name)) (get by-name target)
                     (get by-name (:boxedTarget w)))
        (m/fail "Incomplete evalConst witness roots" {:name target}))
      (let [base (decl (get by-name target)) chosen (decl (get by-name (:boxedTarget w)))
            object-types #{"object" "tobject" "tagged" "erased" "void"}]
        (when-not (and (= (count (:xs base)) (count (:xs chosen)))
                       (if (empty? (:xs base)) (= target (:boxedTarget w))
                         (and (every? #(and (contains? object-types (:ty %)) (false? (:borrow %))) (:xs chosen))
                              (contains? object-types (:type chosen)))))
          (m/fail "evalConst selected entry lacks a faithful boxed ABI" {:name target})))
      (doseq [r rows]
        (when-not (and (boolean? (:sourceLocal r)) (= (:name r) (:f (decl r)))
                       (= 1 (count (:ir r))) (decl r))
          (m/fail "Invalid evalConst witnessed declaration" {:name (:name r)}))
        (doseq [dependency (raw-dependencies r)]
          (when-not (contains? by-name dependency)
            (m/fail "Incomplete evalConst witness dependency closure" {:name (:name r) :dependency dependency}))))
      (assoc w :rows by-name)))

(defn- witness! [value target]
  (validate-witness (json/read-str value :key-fn keyword) target))

(defn- check-function-closure! [world registry roots]
  (loop [pending (vec roots) seen {}]
    (if-let [name (peek pending)]
      (if (contains? seen name) (recur (pop pending) seen)
        (let [actual (get-in world [:functions name]) expected (get registry name)]
          (when-not (and actual expected (identical? actual expected))
            (m/fail "evalConst executable differs from authorized program" {:name name}))
          (recur (into (pop pending) (executable-dependencies actual)) (assoc seen name expected))))
      seen)))

(defn- source-transition? [world options local r]
  (let [name (:name r) proof (get (::source-transitions options) name)
        unit (get-in world [:eval-const-authorizations :units
                           (get-in world [:eval-const-authorizations :unit-digests name])])]
    (and proof (false? (:sourceLocal r))
         (identical? local (:local proof)) (identical? unit (:unit proof))
         (ir-equal? (:ir r) (:ir (:witness proof)))
         (or (nil? (:sourceModule r))
             (= (:sourceModule r) (:sourceModule (:witness proof)))))))

(defn- authorize-source-transitions [world context environment witness options]
  ;; Evidence is scoped to this actual guest witness and this invocation. Never
  ;; mutate a local source receipt into imported provenance for unrelated forks.
  (reduce
    (fn [[world options] r]
      (let [name (:name r) local (get-in world [:eval-const-authorizations :declarations name])]
        (if (and local (true? (:sourceLocal local)) (false? (:sourceLocal r))
                 (:authorize-source-import options))
          (let [module (:sourceModule r)
                unit (get-in world [:eval-const-authorizations :units
                                   (get-in world [:eval-const-authorizations :unit-digests name])])]
            (when-not (and (vector? module) unit
                           (= module (get-in unit [:manifest :initializationPlan :module]))
                           (ir-equal? (:ir local) (:ir r))
                           (or (not (contains? r :runtime))
                               (ir-equal? (:runtime local) (:runtime r))))
              (m/fail "Source import witness differs from admitted source unit" {:name name}))
            (let [registry (merge (:trusted-functions options)
                                  (get-in world [:eval-const-authorizations :functions]))
                  context (assoc context :check-trusted-functions!
                                 (fn [world roots] (check-function-closure! world registry roots)))
                  [world authorized?] ((:authorize-source-import options)
                                      world context environment r local unit)]
              (when-not (true? authorized?)
                (m/fail "Source import lacks checked module installation authority" {:name name}))
              [world (assoc-in options [::source-transitions name]
                               {:local local :unit unit :witness r})]))
          [world options])))
    [world (dissoc options ::source-transitions)] (vals (:rows witness))))

(defn- existing-row! [world options backing-valid r]
  (let [name (:name r) authority (:eval-const-authorizations world)
        local (get-in authority [:declarations name])
        imported (when-not local
                   (or (get-in authority [:imported-declarations name])
                       (when (contains? (:trusted-functions options) name)
                         (force backing-valid) (row (:catalogue options) name))))
        expected (or local imported)]
    (when local
      (let [digest (get-in authority [:unit-digests name]) unit (get-in authority [:units digest])]
        (when-not (and (string? digest) (re-matches #"[0-9a-f]{64}" digest)
                       unit (some #{name} (:declarations unit)))
          (m/fail "Admitted source declaration lacks unit digest authority" {:name name}))))
    (when-not (and expected (ir-equal? (:ir r) (:ir expected))
                   (or (not (contains? r :runtime)) (ir-equal? (:runtime r) (:runtime expected)))
                   ;; Previously admitted local code cannot silently become an
                   ;; imported declaration, or vice versa, in another fork.
                   (if local
                     (or (= (:sourceLocal r) (:sourceLocal local))
                         (source-transition? world options local r))
                     (false? (:sourceLocal r))))
      (m/fail "evalConst selected IR differs from authorized declaration" {:name name}))
    true))

(defn- authorize-existing! [world options backing-valid witness]
  (doseq [r (vals (:rows witness))]
    (existing-row! world options backing-valid r))
  (let [registry (merge (:trusted-functions options) (get-in world [:eval-const-authorizations :functions]))]
    (check-function-closure! world registry (keys (:rows witness))))
  ;; Regular init declarations must already have been initialized by their
  ;; module or admitted local plan. Never reexecute them through evalConst.
  (doseq [name [(:name witness)] :let [f (get-in world [:functions name])]
          :when (:runtime-initializer f)]
    (when-not (= :ready (get-in world [:globals name :status]))
      (m/fail "evalConst initialized declaration is not ready" {:name name})))
  (:boxedTarget witness))

(defn- invoke-string [invoke world helper args]
  (let [[world value] (invoke world helper args)
        text (codec/decode world [:io :string] value)]
    [(m/release world value 1) text]))

(defn- invoke-witness [invoke world helper args options target]
  (case (get options :witness-format :json-string)
    :json-string
    (let [[world text] (invoke-string invoke world helper args)]
      [world (witness! text target)])
    (:guest-json :typed-ir)
    (let [[world value] (invoke world helper args)]
      (try
        (let [node (when (m/ref? value) (m/node world value))]
          ;; Both object transports borrow their entire tree while the owned
          ;; IO wrapper remains alive; neither skips witness validation.
          (when (= 1 (:tag node)) (codec/decode world [:io :unit] value))
          (when-not (and (= :ctor (:kind node)) (= 0 (:tag node))
                         (bridge/constructor-layout? node 1 0))
            (m/fail (if (= :typed-ir (:witness-format options))
                      "Invalid typed IR witness IO result" "Invalid guest Json witness IO result") {}))
          (let [w (if (= :typed-ir (:witness-format options))
                    (ir-value/project-witness world (first (:fields node)))
                    (guest-json/project world (first (:fields node)) {:key-fn keyword}))
                witness (validate-witness w target)]
            [(m/release world value 1) witness]))
        (catch Throwable cause
          ;; Parent control restoration need not leave the child IO value in
          ;; :result. Preserve its exact owner and matching snapshot explicitly.
          ;; Any :guest-error field is borrowed from this retained IO wrapper.
          (throw (ex-info (or (.getMessage cause) "Guest Json witness failed")
                         (merge (ex-data cause) {:checkpoint world :witness-io-result value}) cause)))))
    (m/fail "Invalid evalConst witness format" {:witness-format (:witness-format options)})))

(defn- backing-validation [options]
  (delay
    (when-not (seq (get-in options [:catalogue :manifests]))
      (m/fail "evalConst catalogue lacks pinned provenance" {}))
    ;; Export.lean's lean-ir-probe/1 manifests originally specified version and
    ;; runtime profile only. An absent commit is not build provenance. Imported
    ;; code authority remains the explicit host catalogue/trusted-functions
    ;; capability, mandatory pinned guest witness, exact IR/ABI equality and
    ;; identity of the entire executable closure. Never invent a legacy commit.
    (doseq [manifest (get-in options [:catalogue :manifests])]
      (ir/validate-manifest! manifest)
      (when-not (and (or (not (contains? manifest :leanCommit))
                              (= (get prim/pinned-build "lean_get_githash") (:leanCommit manifest)))
                     (= {:target "x86_64-unknown-linux-gnu" :wordBits 64} (:runtimeProfile manifest)))
        (m/fail "evalConst catalogue profile mismatch" {})))))

(defn- bundle-digest [bundle candidate]
  (let [rows (concat (:manifests candidate)
                     (map #(row candidate %) (sort-by pr-str (keys (:declarations candidate)))))
        text (if (string? bundle) bundle (str/join "\n" (map json/write-str rows)))]
    (apply str (map #(format "%02x" (bit-and 255 %))
                   (.digest (MessageDigest/getInstance "SHA-256") (.getBytes ^String text StandardCharsets/UTF_8))))))

(defn- action-marker [{:keys [action]}]
  (if (= "io" (:kind action)) [::initialization/io (:name action)] (:name action)))
(defn- action-target [world {:keys [action]}]
  (case (:kind action)
    "io" ["str" (:name action) "_ansatz_io_initializer"]
    "initialize" (or (get-in world [:functions (:name action) :init-target])
                     (m/fail "Admitted initialized value lacks wrapper" {:action action}))
    "value" (:name action)
    (m/fail "Unknown admitted initialization action" {:action action})))
(defn- code-registry [world options]
  (merge (:trusted-functions options) (get-in world [:eval-const-authorizations :functions])))

(defn completion-evidence
  "Mint completion evidence only for an admitted action whose exact initializer
   code is still present and whose actual guest ready marker already exists.
   Local macro registration is not completion of its future import initializer."
  [world installation planned]
  (let [digest (:unit-digest installation)
        unit (get-in world [:eval-const-authorizations :units digest])
        target (action-target world planned)
        function (get-in world [:functions target])
        marker (action-marker planned)
        ready (get-in world [:globals marker])]
    (when-not (and unit (some #{planned} (:actions unit)) (= :ready (:status ready)) function)
      (m/fail "Initialization completion requires admitted action and actual ready marker" {:action (:action planned)}))
    (check-function-closure! world (get-in world [:eval-const-authorizations :functions]) [target])
    {:unit-digest digest :planned planned :call-target target :function function
     :marker marker :ready-entry ready}))

(defn- evidence-valid! [world evidence]
  (let [{:keys [unit-digest planned call-target function marker ready-entry]} evidence
        unit (get-in world [:eval-const-authorizations :units unit-digest])]
    (when-not (and unit (some #{planned} (:actions unit))
                   (= marker (action-marker planned)) (= call-target (action-target world planned))
                   (= :ready (:status ready-entry))
                   (identical? function (get-in world [:functions call-target]))
                   (identical? ready-entry (get-in world [:globals marker])))
      (m/fail "Invalid initialization completion evidence" {:action (:action planned)}))
    (check-function-closure! world (get-in world [:eval-const-authorizations :functions]) [call-target])
    evidence))

(defn- record-evidence [world evidence]
  (evidence-valid! world evidence)
  (-> world (update-in [:eval-const-authorizations :completed-actions] (fnil conj #{}) (:planned evidence))
      (assoc-in [:eval-const-authorizations :completion-evidence (:planned evidence)] evidence)))

(defn- pending-actions [world plan]
  (into [] (keep (fn [planned]
                  (let [entry (get-in world [:globals (action-marker planned)])
                        evidence (get-in world [:eval-const-authorizations :completion-evidence planned])]
                    (when (and entry (not= :ready (:status entry)))
                      (m/fail "Initializer has an incomplete prior guest execution" {:action (:action planned)}))
                    (if evidence (do (evidence-valid! world evidence) nil)
                      (assoc planned :call-target (action-target world planned)
                                     :completion-key (:action planned)))))) (:actions plan)))

(declare run-initializers)

(defn- canonical-imported-runtime [world candidate]
  ;; Both classification caches are non-persistent EnvExtensions (pinned Lean
  ;; Compiler/ClosedTermCache.lean:22–38 and
  ;; Compiler/LCNF/SimpleGroundExpr.lean:87–99,129–130). exportCompiled can
  ;; therefore report an imported zero-argument closed/ground constant as a value.
  ;; Preserve its admitted classification, never reclassify executable state.
  ;; This exception belongs only to source-bundle reuse, not witness checking.
  (-> candidate
      (assoc :declarations
      (into {} (map (fn [[name _]]
                      (let [selected (row candidate name)
                            canonical (get-in world [:eval-const-authorizations :imported-declarations name])]
                        [name (if (and (contains? (:functions world) name)
                                       (not (get-in world [:eval-const-authorizations :declarations name]))
                                       (false? (:sourceLocal selected))
                                       (= {:role "value" :initializer nil} (:runtime selected))
                                       (contains? #{{:role "closed" :initializer nil}
                                                    {:role "ground" :initializer nil}} (:runtime canonical))
                                       (contains? (:ir selected) :fdecl)
                                       (empty? (:xs (decl selected)))
                                       (ir-equal? (:ir selected) (:ir canonical)))
                                (assoc selected :runtime (:runtime canonical))
                                selected)]))) (:declarations candidate)))
      (dissoc :read-declaration)))

(defn install-bundle
  "Admit a final file/compiled unit without replaying source-time effects.
   Exact admitted rows, source unit digests, executable identities and prior
   action metadata authorize reuse; the underlying installer remains strict.
   Default installs code and returns ordered :pending-local-initializers only.
   :initialize? true explicitly runs future module initialization after admission.
   :completion-evidence accepts only ready-marker/function-identity receipts;
   a bare :completed-local-actions set is rejected.
   CONTEXT may supply :install-compiled! for a live host callback; otherwise the
   world must be idle. :invoke is used only by explicit initialization."
  ([world bundle] (install-bundle {} world bundle {}))
  ([world bundle options] (install-bundle {} world bundle options))
  ([context world bundle options]
   (when (seq (:completed-local-actions options))
     (m/fail "Source action completion requires explicit evidence, not an action set" {}))
   (let [original-candidate (install/bundle-catalogue bundle)
         candidate (canonical-imported-runtime world original-candidate)
         _ (when-not (= 1 (count (:manifests candidate))) (m/fail "Expected one source unit manifest" {}))
         manifest (first (:manifests candidate))
         _ (ir/validate-manifest! manifest)
         plan (:initializationPlan manifest)
         _ (when-not (and (= "RuntimeCompileShim.exportCompiled" (:producer manifest))
                          (= (get prim/pinned-build "lean_get_githash") (:leanCommit manifest))
                          (= {:target "x86_64-unknown-linux-gnu" :wordBits 64} (:runtimeProfile manifest))
                          (= "all-local-declarations" (:initializationPlanScope manifest))
                          (= "lean-init-plan/1" (:schema plan)) (false? (:moduleSystem plan))
                          (vector? (:actions plan)) (vector? (:requestedRoots manifest))
                          (vector? (:entryPoints manifest)) (empty? (:missingDependencies manifest)))
             (m/fail "Unsupported/incomplete source unit or initialization phases" {}))
         old (:functions world)
         ;; This producer exports the actual selected static IR closure. A
         ;; missing old callee is not permission to substitute a same-named
         ;; executable from a different environment or fork.
         _ (doseq [name (keys (:declarations candidate))
                   :let [r (row candidate name)]
                   dependency (raw-dependencies r)]
             (when-not (= "decl" (:kind (row candidate dependency)))
               (m/fail "Source unit omits selected dependency IR" {:name name :dependency dependency})))
         backing-valid (or (::backing-validation options) (backing-validation options))
         reused (into [] (keep (fn [name]
                                (let [r (row candidate name)]
                                  (when (contains? old name)
                                    (when-not (= "decl" (:kind r))
                                      (m/fail "Existing source dependency lacks actual IR" {:name name}))
                                    (existing-row! world options backing-valid r) name))))
                      (keys (:declarations candidate)))
         _ (check-function-closure! world (code-registry world options) reused)
         _ (doseq [{:keys [action meta] :as planned} (:actions plan)]
             (when-not (and (boolean? meta) (map? action)) (m/fail "Invalid source initialization action" {}))
             (when (and (contains? old (:name action))
                        (not (contains? (get-in world [:eval-const-authorizations :actions] #{}) planned)))
               (m/fail "Repeated evalConst initialization action differs from admitted unit" {:action action})))
         _ (when-not (= (count (:actions plan)) (count (set (map :action (:actions plan)))))
             (m/fail "Duplicate source initialization action" {}))
         entries (:entryPoints manifest)
         _ (when-not (and (= (count entries) (count (set (map :name entries))))
                          (= (count (:requestedRoots manifest)) (count (set (:requestedRoots manifest))))
                          (= (set (:requestedRoots manifest)) (set (map :name entries))))
             (m/fail "Invalid source entrypoint roots" {}))
         boxed-for (fn [name] (let [boxed ["str" name "_boxed"]]
                               (if (= "decl" (:kind (row candidate boxed))) boxed name)))
         _ (doseq [{:keys [name boxedTarget]} entries]
             (when-not (and (= boxedTarget (boxed-for name))
                            (= "decl" (:kind (row candidate name)))
                            (= "decl" (:kind (row candidate boxedTarget)))
                            (= (count (:xs (decl (row candidate name))))
                               (count (:xs (decl (row candidate boxedTarget))))))
               (m/fail "Invalid source boxed entrypoint" {:name name})))
         declarations (into {} (map (fn [name]
                                      (let [r (row candidate name)]
                                        [name (if (contains? old name) (assoc r :sourceLocal false) r)])))
                            (keys (:declarations candidate)))
         new-roots (into [] (keep (fn [[name r]]
                                   (when (and (= "decl" (:kind r)) (:sourceLocal r) (not (contains? old name))) name))) declarations)
         new-actions (filterv #(not (contains? (get-in world [:eval-const-authorizations :actions] #{}) %)) (:actions plan))
         transformed (-> candidate (assoc :declarations declarations) (dissoc :read-declaration)
                         (assoc :manifests [(-> manifest
                                               (assoc :requestedRoots new-roots
                                                      :entryPoints (mapv (fn [n] {:name n :boxedTarget (boxed-for n)}) new-roots))
                                               (assoc-in [:initializationPlan :actions] new-actions))]))
         install-options (dissoc options :witness :witness-format :trusted-functions :initialize? :completion-evidence
                                 :completed-local-actions ::backing-validation)
         [world installed]
         (if (seq new-roots)
           (if-let [install! (:install-compiled! context)] (install! world transformed install-options)
             (let [result (install/install world transformed install-options)] [(:world result) (dissoc result :world)]))
           (do (when (seq new-actions) (m/fail "Source action has no admissible local code" {}))
               [world {:new-functions {}}]))
         source-rows (into {} (keep (fn [[name _]]
                                     (when-let [r (or (row candidate name) (row (:catalogue options) name))]
                                       (when (= "decl" (:kind r)) [name r])))) (:new-functions installed))
         digest (bundle-digest bundle original-candidate)
         world (-> world
                   (assoc-in [:eval-const-authorizations :units digest]
                             {:manifest manifest
                              :declarations (vec (distinct (concat (get-in world [:eval-const-authorizations :units digest :declarations])
                                                                   (keys source-rows))))
                              :actions (:actions plan)})
                   (update-in [:eval-const-authorizations :unit-digests] merge (zipmap (keys source-rows) (repeat digest)))
                   (update-in [:eval-const-authorizations :functions] merge (:new-functions installed))
                   (update-in [:eval-const-authorizations :declarations] merge source-rows)
                   ;; Admission is deliberately distinct from completion.
                   (update-in [:eval-const-authorizations :actions] (fnil into #{}) (:actions plan)))
         reachable (check-function-closure! world (code-registry world options)
                                            (concat (keys (:new-functions installed))
                                                    (map #(action-target world %) (:actions plan))
                                                    (map :boxedTarget entries)))
         world (update-in world [:eval-const-authorizations :functions] merge reachable)
         world (reduce record-evidence world (:completion-evidence options))
         _ (doseq [{:keys [name boxedTarget]} entries]
             (when-not (and (contains? (:functions world) name) (contains? (:functions world) boxedTarget))
               (m/fail "Source entrypoint has no admitted executable code" {:name name})))
         result {:world world :unit-digest digest :manifest manifest :initialization-plan plan
                 :boxed-entrypoints (into {} (map (juxt :name :boxedTarget)) entries)
                 :new-functions (:new-functions installed)
                 :pending-local-initializers (pending-actions world plan)}]
     (if (:initialize? options)
       (let [world (run-initializers context world result)]
         (assoc result :world world :pending-local-initializers (pending-actions world plan))) result))))

(defn run-initializers
  "Explicitly simulate loading the admitted classic module. Runs ordered future
   actions once, records only actual ready-marker completion evidence and leaves
   an entered guard on failure. Never retry a partially failed world as clean.
   CONTEXT :invoke [world target []] must preserve/adopt its session and return
   [world value]. No runner state or side effects live outside the guest world."
  [context world installation]
  (let [digest (:unit-digest installation)
        unit (get-in world [:eval-const-authorizations :units digest])
        plan (:initialization-plan installation)
        _ (when-not (and unit (ir-equal? (:initializationPlan (:manifest unit)) plan))
            (m/fail "Initializer operation differs from admitted source plan" {}))
        status (get-in world [:eval-const-authorizations :initializations digest :status])]
    (cond
      (= status :ready) (do (doseq [p (:actions plan)] (evidence-valid! world (get-in world [:eval-const-authorizations :completion-evidence p]))) world)
      status (m/fail "Cannot retry a partially entered module initializer" {:unit-digest digest :status status})
      :else
      (let [invoke (or (:invoke context) (m/fail "Explicit source initialization requires an invocation context" {}))
            previous (select-keys world [:initializing?])
            world (-> world (assoc :initializing? true)
                      (assoc-in [:eval-const-authorizations :initializations digest] {:status :initializing :next-action 0}))
            world (reduce
                   (fn [state [index planned]]
                     (let [progress (volatile! state)]
                       (try
                         (let [evidence (get-in state [:eval-const-authorizations :completion-evidence planned])
                               next-state
                               (if evidence
                                 (do (evidence-valid! state evidence) state)
                                 (let [target (action-target state planned)
                                       _ (check-function-closure! state (get-in state [:eval-const-authorizations :functions]) [target])
                                       marker (get-in state [:globals (action-marker planned)])
                                       _ (when (and marker (not= :ready (:status marker)))
                                           (m/fail "Initializer has incomplete prior state" {:action (:action planned)}))
                                       [state value] (if (= :ready (:status marker)) [state nil] (invoke state target []))
                                       _ (vreset! progress state)
                                       state (if (nil? value) state (m/release state value 1))
                                       _ (vreset! progress state)
                                       proof (completion-evidence state installation planned)]
                                   (record-evidence state proof)))]
                           (assoc-in next-state [:eval-const-authorizations :initializations digest :next-action] (inc index)))
                         (catch Throwable cause
                           ;; A failed partial world is diagnostic state, never a
                           ;; clean checkpoint from which effects may be retried.
                           (throw (ex-info (or (.getMessage cause) "Module initializer failed")
                                           (assoc (ex-data cause) :module-action planned
                                                  :checkpoint (or (:checkpoint (ex-data cause)) @progress)) cause))))))
                   world (map-indexed vector (:actions plan)))
            world (assoc-in world [:eval-const-authorizations :initializations digest :status] :ready)]
        (merge (dissoc world :initializing?) previous)))))

(defn install-file-bundle
  "Install actual guest file output. Opted-in source imports additionally require
   actual interpreter witnesses from the returned Environment for the original
   borrowed guest root Names. Proofs are invocation-local; bundle rows cannot
   assert their own imported module provenance. Default installation stays strict.
   CONTEXT supplies :invoke; :witness names the trusted guest witness helper."
  [context world environment roots bundle options]
  (if-not (:authorize-source-import options) (install-bundle world bundle options)
    (let [candidate (install/bundle-catalogue bundle)
          transitions (into #{} (keep (fn [[name r]]
                                       (when (and (false? (:sourceLocal r))
                                                  (true? (get-in world [:eval-const-authorizations :declarations name :sourceLocal])))
                                         name))) (:declarations candidate))]
      (if (empty? transitions) (install-bundle world bundle options)
        (let [helper (:witness options)
              _ (when-not (vector? helper) (m/fail "Source file imports require an actual guest interpreter witness" {}))
              _ (check-function-closure! world (code-registry world options) [helper])
              root-node (when (m/ref? roots) (m/node world roots))
              _ (when-not (= :array (:kind root-node)) (m/fail "Source file witness roots must be a guest array" {}))
              [world proofs]
              (reduce
                (fn [[world proofs] name]
                  (let [target (structured-name (bridge/project-name world name))
                        [world witness] (invoke-witness (:invoke context)
                                       (-> world (m/retain environment 1) (m/retain name 1))
                                       helper [environment name m/erased] options target)
                        ;; Only installation transitions present in this bundle
                        ;; need source receipts; every candidate match is exact.
                        witness (update witness :rows select-keys transitions)
                        _ (doseq [[n r] (:rows witness)]
                            (let [exported (row candidate n)]
                              (when-not (and (= (:sourceLocal exported) (:sourceLocal r))
                                             (ir-equal? (:ir exported) (:ir r)))
                                (m/fail "File output differs from actual interpreter import witness" {:name n}))))
                        [world scoped] (authorize-source-transitions world context environment witness options)]
                    [world (merge proofs (::source-transitions scoped))]))
                [world {}] (:fields root-node))
              _ (when-not (= transitions (set (keys proofs)))
                  (m/fail "File source imports lack complete actual interpreter witnesses" {:names (vec transitions)}))]
          (install-bundle world bundle (assoc options ::source-transitions proofs)))))))

(defn- link-imported [context world options backing-valid witness]
  (force backing-valid)
  (let [catalogue (:catalogue options)
        rows (into {} (map (fn [[name selected]]
                             (let [canonical (row catalogue name)]
                               (when-not (and (false? (:sourceLocal selected))
                                              (not (get-in world [:eval-const-authorizations :declarations name]))
                                              (= "decl" (:kind canonical))
                                              (ir-equal? (:ir selected) (:ir canonical))
                                              (or (not (contains? selected :runtime))
                                                  (ir-equal? (:runtime selected) (:runtime canonical))))
                                 (m/fail "evalConst selected IR differs from authorized declaration" {:name name}))
                               [name canonical]))) (:rows witness))
        validate! (fn [next-world new-functions]
                    (check-function-closure! next-world
                                             (merge (code-registry world options) new-functions)
                                             (keys rows))
                    ;; A regular initialized value is not permission to run
                    ;; its initializer again through the interpreter.
                    (doseq [name [(:name witness)]
                            :when (get-in next-world [:functions name :runtime-initializer])]
                      (when-not (= :ready (get-in next-world [:globals name :status]))
                        (m/fail "evalConst initialized declaration is not ready" {:name name}))))
        link! (or (:link-trusted! context)
                  (m/fail "Imported evalConst requires a scoped trusted catalogue linker" {}))
        [world new-functions] (link! world catalogue (vec (keys rows)) validate!)
        world (-> world
                  (update-in [:eval-const-authorizations :functions] merge new-functions)
                  (update-in [:eval-const-authorizations :imported-declarations] merge rows)
                  (assoc-in [:eval-const-authorizations :imported-catalogue-manifests] (:manifests catalogue)))]
    [world (authorize-existing! world options backing-valid witness)]))

(defn- install-new [context world environment name options backing-valid witness exporter]
  (let [invoke (:invoke context)
        world (-> world (m/retain environment 1) (m/retain name 1))
        [world roots] (m/allocate world :array 246 [name])
        _ (when witness (check-function-closure! world (code-registry world options) [exporter]))
        [world exported] (invoke-string invoke world exporter [environment roots m/erased])
        candidate (install/bundle-catalogue exported)
        _ (when witness
            (doseq [[name selected] (:rows witness)]
              (when-not (ir-equal? (:ir selected) (:ir (row candidate name)))
                (m/fail "Compiled bundle differs from interpreter-selected IR" {:name name}))))
        result (install-bundle context world exported (assoc options ::backing-validation backing-valid))
        world (:world result)]
    (when witness (authorize-existing! world options backing-valid witness))
    [world (get (:boxed-entrypoints result) (structured-name (bridge/project-name world name)))]))

(defn make-binding
  "EXPORTER is the owned guest RuntimeCompileShim.exportCompiled helper.
   :witness names the selected trusted witness helper (owned Environment,Name,
   IO world). :witness-format defaults :json-string; :guest-json and :typed-ir
   explicitly select object transports with the same complete authority checks.
   :witness-format :guest-json selects an owned IO Json helper instead of the
   default :json-string transport; both use the same complete witness validator.
   Existing/imported resolution additionally requires :trusted-functions and
   :catalogue from the pinned linked runtime. Missing all-imported closures link
   from this explicit trusted catalogue, preserving canonical global roles;
   they receive imported provenance, never source-unit initializer receipts.
   Snapshot-local admitted units and imported identities live in
   :eval-const-authorizations. Actual static dependencies are checked too.
   No checked-kernel association is needed while finalizing imported extensions."
  ([exporter] (make-binding exporter {}))
  ([exporter options]
   (when-not (contains? #{:json-string :guest-json :typed-ir} (get options :witness-format :json-string))
     (m/fail "Invalid evalConst witness format" {:witness-format (:witness-format options)}))
   (let [backing-valid (backing-validation options)]
     {:signature signature
      :handler
      (fn [context world [_ environment _opts name]]
        (let [target (structured-name (bridge/project-name world name))
              [world witness]
              (if-let [helper (:witness options)]
                (let [_ (check-function-closure! world (merge (:trusted-functions options)
                                                                (get-in world [:eval-const-authorizations :functions])) [helper])
                      world (-> world (m/retain environment 1) (m/retain name 1))
                      [world witness] (invoke-witness (:invoke context) world helper
                                        [environment name m/erased] options target)]
                  [world witness]) [world nil])
              [world options] (authorize-source-transitions world context environment witness options)
              [world boxed]
              (cond
                (and witness (every? #(false? (:sourceLocal %)) (vals (:rows witness)))
                     (not (every? #(contains? (:functions world) %) (keys (:rows witness)))))
                (link-imported context world options backing-valid witness)
                (and witness (contains? (:functions world) target))
                [world (authorize-existing! world options backing-valid witness)]
                :else (install-new context world environment name options backing-valid witness exporter))
              function (get-in world [:functions boxed])
              _ (when-not function (m/fail "Compiled evalConst root missing from actual environment" {:name target}))
              [world value]
              (if (seq (:params function))
                (m/expr world [:closure boxed []])
                (let [[state value] ((:invoke context) world boxed [])
                      type (or (get-in (meta function) [:runtime-signature :return-type])
                               (:type (decl (or (get-in witness [:rows boxed])
                                                (row (:catalogue options) boxed)))))]
                  (if (contains? #{"uint8" "uint16" "uint32" "uint64" "usize" "float" "float32"} type)
                    (m/box-value state type value) [state value])))]
          (m/allocate world :ctor 1 [value])))})))
