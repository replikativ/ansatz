(ns prototype.reconstruction-runtime-test
  "Scoped issued reconstruction with genuine raw evalConst transport and Java
   checking on every backend. Compiler/publication/frontend/getter bodies are
   explicit models; native imported macro acceptance is a separate experiment."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [prototype.resident-source :as resident-source]
            [prototype.eval-const :as eval]
            [prototype.runtime-prim :as prim]
            [prototype.resident-init-prefix :as sut]
            [prototype.resident-init-import-test :as staged]
            [prototype.resident-frontend :as resident]
            [prototype.source-import-test :as publication]
            [prototype.source-import :as source]
            [prototype.module-import :as imports]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]
            [prototype.kernel-bridge :as bridge]
            [prototype.imported-kernel :as imported]
            [prototype.kernel-bridge-test :as guest]
            [prototype.guest-encoding :as encoding]
            [prototype.guest-encoding-test :as encoding-fixture]
            [prototype.raw-inductive-test :as generation]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel Env Name]))

(def limits {:max-constants 100 :name-limits {:max-nodes 64 :max-chars 1024}})
(defn with-original [backend f]
  (staged/with-fixture backend
    (fn [fixture]
      (let [{:keys [control]} (staged/prepare fixture)
            _ (staged/run-to-io! control)
            completed (sut/finish-import! control)
            original (resident/snapshot (:context completed))
            ;; Model the successful checked publication packet with its own
            ;; checked compilation Environment. No imported receipt is used.
            entry (-> (get-in original [:world :source-modules publication/module])
                      (assoc :environment (:environment original)) (dissoc :imports))
            original (assoc-in original [:world :source-modules publication/module] entry)
            prefix (first (vals (get-in original [:world :source-import-prefixes])))
            session (:session original)
            calls (atom [])
            invoke (fn [world helper args]
                     (swap! calls conj helper)
                     (let [result (raw/call session world helper args)]
                       [(:state result) (:value result)]))]
        (try (f {:original original :entry entry :prefix prefix
                 :certificate (get-in fixture [:checked :certificate]) :invoke invoke :calls calls})
             (finally (resident/close! (:context completed))))))))
(defn proof [{:keys [original prefix certificate invoke]} & [selected-limits]]
  ;; This private pure groundwork does not mint execution/publication authority.
  (#'sut/publication-proof! original prefix certificate publication/module invoke (or selected-limits limits)))

(deftest original-checked-map-refs-select-original-java-ci-objects-without-reprojection
  (doseq [backend [:reference :mutable :jvm]]
    (with-original backend
      (fn [{:keys [original entry certificate] :as fixture}]
        (let [{:keys [world proof]} (proof fixture)
              name (Name/fromString "answer")
              ^Env checked (:checked-env proof)]
          (is (= 18 (count (:expected proof))))
          (is (= #{name} (set (keys (:constants proof)))))
          (is (= 2 (count (:guest-names proof))))
          (is (identical? entry (:entry proof)))
          (is (identical? (:unit entry) (:unit proof)))
          (is (identical? checked (get-in original [:world :kernel-environments (:id (:anchor proof)) :env])))
          (is (identical? (.lookup checked name) (get-in proof [:projected name])))
          (doseq [[name ci] (:projected certificate)]
            (is (identical? ci (.lookup checked name))))
          (is (= (:heap (:world original)) (:heap world)))
          (is (identical? (get-in original [:world :kernel-environments]) (:kernel-environments world)))
          (is (nil? (:imports (:entry proof))))
          (is (zero? (:result world))))))))

(deftest publication-ref-substitution-and-map-anchor-replacement-reject
  (doseq [backend [:reference :mutable :jvm]]
    (with-original backend
      (fn [{:keys [original entry] :as fixture}]
        (let [world (:world original)
              data (m/node world (:data entry))
              values-ref (nth (:fields data) 2)
              value (first (:fields (m/node world values-ref)))
              value-node (m/node world value)
              clone-world (reduce #(m/retain %1 %2 1) world (:fields value-node))
              [clone-world clone] (m/allocate clone-world :ctor (:tag value-node) (:fields value-node))
              changed (m/replace-node clone-world values-ref (assoc (m/node clone-world values-ref) :fields [clone]))
              environment (:environment original)
              root (first (:fields (m/node world environment)))
              wrong-map (assoc-in world [:kernel-environments (:id root) :constant-map] root)
              malformed-array (assoc-in world [:heap (:id values-ref) :fields] nil)]
          (doseq [bad-world [changed wrong-map malformed-array]]
            (let [failure (staged/error-of #(proof (assoc-in fixture [:original :world] bad-world)))]
              (is (some? failure))
              (is (:publication-proof-terminal? (ex-data failure)))
              (is (:checkpoint (ex-data failure)))
              (is (map? (:publication-proof-owners (ex-data failure)))))))))))

(deftest bounded-name-and-ci-name-projection-validates-shapes-cycles-and-limits
  (let [[world name] (guest/guest-name (m/world {}) "alpha")
        [world declaration] (guest/declaration world "alpha" 0 0)
        valid {:max-nodes 2 :max-chars 5}
        cycle (m/replace-node world name (assoc-in (m/node world name) [:fields 0] name))]
    (is (= (Name/fromString "alpha") (bridge/project-name-bounded world name valid)))
    (is (= (Name/fromString "alpha") (imported/project-constant-name world declaration valid)))
    (is (some? (staged/error-of #(bridge/project-name-bounded cycle name {:max-nodes 10 :max-chars 100}))))
    (is (some? (staged/error-of #(bridge/project-name-bounded world name (assoc valid :max-nodes 1)))))
    (is (some? (staged/error-of #(bridge/project-name-bounded world name (assoc valid :max-chars 4)))))
    (is (some? (staged/error-of #(imported/project-constant-name world name valid))))))

(deftest generated-family-proofs-retain-original-checked-ci-identities
  (doseq [backend [:reference :mutable :jvm]]
    (with-original backend
      (fn [{:keys [original entry] :as fixture}]
        (let [old-world (:world original)
              old-root (first (:fields (m/node old-world (:environment original))))
              ^Env old-env (get-in old-world [:kernel-environments (:id old-root) :env])
              generated (generation/generate old-env
                          (generation/source [] 0
                            [(generation/type-input "ReconstructedEnum" generation/type1
                               [(generation/ctor "ReconstructedEnum.mk"
                                  (generation/constant (name/from-string "ReconstructedEnum")))])]))
              checked-cis (vec (.constants generated))
              functions (merge (:functions old-world) @encoding-fixture/functions)
              session (raw/open-functions functions (get-in original [:session :bindings])
                                          {:backend backend :fuel 1000000})
              invoke (fn [world helper args]
                       (let [result (raw/call session world helper args)]
                         [(:state result) (:value result)]))
              ;; This is the same real checked-family encoder used by kernel-host.
              ;; It validates a complete checking-shape round trip before return.
              [world encoded] (encoding/encode-family (assoc old-world :functions functions) invoke checked-cis)
              family-values (:fields (m/node world encoded))
              old-data (:fields (m/node world (:data entry)))
              old-source-values (:fields (m/node world (nth old-data 2)))
              source-values (into old-source-values family-values)
              source-names (into [(Name/fromString "answer")] (map #(.name %) checked-cis))
              [world names] (encoding/encode-names world invoke source-names)
              [world constants] (m/allocate (reduce #(m/retain %1 %2 1) world source-values)
                                            :array 246 source-values)
              old-map (get-in world [:kernel-environments (:id old-root) :constant-map])
              all-values (into (:fields (m/node world old-map)) family-values)
              [world constant-map] (m/allocate (reduce #(m/retain %1 %2 1) world all-values)
                                               :array 246 all-values)
              [world root] (m/allocate world :ctor 0 [constant-map])
              [world environment] (m/allocate world :ctor 0 [root])
              [world data] (guest/ctor
                             (reduce #(m/retain %1 %2 1) world [(nth old-data 0) (nth old-data 3) (nth old-data 4)])
                             0 [(nth old-data 0) names constants (nth old-data 3) (nth old-data 4)] 1)
              world (-> world (m/retain root 1) (m/retain constant-map 1) (m/release encoded 1)
                        (assoc-in [:kernel-environments (:id root)]
                          {:anchor root :env (.env generated) :constant-map constant-map :quot-init? true})
                        (assoc-in [:source-modules publication/module]
                          (assoc entry :environment environment :data data)))
              prepared (assoc original :world world :environment environment :session session)
              result (with-redefs [imported/project-constant
                                   (fn [& _] (throw (ex-info "Proof must preserve original Java CI objects" {})))]
                       (proof (assoc fixture :original prepared :invoke invoke)))
              proved (:proof result)]
          (is (= 3 (count checked-cis)))
          (is (= 4 (count (:constants proved))))
          (is (= 21 (count (:expected proved))))
          (is (identical? (.env generated) (:checked-env proved)))
          (doseq [ci checked-cis]
            (is (identical? ci (get-in proved [:projected (.name ci)]))))
          (is (= (:heap world) (get-in result [:world :heap]))))))))

;; The publication/compiler/front-end/getter bodies below are explicit models.
;; The issued public operations, raw evalConst witness path, execution machinery
;; and Java whole-map checking are real on all backends.
(def feature-limits (assoc limits :max-nodes 10000 :max-edges 20000 :max-bytes 1000000
                                  :max-units 100 :max-declarations 10000))
(def answer ["str" ["anonymous"] "answer"])
(def eval-root ["str" ["anonymous"] "ReconstructionEval"])
(def witness-root ["str" ["anonymous"] "ReconstructionWitness"])
(def poison-root ["str" ["anonymous"] "ReconstructionPoison"])
(def local-row {:kind "decl" :name answer :sourceLocal true :sourceModule publication/module
                :ir {:fdecl {:f answer :xs [] :type "object" :body []}}})
(def helper ["str" ["anonymous"] "answer._boxed"])
(def primary-digest (apply str (repeat 64 "b")))
(def helper-digest (apply str (repeat 64 "c")))
(def helper-row (-> local-row (assoc :name helper) (assoc-in [:ir :fdecl :f] helper)))
(defn feature-world [world]
  ;; Real compiler publication may emit evalConst units before the final file
  ;; unit. The primary's executable actually calls a helper in another unit.
  (let [f {:params [] :body [:call 0 [:direct helper] [] [:return [:var 0]]]}
        h {:params [] :body [:return [:imm 42]]}
        unit (get-in world [:eval-const-authorizations :units publication/digest])]
    (reduce (fn [world [digest name row function]]
              (-> world
                  (assoc-in [:functions name] function)
                  (assoc-in [:eval-const-authorizations :units digest] (assoc unit :declarations [name]))
                  (assoc-in [:eval-const-authorizations :functions name] function)
                  (assoc-in [:eval-const-authorizations :declarations name] row)
                  (assoc-in [:eval-const-authorizations :unit-digests name] digest)))
            (assoc-in world [:eval-const-authorizations :units publication/digest] (assoc unit :declarations []))
            [[primary-digest answer local-row f] [helper-digest helper helper-row h]])))
(defn feature-witness []
  {:schema "lean-eval-const-witness/1" :producer "RuntimeCompileShim.exportEvalConstWitness"
   :leanCommit (get prim/pinned-build "lean_get_githash")
   :runtimeProfile {:target "x86_64-unknown-linux-gnu" :wordBits 64}
   :name answer :boxedTarget answer :sorryDep nil :missingDependencies []
   :declarations [(assoc local-row :sourceLocal false) (assoc helper-row :sourceLocal false)]})
(defn with-feature [backend f & {:keys [target-change observer finalizer-error? getter-change witness-change repeat-target publication-change profile-limits finalizer-name]
                                :or {finalizer-name "answer" publication-change identity profile-limits feature-limits target-change (fn [world _] world) getter-change (fn [_ _ world args handler] (handler world args)) witness-change identity}}]
  (let [profile (atom nil) modules (atom nil) enabled? (atom false) seen (atom [])
        configure
        (fn [{:keys [world functions native hybrid]}]
          (let [witness {:params [1 2 3]
                         :body [:dec [:var 1] 1 [:dec [:var 2] 1
                                [:let 4 [:ctor 0 [[:imm (json/write-str (witness-change (feature-witness)))]]]
                                 [:return [:var 4]]]]]}
                ;; Use actual target vars, not their names printed as authority.
                specs {(:is-exporting sut/reconstruction-helpers) [1 "uint8" (fn [world _] [world 0])]
                       @#'sut/module-names-helper
                       [1 "object" (fn [world _]
                                     (let [[world names] (reduce (fn [[world values] module]
                                                                  (let [[world value] (guest/guest-name world (imports/module-string module))]
                                                                    [world (conj values value)])) [world []] @modules)]
                                       (m/allocate world :array 246 names)))]
                       @#'sut/module-index-helper
                       [2 "tobject" (fn [world _] (m/allocate world :ctor 1 [(dec (count @modules))]))]}
                bindings (into {} (for [[target [arity ret handler]] specs]
                                     [(str "reconstruction_model_" (pr-str target))
                                      {:signature {:params (vec (repeat arity {:ty "object" :borrow true})) :return-type ret}
                                       :handler (fn [ctx world args] (getter-change target ctx world args handler))}]))
                helpers (into {} (for [[target [arity ret _]] specs
                                       :let [symbol (str "reconstruction_model_" (pr-str target))
                                             params (vec (range 1 (inc arity)))]]
                                   [target {:params params :raw-extern {:symbol symbol :signature (:signature (get bindings symbol))}
                                            :body [:host symbol (mapv #(vector :var %) params) (inc arity)
                                                   [:return [:var (inc arity)]]]}]))
                functions (merge functions helpers {poison-root {:params [] :body [:invalid-reconstruction-test-operation]}
                                                     witness-root witness
                                                     eval-root {:params [1 2 3 4]
                                                                :body [:host "lean_eval_const" [[:var 1] [:var 2] [:var 3] [:var 4]] 5
                                                                       [:return [:var 5]]]}})
                created (sut/prepare-reconstruction-profile witness-root
                          {:witness witness-root :trusted-functions functions} {:limits profile-limits})]
            (reset! profile (:profile created))
            {:world (assoc world :functions functions) :functions functions
             :native (assoc (merge native bindings) "lean_eval_const" (:eval-binding created))
             :hybrid (assoc (merge hybrid bindings) "lean_eval_const" (:eval-binding created))}))
        finalizer-hook
        (fn [context world values]
          (if-not @enabled? world
            (let [[world io] (publication/final-result world values)
                  environment (first (:fields (m/node world io)))
                  root (first (:fields (m/node world environment)))
                  world (target-change world environment)
                  [world name] (guest/guest-name world finalizer-name)
                  [world result] ((:invoke context) world eval-root [m/erased environment 0 name])]
              (swap! seen conj {:value (first (:fields (m/node world result)))
                               :associated? (contains? (:kernel-environments world) (:id root))
                               :receipt? (boolean (seq (get-in world [:source-modules publication/module :imports])))})
              (when observer (observer world))
              (let [world (m/release world result 1)
                    world (if repeat-target
                            (let [[world next-environment] (repeat-target world environment)
                                  [world result] ((:invoke context) world eval-root [m/erased next-environment 0 name])]
                              (swap! seen conj {:value (first (:fields (m/node world result)))
                                               :associated? false :receipt? false})
                              (-> world (m/release result 1) (m/release next-environment 1)))
                            world)]
                (-> world (m/release name 1) (m/release io 1))))))]
    (staged/with-fixture backend
      (fn [{:keys [context prefix configuration] :as fixture}]
        (reset! modules (conj (mapv :module (get-in (#'sut/capability! prefix) [:prefix :modules])) publication/module))
        (let [{old :control} (staged/prepare fixture)
              _ (staged/run-to-io! old)
              completed (sut/finish-import! old)
              original (resident/snapshot (:context completed))
              entry (-> (get-in original [:world :source-modules publication/module])
                        (assoc :environment (:environment original)) (dissoc :imports))
              original (-> original (assoc-in [:world :source-modules publication/module] entry)
                           (update :world publication-change))
              ;; The mocked compile starts from a distinct genuine input packet;
              ;; only the successful result contains the new source registries.
              baseline (-> (resident/snapshot context)
                           (update :world #(-> %
                                              (update :source-modules dissoc publication/module)
                                              (assoc-in [:eval-const-authorizations :units] {})
                                              (assoc-in [:eval-const-authorizations :unit-digests] {})
                                              (assoc-in [:eval-const-authorizations :declarations] {}))))
              baseline-context (resident/adopt-prepared baseline configuration)
              published-context (resident/adopt-prepared original configuration)
              publications (atom 0)]
          (try
            (let [published (with-redefs [resident-source/load-and-publish
                                         (fn [_ _ _]
                                           (swap! publications inc)
                                           {:context published-context :success true
                                            :publication {:module publication/module :unit-digest publication/digest :profile :over-init}})]
                              (sut/publish-source-for-reconstruction baseline-context staged/request prefix @profile
                                {:proof-budgets {:helper-fuel 1000000 :attempt-fuel 10000000}}))]
              (try
                (reset! enabled? true)
                (f (assoc fixture :context (:context published) :profile @profile
                          :publication (:reconstruction-publication published) :seen seen :publications publications))
                (finally (resident/close! (:context published)))))
            (finally (resident/close! baseline-context) (resident/close! published-context) (resident/close! (:context completed))))))
      :world-transform feature-world :configure configure :finalizer-hook finalizer-hook
      :finalizer-error? #(and @enabled? finalizer-error?))))

(defn prepare-feature [fixture & [options]]
  (sut/prepare-source-reconstruction-import-over-init
    (:context fixture) staged/request (:prefix fixture) (:profile fixture) (:publication fixture)
    (or options staged/options)))

(defn retains-packet? [state packets]
  ;; Walk the actual persistent control data by identity, without descending
  ;; into guest/runtime objects. Stop at a retained packet before traversing its
  ;; possibly large World. Sharing is visited once; no collection/GC is forced.
  (let [forbidden (java.util.IdentityHashMap.) seen (java.util.IdentityHashMap.)]
    (doseq [packet packets :when (some? packet)] (.put forbidden packet true))
    (loop [pending [state]]
      (if (empty? pending) false
        (let [value (peek pending) pending (pop pending)]
          (cond
            (.containsKey forbidden value) true
            (.containsKey seen value) (recur pending)
            :else (do (.put seen value true)
                      (recur (if (coll? value) (into pending value) pending)))))))))

(deftest scoped-raw-evalconst-precedes-real-fresh-check-and-source-only-receipt
  (doseq [backend [:reference :mutable :jvm]]
    (try
      (with-feature backend
        (fn [{:keys [seen publications] :as fixture}]
          (let [{:keys [control]} (prepare-feature fixture)]
            (is (= 1 @publications))
            (is (empty? @seen))
            (let [completed (staged/run-to-io! control)]
              (is (= {:authorization-count 2 :requested-names ["answer"] :names-truncated? false
                      :module publication/module :unit-digest publication/digest}
                     (get-in completed [:progress :reconstruction]))))
            (is (not (contains? (:progress (staged/prepare fixture)) :reconstruction)))
            (is (= [{:value 42 :associated? false :receipt? false}] @seen))
            (let [state @(#'sut/import-control! control)
                  owners (get-in state [:reconstruction :owners])]
              (is (= #{:root :map} (set (keys owners))))
              (is (every? #(= :owned (:status %)) (vals owners)))
              (let [finished (sut/finish-import! control)
                    after (resident/snapshot (:context finished))
                    compact @(#'sut/import-control! control)]
                (is (= 1 (get-in finished [:import-receipt :constant-count])))
                (is (= 18 (count (.allConstants ^Env (:checked-env (first (vals (get-in after [:world :source-modules publication/module :imports]))))))))
                ;; Capture real pre-finish packets and the returned Context,
                ;; rather than duplicate the production tombstone's key list.
                ;; The old noncompacting implementation retains these packets.
                (is (not (retains-packet? compact
                           (concat (keep state [:entry :world :session :assembly :last-call
                                                :configuration :prefix :certificate])
                                   (keep (:reconstruction state) [:profile :publication :proof :cache :owners])
                                   [(:context finished) after (:world after)]))))
                (is (= (assoc (#'sut/import-progress state) :phase :finished)
                       (#'sut/import-progress compact)))
                ;; These fixture roots belonged only to the proof cache after
                ;; finalizer IO. Check actual guest release in the public result,
                ;; not an obsolete private success-owner ledger.
                (doseq [{:keys [value]} (vals owners)]
                  (is (not (contains? (get-in after [:world :heap]) (:id value)))))
                (resident/close! (:context finished)))))))
      (catch Throwable cause
        (is false (str backend " " (.getName (class cause)) " " (.getMessage cause) " "
                       (mapv str (take 20 (.getStackTrace (last (take-while some? (iterate #(.getCause ^Throwable %) cause))))))))))))

(defn bounded-error [cause]
  (str (.getName (class cause)) " " (.getMessage cause)))
(defn check-feature [backend f & options]
  (try (apply with-feature backend f options)
       (catch Throwable cause (is false (str backend " " (bounded-error cause))))))
(defn assert-terminal [control]
  (let [failure (staged/error-of #(staged/run-to-io! control))]
    (is (some? failure))
    (when failure
      (is (:resident-init-import-terminal? (ex-data failure)))
      (is (some? (:checkpoint (ex-data failure))))
      (is (some? (:checkpoint-session (ex-data failure))))
      (is (identical? failure (staged/error-of #(staged/run-to-io! control))))
      (is (identical? failure (staged/error-of #(sut/finish-import! control)))))
    failure))

(deftest exact-fullmap-view-module-and-witness-rejections-poison-on-all-backends
  (doseq [backend [:reference :mutable :jvm]
          [label options]
          [[:missing-ci [:target-change (fn [world environment]
                                         (let [root (first (:fields (m/node world environment)))
                                               array (first (:fields (m/node world root)))]
                                           (m/replace-node world array (assoc (m/node world array) :fields []))))]]
           [:extra-ci [:target-change (fn [world environment]
                                       (let [root (first (:fields (m/node world environment)))
                                             array (first (:fields (m/node world root)))
                                             value (first (:fields (m/node world array)))]
                                         (m/replace-node (m/retain world value 1) array
                                                         (update (m/node world array) :fields conj value))))]]
           [:public-view [:getter-change (fn [target _ world args handler]
                                           (if (= target (:is-exporting sut/reconstruction-helpers))
                                             [world 1] (handler world args)))]]
           [:wrong-module-index [:getter-change (fn [target _ world args handler]
                                                  (if (= target @#'sut/module-index-helper)
                                                    (m/allocate world :ctor 1 [0]) (handler world args)))]]
           [:wrong-module-order [:getter-change (fn [target _ world args handler]
                                                  (let [[world value] (handler world args)]
                                                    (if (= target @#'sut/module-names-helper)
                                                      [(m/replace-node world value (update (m/node world value) :fields #(vec (reverse %)))) value]
                                                      [world value])))]]
           [:wrong-source-module [:witness-change #(assoc-in % [:declarations 0 :sourceModule] source/init-module)]]
           [:wrong-ir [:witness-change #(assoc-in % [:declarations 0 :ir :fdecl :type] "uint8")]]]]
    (check-feature backend
      (fn [{:keys [seen] :as fixture}]
        (let [{:keys [control]} (prepare-feature fixture)]
          (is (some? (assert-terminal control)) (str backend " " label))
          (is (empty? @seen))))
      ;; apply this case's two keyword arguments as actual fixture options.
      (first options) (second options))))

(deftest capabilities-original-payload-and-out-of-band-eval-cannot-arm
  (doseq [backend [:reference :mutable :jvm]]
    (check-feature backend
      (fn [{:keys [context prefix profile publication] :as fixture}]
        (doseq [[p pub] [[{} publication] [profile {}]]]
          (is (some? (staged/error-of #(sut/prepare-source-reconstruction-import-over-init
                                        context staged/request prefix p pub staged/options)))))
        (let [original (resident/snapshot context)
              world (:world original)
              entry (get-in world [:source-modules publication/module])
              value (first (:fields (m/node world (nth (:fields (m/node world (:data entry))) 2))))
              node (m/node world value)
              changed (m/replace-node world value (assoc node :tag (mod (inc (:tag node)) 8)))
              candidate (resident/adopt-prepared (assoc original :world changed) (:configuration fixture))]
          (try
            (is (some? (staged/error-of #(prepare-feature (assoc fixture :context candidate)))))
            (finally (resident/close! candidate)))
          ;; RC-only changes leave the exact immutable payload intact.
          (let [candidate (resident/adopt-prepared (assoc original :world (m/retain world value 1)) (:configuration fixture))]
            (try (is (some? (:control (prepare-feature (assoc fixture :context candidate)))))
                 (finally (resident/close! candidate))))
          (let [[world name] (guest/guest-name world "answer")]
            (is (some? (staged/error-of #(raw/call (:session original) world eval-root
                                          [m/erased (:environment original) 0 name])))))
          (let [{:keys [control]} (prepare-feature fixture)
                called (atom 0)]
            ;; Observer runs after raw scope exits. Even while control is busy,
            ;; a raw evalConst on a retained public snapshot cannot inherit it.
            (sut/advance-import! control
              {:max-operations 1 :wall-ms 1000
               :observe! (fn [_]
                           (swap! called inc)
                           (let [[world name] (guest/guest-name world "answer")]
                             (is (some? (staged/error-of #(raw/call (:session original) world eval-root
                                                           [m/erased (:environment original) 0 name]))))))})
            (is (= 1 @called))
            (staged/run-to-io! control)
            (let [finished (sut/finish-import! control)] (resident/close! (:context finished)))))))))

(deftest extension-only-roots-reuse-protected-map-and-success-releases-once
  (doseq [backend [:reference :mutable :jvm]]
    (check-feature backend
      (fn [{:keys [seen] :as fixture}]
        (let [{:keys [control]} (prepare-feature fixture)]
          (staged/run-to-io! control)
          (is (= [42 42] (mapv :value @seen)))
          (let [owners (get-in @(#'sut/import-control! control) [:reconstruction :owners])
                _ (is (= 2 (count owners)))
                finished (sut/finish-import! control)
                after (resident/snapshot (:context finished))]
            (doseq [{:keys [value]} (vals owners)]
              (is (not (contains? (get-in after [:world :heap]) (:id value)))))
            (is (= {:phase :finished} (ex-data (staged/error-of #(sut/finish-import! control)))))
            (is (identical? after (resident/snapshot (:context finished))))
            (resident/close! (:context finished)))))
      :repeat-target (fn [world environment]
                       (let [root (first (:fields (m/node world environment)))
                             map (first (:fields (m/node world root)))
                             [world root] (m/allocate (m/retain world map 1) :ctor 0 [map])]
                         (m/allocate world :ctor 0 [root]))))))

(deftest finalizer-and-observer-failures-retain-proof-owners-and-no-receipt
  (doseq [backend [:reference :mutable :jvm] failure-kind [:finalizer-io :observer]]
    (check-feature backend
      (fn [{:keys [seen] :as fixture}]
        (let [{:keys [control]} (prepare-feature fixture)
              failure (if (= :finalizer-io failure-kind)
                        (do (staged/run-to-io! control) (staged/error-of #(sut/finish-import! control)))
                        (loop []
                          (let [failure (staged/error-of #(sut/advance-import! control
                                                         {:max-operations 1 :wall-ms 1000
                                                          :observe! (fn [_] (when (seq @seen)
                                                                             (throw (ex-info "observer-stop" {}))))}))]
                            (if failure failure (recur)))))
              data @(#'sut/import-control! control)]
          (is (some? failure))
          (is (identical? failure (staged/error-of #(sut/finish-import! control))))
          (is (= 1 (count @seen)))
          (is (every? #(= :owned (:status %)) (vals (get-in data [:reconstruction :owners]))))
          (is (empty? (get-in (:checkpoint (ex-data failure)) [:source-modules publication/module :imports])))))
      :finalizer-error? (= :finalizer-io failure-kind))))

(deftest callback-owner-ledger-precedes-throwing-checkpoints
  ;; Focused private transition test: issuance still uses public APIs. The raw
  ;; getter transport is real; checkpoint failure is deliberately injected at
  ;; the precise owned-getter/release transition, outside the production driver.
  (doseq [backend [:reference :mutable :jvm] fail-at [1 6]]
    (check-feature backend
      (fn [{:keys [context profile] :as fixture}]
        (let [{:keys [control]} (prepare-feature fixture)
              state (#'sut/import-control! control)
              entry (resident/snapshot context)
              world (:world entry)
              [world requested] (guest/guest-name world "answer")
              checked (atom nil) calls (atom 0) session (atom (:session entry))
              fault (ex-info "injected-proof-checkpoint" {:injected-checkpoint true})
              callback-context {:invoke (fn [world target args]
                                          (let [called (raw/call @session world target args)]
                                            (reset! session (:session called)) [(:state called) (:value called)]))
                                :checkpoint! (fn [world]
                                               (reset! checked world)
                                               (when (= fail-at (swap! calls inc)) (throw fault)))
                                :check-trusted-functions! (fn [world roots]
                                                            (eval/validate-executables! world
                                                              (get-in fixture [:configuration :trusted-functions]) roots))}
              token (:token (#'sut/reconstruction-profile! profile))
              request-local @#'sut/reconstruction-request]
          (swap! state assoc :phase :running :busy? true)
          (.set ^ThreadLocal request-local {:name (Name/fromString "answer") :reference requested})
          (try
            (let [failure (staged/error-of
                            #(#'sut/authorize-reconstruction-row token
                               {:state state :thread (Thread/currentThread)} world callback-context (:environment entry)
                               (assoc local-row :sourceLocal false) local-row
                               (get-in world [:eval-const-authorizations :units primary-digest])))
                  owners (:reconstruction-proof-temporary (ex-data failure))]
              (is (some? failure))
              (is (identical? fault (.getCause ^Throwable failure)))
              (is (identical? @checked (:checkpoint (ex-data failure))))
              (is (= :owned (get-in owners [:root :status])))
              (when (= 6 fail-at) (is (= :released (get-in owners [:header :status])))))
            (finally (.remove ^ThreadLocal request-local))))))))

(deftest a-caught-failed-proof-helper-poisons-the-shared-raw-completion-budget
  (doseq [backend [:reference :mutable :jvm]]
    (let [caught (atom 0)]
      (check-feature backend
        (fn [fixture]
          (let [{:keys [control]} (prepare-feature fixture)
                failure (assert-terminal control)]
            (is (= 1 @caught))
            (is (some? failure))
            (is (empty? @(:seen fixture)))
            (is (every? #(= :owned (:status %))
                        (vals (select-keys (get-in @(#'sut/import-control! control) [:reconstruction :temporary]) [:root :map]))))))
        :getter-change
        (fn [target context world args handler]
          (when (= target @#'sut/module-index-helper)
            (try ((:invoke context) world poison-root [])
                 (catch Throwable _ (swap! caught inc))))
          (handler world args))))))

(deftest publication-proof-bounds-and-partial-helper-release-failures-retain-exact-owners
  (doseq [backend [:reference :mutable :jvm]]
    (with-original backend
      (fn [{:keys [invoke original] :as fixture}]
        (let [failure (staged/error-of #(proof fixture (assoc limits :max-constants 17)))]
          (is (some? failure))
          (is (:publication-proof-terminal? (ex-data failure))))
        (let [calls (atom 0)
              fault (ex-info "second-getter-fails" {})
              failing (fn [world target args]
                        (if (= 2 (swap! calls inc)) (throw fault) (invoke world target args)))
              failure (staged/error-of #(proof (assoc fixture :invoke failing)))]
          (is (identical? fault (.getCause ^Throwable failure)))
          (is (= :owned (get-in (ex-data failure) [:publication-proof-owners :root :state])))
          (is (= 2 @calls)))
        (let [release m/release
              world (:world original)
              root (first (:fields (m/node world (:environment original))))
              constant-map (first (:fields (m/node world root)))
              fault (ex-info "map-release-fails" {})
              failure (with-redefs [m/release (fn [& args]
                                               (if (= constant-map (second args)) (throw fault) (apply release args)))]
                        (staged/error-of #(proof fixture)))]
          (is (identical? fault (.getCause ^Throwable failure)))
          (is (= :released (get-in (ex-data failure) [:publication-proof-owners :constant-array :state])))
          (is (= :owned (get-in (ex-data failure) [:publication-proof-owners :constant-map :state])))
          (is (= :owned (get-in (ex-data failure) [:publication-proof-owners :root :state]))))))))

(deftest bounded-local-ci-payload-walk-rejects-before-unbounded-expansion
  (let [[world root] (m/allocate (m/world {}) :ctor 0 ["abcdef"])
        bounds {:max-nodes 10 :max-edges 10 :max-bytes 100}
        original (#'sut/local-ci-graph! world [root] bounds)]
    (is (= original (#'sut/local-ci-graph! (m/retain world root 1) [root] bounds)))
    (is (some? (staged/error-of #(#'sut/local-ci-graph! world [root] (assoc bounds :max-bytes 5)))))
    (let [too-wide (m/replace-node world root (assoc (m/node world root) :fields (vec (repeat 1000 0))))
          opaque (m/replace-node world root (assoc-in (m/node world root) [:fields 0] (Object.)))
          unknown (m/replace-node world root (assoc (m/node world root) :unbounded-payload (range)))]
      (doseq [bad [too-wide opaque unknown]]
        (is (some? (staged/error-of #(#'sut/local-ci-graph! bad [root] bounds))))))))

(deftest publication-proof-budget-is-separate-reserved-and-terminal-after-real-child-failure
  (doseq [backend [:reference :mutable :jvm]]
    (check-feature backend
      (fn [{:keys [context prefix profile]}]
        (doseq [budgets [{:helper-fuel 1000 :attempt-fuel 999}
                        {:helper-fuel 1000 :attempt-fuel 1000}]]
          (let [loads (atom 0) calls (atom 0) call raw/call
                public-result {:context context :success true :publication {:module publication/module}}
                failure (with-redefs [resident-source/load-and-publish (fn [& _] (swap! loads inc) public-result)
                                      raw/call (fn [& args] (swap! calls inc) (apply call args))]
                          (staged/error-of #(sut/publish-source-for-reconstruction context staged/request prefix profile
                                             {:proof-budgets budgets})))
                state (:reconstruction-publication-state (ex-data failure))]
            (is (some? failure))
            (is (= 1 @loads))
            (is (= (if (= 999 (:attempt-fuel budgets)) 0 1) @calls))
            (is (identical? public-result (:publication state)))
            (is (:reconstruction-publication-terminal? (ex-data failure)))))
        (let [call raw/call loads (atom 0) child (atom nil)
              public-result {:context context :success true :publication {:module publication/module}}
              fault (ex-info "publication-helper-child-fault" {})
              failure (with-redefs [resident-source/load-and-publish (fn [& _] (swap! loads inc) public-result)
                                    raw/call (fn [& args]
                                               (let [called (apply call args)
                                                     world (assoc (:state called) :publication-child-failed true)
                                                     session (assoc (:session called) :fuel 17)]
                                                 (reset! child {:world world :session session})
                                                 (throw (ex-info "real-child-completed-before-failure"
                                                          {:checkpoint world :checkpoint-session session} fault))))]
                        (staged/error-of #(sut/publish-source-for-reconstruction context staged/request prefix profile
                                           {:proof-budgets {:helper-fuel 1000000 :attempt-fuel 10000000}})))
              state (:reconstruction-publication-state (ex-data failure))]
          (is (= 1 @loads))
          (is (some? failure))
          (is (identical? public-result (:publication state)))
          (is (true? (:proof-helper-budget-poisoned? state)))
          (is (= 1000000 (:reserved state)))
          (is (identical? (:world @child) (:world state)))
          (is (identical? (:session @child) (:session state)))
          (is (identical? (:world @child) (:checkpoint (ex-data failure))))
          (is (identical? (:session @child) (:checkpoint-session (ex-data failure)))))))))

(deftest fresh-current-policy-failure-retains-cache-and-adoption-failure-retains-release-checkpoint
  (doseq [backend [:reference :mutable :jvm] failure-kind [:current-policy :adoption]]
    (check-feature backend
      (fn [fixture]
        (let [options (cond-> staged/options
                        (= failure-kind :current-policy) (assoc-in [:kernel-policy :allow-axioms?] false))
              {:keys [control]} (prepare-feature fixture options)
              _ (staged/run-to-io! control)
              fault (ex-info "reconstruction-adoption-fault" {})
              failure (if (= failure-kind :adoption)
                        (with-redefs [resident/adopt-prepared (fn [& _] (throw fault))]
                          (staged/error-of #(sut/finish-import! control)))
                        (staged/error-of #(sut/finish-import! control)))
              data @(#'sut/import-control! control)
              owners (vals (get-in data [:reconstruction :owners]))]
          (is (some? failure))
          (is (identical? failure (staged/error-of #(sut/finish-import! control))))
          (is (identical? failure (staged/error-of #(staged/run-to-io! control))))
          (is (= 2 (count owners)))
          (if (= failure-kind :adoption)
            (do
              (is (identical? fault (.getCause ^Throwable failure)))
              (is (every? #(= :released (:status %)) owners))
              (is (identical? (get-in data [:adoption-entry :world]) (:checkpoint (ex-data failure))))
              (is (seq (get-in data [:adoption-entry :world :source-modules publication/module :imports]))))
            (do
              (is (every? #(= :owned (:status %)) owners))
              (is (empty? (get-in data [:world :source-modules publication/module :imports]))))))))))

(deftest descriptive-name-audit-bounds-real-storage-without-recursive-display
  (let [deep (reduce name/mk-str (name/anonymous) (repeat 5000 "x"))
        too-wide (name/mk-str (name/anonymous) (apply str (repeat 5000 "x")))
        [world mpz] (m/allocate (m/world {}) :mpz 250 [])
        world (m/replace-node world mpz (assoc (m/node world mpz) :integer (.shiftLeft java.math.BigInteger/ONE 10000)))
        bounds {:max-nodes 10 :max-edges 10 :max-bytes 100}]
    (is (nil? (#'sut/bounded-name-display deep)))
    (is (nil? (#'sut/bounded-name-display too-wide)))
    (is (= "alpha.beta" (#'sut/bounded-name-display (Name/fromString "alpha.beta"))))
    (is (some? (staged/error-of #(#'sut/local-ci-graph! world [mpz] bounds)))))
  (let [[world node] (m/scalar-constructor (m/world {}) 0 [] {:objects 0 :usize 0 :ssize 8})
        world (m/replace-node world node (assoc (m/node world node) :scalar-bytes (zipmap (range 8) (repeat 0))))
        raw (prototype.constructor-layout/clone-storage (m/node world node))
        world (m/replace-node world node raw)]
    (is (= raw (assoc (get (#'sut/local-ci-graph! world [node] {:max-nodes 10 :max-edges 10 :max-bytes 100}) (:id node)) :rc 1)))))


(defn admission-model []
  (let [old-function {:params [] :body [:return [:imm 7]]}
        old-row {:name ["old"]}
        unit {:actions [] :declarations []
              :manifest {:initializationPlan {:module publication/module :actions []}}}
        old-digest (apply str (repeat 64 "d"))
        before {:functions {["old"] old-function}
                :eval-const-authorizations {:units {old-digest unit}
                                            :unit-digests {["old"] old-digest}
                                            :declarations {["old"] old-row}
                                            :functions {["old"] old-function}}}
        after (reduce (fn [world [name row digest value]]
                        (-> world (assoc-in [:functions name] value)
                            (assoc-in [:eval-const-authorizations :functions name] value)
                            (assoc-in [:eval-const-authorizations :declarations name] row)
                            (assoc-in [:eval-const-authorizations :unit-digests name] digest)
                            (assoc-in [:eval-const-authorizations :units digest] (assoc unit :declarations [name]))))
                      (assoc-in before [:eval-const-authorizations :units publication/digest] unit)
                      [[answer local-row primary-digest {:params [] :body [:return [:imm 42]]}]
                       [helper helper-row helper-digest {:params [] :body [:return [:imm 42]]}]])
        proof {:unit unit :unit-digest publication/digest :module publication/module}]
    {:before before :after after :proof proof :old-digest old-digest}))

(deftest exact-multiunit-delta-captures-primary-helper-and-separate-final-unit
  (let [{:keys [before after proof]} (admission-model)
        admission (#'sut/capture-publication-admission! before after proof feature-limits)
        proof (assoc proof :admission admission)]
    (is (= 3 (count (:units admission))))
    (is (= 2 (:declaration-count admission)))
    (is (= primary-digest (get-in admission [:rows answer :digest])))
    (is (= helper-digest (get-in admission [:rows helper :digest])))
    (is (not= (:unit-digest proof) (get-in admission [:rows answer :digest])))
    (is (identical? local-row (get-in admission [:rows answer :row])))
    (is (#'sut/publication-admission-matches! after proof feature-limits))
    (doseq [change [#(assoc-in % [:eval-const-authorizations :units primary-digest] (into {} (get-in % [:eval-const-authorizations :units primary-digest])))
                    #(assoc-in % [:eval-const-authorizations :declarations answer] (into {} local-row))
                    #(assoc-in % [:functions answer] {:params [] :body [:return [:imm 43]]})
                    #(assoc-in % [:eval-const-authorizations :functions helper] {:params [] :body [:return [:imm 43]]})
                    #(assoc-in % [:eval-const-authorizations :unit-digests answer] helper-digest)
                    #(assoc-in % [:functions ["old"]] {:replacement true})]]
      (is (some? (staged/error-of #(#'sut/publication-admission-matches! (change after) proof feature-limits)))))))

(deftest publication-delta-rejects-baseline-collisions-foreign-actions-and-aggregate-overflow
  (let [{:keys [before after proof old-digest]} (admission-model)]
    (doseq [change [#(assoc-in % [:eval-const-authorizations :units old-digest] {:replacement true})
                    #(assoc-in % [:eval-const-authorizations :declarations ["old"]] {:replacement true})
                    #(assoc-in % [:eval-const-authorizations :unit-digests ["old"]] primary-digest)
                    #(assoc-in % [:eval-const-authorizations :functions ["old"]] {:replacement true})
                    #(assoc-in % [:eval-const-authorizations :units primary-digest :actions] [{:init true}])
                    #(assoc-in % [:eval-const-authorizations :units helper-digest :manifest :initializationPlan :actions] [{:init true}])
                    #(assoc-in % [:eval-const-authorizations :units primary-digest :manifest :initializationPlan :module] ["foreign"])
                    #(assoc-in % [:eval-const-authorizations :units helper-digest :declarations] [helper answer])
                    #(assoc-in % [:eval-const-authorizations :unit-digests answer] helper-digest)
                    #(assoc-in % [:eval-const-authorizations :declarations answer :sourceModule] ["foreign"])
                    #(assoc-in % [:eval-const-authorizations :declarations ["uncaptured"]] {:name ["uncaptured"]})]]
      (is (some? (staged/error-of #(#'sut/capture-publication-admission! before (change after) proof feature-limits)))))
    (doseq [limits [(assoc feature-limits :max-units 4)
                    (assoc feature-limits :max-declarations 20)]]
      (is (some? (staged/error-of #(#'sut/capture-publication-admission! before after proof limits)))))
    ;; A previously admitted same-module unit never becomes this publication's delta.
    (is (some? (staged/error-of #(#'sut/capture-publication-admission! after after proof feature-limits))))))

(deftest earlier-unit-provenance-replacements-reject-before-assembly-on-all-backends
  (doseq [backend [:reference :mutable :jvm]]
    (check-feature backend
      (fn [{:keys [context configuration assembly-calls] :as fixture}]
        (let [original (resident/snapshot context)]
          (doseq [change [#(update-in % [:eval-const-authorizations :units primary-digest] (fn [unit] (into {} unit)))
                          #(assoc-in % [:eval-const-authorizations :unit-digests helper] publication/digest)
                          #(assoc-in % [:eval-const-authorizations :declarations helper] (into {} helper-row))]]
            (let [candidate (resident/adopt-prepared (update original :world change) configuration)
                  before @assembly-calls]
              (try (is (some? (staged/error-of #(prepare-feature (assoc fixture :context candidate)))))
                   (is (= before @assembly-calls))
                   (finally (resident/close! candidate))))))))))

(deftest same-module-foreign-row-unit-is-not-publication-authority-and-guard-is-bounded
  (doseq [backend [:reference :mutable :jvm]]
    (check-feature backend
      (fn [fixture]
        (let [{:keys [control]} (prepare-feature fixture)
              failure (assert-terminal control)
              chain (take 10 (take-while some? (iterate #(.getCause ^Throwable %) failure)))
              guard (some #(get (ex-data %) :reconstruction-guard) chain)]
          (is (some? guard))
          (is (= false (get-in guard [:predicates :same-row-digest?])))
          (is (= false (get-in guard [:predicates :same-row-unit?])))
          (is (= true (get-in guard [:predicates :exported-primary-ci?])))
          (is (= publication/digest (:publication-unit-digest guard)))
          (is (= primary-digest (:captured-row-unit-digest guard)))
          (is (every? #(or (true? %) (false? %)) (vals (:predicates guard))))))
      :target-change (fn [world _]
                       (let [foreign-digest (apply str (repeat 64 "f"))
                             unit (get-in world [:eval-const-authorizations :units primary-digest])]
                         (-> world
                             (assoc-in [:eval-const-authorizations :units foreign-digest] (into {} unit))
                             (assoc-in [:eval-const-authorizations :unit-digests answer] foreign-digest)))))))


(deftest ir-extra-helper-does-not-become-an-exported-primary-ci
  (doseq [backend [:reference :mutable :jvm]]
    (check-feature backend
      (fn [fixture]
        (let [{:keys [control]} (prepare-feature fixture)
              failure (assert-terminal control)
              guard (some #(get (ex-data %) :reconstruction-guard)
                          (take 10 (take-while some? (iterate #(.getCause ^Throwable %) failure))))]
          (is (= false (get-in guard [:predicates :exported-primary-ci?])))
          (is (= "answer._boxed" (:requested-name guard)))))
      :finalizer-name "answer._boxed"
      :witness-change #(assoc % :name helper :boxedTarget helper))))
