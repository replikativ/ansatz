(ns prototype.source-graph-runtime-test
  "Bounded graph groundwork and publication-only issuance over a genuine small
   checked native base. Compiler/export callbacks are explicit models; no
   completed graph import receipt or genuine frontend chain is claimed."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.string :as str]
            [ansatz.kernel.expr :as expression]
            [ansatz.kernel.env :as kernel-env]
            [ansatz.kernel.level :as level]
            [prototype.guest-encoding :as encoding]
            [prototype.guest-encoding-test :as encoding-fixture]
            [prototype.imported-kernel :as imported]
            [prototype.module-import :as imports]
            [prototype.raw-interop :as raw]
            [prototype.resident-init-prefix :as graph]
            [prototype.source-import :as source]
            [prototype.machine :as m]
            [prototype.eval-const :as eval]
            [prototype.runtime-prim :as prim]
            [prototype.kernel-bridge-test :as guest]
            [prototype.source-module-test :as module-fixture]
            [prototype.source-import-test :as publication-fixture])
  (:import [ansatz.kernel Name]
           [java.util HashMap]))

(def graph-limits
  {:max-modules 16 :max-roots 4 :max-edges 16 :max-depth 8 :max-names 64
   :max-name-nodes 8 :max-name-bytes 32 :max-total-name-bytes 64
   :max-key-bytes 32 :max-total-key-bytes 64})
(defn str-name [s] ["str" ["anonymous"] s])
(def poison
  (reify Object (hashCode [_] (throw (AssertionError. "unvalidated value hashed")))))

(deftest bounded-wire-and-java-names-use-the-same-explicit-profile
  (doseq [text ["A" "Ωλ" "🦉"]]
    (let [wire (str-name text)]
      (is (= wire (#'graph/graph-wire-name! wire true graph-limits)))
      (is (= wire (#'graph/graph-java-name! (Name/mkStr Name/ANONYMOUS_NAME text) true graph-limits)))))
  (let [last ["num" ["anonymous"] "4294967295"]]
    (is (= last (#'graph/graph-wire-name! last false graph-limits)))
    (is (= last (#'graph/graph-java-name! (Name/mkNum Name/ANONYMOUS_NAME 4294967295) false graph-limits))))
  (doseq [wire [[poison ["anonymous"] "x"] ["num" ["anonymous"] "4294967296"]
                ["num" ["anonymous"] "00"] (str-name "A.B") (str-name "")
                (str-name (apply str (repeat 9 "🦉"))) (str-name (str (char 0xd800)))]]
    (is (thrown? clojure.lang.ExceptionInfo (#'graph/graph-wire-name! wire true graph-limits))))
  (doseq [payload ["4294967296" "00" "-1" "+1" "١" "10000000000"]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (#'graph/graph-wire-name! ["num" ["anonymous"] payload] false graph-limits))))
  (is (thrown? clojure.lang.ExceptionInfo
               (#'graph/graph-java-name! (Name/mkNum Name/ANONYMOUS_NAME 4294967296) false graph-limits)))
  (let [deep (reduce #(Name/mkStr %1 %2) Name/ANONYMOUS_NAME (repeat 8 "a"))]
    (is (thrown? clojure.lang.ExceptionInfo (#'graph/graph-java-name! deep true graph-limits))))
  (let [total (volatile! 0) limit (assoc graph-limits :max-total-name-bytes 5)]
    (is (= (str-name "Ω") (#'graph/graph-wire-name! (str-name "Ω") true limit total)))
    (is (= 2 @total))
    (is (thrown? clojure.lang.ExceptionInfo
                 (#'graph/graph-wire-name! (str-name "🦉") true limit total)))
    (is (= 2 @total))))

(deftest bounded-json-precedes-recursive-parsing
  (let [limits {:max-bytes 256} small (assoc graph-limits :max-name-nodes 1)]
    (let [value {:text "[{}]\""}] (is (= value (#'graph/graph-json! (json/write-str value) limits small))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (#'graph/graph-json! (str (apply str (repeat 34 "[")) "0" (apply str (repeat 34 "]"))) limits small)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (#'graph/graph-json! (apply str (repeat 257 "x")) limits small)))
    (is (thrown? clojure.lang.ExceptionInfo (#'graph/graph-json! "]" limits small)))))

(deftest graph-capabilities-reject-forged-values-before-hashing
  (doseq [lookup [#'graph/graph-profile! #'graph/graph-node! #'graph/graph-receipt!]
          value [poison {:profile :graph} nil]]
    (is (thrown? clojure.lang.ExceptionInfo (lookup value)))))

(deftest native-shadow-check-is-bounded-and-never-reuses-mutable-evidence
  (let [source {:base 100 :size 5 :closed (atom false)}
        node {:source source :host-limits {:max-heap-entries 4}}
        heap {1 :old} world {:heap heap :native-imports [source]} evidence (volatile! nil)]
    (is (#'graph/graph-source-matches! world node evidence))
    (is (identical? heap (:heap @evidence)))
    (is (#'graph/graph-source-matches! world node evidence))
    (is (thrown? clojure.lang.ExceptionInfo
                 (#'graph/graph-source-matches! (assoc world :heap (assoc heap 101 :shadow)) node evidence)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (#'graph/graph-source-matches! (assoc world :native-imports [(assoc source :base 101)]) node evidence)))
    (reset! (:closed source) true)
    (is (thrown? clojure.lang.ExceptionInfo (#'graph/graph-source-matches! world node evidence)))
    (reset! (:closed source) false)
    (let [mutable (doto (HashMap.) (.put 1 :old)) evidence (volatile! nil)]
      (is (#'graph/graph-source-matches! (assoc world :heap mutable) node evidence))
      (is (nil? @evidence))
      (.put mutable 102 :shadow)
      (is (thrown? clojure.lang.ExceptionInfo
                   (#'graph/graph-source-matches! (assoc world :heap mutable) node evidence))))
    (let [too-large (reify clojure.lang.Counted (count [_] 5)
                          clojure.lang.Seqable (seq [_] (throw (AssertionError. "heap expanded before count gate"))))]
      (is (thrown? clojure.lang.ExceptionInfo
                   (#'graph/graph-source-matches! (assoc world :heap too-large) node (volatile! nil)))))))

(deftest graph-header-shape-remains-a-bounded-unsealed-description
  (is (= source/init-requests (source/validate-graph-imports! source/init-requests)))
  (let [request {:module (str-name "A") :importAll false :isExported true :isMeta false}]
    (is (= (conj source/init-requests request)
           (source/validate-graph-imports! (conj source/init-requests request))))
    (doseq [edited [(assoc request :importAll true) (assoc request :isMeta true)
                    (assoc request :isExported false) (assoc request :module (str-name "A.B"))
                    (assoc request :extra poison)]]
      (is (thrown? clojure.lang.ExceptionInfo
                   (source/validate-graph-imports! (conj source/init-requests edited)))))))

(deftest aggregate-proof-budget-keeps-the-actual-failure-packet-and-poisons-retry
  (let [initial {:stats {:steps 5}} session {:fuel 99 :marker (Object.)}
        state (atom {:world initial :session session :used 0 :reserved 0})
        budgets {:helper-fuel 10 :attempt-fuel 20}
        after {:stats {:steps 8}}
        result (#'graph/graph-budget-operation! state budgets :first
                 (fn [issued world]
                   (is (= 10 (:fuel issued))) (is (identical? initial world))
                   {:world after :session issued :value 7}))]
    (is (= 7 (:value result)))
    (is (identical? after (:world @state)))
    (is (= 3 (:used @state)))
    (is (= 0 (:reserved @state)))
    (let [failed-world {:stats {:steps 10}} failed-session (assoc session :fuel 8)
          failure (ex-info "actual bounded failure" {:checkpoint failed-world :checkpoint-session failed-session})]
      (is (identical? failure
             (try (#'graph/graph-budget-operation! state budgets :second (fn [_ _] (throw failure)))
                  (catch Throwable cause cause))))
      (is (identical? failed-world (:world @state)))
      (is (identical? failed-session (:session @state)))
      (is (= 5 (:used @state)))
      (is (= 0 (:reserved @state)))
      (is (:budget-poisoned? @state))
      (is (thrown? clojure.lang.ExceptionInfo
                   (#'graph/graph-budget-operation! state budgets :retry
                     (fn [_ _] (throw (AssertionError. "poisoned attempt invoked again"))))))))
  (let [state (atom {:world {:stats {:steps 0}} :session {:fuel 99} :used 0 :reserved 0})]
    (is (thrown? clojure.lang.ExceptionInfo
                 (#'graph/graph-budget-operation! state {:helper-fuel 10 :attempt-fuel 20} :unknown
                   (fn [_ _] (throw (ex-info "no child packet" {}))))))
    (is (= 10 (:reserved @state)))
    (is (:budget-poisoned? @state))))

(deftest module-data-layout-and-scalar-guards-do-not-change-retained-input
  ;; Existing pinned record fixture includes the actual five-object/one-byte
  ;; ModuleData storage; its opaque CI payload is irrelevant to this shape gate.
  (let [[world data] (module-fixture/data-value (m/world {}))
        node (m/node world data)
        expected (#'graph/graph-data-arrays world data 10)
        constants (nth (:fields node) 2)
        bad-count (m/replace-node world constants (assoc (m/node world constants) :fields []))]
    (is (= 1 (count (:names expected)) (count (:constants expected)) (count (:extras expected))))
    (is (false? (:module? expected)))
    (is (thrown? clojure.lang.ExceptionInfo (#'graph/graph-data-arrays bad-count data 10)))
    (is (thrown? clojure.lang.ExceptionInfo (#'graph/graph-data-arrays world data 0)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (#'graph/graph-data-arrays (guest/scalar! world data 0 "uint8" 2) data 10)))
    (is (= expected (#'graph/graph-data-arrays world data 10)))
    (is (identical? node (m/node world data)))))

(deftest an-issued-graph-binding-still-rejects-a-forged-prefix-before-hashing
  (let [limits {:max-constants 32 :name-limits {:max-nodes 32 :max-chars 128}
                :max-nodes 128 :max-edges 256 :max-bytes 4096 :max-units 8 :max-declarations 64}
        configuration {:limits limits :graph-limits graph-limits :host-limits {:max-heap-entries 256}}
        {:keys [profile eval-binding]}
        (graph/prepare-source-graph-profile ["export"] {:witness ["witness"] :trusted-functions {}} configuration)]
    (is (some? eval-binding))
    (doseq [prefix [poison {:state :fake} nil]]
      (is (thrown? clojure.lang.ExceptionInfo (#'graph/graph-readiness! {} prefix profile))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (graph/prepare-source-graph-profile ["export"]
                   {:witness ["witness"] :trusted-functions {} :authorize-source-import identity}
                   configuration)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (graph/prepare-source-graph-profile ["export"] {:witness ["witness"] :trusted-functions {}}
                   (assoc configuration :allow-graph true))))))

(deftest registered-unsealed-graph-cannot-use-legacy-receipt-shaped-data
  (let [{:keys [world compiled name root]} (publication-fixture/ordinary-fixture)
        registered (source/register-compiled-graph world (publication-fixture/ordinary-invoke root)
                                                   compiled name source/init-requests)
        module publication-fixture/module digest publication-fixture/digest
        target ["answer"] local {:name target :sourceModule module :sourceLocal true}
        world (-> (:world registered)
                  (assoc-in [:eval-const-authorizations :declarations target] local)
                  (assoc-in [:eval-const-authorizations :unit-digests target] digest)
                  (assoc-in [:source-modules module :imports :forged]
                            {:unit-digest digest :anchor root :projected {}}))
        unit (get-in world [:source-modules module :unit]) calls (atom 0)
        reject (fn [& _] (swap! calls inc) (throw (AssertionError. "graph reached legacy helper")))
        [after accepted?] (source/authorize-imported-row world {:invoke reject :check-trusted-functions! reject}
                                                       (:environment compiled)
                                                       (assoc local :sourceLocal false) local unit)]
    (is (= :graph (get-in registered [:entry :profile])))
    (is (identical? world after))
    (is (false? accepted?))
    (is (zero? @calls))
    (is (thrown? clojure.lang.ExceptionInfo
                 (source/assemble world (publication-fixture/ordinary-invoke root) module name)))
    (is (thrown? clojure.lang.ExceptionInfo (#'graph/graph-node! (:entry registered))))))

(deftest distinct-manifest-only-modules-retain-empty-unit-provenance
  ;; This tests real source-bundle admission and graph's admission-delta proof,
  ;; not a claim that a theorem-only hosted graph has already been imported.
  (let [manifest (fn [module]
                   {:kind "manifest" :schema "lean-ir-probe/1" :leanVersion "4.33.1"
                    :leanCommit (get prim/pinned-build "lean_get_githash")
                    :producer "RuntimeCompileShim.exportCompiled"
                    :runtimeProfile {:target "x86_64-unknown-linux-gnu" :wordBits 64}
                    :initializationPlanScope "all-local-declarations"
                    :requestedRoots [] :entryPoints [] :missingDependencies [] :exports []
                    :initializationPlan {:kind "initialization-plan" :schema "lean-init-plan/1"
                                         :module module :moduleSystem false
                                         :imports [{:module source/init-module :meta false}
                                                   {:module source/init-module :meta true}]
                                         :actions []}})
        before (m/world {}) module-a (str-name "NoIRA") module-b (str-name "NoIRB")
        a (eval/install-bundle before (json/write-str (manifest module-a)) {})
        b (eval/install-bundle (:world a) (json/write-str (manifest module-b)) {})
        capture (fn [prior installed module]
                  (let [digest (:unit-digest installed)
                        unit (get-in installed [:world :eval-const-authorizations :units digest])]
                    (#'graph/capture-publication-admission! prior (:world installed)
                      {:module module :unit-digest digest :unit unit}
                      {:max-units 8 :max-declarations 16})))
        proof-a (capture before a module-a) proof-b (capture (:world a) b module-b)]
    (is (not= (:unit-digest a) (:unit-digest b)))
    (doseq [[installed proof module] [[a proof-a module-a] [b proof-b module-b]]]
      (is (= {} (:new-functions installed)))
      (is (= 1 (count (:units proof))))
      (is (= {} (:rows proof)))
      (is (zero? (:declaration-count proof)))
      (is (= module (get-in installed [:manifest :initializationPlan :module])))
      (is (= [] (get-in proof [:units (:unit-digest installed) :declarations]))))
    ;; Repeating the same digest from its already-admitted world is not a new
    ;; publication delta. Preserve this explicit limit; no empty-unit bypass.
    (let [again (eval/install-bundle (:world a) (json/write-str (manifest module-a)) {})]
      (is (thrown? clojure.lang.ExceptionInfo (capture (:world a) again module-a))))))

;; The following fixture exercises the PUBLIC node issuer over a genuinely
;; checked 17-CI native Source. Compiler/export callbacks are explicit models;
;; registration, raw getter transport, proof, ownership and minting are real.
(def publication-diagnostics (atom []))

(defn with-empty-publication [backend f & {:keys [local-ci? configure configuration-change]}]
  ((requiring-resolve 'prototype.resident-init-prefix-test/with-fixture) backend
    (fn [{:keys [context checked native-bindings] :as base}]
      (let [snapshot ((requiring-resolve 'prototype.resident-frontend/snapshot) context)
            modules (atom []) operations (atom []) compiler-calls (atom 0)
            module (str-name "EmptyGraphA") witness (str-name "GraphFixtureWitness")
            frontend-header @(requiring-resolve 'prototype.frontend/header-target)
            import-helpers @(requiring-resolve 'prototype.module-import/helpers)
            module-names @#'graph/module-names-helper
            specs {(:header source/helpers)
                   (fn [world _] [world (json/write-str {:schema "lean-source-import-header/1"
                     :producer "SourceModuleImport.finalizerHeader"
                     :leanCommit (get prim/pinned-build "lean_get_githash")
                     :moduleSystem false :imports source/init-requests})])
                   (:is-exporting graph/reconstruction-helpers) (fn [world _] [world 0])
                   module-names (fn [world _]
                                  (let [[world refs] (reduce (fn [[world refs] name]
                                                              (let [[world ref] (guest/guest-name world name)]
                                                                [world (conj refs ref)])) [world []] @modules)]
                                    (m/allocate world :array 246 refs)))
                   frontend-header (fn [world _]
                                     (m/allocate world :ctor 0
                                       [(json/write-str {:schema "lean-file-header/1"
                                         :producer "RuntimeCompileShim.inspectFileHeader"
                                         :leanCommit (get prim/pinned-build "lean_get_githash")
                                         :runtimeProfile {:target "x86_64-unknown-linux-gnu" :wordBits 64}
                                         :fileName "EmptyGraphA.lean" :moduleSystem false :hasErrors false
                                         :headerEndByte 0 :diagnostics [] :requestedImports source/init-requests})]))}
            signatures (into {} (for [[target _] specs]
                                  [target {:params (vec (repeat (if (= target frontend-header) 3 1)
                                                               {:ty "object" :borrow true}))
                                           :return-type (if (= target (:is-exporting graph/reconstruction-helpers)) "uint8" "object")}]))
            bindings (into {} (for [[target handler] specs]
                                [(str "graph_publication_model_" (pr-str target))
                                 {:signature (get signatures target)
                                  :handler (fn [_ world args] (swap! operations conj target) (handler world args))}]))
            helpers (into {} (for [[target signature] signatures
                                   :let [params (vec (range 1 (inc (count (:params signature)))))
                                         symbol (str "graph_publication_model_" (pr-str target))]]
                               [target {:params params :raw-extern {:symbol symbol :signature signature}
                                        :body [:host symbol (mapv #(vector :var %) params) (inc (count params))
                                               [:return [:var (inc (count params))]]]}]))
            functions (merge (zipmap graph/source-graph-roots (repeat {:params [] :body [:return [:imm 0]]}))
                             (:functions (:world snapshot)) @encoding-fixture/functions helpers
                             {witness {:params [] :body [:return [:imm 0]]}})
            configured (when configure (configure {:functions functions :bindings bindings
                                                   :checked checked :modules modules :operations operations
                                                   :snapshot snapshot}))
            functions (or (:functions configured) functions)
            bindings (or (:bindings configured) bindings)
            limits {:max-constants 64 :name-limits {:max-nodes 64 :max-chars 512}
                    :max-nodes 10000 :max-edges 20000 :max-bytes 1000000 :max-units 16
                    :max-declarations (if configure 4096 1024)}
            ;; The actual encoder decoder closure adds141 functions. Bound the
            ;; entire modeled baseline independently before choosing1024: at
            ;; most2*400 before/after functions plus the two-row admission delta.
            _ (when (> (count functions) (if configure 1024 400))
                (throw (ex-info "Publication fixture executable inventory exceeds calibrated bound" {})))
            created (graph/prepare-source-graph-profile witness {:witness witness :trusted-functions functions}
                      {:limits limits :graph-limits (assoc graph-limits :max-names 1000
                         :max-name-nodes 64 :max-name-bytes 512 :max-total-name-bytes 100000
                         :max-key-bytes 256 :max-total-key-bytes 4096)
                       :host-limits {:max-heap-entries 50000}})
            native (assoc (merge native-bindings bindings) "lean_eval_const" (:eval-binding created))
            hybrid (assoc (merge (source/make-hybrid-bindings native-bindings) bindings)
                          "lean_eval_const" (:eval-binding created))
            config (cond-> {:trusted-functions functions :trusted-bindings hybrid
                            :frontend-configuration {:install-options (:install-options created)}}
                     configuration-change configuration-change)
            prepared (assoc snapshot :world (assoc (:world snapshot) :functions functions)
                             :session ((requiring-resolve 'prototype.raw-interop/open-functions)
                                       functions hybrid {:backend backend :fuel 1000000}))
            adopted ((requiring-resolve 'prototype.resident-frontend/adopt-prepared) prepared config)
            prefixed (graph/prepare-init-prefix adopted checked {:configuration config :native-bindings native})
            prefix (:prefix prefixed)
            _ (reset! modules (mapv #(prototype.module-import/module-string (:module %))
                                   (get-in (#'graph/capability! prefix) [:prefix :modules])))
            captured (atom []) completed? (atom false)
            compile-model
            (fn [ctx _ _]
              (swap! compiler-calls inc)
              (let [entry ((requiring-resolve 'prototype.resident-frontend/snapshot) ctx)
                    _ (swap! captured conj entry)
                    ;; Actual Name/Expr IR constructors compute cache fields.
                    ;; ConstantInfo record assembly and compiler/export routing
                    ;; are modeled; independent Java shape equality and the
                    ;; fresh whole-map kernel check are real.
                    [world environment own-ci own-name own-extra]
                    (if local-ci?
                      (let [alpha (Name/mkStr Name/ANONYMOUS_NAME "alpha")
                            x (Name/mkStr Name/ANONYMOUS_NAME "x")
                            answer (Name/mkStr Name/ANONYMOUS_NAME "answer")
                            sort (expression/sort' (level/succ level/zero))
                            type (expression/forall' alpha sort
                                   (expression/forall' x (expression/bvar 0) (expression/bvar 1) :default) :default)
                            value (expression/lam alpha sort
                                    (expression/lam x (expression/bvar 0) (expression/bvar 0) :default) :default)
                            ci (kernel-env/mk-def answer [] type value)
                            invoke (fn [world target args]
                                     (let [result (raw/call (:session entry) world target args)]
                                       (swap! captured conj {:world (:state result) :session (:session result) :raw-result result})
                                       [(:state result) (:value result)]))
                            [world names] (encoding/encode-names (:world entry) invoke
                                            [alpha x answer (Name/mkStr answer "_boxed")])
                            [alpha-ref x-ref own-name own-extra] (:fields (m/node world names))
                            world (-> world (m/retain alpha-ref 1) (m/retain x-ref 1)
                                      (m/retain own-name 1) (m/retain own-extra 1) (m/release names 1))
                            target (fn [& segments] (reduce (fn [p s] ["str" p s]) ["anonymous"] segments))
                            [world one] (invoke world (target "Lean" "Level" "succ" "_override") [0])
                            [world sort-ref] (invoke world (target "Lean" "Expr" "sort" "_override") [one])
                            [world b0] (invoke world (target "Lean" "Expr" "bvar" "_override") [0])
                            [world b1] (invoke world (target "Lean" "Expr" "bvar" "_override") [1])
                            ;; Every constructor consumes ALL object args.
                            ;; Retain shared locals before each additional use.
                            [world inner-type] (invoke (-> world (m/retain x-ref 1) (m/retain b0 1))
                                                 (target "Lean" "Expr" "forallE" "_override")
                                                 [x-ref b0 b1 0])
                            [world type-ref] (invoke (-> world (m/retain alpha-ref 1) (m/retain sort-ref 1))
                                                (target "Lean" "Expr" "forallE" "_override")
                                                [alpha-ref sort-ref inner-type 0])
                            [world inner-value] (invoke (m/retain world b0 1)
                                                  (target "Lean" "Expr" "lam" "_override")
                                                  [x-ref b0 b0 0])
                            [world value-ref] (invoke world (target "Lean" "Expr" "lam" "_override")
                                                 [alpha-ref sort-ref inner-value 0])
                            ;; Cache-free ConstantVal/DefinitionVal/ConstantInfo
                            ;; fixed layouts match the pinned projector. Name has
                            ;; THREE owning uses: base, all-list, exported array.
                            world (m/retain world own-name 2)
                            [world base] (guest/ctor world 0 [own-name guest/nil-tag type-ref] 0)
                            [world all] (guest/ctor world 1 [own-name guest/nil-tag] 0)
                            [world definition] (guest/ctor world 0 [base value-ref guest/nil-tag all] 1)
                            world (guest/scalar! world definition 0 "uint8" 1)
                            [world own-ci] (guest/ctor world 1 [definition] 0)
                            _ (when-not (= (imported/checking-shape ci)
                                           (imported/checking-shape (imported/project-constant world own-ci)))
                                (throw (ex-info "Modeled guest definition differs from independent Java identity" {})))
                            values (conj (vec (vals (get-in checked [:certificate :constants]))) own-ci)
                            [world io] (publication-fixture/final-result world values)
                            finished (imports/finish-finalization world io
                                       (publication-fixture/final-invoke values source/init-requests 1)
                                       {:kernel-policy {:allow-axioms? true :allow-unsafe? true
                                                        ;; Reuse ONLY original immutable native projections;
                                                        ;; checking still starts from a fresh Java Env.
                                                        :projection-certificate (:certificate checked)}
                                        :finalizer-attestation {:requested-imports source/init-requests
                                                               :header-helper (:header source/helpers)}})
                            _ (swap! captured conj (assoc finished :independent-java-ci ci))]
                        [(:world finished) (:environment finished) own-ci own-name own-extra])
                      [(:world entry) (:environment entry) nil nil nil])
                    ;; Explicit test-only Environment model decoration. The
                    ;; staged fixture owns its immutable header payload in the
                    ;; guest envelope, rather than adding unsupported World keys.
                    [world environment] (if-let [decorate (:decorate-compiled-environment configured)]
                                          (decorate world environment) [world environment])
                    digest (apply str (repeat 64 "d"))
                    unit {:actions [] :declarations []
                          :manifest {:initializationPlan {:module module :actions []
                            :imports (mapv #(hash-map :module (:module %) :meta (:isMeta %)) source/init-requests)}}}
                    [world init-name]
                    (if-not configure [world nil]
                      ;; Encode before bundle installation: ENTRY's session
                      ;; matches this exact function map. Keep the returned
                      ;; owner until the exporter transfers it into imports.
                      (encoding/encode-name world
                        (fn [world target args]
                          (let [called (raw/call (:session entry) world target args)]
                            (swap! captured conj {:raw-result called})
                            [(:state called) (:value called)])) (Name/fromString "Init")))
                    installed
                    (when local-ci?
                      (let [rows (mapv #(json/read-str % :key-fn keyword)
                                       (str/split-lines (slurp "fixtures/hosted/PreludeIdentity.ir.jsonl")))
                            rows (mapv (fn [row] (if (= "manifest" (:kind row))
                                                 (-> row (assoc-in [:initializationPlan :module] module)
                                                     (assoc-in [:initializationPlan :imports]
                                                       (mapv #(hash-map :module (:module %) :meta (:isMeta %)) source/init-requests)))
                                                 (assoc row :sourceModule module))) rows)]
                        (eval/install-bundle world (str/join "\n" (map json/write-str rows)) {})))
                    world (if installed (:world installed)
                              (assoc-in world [:eval-const-authorizations :units digest] unit))
                    digest (if installed (:unit-digest installed) digest)
                    [world name] (guest/guest-name world "EmptyGraphA")
                    compilation {:success true :world world :environment environment
                                 :handle {:module-name module :unit-digest digest}
                                 :envelope {:success true :stage "complete" :mainModule module
                                            :moduleSystem false :requestedImports source/init-requests}}
                    exporter (fn [world target args]
                               (if (= target (:root import-helpers))
                                 (let [root (first (:fields (m/node world (first args))))]
                                   [(m/retain world root 1) root])
                                 (let [[world data] (module-fixture/data-value world)
                                       fields (:fields (m/node world data))
                                       ;; The staged actual-G1 fixture needs real cached
                                       ;; Name hashes in its ModuleData import array.
                                       ;; The older shape-only fixtures use fake names.
                                       world (if-not configure world
                                               (let [requests (:fields (m/node world (first fields)))
                                                     world (m/retain world init-name (dec (count requests)))]
                                                 (reduce (fn [world request]
                                                           (let [node (m/node world request) old (first (:fields node))]
                                                             (m/release (m/replace-node world request (assoc node :fields [init-name])) old 1)))
                                                         world requests)))
                                       world (reduce (fn [world array]
                                                       (let [old (:fields (m/node world array))]
                                                         (reduce #(m/release %1 %2 1)
                                                           (m/replace-node world array (assoc (m/node world array) :fields [])) old)))
                                                     world (rest fields))
                                       world (if-not local-ci? world
                                               (reduce (fn [world [array values]]
                                                         (m/replace-node world array (assoc (m/node world array) :fields values)))
                                                 world [[(nth fields 1) [own-name]]
                                                        [(nth fields 2) [own-ci]] [(nth fields 3) [own-extra]]]))
                                       world (-> world (m/release (first args) 1) (m/release (second args) 1))
                                       metadata (assoc module-fixture/metadata :module module
                                                       :constantNames (if local-ci? [(str-name "answer")] [])
                                                       :constantCount (if local-ci? 1 0)
                                                       :extraConstantNames (if local-ci? [["str" (str-name "answer") "_boxed"]] [])
                                                       :extensions [])
                                       [world pair] (m/allocate world :ctor 0 [data (json/write-str metadata)])]
                                   (m/allocate world :ctor 0 [pair]))))
                    registered (source/register-compiled-graph world exporter compilation name source/init-requests)
                    packet (assoc entry :world (:world registered) :environment environment
                                  :session (raw/open-functions (:functions (:world registered)) hybrid
                                                              {:backend backend :fuel 1000000}))
                    result-context ((requiring-resolve 'prototype.resident-frontend/adopt-prepared) packet config)]
                (swap! captured conj packet result-context)
                {:context result-context :success true :publication {:profile :graph}}))]
        (try
          (f {:context (:context prefixed) :prefix prefix :profile (:profile created)
              :checked checked :configuration config :compile-model compile-model :compiler-calls compiler-calls
              :operations operations :captured captured :source (:source base)
              :transport configured :eval-binding (:eval-binding created) :issued-install-options (:install-options created)
              :request {:text (if local-ci? "import Init\ndef answer (alpha : Type) (x : alpha) : alpha := x\n" "import Init\n")
                        :file-name "EmptyGraphA.lean"
                        :module-name (Name/mkStr Name/ANONYMOUS_NAME "EmptyGraphA")
                        :roots (if local-ci? [(Name/mkStr Name/ANONYMOUS_NAME "answer")] []) :initialization :defer}})
          (reset! completed? true)
          (catch Throwable cause
            (swap! publication-diagnostics conj {:backend backend :cause cause :packets @captured})
            (throw (ex-info (or (.getMessage cause) "Publication fixture failed")
                            {:fixture-backend backend :private-diagnostic-index (dec (count @publication-diagnostics))} cause)))
          (finally
            (doseq [ctx (concat [(:context prefixed) adopted]
                                ;; Baseline fixture contexts close separately. Unexpected
                                ;; publication failures retain their actual Context states;
                                ;; the enclosing native-Source fixture still closes its Store.
                                (when @completed?
                                  (filter #(instance? prototype.resident_frontend.Context %) @captured)))]
              ((requiring-resolve 'prototype.resident-frontend/close!) ctx))))))))

(deftest public-empty-node-is-sealed-without-completed-import-permission
  (doseq [backend [:reference :mutable :jvm]]
    (with-empty-publication backend
      (fn [{:keys [context prefix profile compile-model compiler-calls request source captured configuration] :as fixture}]
        (let [snapshot (requiring-resolve 'prototype.resident-frontend/snapshot)
              before (snapshot context)
              result (with-redefs-fn {(requiring-resolve 'prototype.resident-source/load-and-publish-graph) compile-model}
                       #(graph/publish-source-graph-node context request prefix profile []
                          {:proof-budgets {:helper-fuel 1000000 :attempt-fuel 10000000}}))
              node (#'graph/graph-node! (:graph-node result))
              after (snapshot (:context result))
              helper-calls (atom 0)
              deny (fn [& _] (swap! helper-calls inc) (throw (AssertionError. "unimported graph reached getter")))
              p (#'graph/graph-profile! profile)
              [world accepted?] (#'graph/authorize-completed-graph-row (:token p) (:limits p) (:graph-limits p)
                                 (:world after) {:invoke deny} (:environment after)
                                 {:sourceModule (str-name "EmptyGraphA") :name (str-name "absent")} {} {})]
          (is (= 1 @compiler-calls))
          (is (= 1 (get-in result [:graph-publication :unit-count])))
          (is (zero? (get-in result [:graph-publication :row-count])))
          (is (zero? (get-in result [:graph-publication :constant-count])))
          (let [forbidden (vec (concat [before (:world before) (:session before) context result after
                                        (:world after) (:session after)]
                                      @captured
                                      (mapcat (fn [packet] (when (map? packet)
                                                            [(:world packet) (:session packet)])) @captured)))
                seen (java.util.IdentityHashMap.)
                retains? (fn walk [value]
                           (cond
                             (nil? value) false
                             (some #(identical? value %) forbidden) true
                             (identical? configuration value) false
                             (.containsKey seen value) false
                             :else (do (.put seen value true)
                                       (cond (map? value) (boolean (some walk (concat (keys value) (vals value))))
                                             (coll? value) (boolean (some walk value))
                                             :else false))))]
            (is (false? (retains? node))))
          (is (= :graph (get-in node [:entry :profile])))
          (is (= {} (get-in node [:proof :constants])))
          (is (nil? (get-in after [:world :source-modules (str-name "EmptyGraphA") :graph-import])))
          (is (true? (identical? (:world after) world))) (is (false? accepted?)) (is (zero? @helper-calls))
          (is (true? (identical? before (snapshot context))))
          (is (false? @(:closed source)))
          ((requiring-resolve 'prototype.resident-frontend/close!) (:context result)))))))

(deftest returned-final-adoption-context-is-escrowed-before-snapshot-failure
  (with-empty-publication :reference
    (fn [{:keys [context prefix profile request compile-model]}]
      (let [adopt-var (requiring-resolve 'prototype.resident-frontend/adopt-prepared)
            snapshot-var (requiring-resolve 'prototype.resident-frontend/snapshot)
            adopt @adopt-var snapshot @snapshot-var returned (atom [])
            failure (ex-info "selected post-adoption snapshot failure" {:fixture-stage :snapshot})
            cause (with-redefs-fn
                    {(requiring-resolve 'prototype.resident-source/load-and-publish-graph) compile-model
                     adopt-var (fn [& args] (let [ctx (apply adopt args)] (swap! returned conj ctx) ctx))
                     snapshot-var (fn [ctx]
                                    (when (and (= 3 (count @returned)) (identical? ctx (last @returned)))
                                      (throw failure))
                                    (snapshot ctx))}
                    #(try (graph/publish-source-graph-node context request prefix profile []
                            {:proof-budgets {:helper-fuel 1000000 :attempt-fuel 10000000}})
                          nil (catch clojure.lang.ExceptionInfo cause cause)))]
        (is (some? cause))
        (is (true? (identical? failure (.getCause cause))))
        (is (:source-graph-publication-terminal? (ex-data cause)))
        (is (true? (identical? (last @returned)
                       (get-in (ex-data cause) [:source-graph-publication-state :adopted-context]))))
        (is (= :failed (get-in (ex-data cause) [:source-graph-publication-state :phase])))
        (doseq [ctx @returned] ((requiring-resolve 'prototype.resident-frontend/close!) ctx))))))

(deftest public-local-ci-node-captures-actual-identity-ir-without-import-permission
  (doseq [backend [:reference :mutable :jvm]]
    (with-empty-publication backend
      (fn [{:keys [context prefix profile compile-model request captured configuration checked]}]
        (let [snapshot (requiring-resolve 'prototype.resident-frontend/snapshot)
              before (snapshot context)
              result (with-redefs-fn {(requiring-resolve 'prototype.resident-source/load-and-publish-graph) compile-model}
                       #(graph/publish-source-graph-node context request prefix profile []
                          {:proof-budgets {:helper-fuel 1000000 :attempt-fuel 10000000}}))
              after (snapshot (:context result)) node (#'graph/graph-node! (:graph-node result))
              p (#'graph/graph-profile! profile)
              rows (get-in node [:proof :admission :rows])
              {:keys [row unit function]} (get rows (str-name "answer"))
              called (raw/call (:session after) (:world after) (str-name "answer") [m/erased 41])
              _ (swap! captured conj {:world (:state called) :session (:session called) :raw-result called})
              count-helper (atom 0)
              deny (fn [& _] (swap! count-helper inc) (throw (AssertionError. "unimported row queried helper")))
              [denied accepted?] (#'graph/authorize-completed-graph-row (:token p) (:limits p) (:graph-limits p)
                                  (:world after) {:invoke deny} (:environment after)
                                  (assoc row :sourceLocal false) row unit)]
          (is (= 1 (get-in result [:graph-publication :constant-count])))
          (is (= 2 (get-in result [:graph-publication :row-count])))
          (is (= 1 (get-in result [:graph-publication :unit-count])))
          (is (= 41 (:value called)))
          (is (true? (identical? function (get-in after [:world :functions (str-name "answer")]))))
          (let [^ansatz.kernel.Env compiled-checked
                (get-in after [:world :kernel-environments
                               (:id (first (:fields (m/node (:world after) (:environment after))))) :env])
                own-reference (get-in node [:proof :constants (Name/mkStr Name/ANONYMOUS_NAME "answer")])
                independent (:independent-java-ci (first (filter :independent-java-ci @captured)))]
            (is (= 18 (count (.allConstants compiled-checked))))
            (is (false? (identical? compiled-checked (get-in checked [:certificate :env]))))
            (is (true? (every? (fn [[name ci]] (identical? ci (.lookup compiled-checked name)))
                              (get-in checked [:certificate :projected]))))
            (is (false? (m/native-reference? (:world after) own-reference)))
            (is (some? (.lookup compiled-checked (Name/mkStr Name/ANONYMOUS_NAME "answer"))))
            (is (false? (identical? independent (.lookup compiled-checked (Name/mkStr Name/ANONYMOUS_NAME "answer"))))))
          (is (false? accepted?)) (is (zero? @count-helper))
          (is (true? (identical? denied (:world after))))
          (is (true? (identical? before (snapshot context))))
          (let [forbidden (vec (mapcat (fn [packet]
                                        (if (map? packet)
                                          [packet (:world packet) (:session packet) (get-in packet [:certificate :env]) (:independent-java-ci packet)]
                                          [packet])) @captured))
                seen (java.util.IdentityHashMap.)
                retains? (fn walk [value]
                           (cond (nil? value) false
                                 (some #(identical? value %) forbidden) true
                                 (identical? value configuration) false
                                 (.containsKey seen value) false
                                 :else (do (.put seen value true)
                                           (cond (map? value) (boolean (some walk (concat (keys value) (vals value))))
                                                 (coll? value) (boolean (some walk value))
                                                 :else false))))]
            (is (false? (retains? node))))
          ;; Full ModuleData evidence includes the extra-only boxed Name; the
          ;; numeric Ref itself is not an immutable publication witness.
          (let [extra (get-in node [:wire-names ["str" (str-name "answer") "_boxed"]])
                altered (m/replace-node (:world after) extra (assoc (m/node (:world after) extra) :tag 99))]
            (is (thrown? clojure.lang.ExceptionInfo (#'graph/graph-entry-matches! altered node))))
          ((requiring-resolve 'prototype.resident-frontend/close!) (:context result))))
      :local-ci? true)))

(deftest header-mismatch-retains-owned-parser-result-before-any-compilation
  (with-empty-publication :reference
    (fn [{:keys [context prefix profile request compile-model compiler-calls]}]
      (let [before ((requiring-resolve 'prototype.resident-frontend/snapshot) context)
            cause (with-redefs-fn {(requiring-resolve 'prototype.resident-source/load-and-publish-graph) compile-model}
                    #(try (graph/publish-source-graph-node context (assoc request :file-name "Other.lean") prefix profile []
                            {:proof-budgets {:helper-fuel 1000000 :attempt-fuel 10000000}})
                          nil (catch clojure.lang.ExceptionInfo cause cause)))
            state (:source-graph-publication-state (ex-data cause))]
        (is (some? cause)) (is (zero? @compiler-calls))
        (is (= :owned (get-in state [:header-result :status])))
        (is (m/ref? (get-in state [:header-result :value])))
        (is (= :failed (:phase state)))
        (is (true? (identical? before ((requiring-resolve 'prototype.resident-frontend/snapshot) context))))))))
