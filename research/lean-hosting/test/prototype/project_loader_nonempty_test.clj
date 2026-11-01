(ns prototype.project-loader-nonempty-test
  "Real Project load/invoke with actual kernel admission and frontend install.
   Fixed header/compiler/export/witness/finalizer transport remains a MODEL."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.string :as str]
            [ansatz.kernel.expr :as expression]
            [ansatz.kernel.level :as level]
            [ansatz.kernel.env :as kernel-env]
            [prototype.project-loader-integration-test :as empty]
            [prototype.project-loader-test :as protocol]
            [prototype.project-discovery-test :as files]
            [prototype.project-loader :as loader]
            [prototype.source-graph-runtime-test :as publication]
            [prototype.source-graph-staged-test :as staged]
            [prototype.native-init-base-test :as native]
            [prototype.frontend :as frontend]
            [prototype.source-module :as source-module]
            [prototype.source-module-test :as module-model]
            [prototype.source-import :as source]
            [prototype.runtime-prim :as prim]
            [prototype.machine :as m]
            [prototype.interop-codec :as codec]
            [prototype.guest-encoding :as encoding]
            [prototype.kernel-bridge-test :as record]
            [prototype.kernel-bridge :as bridge]
            [prototype.imported-kernel :as imported]
            [prototype.resident-frontend :as resident])
  (:import [ansatz.kernel Name]))
(defn identity-constant! [context world]
  (let [before world
        invoke (fn [world target args]
                 (let [[next value] ((:invoke context) world target args)]
                   [(empty/keep-control world next) value]))
        alpha (Name/fromString "alpha") x (Name/fromString "x") answer (Name/fromString "answer")
        sort (expression/sort' (level/succ level/zero))
        type (expression/forall' alpha sort
               (expression/forall' x (expression/bvar 0) (expression/bvar 1) :default) :default)
        value (expression/lam alpha sort
                (expression/lam x (expression/bvar 0) (expression/bvar 0) :default) :default)
        expected (kernel-env/mk-def answer [] type value)
        [world names] (encoding/encode-names world invoke [alpha x answer (Name/fromString "answer._boxed")])
        ;; Encoder unwrap clears :result for top-level callers. This is an
        ;; active raw host handler: restore parent result BEFORE the next nested
        ;; raw call, whose guard checks entry control state, not just our return.
        world (empty/keep-control before world)
        [alpha-ref x-ref own-name own-extra :as refs] (staged/fields world names)
        world (-> (reduce #(m/retain %1 %2 1) world refs) (m/release names 1))
        target (fn [name] (files/wire ["Lean" "Expr" name "_override"]))
        [world one] (invoke world (files/wire ["Lean" "Level" "succ" "_override"]) [0])
        [world sort-ref] (invoke world (target "sort") [one])
        [world b0] (invoke world (target "bvar") [0])
        [world b1] (invoke world (target "bvar") [1])
        [world inner-type] (invoke (-> world (m/retain x-ref 1) (m/retain b0 1))
                              (target "forallE") [x-ref b0 b1 0])
        [world type-ref] (invoke (-> world (m/retain alpha-ref 1) (m/retain sort-ref 1))
                             (target "forallE") [alpha-ref sort-ref inner-type 0])
        [world inner-value] (invoke (m/retain world b0 1) (target "lam") [x-ref b0 b0 0])
        [world value-ref] (invoke world (target "lam") [alpha-ref sort-ref inner-value 0])
        world (m/retain world own-name 2)
        [world base] (record/ctor world 0 [own-name (m/->Tag 0) type-ref] 0)
        [world all] (record/ctor world 1 [own-name (m/->Tag 0)] 0)
        [world definition] (record/ctor world 0 [base value-ref (m/->Tag 0) all] 1)
        world (record/scalar! world definition 0 "uint8" 1)
        [world declaration] (record/ctor world 1 [definition] 0)]
    (when-not (= (imported/checking-shape expected)
                 (imported/checking-shape (imported/project-constant world declaration)))
      (empty/fail "Identity CI differs from independently built Java declaration"))
    [(empty/keep-control before world) declaration own-name own-extra expected]))

(defn own-constant! [world environment expected]
  ;; Observation is bounded and requires exactly one complete projected Name
  ;; match; a Ref ID never serves as an authority or metadata lookup key.
  (let [root (first (staged/fields world environment))
        values (staged/fields world (first (staged/fields world root)))]
    (when-not (and (vector? values) (<= (count values) 64))
      (empty/fail "Own constant scan exceeds fixture bound"))
    (let [matches (filterv (fn [ci]
                            ;; Generic existing CI-kind dispatch with bounded
                            ;; guest Name projection, before equality or lookup.
                            (let [projected (imported/project-constant-name
                                               world ci {:max-nodes 64 :max-chars 512})]
                              (= (.name ^ansatz.kernel.ConstantInfo expected) projected))) values)]
      (when-not (= 1 (count matches)) (empty/fail "Own declaration is missing or duplicated"))
      (let [ci (first matches)]
        (when-not (= (imported/checking-shape expected)
                     (imported/checking-shape (imported/project-constant world ci)))
          (empty/fail "Published own declaration differs from intended Java definition"))
        ci))))
;; Model only compiler transport; guest CI construction and kernel admission run.
(def module staged/module-a)
(def answer staged/answer-a)
(def source-text "def answer (alpha : Type) (x : alpha) : alpha := x\n")
(def source-text-edited "-- rebuilt identity\ndef answer (alpha : Type) (x : alpha) : alpha := x\n")
(def final-view "import «EmptyGraphA»\n")
(defn unit-rows []
  (into [(-> (first (staged/fixture-rows))
             (assoc-in [:initializationPlan :module] module)
             (assoc-in [:initializationPlan :imports]
                       (mapv #(hash-map :module (:module %) :meta (:isMeta %)) source/init-requests)))]
        (map #(assoc % :sourceModule module :sourceLocal true) (rest (staged/fixture-rows)))))
(defn compile-handler [configured calls]
  (fn [context world [environment text filename main roots options erased :as arguments]]
    (let [before world text-host (codec/decode world :string text)
          file-host (codec/decode world :string filename)
          _ (when-not (and (contains? #{source-text source-text-edited} text-host)
                           (= module (empty/wire-name world main))
                           (= [answer] (mapv #(empty/wire-name world %) (staged/fields world roots))))
              (empty/fail "Nonempty compiler model received different captured inputs"))
          ;; First compiler branch starts from the fixture's one-field native
          ;; Environment. Descriptive metadata is a test transport payload; it
          ;; carries no checked association or authority.
          [world environment] (if (= 1 (count (staged/fields world environment)))
                                ((:decorate-compiled-environment configured) world environment)
                                [world environment])
          [world declaration own-name own-extra expected] (identity-constant! context world)
          ;; Negative fixture changes the definition's value to its Pi TYPE,
          ;; which has the wrong type. Constructed CI shape is otherwise exact;
          ;; rejection must come from actual kernel checking, not transport.
          world (if (:invalid-identity? configured)
                  (let [definition (first (staged/fields world declaration))
                        definition-fields (staged/fields world definition)
                        base (first definition-fields) type (nth (staged/fields world base) 2)
                        old-value (second definition-fields)]
                    (-> world (m/retain type 1)
                        (m/replace-node definition (assoc (m/node world definition) :fields (assoc definition-fields 1 type)))
                        (m/release old-value 1))) world)
          ;; The actual kernel-host binding consumes this compiler-owned Env.
          ;; The caller's independent borrowed original Context remains intact.
          [world result] ((:invoke context) world (:kernel-probe configured)
                          [environment 1000000 1000 declaration (m/->Tag 0)])
          _ (when-not (and (= 1 (:tag (m/node world result)))
                           (bridge/constructor-layout? (m/node world result) 1 0))
              (throw (ex-info "Actual kernel host rejected the identity declaration"
                              {:checkpoint world :kernel-result result :kernel-admitted? false
                               :kernel-owners {:compiler-environment :consumed-by-kernel
                                               :except-result result :declaration declaration
                                               :own-name own-name :own-extra own-extra
                                               :remaining-inputs (vec (rest arguments))}})))
          next-environment (first (staged/fields world result))
          world (-> world (m/retain next-environment 1) (m/release result 1)
                    (m/release declaration 1) (m/release own-name 1) (m/release own-extra 1))
          ;; Environment was consumed by the actual kernel operation above.
          world (reduce #(m/release %1 %2 1) world (rest arguments))
          envelope {:schema "lean-file-compilation/1" :producer "RuntimeCompileShim.compileImportedFileState"
                    :leanCommit (get prim/pinned-build "lean_get_githash") :runtimeProfile (empty/profile)
                    :fileName file-host :mainModule module :moduleSystem false :requestedImports source/init-requests
                    :success true :stage "complete" :environmentState "after-commands" :diagnostics []
                    :bundle (str/join "\n" (map json/write-str (unit-rows)))}
          ;; Restore only parent control state changed by nested helper calls.
          world (empty/keep-control before world)
          [world pair] (m/allocate world :ctor 0 [next-environment (json/write-str envelope)])
          returned (m/allocate world :ctor 0 [pair])]
      (swap! calls conj {:event :compile :text text-host :expected expected}) returned)))

(defn expected-identity []
  (let [alpha (Name/fromString "alpha") x (Name/fromString "x")
        sort (expression/sort' (level/succ level/zero))]
    (kernel-env/mk-def (Name/fromString "answer") []
      (expression/forall' alpha sort
        (expression/forall' x (expression/bvar 0) (expression/bvar 1) :default) :default)
      (expression/lam alpha sort
        (expression/lam x (expression/bvar 0) (expression/bvar 0) :default) :default))))
(defn header-handler [_ world [text filename erased :as arguments]]
  (let [text (codec/decode world :string text) filename (codec/decode world :string filename)
        _ (when-not (contains? #{source-text source-text-edited final-view} text)
            (empty/fail "Nonempty header model received unexpected captured text"))
        imports (if (= final-view text) (empty/requested [["EmptyGraphA"]]) source/init-requests)
        envelope {:schema "lean-file-header/1" :producer "RuntimeCompileShim.inspectFileHeader"
                  :leanCommit (get prim/pinned-build "lean_get_githash") :runtimeProfile (empty/profile)
                  :fileName filename :moduleSystem false :hasErrors false :headerEndByte (empty/utf8 text)
                  :diagnostics [] :requestedImports imports}
        world (reduce #(m/release %1 %2 1) world arguments)]
    (m/allocate world :ctor 0 [(json/write-str envelope)])))
(defn export-handler [context world [environment name erased :as arguments]]
  (when-not (= module (empty/wire-name world name)) (empty/fail "Nonempty exporter main module differs"))
  (let [expected (expected-identity) own-ci (own-constant! world environment expected)
        own-name (first (staged/fields world (first (staged/fields world (first (staged/fields world own-ci))))))
        [world own-extra] (empty/encode-name context world (Name/fromString "answer._boxed"))
        [world requests]
        (reduce (fn [[world out] request]
                  (let [[world n] (empty/encode-name context world (staged/model-index-name (:module request)))
                        [world r] (staged/packed! world [n] 3 {0 (if (:importAll request) 1 0)
                                                           1 (if (:isExported request) 1 0)
                                                           2 (if (:isMeta request) 1 0)})]
                    [world (conj out r)])) [world []] source/init-requests)
        [world imports] (staged/array! world requests)
        [world names] (staged/array! (m/retain world own-name 1) [own-name])
        [world constants] (staged/array! (m/retain world own-ci 1) [own-ci])
        [world extras] (staged/array! world [own-extra])
        [world extensions] (staged/array! world [])
        [world data] (staged/packed! world [imports names constants extras extensions] 1 {0 0})
        metadata (assoc module-model/metadata :module module :imports source/init-requests
                        :constantNames [answer] :constantCount 1 :extraConstantNames [(staged/boxed answer)] :extensions [])
        world (reduce #(m/release %1 %2 1) world arguments)
        [world pair] (m/allocate world :ctor 0 [data (json/write-str metadata)])]
    (m/allocate world :ctor 0 [pair])))
(defn configure [input]
  ;; Start with exactly reviewed empty-integration transport models, then replace
  ;; only those exact three function bodies before profile/config capture. No
  ;; protected real Lean executable is modified or loaded during an operation.
  (let [configured (assoc (empty/configure input) :invalid-identity? (true? (:invalid-identity? input))) calls (atom [])
        handlers {frontend/header-target [3 header-handler]
                  frontend/compile-target [7 (compile-handler configured calls)]
                  source-module/export-helper [3 export-handler]}]
    (assoc
      (reduce-kv
        (fn [out target [arity handler]]
          (let [old-symbol (str "project_loader_fixed_model_" (pr-str target))
                signature {:params (vec (repeat arity {:ty "object" :borrow false})) :return-type "object"}
                _ (when-not (= (get-in configured [:functions target]) (empty/model-function old-symbol arity signature))
                    (empty/fail "Nonempty setup would replace an unknown helper"))
                symbol (str "project_loader_nonempty_fixed_model_" (pr-str target))]
            (-> out (assoc-in [:bindings symbol] {:signature signature :handler handler})
                    (assoc-in [:functions target] (empty/model-function symbol arity signature))))) configured handlers)
      :nonempty-calls calls)))
(def diagnostics (atom nil))
(defn call! [owned project value]
  (let [called (loader/invoke project module (Name/fromString "answer") [nil value]
                             {:arguments [:erased :nat] :result :nat})]
    (swap! owned conj (:project called)) (is (= value (:value called))) called))
(deftest actual-kernel-admitted-file-is-callable-and-rebuild-keeps-old-version
  (doseq [backend [:reference :mutable :jvm]]
    (files/with-files {["EmptyGraphA"] source-text}
      (fn [root provider]
        (publication/with-empty-publication backend
          (fn [{:keys [transport] :as fixture}]
            (let [owned (atom [])]
              (try
                (let [token (native/modeled-stage-token fixture)
                      ready (native/modeled-guards-context fixture (:context fixture) native/complete-guards)
                      policies {:discovery-budgets {:helper-fuel 1000000 :attempt-fuel 100000000}
                                :publication-budgets {:helper-fuel 1000000 :attempt-fuel 100000000}
                                :import-options {:kernel-policy staged/policy :budgets staged/budgets}
                                :native-options {:kernel-policy staged/policy :budgets staged/budgets}}
                      project (loader/open-project ready (assoc (protocol/options fixture provider) :native-readiness token :policies policies))
                      _ (swap! owned conj project)
                      request {:module module :exports [{:module module :roots [(Name/fromString "answer")]}]}
                      loaded (loader/load-file project request {:max-operations 1 :wall-ms 100})
                      old (:project loaded) _ (swap! owned conj old)
                      old-data (#'loader/version! old)
                      old-packet (resident/snapshot (:context old-data))
                      file (get-in loaded [:files ["EmptyGraphA"]])
                      entry (get-in old-packet [:world :source-modules module])
                      own-ci (own-constant! (:world old-packet) (:environment entry) (expected-identity))]
                  (is (instance? prototype.resident_frontend.FileHandle file))
                  (is (identical? (:unit entry) (.-unit ^prototype.resident_frontend.FileHandle file)))
                  (is (= #{answer (staged/boxed answer)} (set (get-in entry [:unit :declarations]))))
                  (is (= 1 (get-in entry [:metadata :constantCount])))
                  (is (= (imported/checking-shape (expected-identity))
                         (imported/checking-shape (imported/project-constant (:world old-packet) own-ci))))
                  (doseq [n [0 41 10000000000]] (call! owned old n))
                  ;; Rebuild the SAME semantically identical function from a
                  ;; different immutable text capture. This proves independent
                  ;; version/Context ownership, not changed function semantics.
                  (files/write! root ["EmptyGraphA"] source-text-edited)
                  (let [rebuilt (loader/load-file old request {:max-operations 1 :wall-ms 100})
                        newer (:project rebuilt) _ (swap! owned conj newer)
                        new-data (#'loader/version! newer)]
                    (is (= source-text (get-in old-data [:captures ["EmptyGraphA"] :text])))
                    (is (= source-text-edited (get-in new-data [:captures ["EmptyGraphA"] :text])))
                    (is (= [source-text source-text-edited] (mapv :text @(:nonempty-calls transport))))
                    (is (identical? old-packet (resident/snapshot (:context old-data))))
                    (is (not (identical? (:context old-data) (:context new-data))))
                    (call! owned newer 42) (call! owned old 41)
                    (loader/close-project! old)
                    (call! owned newer 99))
                  (doseq [p (reverse @owned)] (loader/close-project! p))
                  (reset! owned []))
                (catch Throwable cause
                  (compare-and-set! diagnostics nil {:cause cause :projects @owned :backend backend})
                  (throw cause)))))
          :configure configure)))))


(defn kernel-failure-evidence [cause]
  (loop [cause cause remaining 32]
    (when (and cause (pos? remaining))
      (let [data (ex-data cause)]
        (if (contains? data :kernel-result) data
          (recur (.getCause ^Throwable cause) (dec remaining)))))))
(deftest invalid-definition-is-rejected-by-actual-kernel-before-publication
  (doseq [backend [:reference :mutable :jvm]]
    (files/with-files {["EmptyGraphA"] source-text}
      (fn [_ provider]
        (publication/with-empty-publication backend
          (fn [{:keys [transport] :as fixture}]
            (let [token (native/modeled-stage-token fixture)
                  ready (native/modeled-guards-context fixture (:context fixture) native/complete-guards)
                  before (resident/snapshot ready)
                  policies {:discovery-budgets {:helper-fuel 1000000 :attempt-fuel 100000000}
                            :publication-budgets {:helper-fuel 1000000 :attempt-fuel 100000000}
                            :import-options {:kernel-policy staged/policy :budgets staged/budgets}
                            :native-options {:kernel-policy staged/policy :budgets staged/budgets}}
                  project (loader/open-project ready (assoc (protocol/options fixture provider) :native-readiness token :policies policies))
                  cause (protocol/thrown #(loader/load-file project
                                             {:module module :exports [{:module module :roots [(Name/fromString "answer")]}]}
                                             {:max-operations 1 :wall-ms 100}))
                  evidence (kernel-failure-evidence cause)]
              (is (some? cause))
              (is (true? (:project-load-terminal? (ex-data cause))))
              (is (false? (:kernel-admitted? evidence)))
              (when evidence
                (let [node (m/node (:checkpoint evidence) (:kernel-result evidence))]
                  (is (= 0 (:tag node)))
                  (is (bridge/constructor-layout? node 1 0))
                  (is (nil? (get-in evidence [:checkpoint :source-modules module])))
                  (is (= :consumed-by-kernel (get-in evidence [:kernel-owners :compiler-environment])))
                  (doseq [value (concat (map #(get-in evidence [:kernel-owners %])
                                            [:except-result :declaration :own-name :own-extra])
                                       (get-in evidence [:kernel-owners :remaining-inputs]))
                          :when (m/ref? value)]
                    (is (some? (m/node (:checkpoint evidence) value))))))
              (is (empty? @(:nonempty-calls transport)))
              (is (identical? before (resident/snapshot ready)))
              ;; Failed owned child packets intentionally remain retained by the
              ;; diagnostic token; only this separately issued version closes.
              (compare-and-set! diagnostics nil {:cause cause :backend backend})
              (loader/close-project! project)))
          :configure #(configure (assoc % :invalid-identity? true)))))))
