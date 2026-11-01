(ns prototype.source-inductive-preparation-test
  "Host-only models. Generated fixtures below are NOT Lean admission or
   publication evidence. Production functions/linker are exercised without guest calls."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.java.io :as io]
            [prototype.checkpoint-wire :as wire]
            [prototype.source-inductive-preparation :as preparation]
            [prototype.kernel-host :as kernel]
            [prototype.raw-interop :as raw]))
(defn bytes [s] (.getBytes ^String s java.nio.charset.StandardCharsets/UTF_8))
(def manifest
  {:kind "manifest" :schema "lean-ir-probe/1" :leanVersion "4.33.1"
   :runtimeProfile {:target "x86_64-unknown-linux-gnu" :wordBits 64}
   :modules [] :exports []
   :initializationPlan {:kind "initialization-plan" :schema "lean-init-plan/1"
                        :moduleSystem false :module ["str" ["anonymous"] "Model"] :imports [] :actions []}})
(defn row [name borrows]
  {:kind "decl" :name name :dependencies [] :runtime {:role "ordinary" :initializer nil}
   :sourceLocal true :sourceModule ["str" ["anonymous"] "Model"]
   :ir {:fdecl {:f name :info {} :type "object"
                :xs (mapv (fn [i borrow] {:x {:idx i} :ty "object" :borrow borrow}) (range (count borrows)) borrows)
                :body ["ret" {:var {:id {:idx 0}}}]}}})
(defn artifact [m rows]
  (let [source (bytes "-- labelled model; never compile")
        ir (bytes (apply str (map #(str (json/write-str %) "\n") (cons m rows))))]
    {:source-bytes source :source-sha256 (wire/sha256 source)
     :ir-bytes ir :ir-sha256 (wire/sha256 ir)
     :expected-root-abi {:params (mapv #(select-keys % [:ty :borrow]) (get-in (first rows) [:ir :fdecl :xs]))
                         :return-type (get-in (first rows) [:ir :fdecl :type])}
     :max-bytes 1048576 :max-declarations 100}))
(defn fixture
  ([] (fixture {}))
  ([policy]
  (let [name ["str" ["anonymous"] "old"] f {:params [] :body [:return [:imm 0]]}
        functions {name f} helpers (zipmap [:root :empty? :definition :axiom :error] (repeat name))
        old-kernel (kernel/make-binding helpers policy)
        init {:signature {:params [] :return-type "object"} :handler (fn [& _] (throw (AssertionError. "NO GUEST")))}
        bindings {"lean_elab_add_decl" old-kernel "lean_run_mod_init_core" init}
        catalogue {:declarations {} :manifests [manifest]}
        world {:functions functions :status :done :frames [] :heap {} :globals {}
               :kernel-environments {} :native-imports [:source-model] :stats {:steps 0}}
        session (raw/open-functions functions bindings {:backend :reference :fuel 100})]
    {:candidate {:world world :session session :catalogue catalogue :environment :borrowed-model-root
                 :support {:session session :catalogue catalogue :kernel-helpers helpers :kernel-policy (:kernel-policy old-kernel)}}
     :configuration {:catalogue catalogue :trusted-functions functions :trusted-bindings bindings :kernel-helpers helpers :kernel-policy (:kernel-policy old-kernel)}
     :artifacts {:publication (artifact manifest [(row preparation/generated [false true true])])
                 :encoding (artifact manifest [(row preparation/encoder [false false false false])])}})))
(defn prepare [f] (preparation/prepare-ordinary (:candidate f) (:configuration f) (:artifacts f)))
(defn cause [f] (try (prepare f) nil (catch Throwable e e)))

(deftest opt-in-preserves-old-owners-code-and-binds-one-new-handler
  (let [f (fixture) result (prepare f) next (:candidate result) config (:configuration result)
        old (:candidate f) original (get-in old [:session :bindings "lean_elab_add_decl"])]
    (is (= preparation/profile-id (get-in result [:profile :id])))
    (is (false? (get-in result [:profile :allow-nested?])))
    (is (= ["lean_elab_add_decl"] (get-in result [:profile :binding-replacements])))
    (is (not (identical? original (get-in next [:session :bindings "lean_elab_add_decl"]))))
    (is (identical? (get-in next [:session :bindings "lean_elab_add_decl"])
                    (get-in config [:trusted-bindings "lean_elab_add_decl"])))
    (is (identical? original (get-in old [:session :bindings "lean_elab_add_decl"])))
    (is (identical? (get-in old [:session :bindings "lean_run_mod_init_core"])
                    (get-in next [:session :bindings "lean_run_mod_init_core"])))
    (doseq [key [:heap :globals :kernel-environments :native-imports :stats]]
      (is (identical? (get-in old [:world key]) (get-in next [:world key]))))
    (doseq [[name fun] (get-in old [:world :functions])]
      (is (identical? fun (get-in next [:world :functions name]))))
    (is (= #{:root :empty? :definition :axiom :error :generated :encode-family}
           (set (keys (:kernel-helpers config)))))
    (is (nil? (get-in f [:configuration :kernel-helpers :generated])))
    (is (identical? (get-in next [:support :session :functions]) (:trusted-functions config))))
  (let [policy {:allow-axioms? true :allow-unsafe? true :checker-fuel 1234}
        f (fixture policy)
        old-binding (get-in f [:configuration :trusted-bindings "lean_elab_add_decl"])
        result (preparation/prepare-ordinary (:candidate f) (:configuration f) (:artifacts f) policy)]
    (is (= (:kernel-policy old-binding) (get-in result [:configuration :kernel-policy])))
    (is (= (:kernel-policy old-binding) (get-in result [:candidate :support :kernel-policy])))
    (is (= (:kernel-policy old-binding)
           (get-in result [:configuration :trusted-bindings "lean_elab_add_decl" :kernel-policy])))
    (is (false? (get-in result [:configuration :kernel-policy :allow-nested?])))))

(deftest reject-untrusted-registry-drift-user-state-and-nested-policy
  (doseq [f [(update (fixture) :candidate dissoc :support)
             (assoc-in (fixture) [:candidate :support :kernel-policy] {:allow-axioms? true})
             (assoc-in (fixture) [:candidate :support :kernel-helpers :axiom] ["different"])
             (assoc-in (fixture) [:configuration :trusted-bindings "lean_elab_add_decl"]
                      (kernel/make-binding (get-in (fixture) [:configuration :kernel-helpers]) {}))
             (assoc-in (fixture) [:candidate :world :eval-const-authorizations :units :user] {})
             (assoc-in (fixture) [:configuration :kernel-helpers :generated-nested] ["nested"])
             (assoc-in (fixture) [:configuration :trusted-functions ["str" ["anonymous"] "old"]]
                       {:params [] :body [:return [:imm 0]]})]]
    (let [error (cause f)]
      (is (instance? clojure.lang.ExceptionInfo error))
      (is (identical? (:candidate f) (:source-inductive-preparation-entry (ex-data error))))
      (is (some? (.getCause ^Throwable error)))))
  (is (thrown? clojure.lang.ExceptionInfo
        (let [f (fixture)] (preparation/prepare-ordinary (:candidate f) (:configuration f) (:artifacts f) {:allow-nested? true})))))

(deftest artifact-authentication-inventory-initialization-and-borrow-gates
  (doseq [artifact [(assoc (:publication (:artifacts (fixture))) :source-sha256 (apply str (repeat 64 "0")))
                   (assoc (:publication (:artifacts (fixture))) :ir-sha256 (apply str (repeat 64 "0")))
                   (assoc (:publication (:artifacts (fixture))) :max-bytes 1)
                   (assoc-in (:publication (:artifacts (fixture))) [:expected-root-abi :params 0 :ty] "tobject")
                   (artifact (assoc-in manifest [:initializationPlan :actions] [{:action {:kind "io"}}])
                             [(row preparation/generated [false true true])])
                   (artifact (assoc manifest :leanVersion "4.26.0") [(row preparation/generated [false true true])])
                   (artifact manifest [(row preparation/generated [false true true])
                                       (row preparation/generated [false true true])])
                   (artifact manifest [(row preparation/generated [false true false])])
                   (artifact manifest [(row preparation/generated [false true])])]]
    (is (some? (cause (assoc-in (fixture) [:artifacts :publication] artifact))))))

(deftest catalogue-overlap-collision-and-closure-are-not-self-authorized
  (let [f (fixture)
        ordinary (row preparation/generated [false true true])
        conflicting (assoc-in ordinary [:ir :fdecl :body] ["ret" {:var {:id {:idx 1}}}])
        conflicting-catalogue {:manifests [manifest] :declarations {preparation/generated conflicting}}
        collision {:params [0 1 2] :body [:return [:imm 99]]}
        actual-functions (assoc (get-in f [:candidate :world :functions]) preparation/generated collision)]
    (is (some? (cause (-> f (assoc-in [:candidate :catalogue] conflicting-catalogue)
                         (assoc-in [:configuration :catalogue] conflicting-catalogue)))))
    (is (some? (cause (-> f (assoc-in [:candidate :world :functions] actual-functions)
                         (assoc-in [:candidate :session :functions] actual-functions)))))
    (let [missing (assoc-in ordinary [:ir :fdecl :body]
                           ["vdecl" {:idx 3} "object" {:fap {:c ["str" ["anonymous"] "missing"] :ys []}}
                            ["ret" {:var {:id {:idx 3}}}]])]
      (is (some? (cause (assoc-in f [:artifacts :publication] (artifact manifest [missing]))))))))

(deftest existing-code-edges-and-required-initialized-globals-are-checked
  (let [f (fixture) old-name ["str" ["anonymous"] "old"]
        old-with-missing {:params [] :body [:tail [:direct ["str" ["anonymous"] "missing-private"]] []]}
        old-functions {old-name old-with-missing}
        changed (-> f (assoc-in [:candidate :world :functions] old-functions)
                    (assoc-in [:candidate :session :functions] old-functions)
                    (assoc-in [:candidate :support :session :functions] old-functions)
                    (assoc-in [:configuration :trusted-functions] old-functions))]
    (is (some? (cause changed))))
  (let [f (fixture) global ["str" ["anonymous"] "imported-global"]
        init ["str" ["anonymous"] "imported-global-init"]
        value-body ["vdecl" {:idx 0} "object" {:lit {:v {:str "model"}}}
                    ["ret" {:var {:id {:idx 0}}}]]
        init-row (-> (row init []) (assoc-in [:ir :fdecl :body] value-body))
        global-row (-> (row global []) (assoc :runtime {:role "initialized" :initializer init})
                       (assoc-in [:ir :fdecl :body] value-body))
        base (assoc (:catalogue (:candidate f)) :declarations {global global-row init init-row})
        publication (assoc-in (row preparation/generated [false true true]) [:ir :fdecl :body]
                              ["vdecl" {:idx 3} "object" {:fap {:c global :ys []}}
                               ["ret" {:var {:id {:idx 3}}}]])
        changed (-> f (assoc-in [:candidate :catalogue] base)
                    (assoc-in [:configuration :catalogue] base)
                    (assoc-in [:artifacts :publication] (artifact manifest [publication])))]
    (doseq [status [nil :initializing :failed]]
      (let [error (cause (cond-> changed status (assoc-in [:candidate :world :globals global] {:status status})))]
        (is (some? error))
        (is (re-find #"uninitialized imported global" (.getMessage (.getCause ^Throwable error))))))
    (is (map? (prepare (assoc-in changed [:candidate :world :globals global] {:status :ready :value :model}))))))


(deftest reject-already-sealed-profiles-and-policy-widening
  (doseq [path [[:candidate :graph-profile] [:candidate :prefix] [:candidate :context]
                [:candidate :graph-install-options] [:configuration :graph-profile]
                [:configuration :frontend-configuration :install-options]]]
    (let [f (assoc-in (fixture) path :old-sealed-capability)]
      (is (some? (cause f)))))
  ;; A support map is not provenance for the opaque original kernel handler.
  (let [f (fixture) wider {:allow-axioms? true}
        forged (-> f (assoc-in [:candidate :support :kernel-policy] wider)
                     (assoc-in [:configuration :kernel-policy] wider))]
    (is (thrown? clojure.lang.ExceptionInfo
          (preparation/prepare-ordinary (:candidate forged) (:configuration forged) (:artifacts forged) wider)))))

(deftest returned-preseal-registry-is-coherent-and-helpers-remain-protected
  (let [f (fixture) r (prepare f) c (:candidate r) config (:configuration r)
        binding (get-in config [:trusted-bindings "lean_elab_add_decl"])]
    (is (identical? (:trusted-functions c) (:trusted-functions config)))
    (is (identical? (:trusted-functions c) (get-in c [:support :session :functions])))
    (is (identical? (:catalogue c) (:catalogue config)))
    (is (identical? (:catalogue c) (get-in c [:support :catalogue])))
    (is (identical? binding (get-in c [:support :session :bindings "lean_elab_add_decl"])))
    (is (some #{preparation/generated} (:guest-helper-roots binding)))
    (is (some #{preparation/encoder} (:guest-helper-roots binding)))
    (is (= :before-profile-sealing (get-in r [:profile :stage])))
    (is (nil? (:graph-profile c)))))


(deftest actual-local-native-artifacts-have-full-provenance-and-no-local-actions
  (doseq [[source output count expected-root expected-abi]
          [["KernelSourceInductivePublication.lean" "publication.ndjson" 48 preparation/generated
            {:params [{:ty "object" :borrow false} {:ty "tobject" :borrow true} {:ty "object" :borrow true}]
             :return-type "object"}]
           ["KernelEncoding.lean" "encoding-local.ndjson" 58 preparation/encoder
            {:params (vec (repeat 4 {:ty "object" :borrow false})) :return-type "object"}]]]
    (let [root "fixtures/source-inductive/"
          provenance (json/read-str (slurp (str root "provenance.json")) :key-fn keyword)
          capture (some #(when (= output (:output %)) %) (:captures provenance))
          source-bytes (java.nio.file.Files/readAllBytes (.toPath (io/file (str root source))))
          ir-bytes (java.nio.file.Files/readAllBytes (.toPath (io/file (str root output))))
          index (preparation/authenticated-index {:source-bytes source-bytes :source-sha256 (:source-sha256 capture)
                                                 :ir-bytes ir-bytes :ir-sha256 (:output-sha256 capture)
                                                 :max-bytes 1048576 :max-declarations 1000})
          manifest (first (:manifests index))
          actual (get-in index [:declarations expected-root :ir :fdecl])]
      (is (= count (clojure.core/count (:declarations index))))
      (is (= [] (get-in manifest [:initializationPlan :actions])))
      (is (= expected-abi {:params (mapv #(select-keys % [:ty :borrow]) (:xs actual))
                           :return-type (:type actual)}))
      (is (false? (:full-imported-closure-included capture)))
      (is (true? (:local-only capture))))))
