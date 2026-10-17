(ns prototype.kernel-host-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.kernel-host :as host]
            [prototype.guest-encoding-test :as encoding-fixture]
            [prototype.raw-inductive-test :as generation]
            [prototype.guest-encoding :as encoding]
            [prototype.imported-kernel :as imported]
            [prototype.kernel-bridge :as bridge]
            [prototype.kernel-bridge-test :as fixture]
            [prototype.kernel-declaration-test :as declarations]
            [prototype.machine :as m]
            [prototype.native-scalar :as native]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel Env]))

(def helpers (into {} (map (fn [k] [k ["str" ["anonymous"] (clojure.core/name k)]]))
                   [:root :empty? :definition :axiom :error :compiler-marker :theorem :opaque :mutual :definition-any]))
(defn- empty-world []
  (let [[world root] (m/allocate (m/world {}) :ctor 0 [])
        [world environment] (m/allocate world :ctor 0 [root])]
    [world environment root]))
(defn- axiom [world text type unsafe?]
  (let [[world n] (fixture/guest-name world text)
        [world constant] (fixture/ctor world 0 [n fixture/nil-tag type] 0)
        [world value] (fixture/ctor world 0 [constant] 1)
        world (fixture/scalar! world value 0 "uint8" (if unsafe? 1 0))]
    (fixture/ctor world 0 [value] 0)))
(defn- sort1 [world]
  (let [[world level] (fixture/ctor world 1 [fixture/nil-tag] 8)]
    (fixture/ctor world 3 [level] 8)))
(defn- context [calls]
  ;; Model only the helper ownership boundaries, not Lean's Environment layout.
  ;; Native KernelBridgeShim oracle separately checks real helper publication.
  {:invoke
   (fn [world helper args]
     (swap! calls conj helper)
     (cond
       (= helper (:root helpers))
       (let [root (first (:fields (m/node world (first args))))]
         [(m/retain world root 1) root])
       (= helper (:empty? helpers))
       (let [root (first (:fields (m/node world (first args))))]
         [world (if (empty? (:fields (m/node world root))) 1 0)])
       (= helper (:error helpers))
       (let [[world error] (m/allocate world :ctor 12 [(first args)])]
         (m/allocate world :ctor 0 [error]))
       (contains? #{(:definition helpers) (:axiom helpers) (:compiler-marker helpers)
                    (:theorem helpers) (:opaque helpers) (:mutual helpers) (:definition-any helpers)} helper)
       (let [[environment declaration] args
             world (-> world (m/release environment 1) (m/retain declaration 1))
             [world root] (m/allocate world :ctor 0 [declaration])
             [world next] (m/allocate world :ctor 0 [root])]
         (m/allocate world :ctor 1 [next]))
       :else (throw (AssertionError. "Unexpected helper"))))})
(defn- invoke [binding context world environment declaration]
  ((:handler binding) context world [environment 1000000 1000 declaration (m/->Tag 0)]))
(defn- take-ok [world result]
  (is (= 1 (:tag (m/node world result))))
  (let [environment (first (:fields (m/node world result)))]
    [(-> world (m/retain environment 1) (m/release result 1)) environment]))

(deftest native-imported-none-cancellation-admits-through-the-same-checker
  (let [[world environment _] (empty-world)
        [world type] (sort1 world)
        [world declaration] (axiom world "NativeNoneSort" type false)
        binding (host/make-binding helpers {:allow-axioms? true})
        [world result] ((:handler binding) (context (atom [])) world
                        [environment 1000000 1000 declaration (native/native-scalar 0)])
        [world environment] (take-ok world result)
        root (first (:fields (m/node world environment)))
        ^Env checked (get-in world [:kernel-environments (:id root) :env])]
    (is (some? (.lookup checked (name/from-string "NativeNoneSort"))))
    (is (= 2 (:rc (m/node world declaration))))))

(deftest safe-axiom-publication-anchors-old-and-new-roots-and-forks
  (let [[world environment initial-root] (empty-world)
        [world type] (sort1 world)
        [world declaration] (axiom world "HostedSort" type false)
        calls (atom []) context (context calls)
        binding (host/make-binding helpers {:allow-axioms? true})
        [world result] (invoke binding context world environment declaration)
        [world environment] (take-ok world result)
        root (first (:fields (m/node world environment)))
        ^Env checked (get-in world [:kernel-environments (:id root) :env])
        [fork type] (fixture/constant world "HostedSort")
        [fork second] (axiom fork "hostedValue" type false)
        [fork second-result] (invoke binding context fork environment second)
        second-env (first (:fields (m/node fork second-result)))
        second-root (first (:fields (m/node fork second-env)))
        ^Env checked-next (get-in fork [:kernel-environments (:id second-root) :env])]
    (is (some? (.lookup checked (name/from-string "HostedSort"))))
    (is (nil? (.lookup checked (name/from-string "hostedValue"))))
    (is (some? (.lookup checked-next (name/from-string "hostedValue"))))
    (is (nil? (.lookup ^Env (get-in world [:kernel-environments (:id initial-root) :env])
                      (name/from-string "HostedSort"))))
    (is (= 1 (:rc (m/node world initial-root))))
    (is (= 2 (:rc (m/node world root))))
    (is (= 1 (:rc (m/node fork root))))
    (is (= 2 (:rc (m/node fork second-root))))
    (is (= 2 (:rc (m/node world declaration))))
    (is (contains? (:heap world) (:id environment)))
    (is (= 1 (count (filter #(= (:empty? helpers) %) @calls))))))

(deftest policy-and-checker-errors-return-except-error-without-consuming-borrowed-declaration
  (doseq [[policy unsafe?] [[{} false] [{:allow-axioms? true} true]]]
    (let [[world environment root] (empty-world)
          [world type] (sort1 world)
          [world declaration] (axiom world "HostedSort" type unsafe?)
          before world calls (atom [])
          [world result] (invoke (host/make-binding helpers policy) (context calls) world environment declaration)
          error (first (:fields (m/node world result)))]
      (is (= 0 (:tag (m/node world result))))
      (is (= 12 (:tag (m/node world error))))
      (is (string? (first (:fields (m/node world error)))))
      (is (not (contains? (:heap world) (:id environment))))
      (is (= (m/node before declaration) (m/node world declaration)))
      (is (= 1 (:rc (m/node world root))))
      (is (= [(:root helpers) (:empty? helpers) (:error helpers)] @calls)))))

(deftest unassociated-nonempty-root-is-never-treated-as-an-empty-java-environment
  (let [[world root] (m/allocate (m/world {}) :ctor 0 [42])
        [world environment] (m/allocate world :ctor 0 [root])
        [world type] (sort1 world)
        [world declaration] (axiom world "HostedSort" type false)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"no verified Java association"
          (invoke (host/make-binding helpers {:allow-axioms? true}) (context (atom [])) world environment declaration)))
    (is (nil? (:kernel-environments world)))
    (is (= 1 (:rc (m/node world root))))))

(deftest unsupported-controls-fail-before-entering-any-guest-helper
  (let [[world environment _] (empty-world)
        [world type] (sort1 world)
        [world declaration] (axiom world "HostedSort" type false)
        binding (host/make-binding helpers {:allow-axioms? true}) calls (atom [])]
    (doseq [controls [[-1 1000 (m/->Tag 0)] [1 0 (m/->Tag 0)] [1 1000 (m/->Tag 1)]]]
      (let [[heartbeats depth cancel] controls]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported kernel checking controls"
              ((:handler binding) (context calls) world [environment heartbeats depth declaration cancel])))))
    (is (empty? @calls))))

(deftest checker-exception-without-a-message-is-still-a-guest-error
  (let [[world environment _] (empty-world)
        [world type] (sort1 world)
        [world declaration] (axiom world "HostedSort" type false)
        calls (atom [])]
    (with-redefs [bridge/admit-axiom (fn [& _] (throw (Exception.)))]
      (let [[world result] (invoke (host/make-binding helpers {:allow-axioms? true})
                                  (context calls) world environment declaration)
            error (first (:fields (m/node world result)))]
        (is (= 0 (:tag (m/node world result))))
        (is (= ["Kernel admission failed"] (:fields (m/node world error))))
        (is (not-any? #(= (:axiom helpers) %) @calls))))))


(deftest compiler-marker-capability-is-separate-from-safe-and-general-unsafe-axioms
  (doseq [[policy text unsafe? expected?]
          [[{} "lcAny" true false]
           [{:allow-axioms? true} "lcAny" true false]
           [{:allow-compiler-markers? true} "lcAny" true true]
           [{:allow-compiler-markers? true} "lcErased" true true]
           [{:allow-compiler-markers? true} "lcVoid" true true]
           [{:allow-compiler-markers? true} "arbitraryUnsafe" true false]
           [{:allow-compiler-markers? true :allow-axioms? true} "arbitraryUnsafe" true false]
           [{:allow-compiler-markers? true} "lcAny" false false]
           [{:allow-axioms? true} "ordinarySafe" false true]]]
    (let [[world environment root] (empty-world)
          [world type] (sort1 world)
          [world declaration] (axiom world text type unsafe?)
          calls (atom [])
          [world result] (invoke (host/make-binding helpers policy) (context calls) world environment declaration)]
      (is (= (if expected? 1 0) (:tag (m/node world result))))
      (is (= (and expected? unsafe?) (boolean (some #{(:compiler-marker helpers)} @calls))))
      (is (= (and expected? (not unsafe?)) (boolean (some #{(:axiom helpers)} @calls))))
      (when (and expected? unsafe?)
        (let [next (first (:fields (m/node world result)))
              next-root (first (:fields (m/node world next)))
              ^Env checked (get-in world [:kernel-environments (:id next-root) :env])]
          (is (true? (.isUnsafe (.lookup checked (name/from-string text)))))
          (is (= 1 (:rc (m/node world root))))))))
  (is (map? (host/make-binding (dissoc helpers :compiler-marker) {})))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Missing kernel guest helper"
        (host/make-binding (dissoc helpers :compiler-marker) {:allow-compiler-markers? true}))))

(def witnessed-helpers (assoc helpers :constant-map ["constant-map"] :quot-init? ["quot-init"]))
(defn- witness-context []
  {:invoke (fn [world helper [environment]]
             (let [root (first (:fields (m/node world environment)))
                   node (m/node world root)
                   constants (first (:fields node))]
               (cond
                 (= helper (:root helpers)) [(m/retain world root 1) root]
                 (= helper (:constant-map witnessed-helpers)) [(m/retain world constants 1) constants]
                 (= helper (:quot-init? witnessed-helpers)) [world (if (:quot-init? node) 1 0)]
                 (= helper (:empty? helpers)) [world (if (and (not (:quot-init? node))
                                                                            (empty? (:fields (m/node world constants)))) 1 0)]
                 :else (throw (AssertionError. "Unexpected witness helper")))))})
(defn- header-view [world constants quot?]
  (let [world (m/retain world constants 1)
        [world root] (m/allocate world :ctor 0 [constants])
        world (assoc-in world [:heap (:id root) :quot-init?] quot?)
        [world env] (m/allocate world :ctor 0 [root])]
    [world env root]))

(deftest derived-header-associations-require-identical-map-and-quotient-state
  (let [[world constants] (m/allocate (m/world {}) :ctor 0 [])
        [world env root] (header-view world constants false)
        ctx (witness-context)
        [anchored java-env] (#'host/associate-input ctx world env witnessed-helpers)
        [fork clone clone-root] (header-view anchored constants false)
        before-map-rc (:rc (m/node fork constants))
        [derived derived-java] (#'host/associate-input ctx fork clone witnessed-helpers)
        [other other-map] (m/allocate anchored :ctor 0 [])
        ;; Equal contents/count do not establish guest pointer identity.
        [other other-env _] (header-view other other-map false)
        [quot quot-env _] (header-view anchored constants true)]
    (is (identical? java-env derived-java))
    (is (= constants (get-in derived [:kernel-environments (:id clone-root) :constant-map])))
    (is (= before-map-rc (:rc (m/node derived constants))))
    (is (= 2 (:rc (m/node derived clone-root))))
    (is (= 2 (:rc (m/node anchored root))))
    (is (not (contains? (:kernel-environments anchored) (:id clone-root))))
    ;; A different empty map can establish a fresh empty Java environment, but
    ;; never inherits the existing checker environment by content equivalence.
    (is (not (identical? java-env (second (#'host/associate-input ctx other other-env witnessed-helpers)))))
    (is (thrown-with-msg? Exception #"no verified Java association"
          (#'host/associate-input ctx quot quot-env witnessed-helpers)))
    (is (= false (get-in anchored [:kernel-environments (:id root) :quot-init?])))
    (is (thrown-with-msg? Exception #"Invalid unique constructor tag store"
          (m/set-constructor-tag anchored root 1)))
    (is (thrown-with-msg? Exception #"Invalid unique constructor tag store"
          (m/set-constructor-tag anchored constants 1)))
    (is (= 1 (:rc (m/node world root))))))

(deftest nonempty-map-lookalikes-and-unwitnessed-roots-fail-closed
  (let [[world constants] (m/allocate (m/world {}) :ctor 0 [42])
        [world env root] (header-view world constants false)
        checked (Env.)
        anchored (assoc-in world [:kernel-environments (:id root)]
                           {:anchor root :env checked :constant-map constants :quot-init? false})
        [fork other] (m/allocate anchored :ctor 0 [42])
        [fork other-env _] (header-view fork other false)
        [fork clone _] (header-view fork constants false)
        ctx (witness-context)]
    (is (thrown-with-msg? Exception #"no verified Java association"
          (#'host/associate-input ctx fork other-env witnessed-helpers)))
    (is (identical? checked (second (#'host/associate-input ctx fork clone witnessed-helpers))))
    (is (thrown-with-msg? Exception #"no verified Java association"
          (#'host/associate-input ctx (update-in fork [:kernel-environments (:id root)] dissoc :constant-map)
                                  clone witnessed-helpers)))
    ;; Exact roots may upgrade an old, already authenticated association.
    (let [[upgraded java] (#'host/associate-input ctx
                         (update-in anchored [:kernel-environments (:id root)] dissoc :constant-map)
                         env witnessed-helpers)]
      (is (identical? checked java))
      (is (= constants (get-in upgraded [:kernel-environments (:id root) :constant-map]))))))

(deftest witnessed-publication-keeps-new-map-and-kernel-root-anchors
  (let [[world constants] (m/allocate (m/world {}) :ctor 0 [])
        [world environment _] (header-view world constants false)
        [world type] (sort1 world)
        [world declaration] (axiom world "WitnessPublished" type false)
        base (witness-context)
        ctx {:invoke (fn [world helper args]
                        (if (= helper (:axiom helpers))
                          (let [[env decl] args
                                world (-> world (m/release env 1) (m/retain decl 1))
                                [world constants] (m/allocate world :ctor 0 [decl])
                                [world root] (m/allocate world :ctor 0 [constants])
                                [world env] (m/allocate world :ctor 0 [root])]
                            (m/allocate world :ctor 1 [env]))
                          ((:invoke base) world helper args)))}
        [world result] (invoke (host/make-binding witnessed-helpers {:allow-axioms? true})
                               ctx world environment declaration)
        env (first (:fields (m/node world result)))
        root (first (:fields (m/node world env)))
        map-ref (first (:fields (m/node world root)))
        entry (get-in world [:kernel-environments (:id root)])]
    (is (= map-ref (:constant-map entry)))
    (is (false? (:quot-init? entry)))
    (is (= 2 (:rc (m/node world root))))
    (is (= 2 (:rc (m/node world map-ref))))
    (is (some? (.lookup ^Env (:env entry) (name/from-string "WitnessPublished"))))))


(deftest additional-source-kinds-publish-only-after-strict-admission-and-fork-locally
  (let [{base-world :world values :values :as source} (declarations/fixture)
        checked-base (declarations/base-env source)]
    (doseq [[kind declaration-world declaration policy expected]
            [[:definition-any base-world (get values "unsafeA") {:allow-unsafe? true} ["unsafeA"]]
             [:theorem base-world (get values "identityProof") {} ["identityProof"]]
             [:opaque base-world (get values "hiddenA") {} ["hiddenA"]]
             (let [{:keys [world declaration]} (declarations/mutual base-world 0 "f")]
               [:mutual world declaration {:allow-unsafe? true} ["f" "g"]])]]
      (let [[world root] (m/allocate declaration-world :ctor 0 [])
            [world environment] (m/allocate world :ctor 0 [root])
            world (-> world (m/retain root 1)
                      (assoc-in [:kernel-environments (:id root)] {:anchor root :env checked-base}))
            fork world calls (atom [])
            [after result] (invoke (host/make-binding helpers policy) (context calls) fork environment declaration)
            guest-next (first (:fields (m/node after result)))
            new-root (first (:fields (m/node after guest-next)))
            ^Env checked-next (get-in after [:kernel-environments (:id new-root) :env])]
        (is (= 1 (:tag (m/node after result))))
        (is (some #{(kind helpers)} @calls))
        (is (every? #(some? (.lookup checked-next (name/from-string %))) expected))
        (is (every? #(nil? (.lookup checked-base (name/from-string %))) expected))
        (is (nil? (get-in world [:kernel-environments (:id new-root)])))
        (is (identical? checked-base (get-in world [:kernel-environments (:id root) :env])))
        (is (= 1 (:rc (m/node after root))))
        (is (contains? (:heap world) (:id environment)))
        (is (not (contains? (:heap after) (:id environment))))))))

(deftest additional-source-kind-policy-check-errors-never-publish
  (let [{base-world :world values :values :as source} (declarations/fixture)
        checked-base (declarations/base-env source)
        {:keys [world declaration]} (declarations/mutual base-world 0 "f")
        [world root] (m/allocate world :ctor 0 [])
        [world environment] (m/allocate world :ctor 0 [root])
        world (-> world (m/retain root 1)
                  (assoc-in [:kernel-environments (:id root)] {:anchor root :env checked-base}))
        calls (atom [])
        [after result] (invoke (host/make-binding helpers {}) (context calls) world environment declaration)]
    (is (= 0 (:tag (m/node after result))))
    (is (not-any? #{(:mutual helpers)} @calls))
    (is (= 1 (count (:kernel-environments after))))
    (is (= (m/node world declaration) (m/node after declaration)))
    (is (nil? (.lookup checked-base (name/from-string "f"))))))

(deftest generated-source-family-is-checked-encoded-and-anchored-atomically
  (doseq [backend [:reference :mutable :jvm]]
    (let [{source-world :world declaration :declaration}
          (generation/native-source-declaration ["TinyEnum"] 0)
          world source-world
          ;; The fixture owns persistent native nodes. Allocate the modeled
          ;; environment AFTER those IDs to avoid an unrelated heap collision.
          [world initial-root] (m/allocate world :ctor 0 [])
          [world environment] (m/allocate world :ctor 0 [initial-root])
          [_ encode-invoke] (encoding-fixture/world-and-invoke backend)
          world (assoc world :functions @encoding-fixture/functions)
          generated-helper ["generated"]
          hs (assoc helpers :generated generated-helper :encode-family encoding/family-helper)
          calls (atom []) base-context (context calls)
          context {:invoke (fn [world helper args]
                             (cond
                               (= helper encoding/family-helper) (encode-invoke world helper args)
                               (= helper generated-helper)
                               (let [[environment declaration constants] args
                                     projected (mapv #(imported/project-constant world %) (:fields (m/node world constants)))
                                     _ (is (= #{"TinyEnum" "TinyEnum.a" "TinyEnum.b" "TinyEnum.rec"}
                                              (set (map #(str (.name %)) projected))))
                                     world (-> world (m/release environment 1) (m/retain declaration 1) (m/retain constants 1))
                                     [world root] (m/allocate world :ctor 0 [declaration constants])
                                     [world next] (m/allocate world :ctor 0 [root])]
                                 (m/allocate world :ctor 1 [next]))
                               :else ((:invoke base-context) world helper args)))}
          [after result] (invoke (host/make-binding hs {}) context world environment declaration)
          [after next-environment] (take-ok after result)
          root (first (:fields (m/node after next-environment)))
          ^Env checked (get-in after [:kernel-environments (:id root) :env])
          generated-array (second (:fields (m/node after root)))
          [failed error] (invoke (host/make-binding hs {}) context after next-environment declaration)]
      (is (= 4 (count (.allConstants checked))))
      (is (= 1 (:rc (m/node after generated-array))))
      (is (= 2 (:rc (m/node after root))))
      (is (= 0 (:tag (m/node failed error))))
      (is (empty? (.allConstants ^Env (get-in after [:kernel-environments (:id initial-root) :env]))))
      (is (= (dissoc (m/node world declaration) :rc) (dissoc (m/node after declaration) :rc)))
      (is (= 1 (:rc (m/node world declaration))))
      (is (= 2 (:rc (m/node after declaration)))))))

(deftest explicitly-enabled-nested-source-publication-uses-complete-encoded-family
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [world declaration expected]}
          (generation/native-source-declaration "fixtures/raw-nested-native.jsonl" ["Tree"] 0)
          ^ansatz.kernel.ConstantInfo container (get expected "Container")
          base (.env (generation/generate (Env.)
                       (generation/source [] 1
                         [(generation/type-input "Container" (.type container)
                            (mapv (fn [name]
                                    (generation/ctor (str name) (.type ^ansatz.kernel.ConstantInfo (get expected (str name)))))
                                  (.ctors container)))])))
          [world root] (m/allocate world :ctor 0 [])
          [world environment] (m/allocate world :ctor 0 [root])
          world (assoc-in (m/retain world root 1) [:kernel-environments (:id root)] {:anchor root :env base})
          [_ encode-invoke] (encoding-fixture/world-and-invoke backend)
          world (assoc world :functions @encoding-fixture/functions)
          generated ["generated-nested"]
          hs (assoc helpers :generated ["generated"] :generated-nested generated :encode-family encoding/family-helper)
          calls (atom []) base-context (context calls)
          context {:invoke
                   (fn [world helper args]
                     (cond
                       (= helper encoding/family-helper) (encode-invoke world helper args)
                       (= helper generated)
                       (let [[environment declaration array] args
                             infos (mapv #(imported/project-constant world %) (:fields (m/node world array)))
                             _ (is (= #{"Tree" "Tree.node" "Tree.rec" "Tree.rec_1"}
                                      (set (map #(str (.name ^ansatz.kernel.ConstantInfo %)) infos))))
                             world (-> world (m/release environment 1) (m/retain declaration 1) (m/retain array 1))
                             [world root] (m/allocate world :ctor 0 [declaration array])
                             [world env] (m/allocate world :ctor 0 [root])]
                         (m/allocate world :ctor 1 [env]))
                       :else ((:invoke base-context) world helper args)))}
          [denied error] (invoke (host/make-binding hs {}) context world environment declaration)
          [after result] (invoke (host/make-binding hs {:allow-nested? true}) context world environment declaration)
          [after next-env] (take-ok after result)
          next-root (first (:fields (m/node after next-env)))
          ^Env checked (get-in after [:kernel-environments (:id next-root) :env])]
      (is (= 0 (:tag (m/node denied error))))
      (is (= 8 (count (.allConstants checked))))
      (is (= 4 (count (.allConstants base))))
      (is (= 2 (:rc (m/node after next-root))))
      (is (= 2 (:rc (m/node world root))))
      (is (= 1 (:rc (m/node after root))))
      (is (nil? (.lookup base (name/from-string "Tree")))))))
