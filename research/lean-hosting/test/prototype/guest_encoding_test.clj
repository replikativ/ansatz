(ns prototype.guest-encoding-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.guest-encoding :as encoding] [prototype.machine :as m]
            [prototype.import-ir :as ir] [prototype.runtime-abi :as abi] [prototype.raw-interop :as raw]
            [prototype.kernel-bridge :as bridge] [prototype.raw-inductive-test :as gen]
            [prototype.kernel-declaration :as declaration]
            [prototype.imported-kernel :as imported] [ansatz.kernel.name :as n])
  (:import [ansatz.kernel Name ConstantInfo Env]))
(def functions
  (delay (let [catalogue (ir/index-bundles ["fixtures/kernel-encoding.jsonl"])]
           (ir/load-closure catalogue [encoding/names-helper encoding/family-helper]
                            #(abi/lower-deferred-catalogue catalogue %)))))
(defn world-and-invoke [backend]
  (let [functions @functions session (raw/open-functions functions {} {:backend backend :fuel 1000000})]
    [(m/world functions)
     (fn [world target args]
       (let [result (raw/call session world target args)] [(:state result) (:value result)]))]))
(def names [Name/ANONYMOUS_NAME (Name/mkStr Name/ANONYMOUS_NAME "prefix")
            (Name/mkNum (Name/mkStr Name/ANONYMOUS_NAME "prefix") 42)
            (Name/mkStr (Name/mkNum (Name/mkStr Name/ANONYMOUS_NAME "prefix") 42) "λ.😀")])

(deftest real-name-constructors-preserve-exact-structure-and-ownership
  (doseq [backend [:reference :mutable :jvm]]
    (let [[world invoke] (world-and-invoke backend)
          [after array] (encoding/encode-names world invoke names)
          values (:fields (m/node after array))]
      (is (= names (mapv #(bridge/project-name after %) values)))
      ;; Exact hashes from pinned KernelEncodingNamesOracle, including UInt64
      ;; overflow, a numeric Name component and a dotted Unicode STR segment.
      (is (= [13138023262546087398N 3591884498532866835N 11142020826570219369N]
             (mapv #(m/read-scalar-node (m/node after %) {:index 2 :offset 0 :type "uint64" :region :scalar})
                   (rest values))))
      (is (= 1 (:rc (m/node after array))))
      (is (> (get-in after [:stats :steps]) 50))
      (is (not-any? (fn [[_ node]] (pos? (:rc node))) (:heap (m/release after array 1)))))
    (let [[world invoke] (world-and-invoke backend)
          [after name] (encoding/encode-name world invoke (last names))]
      (is (= (last names) (bridge/project-name after name)))
      (is (= 1 (:rc (m/node after name))))
      (is (not-any? (fn [[_ node]] (pos? (:rc node))) (:heap (m/release after name 1)))))))

(deftest complete-generated-family-reprojects-identically-on-every-backend
  (let [input (gen/source [] 0 [(gen/type-input "Generated" gen/type1
                                    [(gen/ctor "Generated.mk" (gen/constant (n/from-string "Generated")))])])
        result (gen/generate (Env.) input) expected (vec (.constants result))]
    (doseq [backend [:reference :mutable :jvm]]
      (let [[world invoke] (world-and-invoke backend)
            [after array] (encoding/encode-family world invoke expected)
            actual (mapv #(imported/project-constant after %) (:fields (m/node after array)))]
        (is (= (mapv imported/checking-shape expected) (mapv imported/checking-shape actual)))
        (is (= 3 (count actual)))
        (is (not-any? (fn [[_ node]] (pos? (:rc node))) (:heap (m/release after array 1))))))))

(deftest generated-encoding-reuses-source-expressions-in-every-snapshot
  (doseq [backend [:reference :mutable :jvm]
          [group params] [[["TinyEnum"] 0] [["PolyList"] 1] [["SmallEq"] 2]]]
    (let [{:keys [world declaration]} (gen/native-source-declaration group params)
          result (declaration/generate-inductive world (Env.) declaration)
          [_ invoke] (world-and-invoke backend)
          world (assoc world :functions @functions)
          [after array] (encoding/encode-family world invoke (:constants result)
                         {:original-expressions (:original-expressions result)})
          actual (:fields (m/node after array))]
      (doseq [[^ConstantInfo expected ci] (map vector (:constants result) actual)
              :let [original (.get ^java.util.IdentityHashMap (:original-expressions result) (.type expected))]
              :when original]
        (let [payload (first (:fields (m/node after ci)))
              base (first (:fields (m/node after payload)))
              expression (nth (:fields (m/node after base)) 2)]
          (is (= original expression))
          (is (= (m/node world original) (m/node after original)))))
      (let [released (m/release after array 1)]
        (is (= (:heap world) (select-keys (:heap released) (keys (:heap world)))))
        (is (not-any? (fn [[id node]] (and (not (contains? (:heap world) id)) (pos? (:rc node))))
                      (:heap released))))
      ;; Independent re-encoding from the immutable pre-call snapshot cannot
      ;; observe ownership changes in the first branch.
      (let [[fork result-array] (encoding/encode-family world invoke (:constants result)
                                 {:original-expressions (:original-expressions result)})]
        (is (= array result-array))
        (is (= (:heap after) (:heap fork)))))))

(def ^:private scoped-host ["str" ["anonymous"] "encoder-scoped-host"])
(def ^:private following-helper ["str" ["anonymous"] "encoder-following-helper"])
(def ^:private parent-control-keys [:body :locals :joins :frames :status :result :resume-var :host-request])
(defn- encode-selected [kind world invoke]
  (case kind
    :names (encoding/encode-names world invoke names)
    :name (encoding/encode-name world invoke (last names))
    :family (encoding/encode-family world invoke [])))
(defn- invalid-root [world [_ roots]]
  ;; Test-only mutation of the owned root-index array, using its actual layout.
  ;; The real guest decoder consumes both arguments and returns Except.error.
  (m/replace-node world roots (assoc (m/node world roots) :fields [999999])))
(defn- scoped-fixture [backend kind fault]
  (let [observed (atom {})
        binding {:signature {:params [] :return-type "object"}
                 :handler
                 (fn [context world _]
                   (swap! observed assoc :entry world)
                   (let [invoke (fn [w target args]
                                  (let [w (if (and (= fault :bad-descriptor) (= target encoding/names-helper))
                                            (invalid-root w args) w)
                                        [after value] ((:invoke context) w target args)]
                                    (swap! observed assoc :last-invoke {:world after :value value})
                                    [(if (= fault :illegal-control)
                                       (assoc after :locals {999 :illegal-control-mutation}) after) value]))]
                     (try
                       (let [[after value] (encode-selected kind world invoke)
                             _ (swap! observed assoc :encoded {:world after :value value})
                             after (m/release after value 1)
                             [after answer] ((:invoke context) after following-helper [])]
                         (swap! observed assoc :following-completed true)
                         [after answer])
                       (catch Throwable cause
                         (swap! observed assoc :encoder-failure cause)
                         (throw cause)))))}
        functions (assoc @functions
                         scoped-host {:params [] :body [:host "test_guest_encoder" [] 0 [:return [:var 0]]]}
                         following-helper {:params [] :body [:return [:imm 7]]})
        session (raw/open-functions functions {"test_guest_encoder" binding} {:backend backend :fuel 1000000})]
    {:world (m/world functions) :session session :observed observed}))

(deftest real-encoders-preserve-absent-and-present-parent-results-across-raw-helper-boundaries
  (doseq [backend [:reference :mutable :jvm] kind [:names :name :family]
          result-kind [:absent :nil :zero :scalar :owned-ref]]
    (let [{:keys [world session observed]} (scoped-fixture backend kind nil)
          [world marker] (m/allocate world :ctor 0 [])
          started (m/start world scoped-host [])
          ;; raw/continue accepts explicit running machine states. The result
          ;; slot may be absent or an existing register alias; never an owner.
          started (case result-kind :absent started :nil (assoc started :result nil)
                         :zero (assoc started :result 0) :scalar (assoc started :result 41)
                         :owned-ref (assoc started :result marker))
          called (raw/continue session started)
          {:keys [entry encoded following-completed]} @observed]
      (is (= 7 (:value called)))
      (is following-completed)
      (is (= (select-keys entry parent-control-keys)
             (select-keys (:world encoded) parent-control-keys)))
      (is (= (contains? entry :result) (contains? (:world encoded) :result)))
      (is (= 1 (:rc (m/node (:state called) marker))))
      (is (not-any? (fn [[id node]] (and (not= id (:id marker)) (pos? (:rc node)))) (:heap (:state called))))
      (is (not-any? (comp pos? :rc val) (:heap (m/release (:state called) marker 1)))))))

(deftest top-level-invokers-do-not-leave-a-consumed-except-in-the-result-slot
  (doseq [backend [:reference :mutable :jvm] kind [:names :name :family] present? [false true]]
    (let [[world invoke] (world-and-invoke backend)
          [world marker] (m/allocate world :ctor 0 [])
          world (if present? (assoc world :result marker) (dissoc world :result))
          [after value] (encode-selected kind world invoke)]
      (is (= (find world :result) (find after :result)))
      (when present? (is (identical? marker (:result after))))
      (is (= 1 (:rc (m/node after marker))))
      (is (not-any? (comp pos? :rc val)
                    (:heap (-> after (m/release value 1) (m/release marker 1))))))))

(deftest encoder-cleanup-does-not-mask-other-illegal-control-mutations
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [world session observed]} (scoped-fixture backend :family :illegal-control)
          cause (try (raw/call session world scoped-host []) nil (catch Throwable cause cause))]
      (is (instance? clojure.lang.ExceptionInfo cause))
      (is (= "Raw handler changed guest control state" (.getMessage cause)))
      (is (not (:following-completed @observed)))
      (is (= {999 :illegal-control-mutation} (get-in @observed [:encoded :world :locals])))
      (is (= following-helper (get-in (ex-data cause) [:failed-helper :target]))))))

(deftest actual-guest-decoder-error-retains-its-owned-except-and-canonical-checkpoint
  (doseq [backend [:reference :mutable :jvm] scoped? [false true]]
    (let [observed (atom {})
          [world session invoke run]
          (if scoped?
            (let [f (scoped-fixture backend :names :bad-descriptor)]
              [(:world f) (:session f) nil #(raw/call (:session f) (:world f) scoped-host [])])
            (let [[w call] (world-and-invoke backend)
                  invoke (fn [world target args]
                           (let [world (invalid-root world args)
                                 [world value] (call world target args)]
                             (reset! observed {:world world :value value}) [world value]))]
              [w nil invoke #(encoding/encode-names w invoke names)]))
          cause (try (run) nil (catch Throwable cause cause))
          data (ex-data cause) checkpoint (:checkpoint data) result (:result data)
          node (m/node checkpoint result)]
      (is (= "Guest encoding rejected descriptors" (.getMessage cause)))
      (is (= 0 (:tag node))) (is (= 1 (:rc node)))
      (is (= 1 (count (:fields node))))
      (when-not scoped?
        (is (identical? (:world @observed) checkpoint))
        (is (= (:value @observed) result (:result checkpoint))))
      ;; Error ownership is caller-held, not silently consumed/normalized.
      (is (not-any? (comp pos? :rc val) (:heap (m/release checkpoint result 1)))))))
