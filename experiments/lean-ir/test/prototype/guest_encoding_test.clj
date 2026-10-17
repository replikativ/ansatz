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
