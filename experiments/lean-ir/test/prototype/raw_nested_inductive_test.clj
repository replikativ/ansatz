(ns prototype.raw-nested-inductive-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.raw-inductive-test :as raw] [prototype.module-data :as data]
            [prototype.kernel-declaration :as declaration]
            [prototype.guest-encoding-test :as encoding-fixture] [prototype.guest-encoding :as encoding]
            [prototype.imported-kernel :as imported] [prototype.machine :as m])
  (:import [ansatz.kernel ConstantInfo Env RawNestedInductiveGenerator]))
(defn native []
  (let [loaded (data/load-file (m/world {}) "fixtures/raw-nested-native.jsonl")]
    (into {} (map (fn [{:keys [^ConstantInfo constant]}] [(str (.name constant)) constant]))
          (imported/module-constants (:world loaded) (first (:roots loaded))))))
(defn input [constants label parameters]
  (let [^ConstantInfo info (get constants label)]
    (raw/source [] parameters [(raw/type-input label (.type info)
                                (mapv (fn [n] (raw/ctor (str n) (.type ^ConstantInfo (get constants (str n)))))
                                      (.ctors info)))])))
(deftest source-list-nesting-generates-and-restores-the-exact-native-family
  (let [constants (native) before (Env.)
        container (raw/generate before (input constants "Container" 1))
        empty-container (raw/generate (.env container) (input constants "EmptyContainer" 1))]
    (doseq [label ["Tree" "SparseTree" "MixedTree"]]
      (let [result (RawNestedInductiveGenerator/generate (.env empty-container) (input constants label 0) 1000000)
            actual (vec (.constants result))
            expected-names (into #{label (str label ".rec") (str label ".rec_1")}
                                 (map str (.ctors ^ConstantInfo (get constants label))))]
        (is (= 1 (.numNested result)))
        (is (= expected-names (set (map #(str (.name ^ConstantInfo %)) actual))))
        (doseq [^ConstantInfo info actual]
          (is (= (imported/checking-shape (get constants (str (.name info))))
                 (imported/checking-shape info)) (str (.name info))))
        (is (nil? (.lookup ^Env (.env empty-container) (.name ^ConstantInfo (get constants label)))))))
    (is (empty? (.allConstants before)))))

(deftest unsupported-nesting-and-collisions-fail-without-changing-the-base
  (let [constants (native)
        container (raw/generate (Env.) (input constants "Container" 1))
        ^Env before (.env container)
        source (input constants "Tree" 0)
        collision (.addConstant before (ConstantInfo/mkAxiom
                    (ansatz.kernel.Name/fromString "Tree.rec_1") (object-array 0) raw/type1 false))]
    (is (thrown-with-msg? IllegalArgumentException #"name collision"
          (RawNestedInductiveGenerator/generate collision source 1000000)))
    (is (thrown-with-msg? IllegalArgumentException #"checked unary"
          (RawNestedInductiveGenerator/generate (Env.) source 1000000)))
    (is (thrown? IllegalArgumentException
          (RawNestedInductiveGenerator/generate before source 0)))
    (is (nil? (.lookup before (ansatz.kernel.Name/fromString "Tree"))))
    (is (= 4 (count (.allConstants before))))))

(deftest explicit-source-policy-encodes-complete-nested-family-on-all-backends
  (let [constants (native) base (.env (raw/generate (Env.) (input constants "Container" 1)))
        {:keys [world declaration]} (raw/native-source-declaration "fixtures/raw-nested-native.jsonl" ["Tree"] 0)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"explicit bounded-profile policy"
          (declaration/generate-inductive world base declaration)))
    (let [checked (declaration/generate-inductive world base declaration {:allow-nested? true})]
      (is (true? (:nested? checked)))
      (doseq [backend [:reference :mutable :jvm]]
        (let [[_ invoke] (encoding-fixture/world-and-invoke backend)
              world (assoc world :functions @encoding-fixture/functions)
              [after array] (encoding/encode-family world invoke (:constants checked)
                             {:original-expressions (:original-expressions checked)})]
          (is (= #{"Tree" "Tree.node" "Tree.rec" "Tree.rec_1"}
                 (set (map #(str (.name ^ConstantInfo (imported/project-constant after %)))
                           (:fields (m/node after array))))))
          (is (= (mapv imported/checking-shape (:constants checked))
                 (mapv #(imported/checking-shape (imported/project-constant after %))
                       (:fields (m/node after array)))))
          (is (= (:heap world)
                 (select-keys (:heap (m/release after array 1)) (keys (:heap world))))))))))
