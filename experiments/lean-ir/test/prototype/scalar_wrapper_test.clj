(ns prototype.scalar-wrapper-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.java.io :as io]
            [clojure.data.json :as json]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.runtime-abi :as abi]
            [prototype.runtime-prim :as runtime]
            [prototype.runtime-string :as runtime-string]
            [prototype.native-scalar :as native]
            [prototype.scalar :as scalar]
            [prototype.scalar-wrapper :as sw]
            [prototype.block-compile :as block]
            [prototype.lazy-runtime :as lazy]))

(def profile {:schema "lean-block-profile/1" :producer-commit "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
              :phase :expanded-rc :word-bits 64 :layout :lean-64
              :abi-generation "ansatz-runtime/1" :target :jvm})
(def fixture-dir
  (first (filter #(.exists (io/file % "scalar-wrapper-declarations.jsonl"))
                 [(io/file "fixtures") (io/file "experiments/lean-ir/fixtures")
                  (io/file (.getParentFile (.getParentFile (.getParentFile (.getAbsoluteFile (io/file *file*))))) "fixtures")])))
(defn read-rows [file]
  (with-open [r (io/reader (io/file fixture-dir file))]
    (into [] (map #(json/read-str % :key-fn keyword)) (line-seq r))))
(def declarations (delay (vec (rest (read-rows "scalar-wrapper-declarations.jsonl")))))
(def functions (delay (into {} (map abi/lower) @declarations)))
(def descriptions (delay (into {} (map (fn [row] [(:name row) (abi/describe-scalar row profile)])) @declarations)))
(def options (delay {:scalar-wrappers @descriptions}))
(def native-cases (delay (vec (rest (read-rows "scalar-wrapper-native.jsonl")))))
(defn by-symbol [symbol] (first (filter #(= symbol (:runtime-extern (val %))) @functions)))
(defn plan [symbol]
  (let [[_ f] (by-symbol symbol)] (block/compile-runtime-block @functions (:body f) @options)))
(defn initial [symbol args] (m/start (m/world @functions) (first (by-symbol symbol)) args))
(defn carrier [s] (let [n (bigint s)] (if (<= n Long/MAX_VALUE) (long n) n)))

(deftest actual-extern-description-and-native-full-unsigned-oracle
  (is (= 4 (count @descriptions)))
  (is (= 324 (count @native-cases)))
  (let [plans (into {} (for [symbol (map :extern (vals @descriptions))] [symbol (plan symbol)]))]
    (doseq [{:keys [symbol a b result]} @native-cases]
      (let [p (get plans symbol) machine (u/thaw (initial symbol [(carrier a) (carrier b)]))
            route ((:execute! p) machine) s (u/freeze machine)
            dest (second (:body (second (by-symbol symbol))))
            expected (m/step (initial symbol [(carrier a) (carrier b)]))]
        (is (= :specialized route))
        (is (= :long-bits (get-in p [:specialization :lane])))
        (is (= (bigint result) (get-in s [:locals dest])))
        (is (= clojure.lang.BigInt (class (get-in s [:locals dest]))))
        (is (= expected s))))))

(defn run-backend [backend program s fuel]
  (case backend :mutable (u/freeze (u/run! (u/thaw s) fuel))
        :lazy (u/freeze (lazy/run! program (u/thaw s) fuel))
        :eager (u/freeze (block/run! program (u/thaw s) fuel))))

(deftest caller-and-wrapper-every-fuel-saved-siblings
  (let [callers (into {} (for [[name f] @functions]
                         [(keyword (str "caller-" (:runtime-extern f)))
                          {:params [0 1] :body [:call 2 [:direct name] [[:var 0] [:var 1]] [:return [:var 2]]]}]))
        fs (merge @functions callers)
        programs [[:lazy (lazy/open-program fs @options)] [:eager (block/compile-program fs nil @options)] [:mutable nil]]]
    (doseq [[caller f] callers args [[0 1] [Long/MAX_VALUE 1] [18446744073709551615N 1]] fuel (range 7)]
      (let [start (m/start (m/world fs) caller args) expected (m/run start fuel)]
        (doseq [[backend program] programs]
          (let [actual (run-backend backend program start fuel)]
            (is (= expected actual))
            (when (= :paused (:status actual))
              (let [saved actual left (run-backend backend program (m/resume saved nil) 30)
                    right (run-backend backend program (m/resume saved nil) 30)]
                (is (= (m/run start) left right))
                (is (= expected saved))))))))))

(defn attempt [f machine]
  (try (let [route (f machine)] {:route route :state (u/freeze machine)})
       (catch Throwable t {:error [(class t) (.getMessage t) (ex-data t)] :state (u/freeze machine)})))

(deftest failed-carrier-guards-preserve-charged-error-state
  (let [p (plan "lean_uint64_add")]
    (doseq [args [[-1 0] [18446744073709551616N 0] [nil 0] ["bad" 1] [(m/->Ref 999) 0]]]
      (let [start (initial "lean_uint64_add" args)
            expected (dissoc (attempt u/step! (u/thaw start)) :route)
            actual (dissoc (attempt (:execute! p) (u/thaw start)) :route)]
        (is (= expected actual))
        (is (= 1 (get-in actual [:state :stats :steps])))))
    (doseq [args [[(biginteger 7) 2] [(native/native-scalar 7) 2]]]
      (let [start (initial "lean_uint64_add" args) machine (u/thaw start)]
        (is (= :interpreted ((:execute! p) machine)))
        (is (= (u/freeze (u/step! (u/thaw start))) (u/freeze machine)))))
    (let [start (update (initial "lean_uint64_add" [1 2]) :locals dissoc (first (:params (second (by-symbol "lean_uint64_add")))))]
      (is (= (attempt u/step! (u/thaw start)) (attempt (:execute! p) (u/thaw start)))))))

(deftest supported-live-redefinitions-before-and-after-compilation
  (let [symbol "lean_uint64_add" start (initial symbol [3 4]) old (plan symbol)
        add-var (ns-resolve 'prototype.runtime-prim 'add)
        mutations [{#'runtime/evaluate (fn [_ world _ _] [world 77N])}
                   {add-var (fn [_ _] 88N)}
                   {#'scalar/integer! (fn [_ _] 2N)}
                   {#'native/native-scalar? (constantly true)}
                   {#'m/ref? (constantly true)}
                   {(ns-resolve 'prototype.mutable 'node) (fn [_ _] (throw (ex-info "changed-node" {})))}
                   {#'u/runtime-value! (fn [_ _ _] 99N)}
                   {#'runtime-string/supported-symbols (assoc runtime-string/supported-symbols symbol {:arity 2})}
                   {#'runtime-string/supported-symbols (Object.)}]]
    (doseq [mutation mutations]
      (with-redefs-fn mutation
        (fn []
          (doseq [p [old (plan symbol)]]
            (let [expected (dissoc (attempt u/step! (u/thaw start)) :route)
                  actual (attempt (:execute! p) (u/thaw start))]
              (is (= expected (dissoc actual :route)))
              (when-not (:error actual) (is (= :interpreted (:route actual)))))))))))

(deftest explicit-descriptor-validation-and-cache-separation
  (let [[name f] (by-symbol "lean_uint64_add") d (get @descriptions name)
        fs @functions body (:body f) cache (lazy/code-cache)
        optimized (lazy/open-program fs @options cache)
        default (lazy/open-program fs {} cache)
        edited (lazy/open-program fs {:scalar-wrappers (assoc @descriptions name (assoc-in d [:profile :abi-generation] "changed/2"))} cache)
        run #(lazy/run! % (u/thaw (initial "lean_uint64_add" [1 2])) 1)]
    (run optimized) (run default) (run edited)
    (is (= 6 (count (block/runtime-block-key fs body (block/prepare-options @options)))))
    (is (= 5 (count (block/runtime-block-key fs body {}))))
    (is (not= (block/runtime-block-key fs body @options) (block/runtime-block-key fs body (:options edited))))
    (is (= 3 (count @cache)))
    (is (some :specialization (vals @(:dispatch optimized))))
    (is (not-any? :specialization (vals @(:dispatch default))))
    (let [old (block/compile-program fs nil @options)
          changed (assoc-in fs [name :runtime-extern] "changed")
          next (block/compile-program changed old @options)]
      (is (not (:specialization (get (:blocks next) (prototype.fingerprint/key body))))))
    (doseq [bad [(assoc d :operation :sub) (assoc d :result-type "object") (assoc-in d [:profile :word-bits] 32)
                 (assoc-in d [:params 0 :id] Integer/MAX_VALUE) (assoc d :foreign (Object.))]]
      (is (thrown? clojure.lang.ExceptionInfo
                   (block/compile-runtime-block fs body {:scalar-wrappers {name bad} :scalar-wrapper-tokens (u/scalar-wrapper-tokens)}))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (lazy/open-program fs {:scalar-wrappers (into {} (for [n (range 65)] [n d]))})))
    (let [bad (assoc d :extern "lean_nat_add")]
      (is (thrown? clojure.lang.ExceptionInfo
                   (sw/compile-wrapper fs body {:scalar-wrappers {name bad} :scalar-wrapper-tokens (u/scalar-wrapper-tokens)})))
      (is (thrown? clojure.lang.ExceptionInfo
                   (block/runtime-block-key fs body {:scalar-wrappers {name bad} :scalar-wrapper-tokens (u/scalar-wrapper-tokens)}))))))

(def imported-functions (delay (into {} (map abi/lower) (rest (read-rows "scalar-wrapper-programs.jsonl")))))
(def imported-options
  (delay {:scalar-wrappers
          (into {} (keep (fn [row] (when-let [d (abi/describe-scalar row profile)] [(:name d) d])))
                (rest (read-rows "scalar-wrapper-programs.jsonl")))}))
(defn imported-target [label]
  (first (filter #(= label (last %)) (keys @imported-functions))))

(deftest actual-imported-programs-native-results-and-all-fuel-prefixes
  (let [fs @imported-functions options @imported-options
        cases (:cases (json/read-str (slurp (io/file fixture-dir "scalar-wrapper-program-values.json")) :key-fn keyword))
        programs [[:lazy (lazy/open-program fs options)] [:eager (block/compile-program fs nil options)] [:mutable nil]]]
    (is (= 8 (count fs)))
    (doseq [{:keys [function args result]} cases]
      (let [start (m/start (m/world fs) (imported-target function) (mapv carrier args))
            expected (m/run start) steps (get-in expected [:stats :steps])]
        (is (= (bigint result) (:result expected)))
        (doseq [fuel (range (+ 2 steps)) [backend program] programs]
          (let [actual (run-backend backend program start fuel)]
            (is (= (m/run start fuel) actual))
            (when (= :paused (:status actual))
              (let [saved actual]
                (is (= expected (run-backend backend program (m/resume saved nil) 1000)
                       (run-backend backend program (m/resume saved nil) 1000)))
                (is (= actual saved))))))))))

(deftest compiler-and-abi-owner-generations-invalidate-cached-specialization
  (let [symbol "lean_uint64_add" p (plan symbol) start (initial symbol [3 4])
        source-dir (io/file (.getParentFile (.getAbsoluteFile fixture-dir)) "src/prototype")
        fs @functions cache (lazy/code-cache) old (lazy/open-program fs @options cache)]
    (lazy/run! old (u/thaw start) 1)
    ;; Reload the actual emitter in the resident JVM. Old code must delegate,
    ;; and a newly compiled plan must select the new generation.
    (load-file (.getPath (io/file source-dir "scalar_wrapper.clj")))
    (let [machine (u/thaw start)]
      (is (= :interpreted ((:execute! p) machine)))
      (is (= (u/freeze (u/step! (u/thaw start))) (u/freeze machine))))
    (is (= :specialized ((:execute! (plan symbol)) (u/thaw start))))
    (load-file (.getPath (io/file source-dir "runtime_abi.clj")))
    (let [next (lazy/open-program fs @options cache)]
      (lazy/run! next (u/thaw start) 1)
      (is (= 2 (count @cache))))
    ;; Other owner token changes also invalidate old executors before effects.
    (doseq [[namespace token] [['prototype.machine 'scalar-reference-generation]
                              ['prototype.native-scalar 'scalar-carrier-generation]
                              ['prototype.scalar 'scalar-integer-generation]
                              ['prototype.runtime-prim 'scalar-arithmetic-generation]
                              ['prototype.mutable 'scalar-wrapper-generation]]]
      (let [current (plan symbol)]
        (with-redefs-fn {(ns-resolve namespace token) (Object.)}
          #(is (= :interpreted ((:execute! current) (u/thaw start)))))))))

(deftest consumer-reload-cannot-bless-an-overridden-foreign-classifier
  (let [symbol "lean_uint64_add" start (initial symbol [3 4])
        source-dir (io/file (.getParentFile (.getAbsoluteFile fixture-dir)) "src/prototype")]
    (with-redefs [native/native-scalar? (constantly false)]
      (load-file (.getPath (io/file source-dir "scalar.cljc")))
      (let [p (plan symbol) machine (u/thaw start)]
        (is (= :interpreted ((:execute! p) machine)))
        (is (= (u/freeze (u/step! (u/thaw start))) (u/freeze machine)))))
    (is (= :specialized ((:execute! (plan symbol)) (u/thaw start))))))

(deftest versioned-shared-equality-registry-native-values-and-long-carriers
  (let [rows (rest (read-rows "scalar-wrapper-programs.jsonl"))
        fs (into {} (map abi/lower) rows)
        descriptions (into {} (keep (fn [row] (when-let [d (abi/describe-scalar row profile)] [(:name d) d]))) rows)
        options {:scalar-wrappers descriptions}
        cases (rest (read-rows "scalar-wrapper-compare-native.jsonl"))
        plans (into {} (for [[name d] descriptions :when (= :eq (:operation d))]
                        [(:extern d) [name (block/compile-runtime-block fs (get-in fs [name :body]) options)]]))]
    (is (= 6 (count descriptions)))
    (is (= 162 (count cases)))
    (doseq [{:keys [symbol a b result]} cases]
      (let [[name p] (get plans symbol) start (m/start (m/world fs) name [(carrier a) (carrier b)])
            machine (u/thaw start) dest (second (get-in fs [name :body]))]
        (is (= :specialized ((:execute! p) machine)))
        (is (= (Long/parseLong result) (get-in (u/freeze machine) [:locals dest])))
        (is (= Long (class (get-in (u/freeze machine) [:locals dest]))))
        (is (= (m/step start) (u/freeze machine)))))
    (let [d (first (filter #(= :add (:operation %)) (vals descriptions)))
          legacy (assoc d :semantic-generation "unsigned-wrapper/1")]
      (is (= legacy (abi/validate-scalar-description! legacy))))
    (let [d (first (filter #(= :eq (:operation %)) (vals descriptions)))]
      (is (= "unsigned-wrapper/2" (:semantic-generation d)))
      (is (thrown? clojure.lang.ExceptionInfo (abi/validate-scalar-description! (assoc d :semantic-generation "unsigned-wrapper/1")))))))
