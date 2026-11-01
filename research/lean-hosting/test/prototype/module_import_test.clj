(ns prototype.module-import-test
  (:require [clojure.test :refer [deftest is]] [prototype.module-import :as import]
            [prototype.imported-kernel :as kernel] [prototype.module-data :as data] [prototype.module-store :as store]
            [prototype.machine :as m] [prototype.kernel-bridge :as bridge]
            [prototype.import-ir :as ir] [prototype.runtime-abi :as abi]
            [prototype.raw-interop :as raw] [prototype.kernel-bridge-test :as guest])
  (:import [ansatz.kernel ConstantInfo]))

(def options {:allow-standalone? true :kernel-policy {:allow-axioms? true :allow-unsafe? true}})
(defn loaded [] (data/load-file (m/world {}) "fixtures/imported-kernel-native.jsonl"))
(defn constants [loaded]
  (mapv :guest (kernel/module-constants (:world loaded) (first (:roots loaded)))))
(defn names [loaded]
  (into {} (map (fn [{:keys [guest ^ConstantInfo constant]}] [(str (.name constant)) guest]))
        (kernel/module-constants (:world loaded) (first (:roots loaded)))))

(defn helper-model
  "Instrument only the typed helper boundary and guest ownership; this is NOT
   an implementation of Lean finalization. Native oracle executes the genuine
   helpers in target/ModuleImportOracle.lean. Production always calls invoke."
  [calls final-values & {:keys [io-error?]}]
  (fn [world target args]
    (swap! calls conj [target args])
    (cond
      (= target (:part import/helpers))
      (let [[data file bytes] args
            [world region] (m/allocate (m/retain world data 1) :ctor 0 [data file bytes])]
        (m/allocate world :ctor 0 [data region]))
      (= target (:request import/helpers)) (m/allocate world :ctor 0 (vec args))
      (= target (:module import/helpers)) (m/allocate world :ctor 0 (subvec args 7 9))
      (= target (:state import/helpers)) (m/allocate world :ctor 0 args)
      (= target (:finalize import/helpers))
      (let [[state imports _] args world (-> world (m/release state 1) (m/release imports 1))]
        (if io-error?
          (let [[world error] (m/resource world "native-import-error")]
            (m/allocate world :ctor 1 [error]))
          (let [[world values] (m/allocate world :array 246 final-values)
                [world root] (m/allocate world :ctor 0 [values])
                [world environment] (m/allocate world :ctor 0 [root])]
            (m/allocate world :ctor 0 [environment]))))
      (= target (:root import/helpers))
      (let [root (first (:fields (m/node world (first args))))]
        [(m/retain world root 1) root])
      (= target (:constant-map import/helpers))
      (let [root (first (:fields (m/node world (first args))))
            constants (first (:fields (m/node world root)))]
        [(m/retain world constants 1) constants])
      (= target (:constants import/helpers))
      (let [root (first (:fields (m/node world (first args))))
            array (first (:fields (m/node world root)))
            values (:fields (m/node world array))
            world (reduce #(m/retain %1 %2 1) world values)]
        (m/allocate world :array 246 values))
      (= target (:quot-init? import/helpers)) [world 1]
      :else (throw (ex-info "Unexpected import helper" {:target target})))))

(deftest real-typed-helper-sequence-and-import-owners
  (let [loaded (loaded) before (:world loaded) calls (atom [])
        result (import/import-loaded loaded (helper-model calls (constants loaded)) options)
        world (:world result) environment (:environment result)
        root (first (:fields (m/node world environment)))
        first-args (second (first @calls))
        mod-args (second (first (filter #(= (:module import/helpers) (first %)) @calls)))
        request-args (second (first (filter #(= (:request import/helpers) (first %)) @calls)))
        constant-map (get-in world [:kernel-environments (:id root) :constant-map])
        released (cond-> (-> world (m/release environment 1) (update :kernel-environments dissoc (:id root)) (m/release root 1))
                   constant-map (m/release constant-map 1))]
    (is (= :ok (:status result)))
    (is (= 17 (count (get-in result [:certificate :constants]))))
    (is (= (first (:roots loaded)) (first first-args)))
    (is (= ["KernelImportProbe" 0 1 0 0 1 0] (subvec mod-args 0 7)))
    (is (= ["KernelImportProbe" 0 1 0] request-args))
    (is (= 1 (:rc (m/node world environment))))
    (is (= 2 (:rc (m/node world root))))
    (is (identical? (get-in result [:certificate :env]) (get-in world [:kernel-environments (:id root) :env])))
    (is (= (+ 3 (count (:heap before))) (count (:heap world))))
    (is (= (:heap before) (:heap released)))
    (is (nil? (:kernel-environments before)))))

(deftest final-checked-map-is-the-authority-after-guest-finalization
  (let [loaded (loaded) calls (atom []) refs (names loaded)
        selected (filterv #(not= % (get refs "unsafeA")) (constants loaded))
        result (import/import-loaded loaded (helper-model calls selected) options)]
    (is (= :ok (:status result)))
    (is (= 16 (count (get-in result [:certificate :constants]))))
    (is (not (contains? (set (map str (keys (get-in result [:certificate :constants])))) "unsafeA")))
    (is (= 2 (count (filter #(= (:constants import/helpers) (first %)) @calls))))))

(deftest io-error-retains-the-real-owned-error-and-never-associates
  (let [loaded (loaded) calls (atom [])
        result (import/import-loaded loaded (helper-model calls [] :io-error? true) options)
        world (:world result) wrapper (:io-result result)
        released (m/release world wrapper 1)]
    (is (= :io-error (:status result)))
    (is (= 1 (:tag (m/node world wrapper))))
    (is (not-any? #(= (:constants import/helpers) (first %)) @calls))
    (is (nil? (:kernel-environments world)))
    (is (= (:heap (:world loaded)) (:heap released)))))

(deftest strict-check-failure-exposes-a-checkpoint-without-a-java-association
  (let [loaded (loaded) refs (names loaded) alias (get refs "aliasA")
        payload (first (:fields (m/node (:world loaded) alias)))
        [world missing] (guest/constant (:world loaded) "MissingImportType")
        changed (assoc-in world [:heap (:id payload) :fields 1] missing)
        changed-loaded (assoc loaded :world changed) calls (atom [])
        error (try (import/import-loaded changed-loaded (helper-model calls (constants changed-loaded)) options)
                   nil (catch clojure.lang.ExceptionInfo e e))]
    (is (= :kernel-association (:phase (ex-data error))))
    (is (m/ref? (:environment (ex-data error))))
    (is (nil? (:kernel-environments (:checkpoint (ex-data error)))))))

(deftest incomplete-closures-and-lossy-module-names-fail-before-guest-calls
  (let [loaded (loaded) calls (atom []) invoke (helper-model calls [])]
    (is (thrown-with-msg? Exception #"transitive closure" (import/import-loaded loaded invoke)))
    (is (empty? @calls)))
  (is (= "A.B" (import/module-string ["str" ["str" ["anonymous"] "A"] "B"])))
  (doseq [name [["anonymous"] ["str" ["anonymous"] "A.B"] ["str" ["anonymous"] ""] ["num" ["anonymous"] "1"]]]
    (is (thrown? Exception (import/module-string name)))))

(deftest disk-backed-receiver-keeps-source-and-never-hydrates-the-native-heap
  (let [loaded (store/load-file (m/world {}) "fixtures/imported-kernel-native.jsonl" {:cache-size 2})
        source (:source loaded)]
    (try
      (let [calls (atom [])
            result (import/import-loaded loaded (helper-model calls (constants loaded)) options)
            world (:world result)]
        (is (= :ok (:status result)))
        (is (= 17 (count (get-in result [:certificate :constants]))))
        (is (identical? (:native-imports (:world loaded)) (:native-imports world)))
        (is (= 3 (count (:heap world))))
        (is (<= (.size ^java.util.LinkedHashMap (:cache source)) 2)))
      (finally (.close ^java.io.Closeable source)))))

(deftest standalone-mode-examines-real-guest-imports-rather-than-summary-metadata
  (let [loaded (loaded) world (:world loaded)
        [world fake-import] (m/allocate world :ctor 0 [])
        [world imports] (m/allocate world :array 246 [fake-import])
        data (first (:roots loaded))
        world (assoc-in world [:heap (:id data) :fields 0] imports)
        calls (atom [])]
    (is (thrown-with-msg? Exception #"unresolved module dependencies"
          (import/import-loaded (assoc loaded :world world) (helper-model calls []) options)))
    (is (empty? @calls))))

(deftest bulk-validates-all-metadata-before-invoking-guest
  (doseq [change [(fn [loaded] (assoc-in loaded [:modules 0 :parts 0 :artifact :mappedBytes] -1))
                  (fn [loaded] (assoc-in loaded [:modules 0 :parts 0 :artifact :leanCommit] "wrong"))
                  (fn [loaded] (assoc-in loaded [:modules 0 :parts 0 :artifact :filePath] "bad\u0000path"))]]
    (let [calls (atom [])]
      (is (thrown? Exception
            (import/assemble (change (loaded)) (helper-model calls []) (assoc options :assembly :bulk))))
      (is (empty? @calls))))
  (let [calls (atom [])]
    (is (thrown-with-msg? Exception #"Unknown guest import assembly"
          (import/assemble (loaded) (helper-model calls []) (assoc options :assembly :guess))))
    (is (empty? @calls))))

(deftest bulk-input-records-have-only-object-fields-and-transfer-result-owners
  ;; Boundary/ownership test only. The actual pinned batch IR is exercised by
  ;; the separate native oracle and the all-backend exported closure test.
  (let [loaded (loaded) seen (atom []) before (:world loaded)
        result
        (import/assemble loaded
          (fn [world target [modules requests]]
            (swap! seen conj target)
            (is (= import/bulk-helper target))
            (let [module (first (:fields (m/node world modules)))
                  request (first (:fields (m/node world requests)))
                  fields (:fields (m/node world module))
                  part (first (:fields (m/node world (nth fields 7))))]
              (is (= ["KernelImportProbe" 0 1 0 0 1 0] (subvec fields 0 7)))
              (is (= ["KernelImportProbe" 0 1 0] (:fields (m/node world request))))
              (is (= [(first (:roots loaded))
                      (get-in loaded [:modules 0 :parts 0 :artifact :filePath])
                      (get-in loaded [:modules 0 :parts 0 :artifact :mappedBytes])]
                     (:fields (m/node world part))))
              (doseq [record [module request part]]
                (is (nil? (:layout (m/node world record)))))
              (let [world (-> world (m/release modules 1) (m/release requests 1))
                    [world state] (m/allocate world :ctor 0 [])
                    [world imports] (m/allocate world :array 246 [])]
                (m/allocate world :ctor 0 [state imports]))))
          (assoc options :assembly :bulk))
        world (:world result)
        released (-> world (m/release (:state result) 1) (m/release (:imports result) 1))]
    (is (= [import/bulk-helper] @seen))
    (is (= 1 (:rc (m/node world (:state result)))))
    (is (= 1 (:rc (m/node world (:imports result)))))
    (is (= (:heap before) (:heap released)))))


(def bulk-functions
  (delay
    (let [catalogue (ir/index-bundles ["fixtures/module-import-bulk.jsonl"])]
      (ir/load-closure catalogue [import/bulk-helper]
        #(abi/lower-deferred-catalogue catalogue %)))))

(deftest actual-exported-bulk-helper-runs-on-all-three-backends-without-input-leaks
  ;; Exact pinned IR plus exported String implementation aliases; no helper
  ;; stubs. This exercises real mkVirtualPart, String.toName and the Lean
  ;; persistent HashMap assembly. Finalization is covered by the native oracle
  ;; and root's live hosted frontend, not replaced by this assembly-only test.
  (doseq [backend [:reference :mutable :jvm]]
    (let [functions @bulk-functions
          loaded (update (loaded) :world assoc :functions functions)
          before (:world loaded)
          session (raw/open-functions functions {} {:backend backend :fuel 100000})
          calls (atom 0)
          invoke (fn [world target args]
                   (swap! calls inc)
                   (let [result (raw/call session world target args)]
                     [(:state result) (:value result)]))
          result (import/assemble loaded invoke (assoc options :assembly :bulk))
          world (:world result) state (:state result) imports (:imports result)
          request (first (:fields (m/node world imports)))
          imported-name (first (:fields (m/node world request)))
          state-names (second (:fields (m/node world state)))
          released (-> world (m/release state 1) (m/release imports 1))
          original-ids (set (keys (:heap before)))
          remaining-owned (filter (fn [[id node]] (and (not (contains? original-ids id)) (pos? (:rc node))))
                                  (:heap released))]
      (is (= 1 @calls))
      (is (= "KernelImportProbe" (str (bridge/project-name world imported-name))))
      (is (= ["KernelImportProbe"]
             (mapv #(str (bridge/project-name world %)) (:fields (m/node world state-names)))))
      (is (= 1 (:rc (m/node world state))))
      (is (= 1 (:rc (m/node world imports))))
      (is (> (get-in world [:stats :steps]) 2000))
      (is (empty? remaining-owned))
      (is (= (:heap before) (select-keys (:heap released) original-ids))))))


(deftest header-mode-requires-matching-producer-visibility-before-any-guest-call
  (let [loaded (loaded) calls (atom []) invoke (helper-model calls [])]
    (is (thrown-with-msg? Exception #"visibility does not match"
          (import/import-loaded loaded invoke (assoc options :module-system? true))))
    (is (empty? @calls))
    (is (thrown-with-msg? Exception #"explicit Bool"
          (import/assemble loaded invoke (assoc options :module-system? 1))))
    (is (thrown-with-msg? Exception #"visibility does not match"
          (import/assemble (assoc-in loaded [:manifest :input :globalLevel] "exported") invoke options)))
    (is (thrown-with-msg? Exception #"require module artifacts"
          (import/assemble (assoc-in loaded [:manifest :input :globalLevel] "exported") invoke
                           (assoc options :module-system? true))))
    (is (empty? @calls))))
