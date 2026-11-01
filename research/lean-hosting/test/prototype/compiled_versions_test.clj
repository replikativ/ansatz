(ns prototype.compiled-versions-test
  "Separate native A/B exports exercise persistent code images. Resident loading
   and FileHandles use the existing explicit frontend model, not hosted Lean."
  (:require [clojure.test :refer [deftest is]]
            [clojure.java.io :as io]
            [clojure.data.json :as json]
            [prototype.typed-tail-test :as fixture]
            [prototype.import-ir :as ir]
            [prototype.runtime-abi :as abi]
            [prototype.scalar-wrapper-test :as scalar-fixture]
            [prototype.typed-tail-execution-test :as execution-fixture]
            [prototype.session-compiler-options-test :as session-fixture]
            [prototype.typed-tail-execution :as execution]
            [prototype.raw-interop :as raw]
            [prototype.interop :as interop]
            [prototype.interop-codec :as codec]
            [prototype.machine :as m]
            [prototype.block-compile :as compiler]
            [prototype.lazy-runtime :as lazy]
            [prototype.resident-frontend :as resident]
            [prototype.resident-frontend-test :as resident-model]
            [prototype.hosted-file-test :as hosted-model]))

(def fixture-dir
  (first (filter #(.exists (io/file % "compiled-version-a.jsonl"))
                 [(io/file (.getParentFile (.getParentFile (.getParentFile (.getAbsoluteFile (io/file *file*))))) "fixtures")
                  (io/file "fixtures") (io/file "experiments/lean-ir/fixtures")])))
(defn version [label]
  (let [rows (with-open [reader (io/reader (io/file fixture-dir (str "compiled-version-" label ".jsonl")))]
               (mapv #(json/read-str % :key-fn keyword) (rest (line-seq reader))))]
    {:runtime (into {} (map abi/lower) rows)
     :typed (into {} (comp (filter #(get-in % [:ir :fdecl])) (map ir/lower-typed-declaration)) rows)
     :descriptors (into {} (keep (fn [row] (when-let [d (abi/describe-scalar row scalar-fixture/profile)] [(:name d) d]))) rows)}))
(defn source-values []
  (:values (json/read-str (slurp (io/file fixture-dir "compiled-version-values.json")) :key-fn keyword)))
(defn target [input label] (fixture/target (:typed input) label))
(defn options [input label]
  (let [root (target input label)]
    {:typed-tail {:typed-functions (select-keys (:typed input) [root]) :roots [root]
                  :descriptors (:descriptors input) :profile scalar-fixture/profile :budgets fixture/budgets}}))
(defn open [input label cache]
  (raw/open-functions (:runtime input) {} {:cache cache :compiler-options (options input label) :fuel 10000}))
(defn block-key [session name]
  ;; Reuse the compiler's public raw-option key API. Never feed a private
  ;; normalized provider closure back as a validation certificate.
  (compiler/runtime-block-key (:functions session) (get-in session [:functions name :body])
                              (merge (:compiler-options session)
                                     (select-keys (get-in session [:program :options]) [:lexical-joins :direct-linking]))))
(defn state-oracle [world name args called]
  (let [expected (m/run (m/start world name args))]
    (is (= expected (:state called)))
    (is (= (execution-fixture/carrier-shape expected)
           (execution-fixture/carrier-shape (:state called))))))

(defn selected-call [events invoke]
  (let [before (count @events) result (invoke)]
    (is (some #{[:typed-tail :specialized]} (subvec @events before)))
    result))

(deftest native-source-edit-retains-old-images-and-reuses-unaffected-callers
  (let [a (version "a") b (version "b") sum (target a "sum64") entry (target a "entry") identity (target a "identity64")
        cache (lazy/code-cache) events (atom []) compile execution/compile-entry
        sa (open a "sum64" cache) sb (open b "sum64" cache)
        [wa held-a] (m/resource (m/world (:runtime a)) "retained-A")
        [wb held-b] (m/resource (m/world (:runtime b)) "retained-B")
        initial (m/start wa entry [10N 0N])]
    (is (= (set (keys (:runtime a))) (set (keys (:runtime b)))))
    (is (= (get-in a [:runtime entry]) (get-in b [:runtime entry])))
    (is (= (get-in a [:runtime identity]) (get-in b [:runtime identity])))
    (is (not= (get-in a [:runtime sum :body]) (get-in b [:runtime sum :body])))
    (with-redefs [execution/compile-entry (session-fixture/observe-route events compile)]
      (let [old (selected-call events #(raw/call sa wa entry [10N 0N]))
            saved (:state (raw/advance-to-boundary (assoc sa :fuel 7) initial))
            _ (raw/call sa wa identity [18446744073709551615N])
            entry-key (block-key sa entry) identity-key (block-key sa identity) sum-a-key (block-key sa sum)
            entry-artifact (get @cache entry-key) identity-artifact (get @cache identity-key)
            sum-a-artifact (get @cache sum-a-key)
            next (selected-call events #(raw/call sb wb entry [10N 0N]))
            _ (raw/call sb wb identity [18446744073709551615N])
            sum-b-key (block-key sb sum) sum-b-artifact (get @cache sum-b-key)
            retained (selected-call events #(raw/call sa wa entry [10N 0N]))
            left (raw/continue sa (m/resume saved nil)) right (raw/continue sa (m/resume saved nil))
            ia (interop/open-functions (:runtime a) {} :jvm cache {:compiler-options (options a "sum64")})
            ib (interop/open-functions (:runtime b) {} :jvm cache {:compiler-options (options b "sum64")})
            old-handle (interop/function ia entry) new-handle (interop/function ib entry)]
        (is (= [(bigint (get-in (source-values) [:A :entry]))
                (bigint (get-in (source-values) [:B :entry]))
                (bigint (get-in (source-values) [:A :entry]))]
               (mapv :value [old next retained])))
        (is (= [55N 65N 55N] [(selected-call events #(old-handle 10N 0N))
                               (selected-call events #(new-handle 10N 0N))
                               (selected-call events #(old-handle 10N 0N))]))
        (doseq [[world called] [[wa old] [wb next] [wa retained] [wa left] [wa right]]]
          (state-oracle world entry [10N 0N] called))
        (is (= :paused (:status saved)))
        (is (= saved (m/run initial 7)))
        (is (= (:state old) (:state left) (:state right)))
        (is (= entry-key (block-key sb entry)))
        (is (= identity-key (block-key sb identity)))
        (is (some? entry-artifact))
        (is (some? identity-artifact))
        (is (identical? entry-artifact (get @cache (block-key sb entry))))
        (is (identical? identity-artifact (get @cache (block-key sb identity))))
        (is (pos? (:cache-hits (lazy/summary (:program sb)))))
        (is (not= sum-a-key sum-b-key))
        (is (= :typed-tail (get-in sum-a-artifact [:specialization :kind])))
        (is (= :typed-tail (get-in sum-b-artifact [:specialization :kind])))
        (is (not (identical? sum-a-artifact sum-b-artifact)))
        (is (identical? sum-a-artifact (get @cache sum-a-key)))
        (is (some #{[:typed-tail :specialized]} @events))
        (is (= "retained-A" (:tag (m/node (:state retained) held-a))))
        (is (= "retained-B" (:tag (m/node (:state next) held-b))))))
    (is (= initial (m/start wa entry [10N 0N])))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"different executable code"
                         (raw/call sa wb entry [10N 0N])))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"does not match executable code"
                         (raw/open-functions (:runtime b) {} {:compiler-options (options a "sum64")})))))

(deftest actual-external-wrapper-edit-invalidates-an-unchanged-selected-source
  (let [a (version "a") b (version "b") root (target a "externCall")
        chosen (first (filter #(= "chosenOp" (last %)) (keys (:descriptors a))))
        cache (lazy/code-cache) events (atom []) compile execution/compile-entry
        sa (open a "externCall" cache) sb (open b "externCall" cache)
        wa (m/world (:runtime a)) wb (m/world (:runtime b))]
    (is (= (get-in a [:typed root]) (get-in b [:typed root])))
    (is (= "lean_uint64_add" (get-in a [:runtime chosen :runtime-extern])))
    (is (= "lean_uint64_sub" (get-in b [:runtime chosen :runtime-extern])))
    (with-redefs [execution/compile-entry (session-fixture/observe-route events compile)]
      (let [old (selected-call events #(raw/call sa wa root [9N 4N])) key-a (block-key sa root) artifact-a (get @cache key-a)
            next (selected-call events #(raw/call sb wb root [9N 4N])) key-b (block-key sb root) artifact-b (get @cache key-b)
            retained (selected-call events #(raw/call sa wa root [9N 4N]))]
        (is (= [(bigint (get-in (source-values) [:A :operation-source-oracle]))
                (bigint (get-in (source-values) [:B :operation-source-oracle]))
                (bigint (get-in (source-values) [:A :operation-source-oracle]))]
               (mapv :value [old next retained])))
        (doseq [[world called] [[wa old] [wb next] [wa retained]]]
          (state-oracle world root [9N 4N] called))
        (is (not= key-a key-b))
        (is (= :typed-tail (get-in artifact-a [:specialization :kind])))
        (is (= :typed-tail (get-in artifact-b [:specialization :kind])))
        (is (not (identical? artifact-a artifact-b)))
        (is (identical? artifact-a (get @cache key-a)))
        (is (some #{[:typed-tail :specialized]} @events))))
    ;; Only the actual external declaration changed; stale source facts cannot
    ;; turn its old add descriptor into permission to specialize the new sub.
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"does not match executable code"
                         (raw/open-functions (:runtime b) {} {:compiler-options (options a "externCall")})))))

(defn modeled-context [input cache]
  (let [p (resident-model/prepared :jvm true @hosted-model/captured)
        functions (merge (get-in p [:world :functions]) (:runtime input))
        prepared (assoc p :world (assoc (:world p) :functions functions)
                         :session (raw/open-functions functions {}
                                                      {:cache cache :compiler-options (options input "sum64")}))]
    (resident/adopt-prepared prepared {:trusted-functions functions :trusted-bindings {}
                                      :application-extern-symbols #{"application_answer"}})))

(deftest modeled-resident-handles-belong-to-their-retained-image-contexts
  (let [a (version "a") b (version "b") cache (lazy/code-cache)
        ca (modeled-context a cache) cb (modeled-context b cache)
        binding-a {:signature {:params [] :return-type "object"} :handler (fn [_ world _] [world 41])}
        binding-b {:signature {:params [] :return-type "object"} :handler (fn [_ world _] [world 42])}
        extended-a (resident/with-externs ca {"application_answer" binding-a})
        extended-b (resident/with-externs cb {"application_answer" binding-b})
        loaded-a (resident-model/load-identity extended-a) loaded-b (resident-model/load-identity extended-b)
        image-a (:context loaded-a) image-b (:context loaded-b)
        sibling (resident/fork image-a) owned (atom [ca cb extended-a extended-b image-a image-b sibling])]
    (try
      (is (:success loaded-a)) (is (:success loaded-b))
      (doseq [[context file] [[image-a (:file loaded-a)] [image-b (:file loaded-b)] [sibling (:file loaded-a)]]]
        (let [called (resident/call context file hosted-model/answer-name [nil 42N] resident-model/identity-signature)]
          (swap! owned conj (:context called))
          (is (= 42N (:value called)))))
      ;; The native A/B scalar programs were preinstalled in these independently
      ;; prepared images. Only identity compilation/FileHandle transport is modeled.
      (is (= [55N 65N 55N]
             (mapv (fn [context]
                     (let [{:keys [session world]} (resident/snapshot context)]
                       (:value (raw/call session world (target a "entry") [10N 0N]))))
                   [image-a image-b sibling])))
      (doseq [context [ca cb extended-a extended-b image-a image-b sibling]]
        (is (identical? cache (get-in (resident/snapshot context) [:session :cache]))))
      (is (identical? binding-a (get-in (resident/snapshot image-a) [:session :bindings "application_answer"])))
      (is (identical? binding-b (get-in (resident/snapshot image-b) [:session :bindings "application_answer"])))
      (with-redefs [codec/encode-boxed (fn [& _] (throw (AssertionError. "wrong handle must reject before encoding")))]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"different context generation"
                             (resident/call image-b (:file loaded-a) hosted-model/answer-name [nil 42N]
                                            resident-model/identity-signature)))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"different context generation"
                             (resident/call image-a (:file loaded-b) hosted-model/answer-name [nil 42N]
                                            resident-model/identity-signature))))
      (finally (doseq [context @owned] (resident/close! context))))))
