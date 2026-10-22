(ns prototype.classic-header-discovery-test
  "Packet/ownership/bounds over a fixed-target transport MODEL. Native parser
   oracle data is separate evidence, not execution of the full guest frontend."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.string :as str]
            [prototype.source-graph-runtime-test :as fixture]
            [prototype.resident-init-prefix :as prefix]
            [prototype.resident-frontend :as resident]
            [prototype.source-import :as source]
            [prototype.frontend :as frontend]
            [prototype.raw-interop :as raw]
            [prototype.runtime-prim :as prim]
            [prototype.machine :as m]))

(def limits {:max-source-bytes 4096 :max-file-name-bytes 256 :max-output-bytes 8192 :max-json-depth 64
             :max-imports 16 :max-diagnostics 16 :max-name-nodes 32 :max-name-bytes 256 :max-total-name-bytes 4096})
(def budgets {:helper-fuel 1000 :attempt-fuel 1000})
(def marker (fixture/str-name "DiscoveryModelCounter"))
(defn request [] {:text "import Package.A\n" :file-name "Discovery.lean"})
(defn header []
  {:schema "lean-file-header/1" :producer "RuntimeCompileShim.inspectFileHeader"
   :leanCommit (get prim/pinned-build "lean_get_githash")
   :runtimeProfile {:target "x86_64-unknown-linux-gnu" :wordBits 64}
   :fileName "Discovery.lean" :moduleSystem false :hasErrors false :headerEndByte 0 :diagnostics []
   :requestedImports (conj source/init-requests
                          (assoc source/init-request :module ["str" (fixture/str-name "Package") "A"]))})
(def diagnostics (atom nil))
(defn remember-first-failure! [packet] (compare-and-set! diagnostics nil packet))
(defn failure [f] (try (f) nil (catch Throwable cause cause)))
(defn configure [input]
  (let [output (atom {:text (json/write-str (header)) :tag 0}) calls (atom [])
        selected (ex-info "selected actual header host failure" {})
        signature {:params (vec (repeat 3 {:ty "object" :borrow false})) :return-type "object"}
        symbol "classic_header_discovery_model"
        binding {:signature signature
                 :handler (fn [context world args]
                            (swap! calls conj args)
                            (let [n (inc (get-in world [:globals marker :value] 0))
                                  world (assoc-in world [:globals marker] {:status :ready :value n})]
                              (if (:throw? @output)
                                (do ((:checkpoint! context) world) (throw selected))
                                (m/allocate world :ctor (:tag @output) [(:text @output)]))))}
        function {:params [1 2 3] :raw-extern {:symbol symbol :signature signature}
                  :body [:let 5 [:literal 0]
                         [:host symbol [[:var 1] [:var 2] [:var 3]] 4 [:return [:var 4]]]]}]
    {:functions (assoc (:functions input) frontend/header-target function)
     :bindings (assoc (:bindings input) symbol binding)
     :output output :calls calls :selected selected}))
(defn discover [f packet text & [changed-limits]]
  (prefix/discover-classic-source-header packet text
    {:configuration (:configuration f) :limits (or changed-limits limits) :budgets budgets}))

(deftest updated-packets-preserve-effects-and-adopt-once-after-discovery
  (doseq [backend [:reference :mutable :jvm]]
    (fixture/with-empty-publication backend
      (fn [{:keys [context configuration transport source] :as f}]
        (let [entry (resident/snapshot context) observed (atom []) call @#'raw/call
              [first-result second-result]
              (with-redefs [raw/call (fn [& args]
                                      (let [result (apply call args)]
                                        (swap! observed conj {:target (nth args 2) :result result}) result))]
                (let [first-result (discover f entry (request))
                      second-result (discover f (:packet first-result) (request))]
                  [first-result second-result]))
              packet (:packet second-result)
              adopted (resident/adopt-prepared packet configuration)]
          (swap! (:captured f) conj {:result second-result} adopted)
          (is (= :ok (:status second-result)))
          (is (= (:requestedImports (header)) (get-in second-result [:header :requestedImports])))
          (is (= 2 (count @(:calls transport))))
          (is (= 1 (get-in first-result [:packet :world :globals marker :value])))
          (is (= 2 (get-in packet [:world :globals marker :value])))
          (is (= 2 (get-in (resident/snapshot adopted) [:world :globals marker :value])))
          (is (= (get-in entry [:session :fuel]) (get-in packet [:session :fuel])))
          (doseq [[key value] (get-in (last @observed) [:result :session]) :when (not= key :fuel)]
            (is (true? (identical? value (get-in packet [:session key])))))
          (is (true? (identical? (:environment entry) (:environment packet))))
          (is (true? (identical? (:options entry) (:options packet))))
          (is (true? (identical? (:catalogue entry) (:catalogue packet))))
          (is (true? (identical? entry (resident/snapshot context))))
          (is (true? (= (get-in entry [:world :heap]) (get-in packet [:world :heap]))))
          (is (every? #(= frontend/header-target (:target %)) @observed))
          (doseq [{:keys [result]} @observed]
            (is (not (contains? (get-in packet [:world :heap]) (:id (:value result))))))
          (is (pos? (get-in second-result [:progress :helper-steps])))
          (is (= (- (get-in packet [:world :stats :steps]) (get-in first-result [:packet :world :stats :steps]))
                 (get-in second-result [:progress :guest-steps])))
          (is (false? @(:closed source)))
          (resident/close! adopted)))
      :configure configure)))

(deftest parser-errors-return-owned-packet-with-diagnostics-and-no-imports
  (fixture/with-empty-publication :reference
    (fn [{:keys [context transport] :as f}]
      (let [error-header (assoc (header) :hasErrors true :requestedImports []
                                       :diagnostics [{:severity "error" :data "model parser diagnostic"}])
            _ (reset! (:output transport) {:text (json/write-str error-header) :tag 0})
            result (with-redefs [source/validate-graph-imports!
                                (fn [_] (throw (ex-info "error envelope must not validate imports" {})))]
                     (discover f (resident/snapshot context) (request)))]
        (swap! (:captured f) conj result)
        (is (= :header-error (:status result)))
        (is (= [] (get-in result [:header :requestedImports])))
        (is (= (:diagnostics error-header) (get-in result [:header :diagnostics])))
        (is (= 1 (get-in result [:packet :world :globals marker :value])))))
    :configure configure))

(deftest bounds-and-owned-invalid-results-retain-the-exact-latest-packet
  (fixture/with-empty-publication :reference
    (fn [{:keys [context transport] :as f}]
      (let [entry (resident/snapshot context) parser @#'json/read-str]
        (doseq [[label output bound before-parser?]
                [[:oversized (apply str (repeat 8193 "x")) limits true]
                 [:utf8 (apply str (repeat 4097 "λ")) limits true]
                 [:depth (str (apply str (repeat 65 "[")) "0" (apply str (repeat 65 "]"))) limits true]
                 [:offset (json/write-str (assoc (header) :headerEndByte 100000)) limits false]
                 [:imports (json/write-str (header)) (assoc limits :max-imports 2) false]
                 [:diagnostics (json/write-str (assoc (header) :diagnostics [{} {}])) (assoc limits :max-diagnostics 1) false]
                 [:names (json/write-str (header)) (assoc limits :max-name-bytes 3) false]
                 [:aggregate (json/write-str (header)) (assoc limits :max-total-name-bytes 8) false]
                 [:name-depth (json/write-str (header)) (assoc limits :max-name-nodes 2) false]
                 [:flags (json/write-str (assoc-in (header) [:requestedImports 2 :isMeta] true)) limits false]
                 [:error-imports (json/write-str (assoc (header) :hasErrors true)) limits false]
                 [:module (json/write-str (assoc (header) :moduleSystem true)) limits false]
                 [:prelude (json/write-str (assoc (header) :requestedImports [])) limits false]]]
          (reset! (:output transport) {:text output :tag 0})
          (let [parsed (atom 0)
                cause (with-redefs [json/read-str (fn [& args] (swap! parsed inc) (apply parser args))]
                        (failure #(discover f entry (request) bound)))
                state (:classic-header-discovery-state (ex-data cause))
                raw-result (get-in state [:last-operation :returned :raw-result])
                wrapper (:value raw-result)]
            (remember-first-failure! {:label label :cause cause})
            (is (some? cause) (name label))
            (is (= :owned (get-in state [:header-result :status])) (name label))
            (is (true? (identical? (:state raw-result) (:checkpoint (ex-data cause)))) (name label))
            (is (true? (identical? (:session raw-result) (:checkpoint-session (ex-data cause)))) (name label))
            (is (contains? (get-in state [:world :heap]) (:id wrapper)) (name label))
            (is (pos? (:used state)) (name label))
            (when before-parser? (is (zero? @parsed) (name label)))))
        (doseq [input [(assoc (request) :text (apply str (repeat 4097 "x")))
                       (assoc (request) :text (apply str (repeat 2049 "λ")))
                       (assoc (request) :file-name (apply str (repeat 257 "x")))]]
          (let [calls-before (count @(:calls transport)) cause (failure #(discover f entry input))]
            (remember-first-failure! {:input-bounds cause})
            (is (some? cause)) (is (= calls-before (count @(:calls transport))))))
        (reset! (:output transport) {:text "owned IO error model" :tag 1})
        (let [cause (failure #(discover f entry (request)))
              state (:classic-header-discovery-state (ex-data cause))]
          (remember-first-failure! {:malformed-io cause})
          (is (= :owned (get-in state [:header-result :status]))))))
    :configure configure))

(deftest native-parser-unicode-byte-offset-is-accepted-through-modeled-transport
  ;; This is captured native parseHeader DATA, not actual guest-helper execution.
  ;; Its offset exceeds UTF-16 character count and must be checked as UTF-8 bytes.
  (let [text "-- λ界\n/- α -/\nimport Init\n"
        row (first (filter #(= text (:input %))
                     (map #(json/read-str % :key-fn keyword)
                          (str/split-lines (slurp "fixtures/parser-header-full-oracle.jsonl")))))]
    (is (some? row)) (is (> (:position row) (count text)))
    (fixture/with-empty-publication :reference
      (fn [{:keys [context transport] :as f}]
        (reset! (:output transport)
                {:tag 0 :text (json/write-str (assoc (header) :headerEndByte (:position row)
                                                 :requestedImports (conj source/init-requests source/init-request)))})
        (let [result (discover f (resident/snapshot context) (assoc (request) :text text))]
          (swap! (:captured f) conj result)
          (is (= :ok (:status result)))
          (is (= (:position row) (get-in result [:header :headerEndByte])))))
      :configure configure)))

(deftest raw-failure-preserves-checkpoint-session-and-known-helper-charge
  (fixture/with-empty-publication :reference
    (fn [{:keys [context transport] :as f}]
      (reset! (:output transport) {:throw? true})
      (let [entry (resident/snapshot context)
            cause (failure #(discover f entry (request)))
            state (:classic-header-discovery-state (ex-data cause))
            world (:checkpoint (ex-data cause))]
        (remember-first-failure! {:raw-failure cause})
        (is (some? cause))
        (is (true? (identical? world (:world state))))
        (is (true? (identical? (:checkpoint-session (ex-data cause)) (:session state))))
        (is (= 1 (get-in world [:globals marker :value])))
        (is (= (- (get-in world [:stats :steps]) (get-in entry [:world :stats :steps])) (:used state)))
        (is (pos? (:used state))) (is (zero? (:reserved state)))
        (is (true? (:budget-poisoned? state)))
        (is (true? (loop [c cause remaining 8]
                     (cond (identical? c (:selected transport)) true
                           (or (nil? c) (zero? remaining)) false
                           :else (recur (.getCause ^Throwable c) (dec remaining))))))
        (let [selected (ex-info "selected unknown transport failure" {})
              calls-before (count @(:calls transport))
              unknown (with-redefs [raw/call (fn [& _] (throw selected))]
                        (failure #(discover f entry (request))))
              state (:classic-header-discovery-state (ex-data unknown))]
          (remember-first-failure! {:unknown-transport unknown})
          (is (= calls-before (count @(:calls transport))))
          (is (zero? (:used state))) (is (= 1000 (:reserved state)))
          (is (true? (:budget-poisoned? state)))
          (is (true? (identical? (:world entry) (:checkpoint (ex-data unknown))))))))
    :configure configure))

(deftest fallible-post-release-work-retains-the-actual-released-checkpoint
  (fixture/with-empty-publication :reference
    (fn [{:keys [context] :as f}]
      (let [entry (resident/snapshot context) original @#'clojure.core/swap!
            selected (ex-info "selected failure after header release" {})
            cause (with-redefs [clojure.core/swap!
                               (fn [target operation & args]
                                 ;; Fault only the existing phase transition
                                 ;; AFTER release-classic-header-result! recorded
                                 ;; its actual post-release World/owner status.
                                 (if (and (= operation assoc) (= args [:phase :header-result-released])
                                          (map? @target) (contains? @target :header-result))
                                   (throw selected) (apply original target operation args)))]
                    (failure #(discover f entry (request))))
            state (:classic-header-discovery-state (ex-data cause))
            wrapper (get-in state [:header-result :value])]
        (remember-first-failure! {:post-release cause})
        (is (true? (identical? selected (.getCause ^Throwable cause))))
        (is (= :released (get-in state [:header-result :status])))
        (is (false? (contains? (get-in state [:world :heap]) (:id wrapper))))
        (is (true? (identical? (:world state) (:checkpoint (ex-data cause)))))
        (is (true? (identical? (:session state) (:checkpoint-session (ex-data cause)))))))
    :configure configure))
