(ns ansatz.lean-test
  "Facade orchestration MODELS only. Resident operations are substituted locally;
   these tests cannot establish strict/frontend/real-codec acceptance."
  (:require [clojure.test :refer [deftest is run-tests]]
            [ansatz.lean :as lean]
            [prototype.resident-preparation :as preparation]
            [prototype.resident-frontend :as resident]
            [prototype.machine :as machine]
            [prototype.interop-codec :as codec])
  (:import [ansatz.kernel Name]
           [ansatz.lean LeanRuntime LeanRuntime$PreparedInput LeanRuntime$PreparedProvider
            LeanRuntime$OpenOptions LeanRuntime$SourceRequest LeanRuntime$Initialization
            LeanRuntime$CallSignature LeanRuntime$HostFunction LeanRuntime$ExternArgument LeanRuntime$ExternSpec]
           [java.math BigInteger]
           [java.nio.file Files]
           [java.nio.charset StandardCharsets]))

(defn failure [f] (try (f) nil (catch clojure.lang.ExceptionInfo cause cause)))
(defn packet [lease] {:candidate {:owned :environment} :configuration {:independent :registries} :source-lease lease})
(def request {:module "Test" :roots ["answer"] :initialization :defer :file-name "Test.lean"})

(deftest names-preserve-string-numeric-and-escaped-segments
  (let [dotted (lean/name "A.42") structured (lean/name ["A.B" 42])]
    (is (.isStr dotted)) (is (= "42" (.-str dotted)))
    (is (.isNum structured)) (is (= 42 (.-num structured)))
    (is (= "A.B" (.-str (.-prefix structured))))
    (is (identical? Name/ANONYMOUS_NAME (lean/name [])))
    (doseq [bad [nil "" "A..B" [-1] [9223372036854775808N] [true]]]
      (is (= :invalid-request (:lean/code (ex-data (failure #(lean/name bad)))))))))

(deftest checked-provider-and-borrowed-lease-survive-descendants-and-failures
  (let [closes (atom []) lease-closes (atom 0)
        lease (reify java.io.Closeable (close [_] (swap! lease-closes inc)))
        input (packet lease) seen (atom nil)]
    (with-redefs [preparation/open-checked (fn [candidate configuration]
                                           (reset! seen [candidate configuration]) :root)
                  resident/fork (fn [r] [:fork r])
                  resident/close! #(swap! closes conj %)]
      (let [root (lean/open {:provider (fn [_] input)}) child (lean/fork root)]
        (is (= [(:candidate input) (:configuration input)] @seen))
        (lean/close! root) (lean/close! root)
        (is (= :closed-context (:lean/code (ex-data (failure #(lean/fork root))))))
        (with-open [grandchild (lean/fork child)] (is grandchild))
        (lean/close! child)
        (is (= [:root [:fork [:fork :root]] [:fork :root]] @closes))
        (is (zero? @lease-closes))))
    (let [original (ex-info "adoption failed" {:checkpoint {:exact :world} :checkpoint-session :session})
          error (with-redefs [preparation/open-checked (fn [& _] (throw original))]
                  (failure #(lean/open {:provider (fn [_] input)})))
          evidence (:lean/failure (ex-data error))]
      (is (identical? original (.getCause error)))
      (is (identical? original (lean/failure-cause evidence)))
      (is (= "#<Failure>" (pr-str evidence)))
      (is (not (contains? (ex-data error) :checkpoint)))
      (is (zero? @lease-closes)))))

(deftest source-is-captured-once-and-diagnostics-return-the-partial-context
  (let [path (Files/createTempFile "ansatz-lean-capture" ".lean" (make-array java.nio.file.attribute.FileAttribute 0))
        text "def answer : String := \"éλ\u0000😀\"\n" seen (atom nil)]
    (try
      (Files/write path (.getBytes text StandardCharsets/UTF_8) (make-array java.nio.file.OpenOption 0))
      (with-redefs [preparation/open-checked (fn [& _] :root)
                    resident/close! (fn [_])
                    resident/load-source (fn [r source]
                                           (Files/write path (.getBytes "changed" StandardCharsets/UTF_8) (make-array java.nio.file.OpenOption 0))
                                           (reset! seen [r source])
                                           {:context :partial :success false :diagnostics [{:severity "error" :message "modeled"}]})]
        (with-open [root (lean/open {:provider (fn [_] (packet (Object.)))})]
          (let [loaded (lean/load-file root path request)]
            (is (false? (:success? loaded))) (is (nil? (:file loaded)))
            (is (= text (get-in loaded [:source :text])))
            (is (= text (get-in @seen [1 :text])))
            (is (not (contains? (second @seen) :path)))
            (is (= 64 (count (get-in loaded [:source :sha256]))))
            (is (= (lean/name "Test") (get-in loaded [:source :module])))
            (is (= [{:severity "error" :message "modeled"}] (:diagnostics loaded)))
            (lean/close! (:context loaded)))))
      (finally (Files/deleteIfExists path)))))

(deftest operations-forward-generic-codecs-and-retain-exact-failure-without-retry
  (let [signature {:arguments [[:option :bytes] :unit :uint64] :result [:option :bytes]}
        calls (atom []) original (ex-info "host throw" {:typed-extern-phase :host-call :typed-extern-terminal? true})]
    (with-redefs [preparation/open-checked (fn [& _] :root)
                  resident/close! (fn [_])
                  resident/load-source (fn [_ _] {:context :loaded :file :admitted :success true :diagnostics []})
                  resident/call (fn [r file target values codecs]
                                  (swap! calls conj [r file target values codecs])
                                  (if (= values [:throw]) (throw original) {:context :called :value {:some [0 255]}}))]
      (with-open [root (lean/open {:provider (fn [_] (packet (Object.)))})]
        (let [loaded (lean/load-string root "captured" request)
              called (lean/call (:context loaded) (:file loaded) "answer" [{:some [0]} nil 2N] signature)
              error (failure #(lean/call (:context loaded) (:file loaded) "answer" [:throw] signature))]
          (is (= {:some [0 255]} (:value called)))
          (is (identical? signature (last (first @calls))))
          (is (identical? original (lean/failure-cause (:lean/failure (ex-data error)))))
          (is (= 2 (count @calls)))
          (lean/close! (:context loaded)) (lean/close! (:context called)))))))

(deftest invalid-source-policies-and-extern-profiles-reject
  (with-redefs [preparation/open-checked (fn [& _] :root)
                resident/close! (fn [_])
                resident/load-source (fn [& _] (throw (AssertionError. "must reject before guest")))]
    (with-open [root (lean/open {:provider (fn [_] (packet (Object.)))})]
      (doseq [options [(dissoc request :initialization) (assoc request :initialization :automatic)
                       (assoc request :roots nil) (assoc request :calls [])]]
        (is (failure #(lean/load-string root "text" options))))
      (is (failure #(lean/load-string root (str (char 0xD800)) request)))))
  (doseq [result [:bytes :unit [:option :nat]]]
    (is (failure #(lean/extern {:symbol "application" :signature {:params [] :return-type "object"}
                               :arguments [] :result result :fn (fn [] 0)}))))
  (is (contains? (lean/extern {:symbol "application" :signature {:params [{:ty "object" :borrow true}] :return-type "object"}
                              :arguments [{:codec :nat :ownership :borrowed}] :result :nat :fn identity}) "application")))

(deftest java-wrapper-model-preserves-null-values-big-nats-and-sam-lists
  (let [large (.add (.shiftLeft BigInteger/ONE 90) (BigInteger/valueOf 42))
        java-options (LeanRuntime$OpenOptions. {})
        provider (reify LeanRuntime$PreparedProvider
                   (prepare [_ options]
                     (is (identical? java-options options))
                     (LeanRuntime$PreparedInput. {:owned :environment} {:independent :registry} (Object.))))
        request (LeanRuntime$SourceRequest. (lean/name "JavaModel") [(lean/name "answer")]
                                            LeanRuntime$Initialization/DEFER "JavaModel.lean")
        callback-values (atom nil) throws? (atom false)
        callback (reify LeanRuntime$HostFunction
                   (apply [_ values]
                     (reset! callback-values values)
                     (is (instance? BigInteger (first values)))
                     (is (thrown? UnsupportedOperationException (.add ^java.util.List values 7)))
                     (when @throws? (throw (Exception. "SAM failure")))
                     (first values)))
        extern (LeanRuntime$ExternSpec. "application"
                 [(LeanRuntime$ExternArgument. "object" false "nat")] "object" "nat" callback)
        captured-binding (atom nil)]
    (with-redefs [preparation/open-checked (fn [& _] :root)
                  resident/close! (fn [_])
                  resident/load-source (fn [& _] {:context :loaded :file :admitted :success true :diagnostics []})
                  resident/with-externs (fn [_ bindings] (reset! captured-binding (get bindings "application")) :externs)
                  resident/call (fn [_ _ _ values signature]
                                  (is (= [nil large] values))
                                  (is (= {:arguments [:unit :nat] :result :nat} signature))
                                  {:context :called :value (bigint large)})]
      (with-open [root (LeanRuntime/open provider java-options)]
        (let [loaded (.loadString root "captured" request)]
          (with-open [compiled (.context loaded)]
            (let [called (.call compiled (.file loaded) "answer" [nil large]
                                (LeanRuntime$CallSignature. ["unit" "nat"] "nat"))]
              (with-open [after-call (.context called)]
                (is (instance? BigInteger (.value called))) (is (= large (.value called)))))
            (with-open [bound (.withExterns compiled [extern])]
              (let [{:keys [signature handler]} @captured-binding
                    context {:signature signature :checkpoint! identity}
                    [world value] (handler context (machine/world {}) [large])]
                (is (= large value)) (is (= [large] @callback-values))
                (reset! throws? true)
                (let [error (failure #(handler context world [large]))]
                  (is (= :host-call (:typed-extern-phase (ex-data error))))
                  (is (:typed-extern-terminal? (ex-data error))))))))))))

(deftest java-generic-byte-and-option-model-uses-existing-codec-validation
  (let [provider (reify LeanRuntime$PreparedProvider
                   (prepare [_ _] (LeanRuntime$PreparedInput. {} {} (Object.))))
        request (LeanRuntime$SourceRequest. (lean/name "GenericModel") [(lean/name "answer")]
                                            LeanRuntime$Initialization/DEFER "GenericModel.lean")]
    (with-redefs [preparation/open-checked (fn [& _] :root)
                  resident/close! (fn [_])
                  resident/load-source (fn [& _] {:context :loaded :file :admitted :success true :diagnostics []})
                  resident/call (fn [_ _ _ [value] {:keys [arguments result]}]
                                  (let [[world encoded] (codec/encode-boxed (machine/world {}) (first arguments) value)]
                                    {:context :called :value (codec/decode-boxed world result encoded)}))]
      (with-open [root (LeanRuntime/open provider (LeanRuntime$OpenOptions. {}))]
        (let [loaded (.loadString root "captured" request)]
          (with-open [compiled (.context loaded)]
            (doseq [[descriptor value expected]
                    [["bytes" (java.util.Arrays/asList (object-array [0 128 255])) [0 128 255]]
                     [["option" "bytes"] (java.util.Collections/singletonMap "some" [0 255])
                      (java.util.Collections/singletonMap "some" [0 255])]
                     [["option" "unit"] (java.util.Collections/singletonMap "some" nil)
                      (java.util.Collections/singletonMap "some" nil)]
                     [["option" "unit"] nil nil]]]
              (let [called (.call compiled (.file loaded) "answer" [value]
                                  (LeanRuntime$CallSignature. [descriptor] descriptor))]
                (with-open [after-call (.context called)] (is (= expected (.value called))))))
            (is (thrown? ansatz.lean.LeanRuntime$LeanException
                         (.call compiled (.file loaded) "answer" [[-1 0]]
                                (LeanRuntime$CallSignature. ["bytes"] "bytes"))))))))))

(defn -main [& _]
  (let [{:keys [fail error]} (run-tests 'ansatz.lean-test)]
    (when (pos? (+ fail error)) (System/exit 1))))
