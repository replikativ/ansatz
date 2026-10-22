(ns prototype.project-loader-test
  "Renderer differential data + coordinator PROTOCOL MODELS. Model graph/native
   callbacks issue NO real node/receipt authority; actual integration is separate."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.string :as str]
            [prototype.project-loader :as loader]
            [prototype.project-discovery-test :as files]
            [prototype.classic-header-discovery-test :as header]
            [prototype.source-graph-runtime-test :as fixture]
            [prototype.resident-init-prefix :as graph]
            [prototype.resident-frontend :as resident])
  (:import [ansatz.kernel Name]
           [java.nio.charset StandardCharsets]))

(def limits {:discovery files/limits :header header/limits :max-exports 32
             :max-export-name-bytes 4096 :max-view-bytes 4096 :max-owned-contexts 3 :max-operations 256})
(def child-options {:kernel-policy {:allow-axioms? true :fuel 1000000}
                    :budgets {:outer-fuel 1000 :helper-fuel 1000 :attempt-fuel 20000}})
(def policies {:discovery-budgets {:helper-fuel 1000 :attempt-fuel 16000}
               :publication-budgets {:helper-fuel 1000 :attempt-fuel 16000}
               :import-options child-options :native-options child-options})
(defn thrown [f] (try (f) nil (catch Throwable cause cause)))
(defn exports [modules] (mapv #(hash-map :module (files/wire [%]) :roots [(Name/fromString (str % ".answer"))]) modules))
(defn fresh-equal-name [^Name name]
  ;; Deliberately bypass the source tree's intern table in this test: descriptive
  ;; Name values are not issued capabilities. Covers either loaded Name variant.
  (let [ctor (.getDeclaredConstructor Name (into-array Class [Byte/TYPE Integer/TYPE Name String Long/TYPE]))]
    (.setAccessible ctor true)
    (.newInstance ctor (object-array [(.-tag name) (.-hash name) (.-prefix name) (.-str name) (.-num name)]))))
(defn options [f provider]
  {:configuration (:configuration f) :prefix (:prefix f) :profile (:profile f) :native-readiness (Object.)
   :provider provider :native-modules [(files/wire ["Init"])] :limits limits :policies policies})

(deftest quoted-renderer-matches-pinned-native-observations-and-rejects-truncation
  (let [rows (mapv #(json/read-str % :key-fn keyword) (str/split-lines (slurp "fixtures/project-import-name-renderer.jsonl")))
        expected-text {"keyword" "import «import»\n" "space-unicode" "import «my package».«λ界»\n"
                       "apostrophe" "import «foo'»\n" "numeric-string" "import «123»\n"
                       "inner-open" "import «a«b»\n" "comment-looking" "import «a -- x»\n"}]
    (doseq [row rows :let [label (:case row)] :when (contains? expected-text label)]
      (let [result (#'loader/render! [(get-in row [:imports 2 :module])] files/limits header/limits 4096)]
        (is (= (get expected-text label) (:text result)))
        (is (= (:headerEndByte row) (:byte-count result)))
        (is (= (:byte-count result) (alength (.getBytes ^String (:text result) StandardCharsets/UTF_8))))))
    (doseq [part ["a»b" "a\nb" "a\rb"]]
      (is (some? (thrown #(#'loader/render! [(files/wire [part])] files/limits header/limits 4096)))))
    (let [exact (#'loader/render! [(files/wire ["123"])] files/limits header/limits 15)]
      (is (= 15 (:byte-count exact)))
      (is (some? (thrown #(#'loader/render! [(files/wire ["123"])] files/limits header/limits 14))))))
  (let [poison (proxy [Object] [] (hashCode [] (throw (ex-info "unvalidated tag hashed" {}))))]
    (is (some? (thrown #(#'loader/render! [[poison ["anonymous"] "x"]] files/limits header/limits 4096)))))
  (let [^Name name (#'loader/java-module ["123"])]
    (is (= 1 (int (.-tag name))))
    (is (= "123" (.-str name)))))

(defn protocol-models [events returned]
  (let [prepare (fn [kind context request roots]
                  (swap! events conj {:event :prepare :kind kind :request request :roots roots :context context})
                  {:control (atom {:kind kind :context context :request request :advanced? false})
                   :progress {:phase :assembled}})
        advance (fn [control slice]
                  (is (= 1 (:max-operations slice)))
                  (swap! control assoc :advanced? true)
                  {:progress {:phase :io-completed}})
        finish (fn [control]
                 (when-not (:advanced? @control) (throw (ex-info "model child not advanced" {})))
                 (let [context (resident/fork (:context @control))
                       result {:context context :header {:headerEndByte (alength (.getBytes ^String (get-in @control [:request :text]) StandardCharsets/UTF_8))}}]
                   (swap! returned conj result)
                   (swap! events conj {:event :finish :kind (:kind @control)}) result))
        publish (fn [context request _ _ parents _]
                  (swap! events conj {:event :publish :request request :parents parents :context context})
                  (let [name (:module-name request)
                        module [(.-str ^Name name)]
                        context (resident/fork context)
                        result {:success true :context context :graph-node (graph/->SourceGraphNode)
                                :file (resident/->FileHandle "model-only" {} name)
                                :graph-publication {:module (files/wire module)}}]
                    (swap! returned conj result) result))]
    {#'graph/prepare-source-graph-import (fn [context request _ _ roots _] (prepare :graph context request roots))
     #'graph/advance-source-graph-import! advance #'graph/finish-source-graph-import! finish
     #'graph/prepare-native-init-base (fn [context request _ _ _ _] (prepare :native context request []))
     #'graph/advance-native-init-base! advance #'graph/finish-native-init-base! finish
     #'graph/publish-source-graph-node publish}))
(defn complete! [control]
  (loop []
    (let [result (loader/advance-load! control {:max-operations 1 :wall-ms 100})]
      (if (= :complete (get-in result [:progress :phase])) (loader/finish-load! control) (recur)))))

(deftest ordered-controller-compiles-once-after-parent-base-and-keeps-versions-owned
  (doseq [backend [:reference :mutable :jvm]]
    (let [specs (atom {(files/text "A") {:deps []} (files/text "B") {:deps [["A"]]}})]
      (files/with-files {["A"] (files/text "A") ["B"] (files/text "B")}
        (fn [root provider]
          (fixture/with-empty-publication backend
            (fn [{:keys [context] :as f}]
              (let [project (loader/open-project context (options f provider))
                    events (atom []) returned (atom []) models (protocol-models events returned)
                    prepared (with-redefs-fn models #(loader/prepare-load project {:roots [(files/wire ["B"])] :exports (exports ["A" "B"])}))
                    ;; Compilation consumes captured text even if the provider's
                    ;; file changes between discovery and the first publication.
                    _ (files/write! root ["A"] (files/text "A edited after capture"))
                    result (with-redefs-fn models #(complete! (:control prepared)))
                    version (:project result)]
                (is (= [["A"] ["B"]] (get-in result [:modules :order])))
                (is (= [:publish :prepare :finish :publish :prepare :finish] (mapv :event @events)))
                (is (= [(files/text "A") (files/text "B")]
                       (mapv #(get-in % [:request :text]) (filter #(= :publish (:event %)) @events))))
                (is (= "import «B»\n" (get-in (last (filter #(= :prepare (:event %)) @events)) [:request :text])))
                (is (some? (thrown #(loader/finish-load! (:control prepared)))))
                ;; All operation-owned stage inputs have been retired after
                ;; successful transfer. The separately borrowed version survives.
                (is (every? (fn [entry] (some? (thrown #(resident/snapshot (:context entry)))))
                            (filter #(contains? #{:prepare :publish} (:event %)) @events)))
                (is (map? (resident/snapshot context)))
                (is (= :finished (:phase @(#'loader/load-state! (:control prepared)))))
                (is (= #{:phase :operations} (set (keys @(#'loader/load-state! (:control prepared))))))
                (loader/close-project! project)
                ;; Real Context forks/close, modeled resident call only: this
                ;; proves ownership/delegation, NOT a callable admitted IR unit.
                (let [canonical (Name/fromString "B.answer")
                      reconstructed (fresh-equal-name canonical)
                      _ (is (false? (identical? canonical reconstructed)))
                      _ (is (= canonical reconstructed))
                      fake-call (fn [ctx file name values _]
                                  (is (true? (identical? file (get-in result [:files ["B"]]))))
                                  (is (= canonical name))
                                  {:context (resident/fork ctx) :value (first values)})
                      called (with-redefs [resident/call fake-call]
                               (loader/invoke version (files/wire ["B"]) reconstructed [41] {:arguments [:nat] :result :nat}))]
                  (is (= 41 (:value called)))
                  (loader/close-project! version)
                  (let [again (with-redefs [resident/call fake-call]
                                (loader/invoke (:project called) (files/wire ["B"]) (Name/fromString "B.answer") [42] {:arguments [:nat] :result :nat}))]
                    (is (= 42 (:value again)))
                    (loader/close-project! (:project again)))
                  (loader/close-project! (:project called)))))
            :configure (files/configure specs)))))))

(deftest independent-leaf-resets-in-current-lineage-and-late-header-failure-keeps-returned-context
  (files/with-files {["A"] (files/text "A") ["D"] (files/text "D")}
    (fn [_ provider]
      (fixture/with-empty-publication :reference
        (fn [{:keys [context] :as f}]
          (let [project (loader/open-project context (options f provider))
                events (atom []) returned (atom []) models (protocol-models events returned)
                prepared (with-redefs-fn models #(loader/prepare-load project {:roots [(files/wire ["A"]) (files/wire ["D"])] :exports (exports ["A" "D"])}))
                result (with-redefs-fn models #(complete! (:control prepared)))]
            (is (= [:native :graph] (mapv :kind (filter #(= :prepare (:event %)) @events))))
            (let [published-a (first @returned)
                  native-entry (first (filter #(and (= :prepare (:event %)) (= :native (:kind %))) @events))]
              (is (true? (identical? (:context published-a) (:context native-entry)))))
            (loader/close-project! (:project result))
            (let [events2 (atom []) returned2 (atom []) models2 (protocol-models events2 returned2)
                  finish (get models2 #'graph/finish-source-graph-import!)
                  bad (assoc models2 #'graph/finish-source-graph-import!
                             (fn [control] (update (finish control) :header assoc :headerEndByte 0)))
                  prepared2 (with-redefs-fn bad #(loader/prepare-load project {:roots [(files/wire ["A"])] :exports (exports ["A"])}))
                  cause (with-redefs-fn bad #(thrown (fn [] (complete! (:control prepared2)))))
                  state (:project-load-state (ex-data cause))]
              (is (.contains (.getMessage cause) "not fully consumed"))
              (is (true? (identical? (:context (last @returned2)) (:context state))))
              (is (true? (identical? cause (thrown #(loader/advance-load! (:control prepared2) {:max-operations 1 :wall-ms 1}))))))
            (loader/close-project! project)))
        :configure (files/configure (atom {(files/text "A") {:deps []} (files/text "D") {:deps []}}))))))

(deftest minimum-owned-capacity-is-checked-before-context-forks
  (let [forks (atom 0)
        opts {:configuration {} :prefix nil :profile nil :native-readiness nil
              :provider {} :native-modules [] :limits (assoc limits :max-owned-contexts 2) :policies policies}
        cause (with-redefs [resident/fork (fn [_] (swap! forks inc))]
                (thrown #(loader/open-project nil opts)))]
    (is (some? cause))
    (is (.contains (.getMessage cause) "baseline/current/returned"))
    (is (zero? @forks))))

(deftest synchronous-failure-keeps-private-child-evidence-without-a-continuation
  (files/with-files {["A"] (files/text "A")}
    (fn [_ provider]
      (fixture/with-empty-publication :reference
        (fn [{:keys [context] :as f}]
          (let [project (loader/open-project context (options f provider))
                models (protocol-models (atom []) (atom []))
                advanced (atom nil)
                advance (get models #'graph/advance-source-graph-import!)
                models (assoc models #'graph/advance-source-graph-import!
                              (fn [child slice] (reset! advanced child) (advance child slice)))
                selected (ex-info "selected observer failure after child advance" {})
                cause (with-redefs-fn models
                        #(thrown (fn [] (loader/load-file project
                                          {:module (files/wire ["A"]) :exports (exports ["A"])}
                                          {:max-operations 1 :wall-ms 100
                                           :observe! (fn [p] (when (= :child-finish (:phase p)) (throw selected)))}))))
                token (:project-failure-diagnostic (ex-data cause))
                registry @#'loader/failures
                saved (locking registry (.get ^java.util.WeakHashMap registry token))]
            (is (some? @advanced))
            (is (instance? prototype.project_loader.ProjectFailure token))
            (is (not (instance? prototype.project_loader.ProjectLoad token)))
            (is (nil? (:child (:project-load-state (ex-data cause)))))
            (is (true? (identical? @advanced (:child saved))))
            (is (= :io-completed (get-in saved [:child-progress :phase])))
            (is (nil? (:failure saved)))
            (is (true? (identical? selected (.getCause cause))))
            (loader/close-project! project)))
        :configure (files/configure (atom {(files/text "A") {:deps []}}))))))
