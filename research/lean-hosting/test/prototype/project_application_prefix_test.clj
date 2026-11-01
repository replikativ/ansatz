(ns prototype.project-application-prefix-test
  "Public application registry/adoption/fresh-prefix composition over a small
   verified native Store. Compiler transport and Project storage are MODELS;
   FileHandles, prefix preparation, typed raw callbacks and invocation are real.
   No genuine Lean frontend/Project graph or initializer permission is claimed."
  (:require [clojure.test :refer [deftest is]]
            [clojure.string :as str]
            [prototype.resident-init-prefix-test :as fixture]
            [prototype.resident-init-prefix :as prefix]
            [prototype.resident-frontend :as resident]
            [prototype.frontend-test :as compiler]
            [prototype.hosted-file-test :as hosted]
            [prototype.typed-extern :as typed]
            [prototype.typed-extern-test :as typed-model]
            [prototype.project-loader :as project]
            [prototype.project-loader-test :as project-model]
            [prototype.project-discovery-test :as files])
  (:import [java.util WeakHashMap]))

(def nat-symbol "ansatz_app_prefix_nat")
(def text-symbol "ansatz_app_prefix_text")
(def module (files/wire ["PreludeIdentity"]))
(defn- failure [f] (try (f) nil (catch clojure.lang.ExceptionInfo cause cause)))
(defn- typed-binding [codec type f]
  (typed/binding {:signature {:params [{:ty type :borrow false}] :return-type type}
                  :arguments [{:codec codec :ownership :owned}] :result codec :fn f}))

(defn- with-composition [backend codec bad-abi? f]
  (let [calls (atom {:nat [] :string []}) host-failure (ex-info "Nat13 application host failure" {:fixture-host? true})
        nat (typed-binding :nat "tobject" #(do (swap! calls update :nat conj %)
                                          (if (= 13 %) (throw host-failure) (inc' %))))
        text (typed-binding :string "object" #(do (swap! calls update :string conj %) %))
        app-bindings {nat-symbol nat text-symbol text}
        selected (if (= codec :nat) nat text)
        signature (cond-> (:signature selected) bad-abi? (assoc-in [:params 0 :borrow] true))
        bundle (str/replace (typed-model/extern-bundle signature) typed-model/symbol-name
                            (if (= codec :nat) nat-symbol text-symbol))
        setup compiler/setup
        envelope (assoc (compiler/envelope true) :fileName hosted/file-path
                        :mainModule module :bundle bundle)]
    ;; Fix transport before fixture preparation captures trusted function objects.
    ;; Never replace a protected runtime function in a live candidate Context.
    (with-redefs [compiler/setup (fn [backend _ header] (setup backend envelope header))]
      (fixture/with-fixture backend
        (fn [{:keys [context checked configuration native-bindings source] :as native}]
          (let [owned (atom []) projects (atom []) diagnostics (atom [])
                own! #(do (swap! owned conj %) %)]
            (try
              (let [before (resident/snapshot context)
                    old (fixture/prepare native) _ (own! (:context old))
                    allow-config (assoc configuration :application-extern-symbols (set (keys app-bindings)))
                    admitted (own! (resident/adopt-prepared before allow-config))
                    configured (own! (resident/with-externs admitted app-bindings))
                    ;; Extend ORIGINAL independently constructed objects, never
                    ;; recapture configured's live registry as its own authority.
                    app-config (update allow-config :trusted-bindings merge app-bindings)
                    app-native (merge native-bindings app-bindings)
                    application (own! (resident/adopt-prepared (resident/snapshot configured) app-config))
                    fresh (prefix/prepare-init-prefix application checked
                                                     {:configuration app-config :native-bindings app-native})
                    _ (own! (:context fresh))]
                (f {:native native :original before :old old :fresh fresh :application application
                    :configured configured :allow-config allow-config :configuration app-config
                    :native-bindings app-native :bindings app-bindings :calls calls :source source
                    :host-failure host-failure :own! own!
                    :own-project! #(do (swap! projects conj %) %)
                    :own-diagnostics! #(swap! diagnostics into (:project-owned-contexts (ex-data %)))}))
              (finally
                (doseq [p (reverse @projects)] (project/close-project! p))
                (doseq [ctx (reverse @diagnostics)] (resident/close! ctx))
                (doseq [ctx (reverse @owned)] (resident/close! ctx))))))))))

(defn- stored-project!
  "Model only Project's post-load storage, without graph/prefix authority claims.
   Keep its pristine baseline; the stored file and current Context are real and
   from the same returned resident lineage. No world merge or handle fabrication."
  [{:keys [fresh configuration own! own-project!]} loaded provider]
  (let [p (own-project! (project/open-project (:context fresh)
                                            (assoc (project-model/options {:configuration configuration} provider)
                                                   :prefix (:prefix fresh) :profile (Object.))))
        ^WeakHashMap versions @#'project/versions
        state (locking versions (.get versions p))
        previous (:context @state)
        current (resident/fork (:context loaded))]
    (swap! state assoc :context current :files {["PreludeIdentity"] (:file loaded)}
           :exports {["PreludeIdentity"] [hosted/answer-name]})
    (resident/close! previous)
    p))

(deftest independent-application-registry-fresh-prefix-and-project-callbacks
  (doseq [backend [:reference :mutable :jvm] codec [:nat :string]]
    (with-composition backend codec false
      (fn [{:keys [native original old fresh application configured allow-config configuration
                    native-bindings bindings calls source own! own-project!] :as composition}]
        (let [configured-packet (resident/snapshot configured)
              app-packet (resident/snapshot application)
              old-packet (resident/snapshot (:context old))
              new-packet (resident/snapshot (:context fresh))]
          (is (not (identical? (:prefix old) (:prefix fresh))))
          (is (= (prefix/descriptor (:prefix old)) (prefix/descriptor (:prefix fresh))))
          (is (identical? original (resident/snapshot (:context native))))
          (is (identical? (:functions (:world original)) (:functions (:world app-packet))))
          (is (identical? (get-in original [:session :cache]) (get-in new-packet [:session :cache])))
          (doseq [[symbol b] bindings]
            (is (identical? b (get-in configuration [:trusted-bindings symbol])))
            (is (identical? b (get native-bindings symbol)))
            (is (identical? b (get-in new-packet [:session :bindings symbol]))))
          (doseq [[symbol b] (get-in native [:configuration :trusted-bindings])]
            (is (identical? b (get-in new-packet [:session :bindings symbol]))))
          (is (identical? (get-in native [:native-bindings "lean_run_mod_init_core"])
                          (get-in new-packet [:session :bindings "lean_run_mod_init_core"])))
          (is (= {:nat [] :string []} @calls))
          ;; Old prefix cannot authenticate an extended registry; exact original
          ;; configuration remains mandatory even when the Java checked Env agrees.
          (let [cause (failure #(prefix/release-prefix application (:prefix old)))]
            (is (some? cause))
            (is (re-find #"bindings differ" (.getMessage cause)))
            (is (identical? (:world app-packet) (:checkpoint (ex-data cause)))))
          (is (identical? old-packet (resident/snapshot (:context old))))
          (is (identical? configured-packet (resident/snapshot configured)))
          (files/with-files {["PreludeIdentity"] "-- modeled compiler transport\n"}
            (fn [_ provider]
              (let [loaded (resident/load-source (:context fresh) (hosted/request :run))
                    _ (own! (:context loaded))
                    p (stored-project! composition loaded provider)
                    inputs (if (= codec :nat) [41 1208925819614629174706176N] ["" "λ😀"])]
                (is (:success loaded))
                (is (= [] (:diagnostics loaded)))
                (is (= {:nat [] :string []} @calls))
                (doseq [value inputs]
                  (let [called (project/invoke p module hosted/answer-name [value]
                                               {:arguments [codec] :result codec})
                        child (own-project! (:project called))]
                    (is (= (if (= codec :nat) (inc' value) value) (:value called)))
                    (project/close-project! child)))
                ;; Explicit older version remains callable after child close.
                (let [called (project/invoke p module hosted/answer-name [(first inputs)]
                                             {:arguments [codec] :result codec})]
                  (own-project! (:project called))
                  (is (= (if (= codec :nat) (inc' (first inputs)) (first inputs)) (:value called))))
                (is (= (conj inputs (first inputs)) (get @calls codec)))
                (is (empty? (get @calls (if (= codec :nat) :string :nat)))))))
          (is (identical? old-packet (resident/snapshot (:context old))))
          (is (identical? original (resident/snapshot (:context native))))
          (is (false? @(:closed source))))))))

(deftest registry-mismatch-and-binding-replacement-reject-before-callbacks
  (with-composition :reference :nat false
    (fn [{:keys [native configured application allow-config configuration native-bindings bindings calls own!]}]
      (is (some? (failure #(resident/with-externs (:context native) bindings))))
      (is (some? (failure #(resident/with-externs configured bindings))))
      (is (some? (failure #(prefix/prepare-init-prefix configured (:checked native)
                                                     {:configuration allow-config :native-bindings native-bindings}))))
      (let [b (get bindings nat-symbol) clone (into {} b)]
        (is (= b clone))
        (is (not (identical? b clone)))
        (is (some? (failure #(prefix/prepare-init-prefix application (:checked native)
                                                       {:configuration configuration
                                                        :native-bindings (assoc native-bindings nat-symbol clone)})))))
      (let [reserved (own! (resident/adopt-prepared
                            (resident/snapshot application)
                            (update configuration :application-extern-symbols conj "lean_io_getenv")))
            cause (failure #(resident/with-externs reserved {"lean_io_getenv" (get bindings nat-symbol)}))]
        (is (some? cause))
        (is (re-find #"reserved runtime capability" (.getMessage cause))))
      (is (= {:nat [] :string []} @calls)))))

(deftest emitted-abi-mismatch-fails-installation-before-a-host-call
  (with-composition :reference :nat true
    (fn [{:keys [fresh calls]}]
      (let [cause (failure #(resident/load-source (:context fresh) (hosted/request :run)))]
        (is (some? cause))
        (is (re-find #"ABI mismatch" (.getMessage cause)))
        (is (= {:nat [] :string []} @calls))))))

(deftest project-host-exception-runs-once-and-keeps-matching-diagnostic-owners
  (doseq [backend [:reference :mutable :jvm]]
    (with-composition backend :nat false
      (fn [{:keys [fresh calls host-failure own! own-diagnostics!] :as composition}]
        (files/with-files {["PreludeIdentity"] "-- modeled compiler transport\n"}
          (fn [_ provider]
            (let [loaded (resident/load-source (:context fresh) (hosted/request :run))
                  _ (own! (:context loaded)) p (stored-project! composition loaded provider)
                  cause (failure #(project/invoke p module hosted/answer-name [13]
                                                   {:arguments [:nat] :result :nat}))
                  _ (own-diagnostics! cause) data (ex-data cause)
                  causes (take-while some? (iterate #(some-> ^Throwable % .getCause) cause))]
              (is (some #(identical? host-failure %) causes))
              (is (= :invoke (:project-operation data)))
              (is (:typed-extern-terminal? data))
              (is (= :host-call (:typed-extern-phase data)))
              (is (= :owned (get-in data [:typed-extern-input-owners 0 :state])))
              (is (identical? (:checkpoint data) (:typed-extern-checkpoint data)))
              (is (identical? (get-in data [:checkpoint :functions]) (get-in data [:checkpoint-session :functions])))
              (is (= 2 (count (:project-owned-contexts data))))
              (is (every? #(map? (resident/snapshot %)) (:project-owned-contexts data)))
              (is (= {:nat [13] :string []} @calls)))))))))
