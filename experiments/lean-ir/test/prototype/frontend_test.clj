(ns prototype.frontend-test
  "Orchestration/ownership contracts using guest helper stubs and native-exported
   IR fixtures. These tests do not claim the stubs implement Lean's frontend."
  (:require [clojure.test :refer [deftest is]] [clojure.data.json :as json]
            [prototype.frontend :as frontend] [prototype.machine :as m]
            [prototype.raw-interop :as raw] [prototype.runtime-prim :as prim]
            [prototype.eval-const :as eval]))
(def answer ["str" ["anonymous"] "answer"])
(def main-module ["str" ["anonymous"] "Hosted"])
(defn envelope [success]
  {:schema "lean-file-compilation/1" :producer "RuntimeCompileShim.compileImportedFileState"
   :leanCommit (get prim/pinned-build "lean_get_githash")
   :runtimeProfile {:target "x86_64-unknown-linux-gnu" :wordBits 64}
   :fileName "Hosted.lean" :mainModule main-module :moduleSystem false :requestedImports []
   :success success :stage (if success "complete" "commands") :environmentState "after-commands"
   :diagnostics (if success [] [{:severity "error" :data "unknown identifier"}])
   :bundle (when success (slurp "fixtures/runtime-compiled-identity.jsonl"))})
(defn header []
  {:schema "lean-file-header/1" :producer "RuntimeCompileShim.inspectFileHeader"
   :leanCommit (get prim/pinned-build "lean_get_githash")
   :runtimeProfile {:target "x86_64-unknown-linux-gnu" :wordBits 64}
   :fileName "Hosted.lean" :moduleSystem false :requestedImports [] :hasErrors false
   :headerEndByte 8 :diagnostics []})
(defn drop-args [args body] (reduce (fn [body arg] [:dec [:var arg] 1 body]) body (reverse args)))
(defn setup [backend envelope header]
  (let [functions
        {frontend/header-target {:params [1 2 3]
                                 :body (drop-args [1 2] [:let 4 [:ctor 0 [[:imm (json/write-str header)]]]
                                                        [:return [:var 4]]])}
         frontend/compile-target {:params [1 2 3 4 5 6 7]
                                  :body (drop-args [2 3 4 5 6]
                                          [:let 8 [:ctor 0 [[:var 1] [:imm (json/write-str envelope)]]]
                                           [:let 9 [:ctor 0 [[:var 8]]] [:return [:var 9]]]])}}
        [world env] (m/allocate (m/world functions) :ctor 0 [])
        [world module] (m/allocate world :ctor 1 ["Hosted"])
        [world roots] (m/allocate world :array 246 [])
        [world options] (m/allocate world :ctor 0 [])]
    {:session (raw/open-functions functions {} {:backend backend}) :world world
     :arguments {:environment env :text "prelude\ndef answer := 42\n" :file-name "Hosted.lean"
                 :module-name module :roots roots :options options}}))

(deftest borrowed-inputs-and-owned-final-environment-survive-result-cleanup
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [world session arguments]} (setup backend (envelope true) (header))
          session (raw/open-functions (:functions session) (:bindings session)
                    {:backend backend :compile-threshold 64})
          before world
          result (frontend/compile-file-refs session world arguments)
          next (:world result) env (:environment arguments)]
      (is (:success result))
      (is (= 64 (get-in result [:session :compile-threshold])))
      (is (= 0 (:result next)))
      (is (= env (:environment result)))
      (is (= 2 (:rc (m/node next env))))
      (doseq [key [:module-name :roots :options]]
        (is (= 1 (:rc (m/node next (get arguments key))))))
      (is (= 4 (count (:heap next))))
      (is (= {answer ["str" answer "_boxed"]} (:boxed-entrypoints result)))
      (is (some? (:handle result)))
      (is (= [] (:pending-local-initializers result)))
      (is (not (contains? (:functions before) answer)))
      (is (contains? (:functions next) answer))
      (is (= 42 (:value (raw/call (:session result) next ["str" answer "_boxed"] [m/erased 42])))))))

(deftest failed-envelope-preserves-actual-environment-and-never-installs
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [world session arguments]} (setup backend (envelope false) (header))
          result (frontend/compile-file-refs session world arguments)]
      (is (false? (:success result)))
      (is (= 0 (get-in result [:world :result])))
      (is (= (:environment arguments) (:environment result)))
      (is (= 2 (:rc (m/node (:world result) (:environment result)))))
      (is (= [{:severity "error" :data "unknown identifier"}] (:diagnostics result)))
      (is (identical? (:functions world) (get-in result [:world :functions])))
      (is (nil? (:handle result)))
      (is (= {} (:boxed-entrypoints result))))))

(deftest actual-header-envelope-contract-and-owned-wrapper-cleanup
  (let [{:keys [world session]} (setup :reference (envelope false) (header))
        [world text] (m/allocate world :string 249 [])
        world (assoc-in world [:heap (:id text) :text] "prelude\n")
        result (frontend/inspect-file-header session world text "Hosted.lean")]
    (is (= (header) (:header result)))
    (is (= 0 (get-in result [:world :result])))
    (is (= 1 (:rc (m/node (:world result) text))))
    (is (= (count (:heap world)) (count (:heap (:world result)))))))

(deftest producer-profile-validation-and-no-implicit-initialization
  (doseq [change [#(assoc % :leanCommit "wrong") #(assoc-in % [:runtimeProfile :wordBits] 32)
                  #(assoc % :producer "untrusted") #(assoc % :fileName "Other.lean")
                  #(assoc % :success false)]]
    (let [{:keys [world session arguments]} (setup :reference (change (envelope true)) (header))]
      (is (thrown? clojure.lang.ExceptionInfo (frontend/compile-file-refs session world arguments)))))
  (let [{:keys [world session arguments]} (setup :reference (envelope true) (header))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"separate explicit initialization"
          (frontend/compile-file-refs session world arguments {:install-options {:initialize? true}})))
    (is (nil? (:eval-const-authorizations world)))))

(deftest compilation-preserves-units-installed-during-macro-evaluation
  (let [{:keys [world arguments]} (setup :reference (envelope true) (header))
        signature {:params (conj (vec (repeat 6 {:ty "object" :borrow false})) {:ty "void" :borrow false})
                   :return-type "object"}
        bundle (:bundle (envelope true))
        symbol "frontend_compile_fixture"
        binding {:signature signature
                 :handler (fn [context world [environment text filename module roots options _]]
                            (let [installed (eval/install-bundle context world bundle {})
                                  world (reduce #(m/release %1 %2 1) (:world installed) [text filename module roots options])
                                  [world pair] (m/allocate world :ctor 0 [environment (json/write-str (envelope true))])]
                              (m/allocate world :ctor 0 [pair])))}
        functions (assoc (:functions world) frontend/compile-target
                         {:params [1 2 3 4 5 6 7] :raw-extern {:symbol symbol :signature signature}
                          :body [:host symbol (mapv #(vector :var %) (range 1 8)) 8 [:return [:var 8]]]})
        world (assoc world :functions functions)
        session (raw/open-functions functions {symbol binding} {:backend :reference})
        result (frontend/compile-file-refs session world arguments)
        final (:world result)]
    (is (:success result))
    (is (= 1 (count (get-in final [:eval-const-authorizations :units]))))
    (is (= #{answer ["str" answer "_boxed"]}
           (set (keys (get-in final [:eval-const-authorizations :declarations])))))
    (is (= 42 (:value (raw/call (:session result) final ["str" answer "_boxed"] [m/erased 42]))))))

(deftest invalid-result-retains-a-recoverable-owned-wrapper-checkpoint
  (let [{:keys [world session arguments]} (setup :reference (assoc (envelope false) :leanCommit "wrong") (header))
        error (try (frontend/compile-file-refs session world arguments) nil
                   (catch clojure.lang.ExceptionInfo error error))
        {:keys [checkpoint raw-result frontend-result frontend-decoder-ownership]} (ex-data error)]
    (is (some? error))
    (is (nil? raw-result))
    (is (= 0 (:tag (m/node (:checkpoint frontend-result) (:raw-result frontend-result)))))
    (is (nil? (get-in checkpoint [:heap (:id (:raw-result frontend-result))])))
    (is (= :released (:wrapper-state frontend-decoder-ownership)))
    (is (= :owned (:environment-state frontend-decoder-ownership)))
    (is (= 2 (:rc (m/node checkpoint (:environment arguments)))))
    (is (= 1 (:rc (m/node world (:environment arguments)))))))

(deftest command-failure-returns-new-partial-environment-with-one-owner
  (let [{:keys [world session arguments]} (setup :reference (envelope false) (header))
        functions (assoc (:functions world) frontend/compile-target
                    {:params [1 2 3 4 5 6 7]
                     :body (drop-args [1 2 3 4 5 6]
                             [:let 8 [:ctor 0 [[:imm 42]]]
                              [:let 9 [:ctor 0 [[:var 8] [:imm (json/write-str (envelope false))]]]
                               [:let 10 [:ctor 0 [[:var 9]]] [:return [:var 10]]]]])})
        world (assoc world :functions functions)
        result (frontend/compile-file-refs (raw/open-functions functions {} {:backend :reference}) world arguments)
        next (:world result)]
    (is (false? (:success result)))
    (is (not= (:environment arguments) (:environment result)))
    (is (= [42] (:fields (m/node next (:environment result)))))
    (is (= 1 (:rc (m/node next (:environment result)))))
    (is (= 1 (:rc (m/node next (:environment arguments)))))))

(deftest final-installation-preserves-explicit-raw-extern-bindings
  (let [rows (mapv #(json/read-str % :key-fn keyword)
                   (clojure.string/split-lines (slurp "fixtures/runtime-compiled-identity.jsonl")))
        original (last rows) declaration (get-in original [:ir :fdecl])
        signature {:params (mapv #(select-keys % [:ty :borrow]) (:xs declaration)) :return-type (:type declaration)}
        symbol "frontend_host_identity"
        extern (assoc original :ir {:extern (-> declaration (dissoc :body :info)
                                                (assoc :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"] :fn symbol}}]}))})
        bundle (clojure.string/join "\n" (map json/write-str (conj (pop rows) extern)))
        {:keys [world arguments]} (setup :reference (assoc (envelope true) :bundle bundle) (header))
        binding {:signature signature :handler (fn [_ world [_ value]] [(m/retain world value 1) value])}
        session (raw/open-functions (:functions world) {symbol binding} {:backend :reference})
        result (frontend/compile-file-refs session world arguments)
        called (raw/call (:session result) (:world result) ["str" answer "_boxed"] [m/erased 42])]
    (is (:success result))
    (is (= 42 (:value called)))
    (is (= symbol (get-in result [:world :functions answer :raw-extern :symbol])))))

(deftest structured-layer-releases-only-its-generated-name-owners
  (let [{:keys [world session arguments]} (setup :reference (envelope true) (header))
        generated (atom [])
        encode-name (fn [world _ value _]
                      (is (= :structured-module value))
                      (let [[world name] (m/allocate world :ctor 1 ["Hosted"])]
                        (swap! generated conj name) [world name]))
        encode-names (fn [world _ values _]
                       (is (= [:structured-root] values))
                       (let [[world names] (m/allocate world :array 246 [])]
                         (swap! generated conj names) [world names]))
        result (frontend/compile-file session world
                 (assoc arguments :module-name :structured-module :roots [:structured-root])
                 {:encode-name encode-name :encode-names encode-names})]
    (is (:success result))
    (doseq [ref @generated] (is (not (contains? (get-in result [:world :heap]) (:id ref)))))
    (doseq [key [:module-name :roots :options]]
      (is (= 1 (:rc (m/node (:world result) (get arguments key))))))))

(deftest later-witness-failure-preserves-its-checkpoint-and-the-original-io-owner-separately
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [world arguments]} (setup backend (envelope true) (header))
          target ["str" ["anonymous"] "failingWitness"]
          functions (assoc (:functions world) target
                           {:params [] :body [:trap {:symbol "test_witness_failure"} []]})
          world (assoc world :functions functions)
          session (raw/open-functions functions {} {:backend backend})
          ;; Inject a real guest helper failure at the post-compilation installer
          ;; boundary, with the same invocation/ownership path as file witnesses.
          error (with-redefs [eval/install-file-bundle
                             (fn [context world & _] ((:invoke context) world target []))]
                  (try (frontend/compile-file-refs session world arguments) nil
                       (catch clojure.lang.ExceptionInfo e e)))
          {:keys [checkpoint checkpoint-session frontend-result raw-result] :as data} (ex-data error)
          original (:checkpoint frontend-result)
          wrapper (:raw-result frontend-result)]
      (is (some? error))
      (is (nil? raw-result))
      (is (= 0 (:tag (m/node original wrapper))))
      (is (nil? (get-in checkpoint [:heap (:id wrapper)])))
      (is (identical? checkpoint-session (:session data)))
      (is (not= (:status original) (:status checkpoint)))
      (is (= 2 (:rc (m/node checkpoint (:environment arguments)))))
      (is (= 1 (:rc (m/node world (:environment arguments))))))))

(defn independently-completed-compilation
  "Helper MODEL: run the guest helper directly, pause, then explicitly resume.
   No frontend result processing or file-handler retry occurs here."
  [{:keys [session world arguments]}]
  (let [args (mapv arguments [:environment :text :file-name :module-name :roots :options])
        entry (reduce #(m/retain %1 %2 1) world args)
        short (assoc session :fuel 1)
        failure (try (raw/call short entry frontend/compile-target (conj args m/erased)) nil
                     (catch clojure.lang.ExceptionInfo cause cause))
        _ (is (re-find #"budget exhausted" (.getMessage failure)))
        paused (:checkpoint (ex-data failure))]
    (is (= :paused (:status paused)))
    (raw/continue (assoc (:checkpoint-session (ex-data failure)) :fuel 1000000) paused)))

(deftest staged-compilation-finisher-uses-completed-guest-result-and-matches-normal-ownership
  (doseq [backend [:reference :mutable :jvm] success [true false]]
    (let [context (setup backend (envelope success) (header))
          {:keys [session world arguments]} context
          normal (frontend/compile-file-refs session world arguments)
          completed (independently-completed-compilation context)
          result (frontend/finish-compilation-refs completed (select-keys arguments [:file-name :roots]))]
      (is (= (:success normal) (:success result)))
      (is (= (:diagnostics normal) (:diagnostics result)))
      (is (= (:boxed-entrypoints normal) (:boxed-entrypoints result)))
      (is (= (:heap (:world normal)) (:heap (:world result))))
      (is (= (:environment arguments) (:environment result)))
      (is (= 2 (:rc (m/node (:world result) (:environment result)))))
      (is (not (contains? (:heap (:world result)) (:id (:value completed)))))
      (is (= 1 (:rc (m/node world (:environment arguments)))))
      (is (identical? (get-in result [:world :functions]) (get-in result [:session :functions]))))))

(deftest staged-compilation-finisher-rejects-incomplete-or-mismatched-results
  (let [context (setup :reference (envelope false) (header))
        completed (independently-completed-compilation context)
        args (select-keys (:arguments context) [:file-name :roots])]
    (doseq [changed [(assoc-in completed [:state :status] :host-call)
                     (assoc completed :value 0)
                     (update-in completed [:session :functions] with-meta {:different-identity true})]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"completed frontend raw result"
            (frontend/finish-compilation-refs changed args))))
    (is (= 1 (:rc (m/node (:state completed) (:value completed)))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"separate explicit initialization"
          (frontend/finish-compilation-refs completed args {:install-options {:initialize? true}})))))

(deftest staged-compilation-finisher-preserves-owned-error-result
  (let [context (setup :reference (assoc (envelope false) :leanCommit "wrong") (header))
        completed (independently-completed-compilation context)
        error (try (frontend/finish-compilation-refs completed (select-keys (:arguments context) [:file-name :roots])) nil
                   (catch clojure.lang.ExceptionInfo error error))
        data (ex-data error)]
    (is (re-find #"producer/profile" (.getMessage error)))
    (is (identical? (:state completed) (get-in data [:frontend-result :checkpoint])))
    (is (= (:value completed) (get-in data [:frontend-result :raw-result])))
    (is (= 1 (:rc (m/node (get-in data [:frontend-result :checkpoint]) (:value completed)))))
    (is (nil? (:raw-result data)))
    (is (nil? (get-in data [:checkpoint :heap (:id (:value completed))])))
    (is (= 2 (:rc (m/node (:checkpoint data) (get-in context [:arguments :environment])))))
    (is (= 1 (:rc (m/node (:world context) (get-in context [:arguments :environment])))))))

(defn caused-by? [error selected]
  (loop [current error remaining 8]
    (cond (identical? current selected) true
          (or (nil? current) (zero? remaining)) false
          :else (recur (.getCause ^Throwable current) (dec remaining)))))

(deftest installer-owner-checkpoint-survives-a-later-pure-failure
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [world arguments]} (setup backend (envelope true) (header))
          target ["str" ["anonymous"] "ownedWitness"]
          functions (assoc (:functions world) target
                      {:params [] :body [:let 1 [:ctor 0 [[:imm 99]]] [:return [:var 1]]]})
          world (assoc world :functions functions)
          session (raw/open-functions functions {} {:backend backend})
          selected (ex-info "selected failure after owner checkpoint" {})
          observed (atom nil)
          error (with-redefs [eval/install-file-bundle
                             (fn [{:keys [invoke checkpoint!]} world & _]
                               (let [[world value] (invoke world target [])
                                     world (assoc (m/release world value 1) :result 0)]
                                 (reset! observed {:world world :value value})
                                 (checkpoint! world)
                                 (throw selected)))]
                  (try (frontend/compile-file-refs session world arguments) nil
                       (catch clojure.lang.ExceptionInfo e e)))
          data (ex-data error)]
      (is (some? error))
      (is (identical? (:world @observed) (:checkpoint data)))
      (is (nil? (get-in data [:checkpoint :heap (:id (:value @observed))])))
      (is (identical? (:checkpoint-session data) (:session data)))
      (is (identical? (get-in data [:checkpoint :functions]) (get-in data [:session :functions])))
      (is (= 0 (get-in data [:checkpoint :result])))
      (is (caused-by? error selected)))))

(deftest later-helper-failure-outranks-the-last-successful-owner-checkpoint
  (doseq [backend [:reference :mutable :jvm]]
    (let [{:keys [world arguments]} (setup backend (envelope true) (header))
          successful ["str" ["anonymous"] "successfulWitness"]
          failing ["str" ["anonymous"] "laterFailingWitness"]
          functions (assoc (:functions world)
                      successful {:params [] :body [:let 1 [:literal 7] [:return [:var 1]]]}
                      failing {:params [] :body [:trap {:symbol "later_witness_failure"} []]})
          world (assoc world :functions functions)
          session (raw/open-functions functions {} {:backend backend})
          saved (atom nil)
          error (with-redefs [eval/install-file-bundle
                             (fn [{:keys [invoke checkpoint!]} world & _]
                               (let [[world _] (invoke world successful [])]
                                 (reset! saved (checkpoint! (assoc world :result 0)))
                                 (invoke @saved failing [])))]
                  (try (frontend/compile-file-refs session world arguments) nil
                       (catch clojure.lang.ExceptionInfo e e)))
          data (ex-data error)
          child (:frontend-installation-child-failure data)]
      (is (some? error))
      (is (identical? (:checkpoint child) (:checkpoint data)))
      (is (identical? (:checkpoint-session child) (:checkpoint-session data)))
      (is (not (identical? @saved (:checkpoint data))))
      (is (= :running (get-in data [:checkpoint :status])))
      (is (= :done (:status @saved)))
      (is (= 2 (:rc (m/node (:checkpoint data) (:environment arguments)))))
      (is (= 1 (:rc (m/node (get-in data [:frontend-result :checkpoint])
                            (get-in data [:frontend-result :raw-result]))))))))

(deftest installed-candidate-is-separate-from-coherent-session-if-reopening-fails
  (doseq [backend [:reference :mutable :jvm]]
    (let [context (setup backend (envelope true) (header))
          completed (independently-completed-compilation context)
          selected (ex-info "selected session construction failure" {})
          error (with-redefs [raw/open-functions (fn [& _] (throw selected))]
                  (try (frontend/finish-compilation-refs completed
                         (select-keys (:arguments context) [:file-name :roots])) nil
                       (catch clojure.lang.ExceptionInfo e e)))
          data (ex-data error)
          candidate (:frontend-installation-installed-candidate data)]
      (is (some? error))
      (is (contains? (get-in candidate [:world :functions]) answer))
      (is (not (contains? (get-in data [:checkpoint :functions]) answer)))
      (is (identical? (get-in data [:checkpoint :functions]) (get-in data [:session :functions])))
      (is (not (identical? (get-in candidate [:world :functions]) (get-in data [:session :functions]))))
      (is (= 2 (:rc (m/node (:world candidate) (get-in context [:arguments :environment])))))
      (is (= 1 (:rc (m/node (get-in data [:frontend-result :checkpoint]) (:value completed))))))))

(deftest invalid-file-name-is-rejected-before-guest-compilation
  (let [{:keys [session world arguments]} (setup :reference (envelope true) (header))
        calls (atom 0)]
    (with-redefs [raw/call (fn [& _] (swap! calls inc) (throw (Exception. "must not execute")))]
      (is (thrown? clojure.lang.ExceptionInfo
            (frontend/compile-file-refs session world (assoc arguments :file-name [])))))
    (is (zero? @calls))))
