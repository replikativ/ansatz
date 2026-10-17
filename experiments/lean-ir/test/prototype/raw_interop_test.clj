(ns prototype.raw-interop-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]
            [prototype.lazy-runtime :as lazy]
            [prototype.native-scalar :as native])
  (:import [ansatz.kernel Env]))

(def backends [:reference :mutable :jvm])
(def root ["str" ["anonymous"] "raw-root"])
(defn row [symbol params result]
  {:kind "decl" :name root
   :ir {:extern {:f root :xs (mapv (fn [idx p] (assoc p :x {:idx idx})) (range 1 (inc (count params))) params)
                 :type result :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"] :fn symbol}}]}}}})
(def owned {:ty "object" :borrow false})
(def borrowed {:ty "object" :borrow true})
(defn binding-for [params result handler]
  {:signature {:params params :return-type result} :handler handler})
(defn session [backend symbol binding helpers]
  (let [bindings {symbol binding} functions (assoc helpers root (second (raw/lower bindings (row symbol (get-in binding [:signature :params]) (get-in binding [:signature :return-type])))))]
    (raw/open-functions functions bindings {:backend backend})))

(deftest raw-owned-and-borrowed-transfers-are-not-auto-released
  (doseq [backend backends]
    (let [helper ["str" ["anonymous"] "post-check-helper"]
          java-env (Env.)
          binding (binding-for [owned borrowed] "object"
                    (fn [{:keys [invoke checkpoint!]} world [environment declaration]]
                      (let [world (checkpoint! (assoc-in world [:kernel-environments environment] java-env))
                            ;; Helper's constructor consumes both fields. The declaration was
                            ;; borrowed from the caller, so create the helper's owned token.
                            [world result] (invoke (m/retain world declaration 1) helper [environment declaration])]
                        [(assoc-in world [:kernel-environments result] java-env) result])))
          s (session backend "strict-admission" binding
                     {helper {:params [1 2] :body [:let 3 [:ctor 0 [[:var 1] [:var 2]]] [:return [:var 3]]]}})
          [before environment] (m/allocate (m/world (:functions s)) :ctor 99 [])
          [before declaration] (m/allocate before :ctor 98 [])
          result (raw/call s before root [environment declaration]) state (:state result)
          value (:value result)]
      (is (identical? java-env (get-in state [:kernel-environments value])) (str backend))
      (is (= [environment declaration] (:fields (m/node state value))))
      (is (= 1 (:rc (m/node state environment))))
      (is (= 2 (:rc (m/node state declaration))))
      (let [released (m/release state value 1)]
        (is (not (contains? (:heap released) (:id environment))))
        (is (= 1 (:rc (m/node released declaration)))))
      (is (nil? (:kernel-environments before)))
      (is (= 1 (:rc (m/node before declaration)))))))

(deftest handlers-release-owned-arguments-once-and-driver-does-not-repeat-it
  (doseq [backend backends]
    (let [s (session backend "release-owned" (binding-for [owned] "object"
                                             (fn [_ world [value]] [(m/release world value 1) 0])) {})
          [before resource] (m/resource (m/world (:functions s)) "owned-resource")
          result (raw/call s before root [resource])]
      (is (= 0 (:value result)))
      (is (empty? (get-in result [:state :heap])))
      (is (= [[:released "owned-resource"]] (get-in result [:state :events])))
      (is (empty? (:events before))))))

(deftest closure-callback-consumes-its-owner-and-transfers-captures
  (doseq [backend backends]
    (let [helper ["str" ["anonymous"] "capture-return"]
          s (session backend "apply-owned" (binding-for [owned] "object"
                    (fn [{:keys [invoke]} world [closure]] (invoke world closure [0])))
                     {helper {:params [1 2] :body [:return [:var 1]]}})
          [world resource] (m/resource (m/world (:functions s)) "capture")
          [world closure] (m/expr (assoc world :locals {1 resource}) [:closure helper [[:var 1]]])
          result (raw/call s world root [closure]) after (:state result)]
      (is (= resource (:value result)))
      (is (not (contains? (:heap after) (:id closure))))
      (is (= 1 (:rc (m/node after resource))))
      (is (= [[:released "capture"]] (:events (m/release after resource 1))))
      (is (contains? (:heap world) (:id closure))))))

(deftest nested-host-callbacks-use-the-same-world
  (doseq [backend backends]
    (let [nested ["str" ["anonymous"] "nested-extern"]
          bindings {"outer" (binding-for [owned] "object"
                              (fn [{:keys [invoke]} world args]
                                (invoke (assoc-in world [:kernel-environments :outer] :checked) nested args)))
                    "inner" (binding-for [owned] "object"
                              (fn [_ world [value]] [(assoc-in world [:kernel-environments :inner] :checked) value]))}
          outer (second (raw/lower bindings (row "outer" [owned] "object")))
          inner-row (-> (row "inner" [owned] "object") (assoc :name nested) (assoc-in [:ir :extern :f] nested))
          functions {root outer nested (second (raw/lower bindings inner-row))}
          s (raw/open-functions functions bindings {:backend backend})
          before (m/world functions) result (raw/call s before root [42])]
      (is (= 42 (:value result)))
      (is (= {:outer :checked :inner :checked} (get-in result [:state :kernel-environments])))
      (is (nil? (:kernel-environments before))))))

(deftest handler-world-associations-fork-without-global-state
  (doseq [backend backends]
    (let [binding (binding-for [owned] "object"
                    (fn [_ world [value]] [(assoc-in world [:kernel-environments :selected] value) value]))
          s (session backend "world-value" binding {}) parent (m/world (:functions s))
          left (raw/call s parent root [10]) right (raw/call s parent root [20])]
      (is (= 10 (get-in left [:state :kernel-environments :selected])))
      (is (= 20 (get-in right [:state :kernel-environments :selected])))
      (is (nil? (:kernel-environments parent)))
      (is (= 10 (get-in left [:state :kernel-environments :selected]))))))

(deftest raw-callbacks-are-scoped-and-failures-retain-checkpoints
  (doseq [backend backends]
    (let [captured (atom nil)
          binding (binding-for [owned] "object"
                    (fn [{:keys [invoke checkpoint!]} world _]
                      (reset! captured [invoke world])
                      (checkpoint! (assoc-in world [:kernel-environments :survives] :checked))
                      (throw (ex-info "handler failed after checkpoint" {}))))
          s (session backend "fails" binding {}) parent (m/world (:functions s))
          error (try (raw/call s parent root [42]) nil (catch clojure.lang.ExceptionInfo e e))
          [invoke world] @captured]
      (is (= :checked (get-in (ex-data error) [:checkpoint :kernel-environments :survives])))
      (is (= :host-call (get-in (ex-data error) [:checkpoint :status])))
      (is (nil? (:kernel-environments parent)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"synchronous invocation" (invoke world root [42]))))))

(deftest nested-failures-retain-the-child-checkpoint-and-kernel-associations
  (doseq [backend backends]
    (let [helper ["str" ["anonymous"] "unreachable-helper"]
          s (session backend "nested-failure"
                     (binding-for [owned] "object"
                       (fn [{:keys [invoke]} world args]
                         (invoke (assoc-in world [:kernel-environments :before-child] :checked) helper args)))
                     {helper {:params [1] :body [:unreachable]}})
          error (try (raw/call s (m/world (:functions s)) root [42]) nil
                     (catch clojure.lang.ExceptionInfo e e))]
      (is (some? error))
      (is (= :checked (get-in (ex-data error) [:checkpoint :kernel-environments :before-child]))))))

(deftest exact-abi-validation-precedes-host-lowering
  (let [bindings {"raw" (binding-for [borrowed] "object" (fn [_ world args] [world (first args)]))}]
    (doseq [bad [(row "raw" [owned] "object") (row "raw" [borrowed] "tobject")
                 (row "raw" [borrowed borrowed] "object") (row "raw" [{:ty "tobject" :borrow true}] "object")]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"ABI mismatch" (raw/lower bindings bad)))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"explicit parameter ownership"
        (raw/open-functions {} {"raw" (binding-for [{:ty "object"}] "object" (fn [_ world _] [world 0]))}))))

(deftest shared-jvm-code-cache-does-not-capture-host-bindings
  (let [bindings (fn [result] {"selected" (binding-for [owned] "object"
                                           (fn [_ world _] [world result]))})
        left-bindings (bindings 10) right-bindings (bindings 20)
        functions {root (second (raw/lower left-bindings (row "selected" [owned] "object")))}
        cache (lazy/code-cache)
        left (raw/open-functions functions left-bindings {:backend :jvm :cache cache})
        right (raw/open-functions functions right-bindings {:backend :jvm :cache cache})
        parent (m/world functions)]
    (is (= 10 (:value (raw/call left parent root [0]))))
    (is (= 20 (:value (raw/call right parent root [0]))))
    (is (pos? (:cache-hits (lazy/summary (:program right)))))
    (is (= 10 (:value (raw/call left parent root [0]))))))

(deftest instruction-budget-failure-is-explicit-and-inspectable
  (doseq [backend backends]
    (let [s (assoc (session backend "identity" (binding-for [owned] "object"
                            (fn [_ world [value]] [world value])) {}) :fuel 0)
          error (try (raw/call s (m/world (:functions s)) root [42]) nil
                     (catch clojure.lang.ExceptionInfo e e))]
      (is (re-find #"budget" (.getMessage error)))
      (is (= :paused (get-in (ex-data error) [:checkpoint :status]))))))

(deftest compiled-code-installation-preserves-active-continuations-and-forks
  (doseq [backend backends]
    (let [bundle (slurp "fixtures/runtime-compiled-identity.jsonl")
          answer ["str" ["anonymous"] "answer"]
          installer (binding-for [owned] "object"
                      (fn [{:keys [install-compiled! invoke]} world [input]]
                        (let [[world installed] (install-compiled! world bundle {})
                              target (get (:boxed-entrypoints installed) answer)]
                          (is (empty? (:pending-local-initializers installed)))
                          (invoke world target [0 input]))))
          callback ["str" ["anonymous"] "compile-callback"]
          bindings {"compile" installer}
          callback-row (-> (row "compile" [owned] "object") (assoc :name callback)
                           (assoc-in [:ir :extern :f] callback))
          functions {callback (second (raw/lower bindings callback-row))
                     root {:params [1] :body [:call 2 [:direct callback] [[:var 1]]
                                             [:let 3 [:prim :add [[:var 2] [:imm 1]]]
                                              [:return [:var 3]]]]}}
          s (raw/open-functions functions bindings {:backend backend})
          parent (m/world functions)
          left (raw/call s parent root [41])
          right (raw/call s parent root [99])]
      (is (= 42 (:value left)))
      (is (= 100 (:value right)))
      (is (not (contains? (:functions parent) answer)))
      (is (identical? (get functions root) (get-in left [:state :functions root])))
      (is (identical? (get functions callback) (get-in left [:state :functions callback])))
      (is (= 7 (:value (raw/call (:session left) (:state left) answer [0 7]))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"different executable code"
            (raw/call s (:state left) root [0]))))))

(deftest native-immediate-objects-cross-raw-callbacks-with-their-bits-intact
  (doseq [backend backends]
    (let [value (native/native-scalar 4294967295)
          binding (binding-for [borrowed] "object"
                    (fn [_ world [actual]] (is (identical? value actual)) [world actual]))
          s (session backend "native-immediate" binding {})
          result (raw/call s (m/world (:functions s)) root [value])]
      (is (identical? value (:value result))))))

(deftest native-unboxed-scalar-boundaries-provide-typed-host-values
  (doseq [backend backends]
    (let [binding (binding-for [{:ty "uint32" :borrow false}] "uint32"
                    (fn [_ world [value]]
                      (is (integer? value)) (is (= 4294967295 value))
                      [world (native/native-scalar 4294967295)]))
          s (session backend "native-unboxed" binding {})
          result (raw/call s (m/world (:functions s)) root [(native/native-scalar 4294967295)])]
      (is (= 4294967295 (:value result)))
      (is (integer? (:value result))))))

(deftest nested-helper-failure-preserves-original-owned-host-boundaries-without-retry
  (doseq [backend backends]
    (let [middle ["str" ["anonymous"] "middle-host"]
          trap ["str" ["anonymous"] "final-trap"]
          effects (atom [])
          bindings {"outer-failure" (binding-for [borrowed] "object"
                                     (fn [{:keys [invoke]} world [resource]]
                                       (swap! effects conj :outer)
                                       (invoke (m/retain world resource 1) middle [resource])))
                    "inner-failure" (binding-for [owned] "object"
                                     (fn [{:keys [invoke]} world [resource]]
                                       (swap! effects conj :inner)
                                       (invoke (m/release world resource 1) trap [])))}
          middle-row (-> (row "inner-failure" [owned] "object")
                         (assoc :name middle) (assoc-in [:ir :extern :f] middle))
          functions {root (second (raw/lower bindings (row "outer-failure" [borrowed] "object")))
                     middle (second (raw/lower bindings middle-row))
                     trap {:params [] :body [:unreachable]}}
          s (raw/open-functions functions bindings {:backend backend})
          [before resource] (m/resource (m/world functions) "retained-input")
          error (try (raw/call s before root [resource]) nil (catch clojure.lang.ExceptionInfo e e))
          data (ex-data error) outer (:host-boundary-checkpoint data)
          helper-entry (:helper-entry-checkpoint data)]
      (is (some? error))
      (is (= [:outer :inner] @effects))
      (is (= :host-call (:status outer)))
      (is (= "outer-failure" (get-in outer [:host-request :symbol])))
      (is (= [resource] (get-in outer [:host-request :arguments])))
      (is (= 1 (:rc (m/node outer resource))))
      (is (= 2 (:rc (m/node helper-entry resource))))
      (is (= 1 (:rc (m/node before resource))))
      (is (empty? (:events before)))
      (is (= :running (get-in data [:checkpoint :status])))
      (is (= {:target middle :argument-count 1} (:failed-helper data)))
      (is (= [middle trap] (mapv #(get-in % [:helper :target]) (:host-boundaries data))))
      (is (= ["outer-failure" "inner-failure"]
             (mapv #(get-in % [:checkpoint :host-request :symbol]) (:host-boundaries data))))
      (is (identical? s (:host-boundary-session data)))
      (doseq [[world session] [[outer (:host-boundary-session data)]
                              [helper-entry (:helper-entry-session data)]
                              [(:checkpoint data) (:checkpoint-session data)]]]
        (is (identical? (:functions world) (:functions session)))))))

(deftest failed-helper-retains-matching-old-and-extended-program-sessions
  (doseq [backend backends]
    (let [effects (atom 0)
          answer ["str" ["anonymous"] "answer"]
          binding (binding-for [owned] "object"
                    (fn [{:keys [install-compiled! invoke]} world _]
                      (swap! effects inc)
                      (let [[world _] (install-compiled! world (slurp "fixtures/runtime-compiled-identity.jsonl") {})]
                        ;; Actual new helper exists, but this invocation lacks
                        ;; its arguments. Failure occurs before child start.
                        (invoke world answer []))))
          s (session backend "extend-then-fail" binding {})
          before (m/world (:functions s))
          error (try (raw/call s before root [0]) nil (catch clojure.lang.ExceptionInfo e e))
          data (ex-data error) outer (:host-boundary-checkpoint data)
          entry (:helper-entry-checkpoint data) active (:helper-entry-session data)]
      (is (some? error))
      (is (= 1 @effects))
      (is (identical? s (:host-boundary-session data)))
      (is (not (contains? (:functions outer) answer)))
      (is (contains? (:functions entry) answer))
      (is (identical? (:functions entry) (:functions active)))
      (is (identical? (:functions (:checkpoint data)) (:functions (:checkpoint-session data))))
      (is (= (:host-request outer) (:host-request entry)))
      (is (identical? (get (:functions outer) root) (get (:functions entry) root)))
      (is (not (contains? (:functions before) answer))))))

(deftest scoped-backend-switch-preserves-control-fuel-owners-and-old-forks
  (doseq [[from to] [[:mutable :jvm] [:jvm :mutable] [:reference :jvm]]]
    (let [helper ["str" ["anonymous"] "switched-helper"]
          calls (atom 0)
          captured (atom nil)
          binding (binding-for [owned] "object"
                    (fn [{:keys [switch-backend! invoke]} world args]
                      (swap! calls inc)
                      (reset! captured [switch-backend! world])
                      (let [switched (switch-backend! world to)]
                        (is (identical? world switched))
                        (invoke switched helper args))))
          s (assoc (session from "switch" binding
                            {helper {:params [1] :body [:let 2 [:ctor 0 [[:var 1]]] [:return [:var 2]]]}})
                   :fuel 4)
          [before input] (m/resource (m/world (:functions s)) "switched-input")
          result (raw/call s before root [input])
          after (:state result) value (:value result)
          [switch! captured-world] @captured]
      (is (= to (get-in result [:session :backend])))
      (is (= 4 (get-in result [:session :fuel])))
      (is (= 4 (get-in after [:stats :steps])))
      (is (= 1 @calls))
      (is (= [input] (:fields (m/node after value))))
      (is (= 1 (:rc (m/node after input))))
      (is (= [[:released "switched-input"]] (:events (m/release after value 1))))
      (is (= 1 (:rc (m/node before input))))
      (is (empty? (:events before)))
      (doseq [[name f] (:functions s)] (is (identical? f (get-in result [:session :functions name]))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"synchronous invocation"
            (switch! captured-world from)))
      (let [error (try (raw/call (assoc s :fuel 3) before root [input]) nil
                       (catch clojure.lang.ExceptionInfo error error))
            data (ex-data error)]
        (is (re-find #"budget" (.getMessage error)))
        (is (= :paused (get-in data [:checkpoint :status])))
        (is (= 3 (get-in data [:checkpoint :stats :steps])))
        (is (= to (get-in data [:checkpoint-session :backend])))
        (is (= 3 (get-in data [:checkpoint-session :fuel])))
        (is (= 2 @calls))))))

(deftest backend-switch-rejects-invalid-options-and-control-before-adoption
  (doseq [[backend options changed? pattern]
          [[:invalid {} false #"Unknown raw runtime backend"]
           [:jvm {:fuel 100} false #"only :cache"]
           [:jvm {:compile-threshold 0} false #"Invalid raw compilation threshold"]
           [:jvm {:cache nil} false #"cache must be an atom"]
           [:jvm {:cache (atom [])} false #"cache must be an atom"]
           [:jvm {} true #"changed guest control"]]]
    (let [binding (binding-for [owned] "object"
                    (fn [{:keys [switch-backend!]} world [value]]
                      [(switch-backend! (if changed? (assoc world :body [:return [:imm 99]]) world) backend options) value]))
          s (session :mutable "bad-switch" binding {})
          before (m/world (:functions s))
          error (try (raw/call s before root [42]) nil (catch clojure.lang.ExceptionInfo error error))]
      (is (re-find pattern (.getMessage error)))
      (is (identical? s (:checkpoint-session (ex-data error))))
      (is (= :host-call (get-in (ex-data error) [:checkpoint :status])))
      (is (= 1 (get-in (ex-data error) [:checkpoint :stats :steps]))))))

(deftest backend-roundtrip-and-explicit-cache-keep-the-same-compiled-cache
  (let [cache (lazy/code-cache)
        binding (binding-for [owned] "object"
                  (fn [{:keys [switch-backend!]} world [value]]
                    (let [world (switch-backend! world :mutable)
                          world (switch-backend! world :jvm)] [world value])))
        s (session :jvm "roundtrip-switch" binding {})
        s (raw/open-functions (:functions s) (:bindings s) {:backend :jvm :cache cache :fuel 2})
        result (raw/call s (m/world (:functions s)) root [42])]
    (is (= 42 (:value result)))
    (is (= 2 (get-in result [:state :stats :steps])))
    (is (identical? cache (get-in result [:session :cache])))
    (is (identical? cache (get-in result [:session :program :cache])))
    (is (pos? (count @cache))))
  (let [cache (lazy/code-cache)
        binding (binding-for [owned] "object"
                  (fn [{:keys [switch-backend!]} world [value]]
                    [(switch-backend! world :jvm {:cache cache}) value]))
        s (session :mutable "explicit-cache-switch" binding {})
        result (raw/call s (m/world (:functions s)) root [42])]
    (is (= 42 (:value result)))
    (is (identical? cache (get-in result [:session :program :cache])))))

(deftest program-installation-and-trusted-linking-preserve-current-cache
  (doseq [threshold [1 64]]
   (let [cache (lazy/code-cache)
        linked ["str" ["anonymous"] "linkedSeven"]
        catalogue {:manifests [{:kind "manifest" :schema "lean-ir-probe/1" :leanVersion "4.33.1"
                               :runtimeProfile {:target "x86_64-unknown-linux-gnu" :wordBits 64}}]
                   :declarations {linked {:kind "decl" :name linked :runtime {:role "ordinary" :initializer nil}
                                          :ir {:fdecl {:f linked :xs [] :type "object"
                                                       :body ["vdecl" {:idx 1} "object" {:lit {:v {:num {:v 7}}}}
                                                              ["ret" {:var {:id {:idx 1}}}]]}}}}}
        cached-before (atom nil)
        binding (binding-for [owned] "object"
                  (fn [{:keys [install-compiled! link-trusted! invoke]} world [input]]
                    (reset! cached-before @cache)
                    (let [[world installed] (install-compiled! world (slurp "fixtures/runtime-compiled-identity.jsonl") {})
                          [world value] (invoke world (get (:boxed-entrypoints installed) ["str" ["anonymous"] "answer"]) [m/erased input])
                          [world _] (link-trusted! world catalogue [linked] (fn [_ new-functions] (is (contains? new-functions linked))))
                          [world seven] (invoke world linked [])]
                      (is (= 7 seven))
                      [world value])))
        s (session :jvm "extend-cache" binding {})
        s (raw/open-functions (:functions s) (:bindings s) {:backend :jvm :cache cache :compile-threshold threshold})
        [before input] (m/resource (m/world (:functions s)) "extended-input")
        result (raw/call s before root [input])]
    (is (= input (:value result)))
    (is (= threshold (get-in result [:session :compile-threshold])))
    (is (= threshold (get-in result [:session :program :options :compile-threshold])))
    (is (= 1 (:rc (m/node (:state result) input))))
    (is (identical? cache (get-in result [:session :cache])))
    (is (identical? cache (get-in result [:session :program :cache])))
    (doseq [[key block] @cached-before] (is (identical? block (get @cache key))))
    (is (identical? (get-in s [:functions root]) (get-in result [:state :functions root])))
    (is (not (contains? (:functions before) linked)))
    (is (not (contains? (:functions before) ["str" ["anonymous"] "answer"]))))))

(deftest compilation-threshold-is-validated-and-retained-through-backend-roundtrips
  (doseq [backend backends invalid [nil 0 -1 1.5 2147483648N]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid raw compilation threshold"
          (raw/open-functions {} {} {:backend backend :compile-threshold invalid}))))
  (doseq [backend backends]
    (let [cache (lazy/code-cache)
          binding (binding-for [owned] "object"
                    (fn [{:keys [switch-backend!]} world [value]]
                      (let [world (switch-backend! world :mutable)
                            world (switch-backend! world :jvm)] [world value])))
          s (session backend "threshold-switch" binding {})
          s (raw/open-functions (:functions s) (:bindings s)
                               {:backend backend :cache cache :compile-threshold 64 :fuel 2})
          result (raw/call s (m/world (:functions s)) root [42])]
      (is (= 42 (:value result)))
      (is (= 2 (get-in result [:state :stats :steps])))
      (is (= 64 (get-in result [:session :compile-threshold])))
      (is (= 64 (get-in result [:session :program :options :compile-threshold])))
      (is (identical? cache (get-in result [:session :program :cache])))
      (is (empty? @cache))))
  (let [binding (binding-for [owned] "object"
                  (fn [{:keys [switch-backend!]} world [value]]
                    [(switch-backend! world :jvm {:compile-threshold 32}) value]))
        s (session :mutable "threshold-override" binding {})
        result (raw/call s (m/world (:functions s)) root [42])]
    (is (= 32 (get-in result [:session :compile-threshold])))
    (is (= 32 (get-in result [:session :program :options :compile-threshold])))))
