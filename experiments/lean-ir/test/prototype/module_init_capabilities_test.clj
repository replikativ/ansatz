(ns prototype.module-init-capabilities-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.module-init-capabilities :as capability]
            [prototype.raw-interop :as raw] [prototype.machine :as m]))
(def a ["str" ["anonymous"] "A"])
(def b ["str" ["anonymous"] "B"])
(def run-name ["str" ["anonymous"] "runModInitCore"])
(defn producer [name split imports]
  {:schema "lean-init-plan/1" :module name :moduleSystem split :imports imports :actions []})
(def plans {a (producer a true [{:module b :meta true}]) b (producer b true [])})
(def options
  {:module-plans plans
   :initialized-symbols {"initialize_A" {:module a :phase :all}
                         "runtime_initialize_A" {:module a :phase :runtime}
                         "meta_initialize_A" {:module a :phase :comptime}}})
(def all-guards (set (for [name [a b] phase [:all :runtime :comptime]] [name phase])))
(defn program [bindings]
  (into {} [(raw/lower bindings
    {:name run-name
     :ir {:extern {:f run-name
                   :xs [{:x {:idx 1} :ty "object" :borrow true}
                        {:x {:idx 2} :ty "void" :borrow false}]
                   :type "object"
                   :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"]
                                               :fn "lean_run_mod_init_core"}}]}}}})]))
(defn invoke [backend bindings guards symbol]
  (let [functions (program bindings)
        world (assoc (m/world functions) :initialized-modules guards)
        result (raw/call (raw/open-functions functions bindings {:backend backend :fuel 1000})
                        world run-name [symbol m/erased])]
    [world (:state result) (:value result)]))

(deftest trusted-complete-guards-prove-availability-in-each-backend
  (doseq [backend [:reference :mutable :jvm]]
    (let [bindings (capability/make-bindings options)
          [before after value] (invoke backend bindings all-guards "initialize_A")]
      (is (= [1] (:fields (m/node after value)))))
    (let [bindings (capability/make-bindings options)
          [before after value] (invoke backend bindings all-guards "meta_initialize_A")]
      (is (= [1] (:fields (m/node after value)))))
    (let [bindings (capability/make-bindings options)
          [before after value] (invoke backend bindings all-guards "runtime_initialize_A")]
      (is (= [1] (:fields (m/node after value)))))
    (let [bindings (capability/make-bindings options)
          [before after value] (invoke backend bindings all-guards "initialize_A")]
      (is (= all-guards (:initialized-modules after)))
      (is (= (:heap before) (:heap (m/release after value 1)))))))

(deftest unknown-and-incomplete-guards-do-not-suppress-real-guest-fallback
  (doseq [backend [:reference :mutable :jvm]
          [guards symbol] [[#{} "initialize_A"]
                           [#{[a :all]} "initialize_A"]
                           [(disj all-guards [a :comptime]) "initialize_A"]
                           [(disj all-guards [b :runtime]) "meta_initialize_A"]
                           [all-guards "initialize_KernelImportProbe"]
                           [all-guards "initialize_A_guess"]]]
    (let [[_ after value] (invoke backend (capability/make-bindings options) guards symbol)]
      ;; False is native's lookup-unavailable result; InitAttr owns interpretation.
      (is (= [0] (:fields (m/node after value)))))
    (let [[_ after value] (invoke backend (capability/make-bindings options) guards symbol)]
      (is (= guards (:initialized-modules after)))))
  (let [[_ after value] (invoke :reference (capability/make-bindings) #{} "anything")]
    (is (= [0] (:fields (m/node after value))))))

(deftest trusted-inputs-and-exact-borrowed-abi-are-validated
  (is (thrown-with-msg? Exception #"Missing producer"
        (capability/make-bindings (assoc options :module-plans {}))))
  (is (thrown-with-msg? Exception #"Invalid trusted producer"
        (capability/make-bindings (assoc-in options [:module-plans a :schema] "other"))))
  (is (thrown-with-msg? Exception #"Unknown module|Invalid trusted native"
        (capability/make-bindings (assoc-in options [:initialized-symbols "initialize_A" :phase] :bad))))
  (is (thrown-with-msg? Exception #"Classic Lean module"
        (capability/make-bindings (assoc-in options [:module-plans a :moduleSystem] false))))
  (is (= {:params [{:ty "object" :borrow true} {:ty "void" :borrow false}]
          :return-type "object"} capability/signature)))

(def witness
  {:schema "lean-module-initializer-symbols/1" :leanVersion "4.33.1"
   :leanCommit "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
   :nativeEnvironmentTransported false
   :runtimeProfile {:wordBits 64 :target "x86_64-unknown-linux-gnu"}
   :symbols [{:symbol "initialize_A" :module a :phase "all"}
             {:symbol "runtime_initialize_A" :module a :phase "runtime"}
             {:symbol "meta_initialize_A" :module a :phase "comptime"}
             {:symbol "initialize_missing" :module ["str" ["anonymous"] "Missing"] :phase "all"}]})

(deftest native-witness-intersects-only-authenticated-known-plans
  (let [options (capability/options-from-witness plans witness)]
    (is (= 3 (count (:initialized-symbols options))))
    (is (= {:module a :phase :all} (get-in options [:initialized-symbols "initialize_A"])))
    (is (= #{"initialize_A"}
           (set (keys (:initialized-symbols
                        (capability/options-from-witness
                          {a (producer a false [])} witness)))))))
  (doseq [bad [(assoc witness :leanCommit "other")
               (assoc witness :nativeEnvironmentTransported true)
               (assoc-in witness [:runtimeProfile :wordBits] 32)
               (assoc-in witness [:symbols 0 :phase] "invalid")]]
    (is (thrown? Exception (capability/options-from-witness plans bad))))
  (is (thrown-with-msg? Exception #"Conflicting module initializer"
        (capability/options-from-witness plans
          (update witness :symbols conj {:symbol "initialize_A" :module b :phase "all"})))))
