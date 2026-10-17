(ns prototype.compiled-host-interop-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.program-install :as install]
            [prototype.raw-interop :as raw]
            [prototype.runtime-abi :as abi]
            [prototype.interop-codec :as codec]
            [prototype.machine :as m]))

(defn n [part] ["str" ["str" ["anonymous"] "HostInteropProbe"] part])
(def scalar-root (n "roundTrip"))
(def string-root (n "roundTripString"))
(def installer ["str" ["anonymous"] "installAndCallHostInterop"])
(def bundle (delay (slurp "fixtures/runtime-compiled-host-interop.jsonl")))
(def world-param {:ty "void" :borrow false})
(def bindings
  {"ansatz_host_double"
   {:signature {:params [{:ty "uint32" :borrow false}] :return-type "uint32"}
    :handler (fn [_ world [x]] [world (bit-and 0xffffffff (* 2 x))])}
   "ansatz_host_string"
   {:signature {:params [{:ty "object" :borrow false} world-param] :return-type "object"}
    :handler (fn [_ world [text _]]
               (let [text-value (codec/decode world :string text)
                     world (m/release world text 1)]
                 (m/allocate world :ctor 0 [(str "Clojure: " text-value)])))}})
(defn selected-lowerer [bindings]
  (fn [row] (when (contains? bindings (abi/symbol-for (get-in row [:ir :extern])))
              (raw/lower bindings row))))
(def installer-row
  {:kind "decl" :name installer
   :ir {:extern {:f installer :xs [{:x {:idx 1} :ty "void" :borrow false}]
                 :type "object" :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"]
                                                           :fn "install_host_interop"}}]}}}})

(deftest native-compiled-externs-install-with-an-explicit-abi-checked-lowerer
  (let [lowered (atom [])
        lower (selected-lowerer bindings)
        installed (install/install (m/world {}) @bundle
                                   {:lower-extern (fn [row]
                                                    (is (some? (get-in row [:ir :extern])))
                                                    (swap! lowered conj (:name row))
                                                    (lower row))})
        world (:world installed)]
    (is (= #{(n "hostDouble") (n "hostString")} (set @lowered)))
    (is (empty? (:pending-local-initializers installed)))
    (is (= ["uint32"] (:runtime-param-types (meta (get-in world [:functions scalar-root])))))
    (doseq [backend [:reference :mutable :jvm]]
      (let [session (raw/open-functions (:functions world) bindings {:backend backend})
            result (raw/call session world scalar-root [21])
            [input-world input] (m/allocate (:state result) :string 249 [])
            text "λ\u0000🙂"
            input-world (assoc-in input-world [:heap (:id input) :text] text)
            io (raw/call (:session result) input-world string-root [input m/erased])]
        (is (= 42 (:value result)))
        (is (= "Clojure: λ\u0000🙂" (codec/decode (:state io) [:io :string] (:value io))))
        (is (not (contains? (get-in io [:state :heap]) (:id input))))
        (is (empty? (:heap (m/release (:state io) (:value io) 1))))))))

(deftest live-session-installs-and-calls-new-lean-host-externs-without-reopening-by-name
  (doseq [backend [:reference :mutable :jvm]]
    (let [binding {:signature {:params [world-param] :return-type "object"}
                   :handler (fn [{:keys [install-compiled! invoke]} world _]
                              (let [[world installed] (install-compiled! world @bundle {})
                                    _ (is (empty? (:pending-local-initializers installed)))
                                    [world answer] (invoke world scalar-root [21])
                                    [world text] (invoke world string-root ["héllo" m/erased])
                                    _ (is (= "Clojure: héllo" (codec/decode world [:io :string] text)))
                                    world (m/release world text 1)]
                                (m/allocate world :ctor 77 [answer])))}
          all-bindings (assoc bindings "install_host_interop" binding)
          functions {installer (second (raw/lower all-bindings installer-row))}
          session (raw/open-functions functions all-bindings {:backend backend})
          parent (m/world functions)
          result (raw/call session parent installer [m/erased])
          after (:state result)
          again (raw/call (:session result) after scalar-root [2147483649])]
      (is (= [42] (:fields (m/node after (:value result)))))
      (is (= 2 (:value again)))
      (is (= functions (:functions parent)))
      (is (identical? (get functions installer) (get-in after [:functions installer])))
      (is (= (:functions (:session result)) (:functions after)))
      (is (= #{"ansatz_host_double" "ansatz_host_string"}
             (into #{} (keep #(get-in % [:raw-extern :symbol]))
                   (vals (dissoc (:functions after) installer))))))))

(deftest extern-abi-mismatches-never-fall-back-to-a-trap-or-silently-convert
  (doseq [change [#(assoc-in % ["ansatz_host_double" :signature :params 0 :ty] "uint64")
                  #(assoc-in % ["ansatz_host_string" :signature :params 0 :borrow] true)
                  #(assoc-in % ["ansatz_host_double" :signature :return-type] "object")]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"ABI mismatch"
                         (install/install (m/world {}) @bundle
                                          {:research-traps? true :lower-extern (selected-lowerer (change bindings))}))))
  (is (thrown? clojure.lang.ExceptionInfo (install/install (m/world {}) @bundle)))
  (let [result (install/install (m/world {}) @bundle {:research-traps? true
                                                    :lower-extern (constantly nil)})
        world (:world result)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"(unsupported|Unsupported)"
                         (raw/call (raw/open-functions (:functions world) {} {:backend :reference})
                                   world scalar-root [21])))))
