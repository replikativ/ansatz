(ns prototype.eval-const-typed-ir-test
  "Typed transport integration using an independent pinned native witness DAG
   and its native JSON oracle. The tiny IO helper only returns that captured
   object; this does not claim another full hosted frontend execution."
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [prototype.eval-const :as eval]
            [prototype.eval-const-test :as fixtures]
            [prototype.eval-const-resolution-test :as resolution]
            [prototype.ir-value :as typed]
            [prototype.module-data :as data]
            [prototype.import-ir :as ir]
            [prototype.runtime-abi :as abi]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]))

(def native-data
  (delay (data/load-file (m/world {}) "fixtures/ir-witness-native.jsonl"
                        {:sha256 "c5b3902b3ad1446800f57c0fd32726173ff84faab388c46173b0aa34d487f59f"})))
(def expected (delay (json/read-str (slurp "fixtures/ir-witness-native.expected.json") :key-fn keyword :bigdec true)))
(defn catalogue []
  {:manifests (:manifests resolution/fixture)
   :declarations (into {} (map (fn [r] [(:name r) (assoc r :kind "decl" :runtime {:role "ordinary" :initializer nil})]))
                       (:declarations (nth @expected 2)))})
(defn setup [backend {:keys [index io-tag mutate-root change-catalogue format]
                      :or {index 2 io-tag 0 mutate-root identity change-catalogue identity format :typed-ir}}]
  (let [catalogue (catalogue)
        functions (ir/load-closure catalogue [resolution/answer] #(abi/lower-deferred-catalogue catalogue %))
        boxed (:boxedTarget (nth @expected 2))
        functions (ir/load-closure catalogue [boxed] #(abi/lower-deferred-catalogue catalogue %) {:existing-functions functions})
        loaded @native-data world (assoc (:world loaded) :functions functions)
        native-root (nth (:roots loaded) index)
        node (mutate-root (m/node world native-root))
        [world payload] (m/allocate world :ctor (:tag node) (:fields node))
        [world environment] (m/allocate world :ctor 0 [payload])
        helper {:params [1 2 3]
                :body [:let 4 [:project [:var 1] 0]
                       [:inc [:var 4] 1 [:dec [:var 1] 1 [:dec [:var 2] 1
                        [:let 5 [:ctor io-tag [[:var 4]]] [:return [:var 5]]]]]]]}
        functions (assoc functions resolution/witness-helper helper
                                   fixtures/exporter {:params [1 2 3] :body [:unreachable]}
                                   fixtures/apply-answer {:params [1 2] :body [:tail [:closure [:var 1]] [[:imm 0] [:var 2]]]})
        binding (eval/make-binding fixtures/exporter
                  {:witness resolution/witness-helper :witness-format format
                   :trusted-functions functions :catalogue (change-catalogue catalogue)})
        params (get-in binding [:signature :params])
        row {:kind "decl" :name fixtures/root
             :ir {:extern {:f fixtures/root :xs (mapv (fn [i p] (assoc p :x {:idx i})) (range 1 5) params)
                           :type "object" :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"] :fn "lean_eval_const"}}]}}}}
        functions (assoc functions fixtures/root (second (raw/lower {"lean_eval_const" binding} row)))
        name (nth (:fields node) 5)
        world (assoc world :functions functions)]
    {:world world :session (raw/open-functions functions {"lean_eval_const" binding} {:backend backend})
     :environment environment :name name :payload payload :native-root native-root}))

(deftest independent-native-typed-witness-resolves-and-preserves-actual-code-and-owners
  (doseq [backend [:reference :mutable :jvm]]
    (let [context (setup backend {})
          result (resolution/evaluate context)
          [world closure] (resolution/unwrap result)
          called (raw/call (:session result) world fixtures/apply-answer [closure 42])]
      (is (= 42 (:value called)))
      (is (= (nth @expected 2) (typed/project-witness (:state called) (:payload context))))
      (is (= 1 (:rc (m/node (:state called) (:payload context)))))
      (is (= 1 (:rc (m/node (:state called) (:environment context)))))
      (is (zero? (:rc (m/node (:state called) (:name context)))))
      (doseq [[name function] (get-in context [:world :functions])]
        (is (identical? function (get-in called [:state :functions name]))))
      (is (empty? (:eval-const-authorizations (:state called))))
      (is (= 1 (:rc (m/node (:world context) (:payload context))))))))

(deftest typed-witness-rejections-preserve-exact-io-owner-without-format-fallback
  (doseq [backend [:reference :mutable :jvm]
          options [{:index 1}
                   {:mutate-root #(assoc-in % [:fields 2] "wrong-commit")}
                   {:mutate-root #(assoc-in % [:fields 3] 32)}
                   {:io-tag 7}
                   {:change-catalogue #(assoc-in % [:declarations resolution/answer :ir :fdecl :body] ["unreachable"])}
                   {:format :guest-json}]]
    (let [context (setup backend options)
          error (try (resolution/evaluate context) nil (catch clojure.lang.ExceptionInfo e e))
          {:keys [checkpoint checkpoint-session witness-io-result]} (ex-data error)]
      (is (some? error))
      (is (identical? (:functions checkpoint) (:functions checkpoint-session)))
      (if witness-io-result
        (let [node (m/node checkpoint witness-io-result)]
          (is (= [(:payload context)] (:fields node)))
          (is (= 1 (:rc node)))
          (is (= 1 (:rc (m/node (m/release checkpoint witness-io-result 1) (:payload context))))))
        ;; Authority mismatch follows successful transport. The raw driver may
        ;; retain its earlier immutable host checkpoint; the original fork's
        ;; owners remain intact regardless of that diagnostic snapshot.
        (is (= 1 (:rc (m/node (:world context) (:payload context)))))))))

(deftest typed-io-error-keeps-wrapper-and-borrowed-error-distinct
  (doseq [backend [:reference :mutable :jvm]]
    (let [context (setup backend {:io-tag 1})
          error (try (resolution/evaluate context) nil (catch clojure.lang.ExceptionInfo e e))
          {:keys [checkpoint witness-io-result guest-error type]} (ex-data error)]
      (is (= :guest-error type))
      (is (= (:payload context) guest-error))
      (is (= [guest-error] (:fields (m/node checkpoint witness-io-result))))
      (is (= 2 (:rc (m/node checkpoint guest-error))))
      (is (= 1 (:rc (m/node (m/release checkpoint witness-io-result 1) guest-error)))))))
