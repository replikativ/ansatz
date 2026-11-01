(ns prototype.nat-tail-execution-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.walk :as walk]
            [prototype.import-ir :as ir]
            [prototype.nat-regions-test :as data]
            [prototype.typed-tail-test :as fixture]
            [prototype.typed-tail-execution-test :as contract]
            [prototype.tail-caller-frames-test :as callers]
            [prototype.typed-tail-execution :as execution]
            [prototype.typed-tail-emit :as emit]
            [prototype.runtime-abi :as abi]
            [prototype.runtime-prim :as runtime]
            [prototype.native-scalar :as native]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.lazy-runtime :as lazy]
            [prototype.block-compile :as block]))

(defn input []
  (let [all (data/nat-program)] (update all :typed select-keys (data/fast-roots all))))

(deftest actual-nat-native-values-every-fuel-and-persistent-siblings
  (let [input (input)
        examples (filterv #(contains? #{"sum" "subtract" "identityNat" "constantNat"} (:label %))
                          (contract/cases input "nat-region-program-values.json"))]
    (contract/check-prefixes input examples)
    (doseq [[label args] [["identityNat" [9]] ["constantNat" [99]] ["subtract" [7 2]] ["sum" [10 0]]]]
      (let [initial (contract/start input label args) actual (contract/execute-plan input label initial 1000)]
        (is (= :specialized (:route actual)))
        (is (= (m/run initial 1000) (:state actual)))))
    (doseq [label ["bounceA" "bounceB"]]
      (is (= :non-intrinsic-call (:reason (data/prepare-program (data/nat-program)
                                           [(fixture/target (:typed (data/nat-program)) label)])))))))

(deftest promotion-after-completed-chunks-restores-real-callers-and-dead-locals
  (let [input (input)]
    ;; First completed iteration adds 3 safely; the second promotes. The current
    ;; speculative chunk also completed equality/subtraction wrappers before add.
    (doseq [depth [0 1 2] peak [nil 7]
            :let [wrapped (callers/wrapped input "sum" depth)
                  initial (cond-> (callers/entry wrapped [3 (- Long/MAX_VALUE 4)])
                            peak (assoc-in [:stats :max-frames] peak))
                  ctx (contract/context wrapped)
                  plan (execution/compile-entry ctx (:body initial))]]
      (doseq [fuel (range 53)]
        (let [mutable (contract/attempt #(u/run! % fuel) (u/thaw initial))
              actual (contract/attempt #((:execute-budget! plan) % fuel)
                                       (execution/bind-context (u/thaw initial) ctx))]
          (is (= (:error mutable) (:error actual)))
          (is (= (:state mutable) (:state actual)))
          (is (= (contract/carrier-shape (:state mutable)) (contract/carrier-shape (:state actual)))))))))

(deftest nat-entry-carriers-decline-before-any-speculative-work
  (let [input (input)]
    (doseq [value [9N (biginteger 9) (native/native-scalar 9) -1 (m/->Ref 0)]
            label ["identityNat" "constantNat"]
            :let [initial (contract/start input label [value])]
            fuel [1 2 10]]
      (let [actual (contract/execute-plan input label initial fuel)
            expected (contract/attempt #(u/run! % fuel) (u/thaw initial))]
        (is (= (when-not (:error expected) :interpreted) (:route actual)))
        (is (= (:error expected) (:error actual)))
        (is (= (:state expected) (:state actual)))
        (is (= (contract/carrier-shape (:state expected)) (contract/carrier-shape (:state actual))))))))

(deftest nat-definition-owner-seals-decline-before-and-after-compilation
  (let [input (input) initial (contract/start input "sum" [3 0])
        vars [#'native/number-value #'native/nat-value #'native/payload
              #'runtime/evaluate (ns-resolve 'prototype.runtime-prim 'numeric)
              (ns-resolve 'prototype.runtime-prim 'nat!) (ns-resolve 'prototype.runtime-prim 'exact!)
              (ns-resolve 'prototype.runtime-prim 'add) (ns-resolve 'prototype.runtime-prim 'negate)
              #'u/retain! #'u/release! #'u/assert-persistent! #'m/ref?]]
    (doseq [precompiled? [false true] v vars]
      (let [ctx (contract/context input) plan (execution/compile-entry ctx (:body initial)) old @v
            _ (when precompiled? (execution/force-compilation! ctx))]
        (with-redefs-fn {v (fn [& args] (apply old args))}
          (fn []
            (let [actual (contract/attempt #((:execute-budget! plan) % 1000)
                                           (execution/bind-context (u/thaw initial) ctx))
                  expected (contract/attempt #(u/run! % 1000) (u/thaw initial))]
              (is (= :interpreted (:route actual)))
              (is (= (:state expected) (:state actual)))
              (is (= (:error expected) (:error actual))))))))
    (doseq [v [#'abi/scalar-operation #'abi/validate-scalar-description! #'abi/describe-scalar]]
      (let [old @v]
        (with-redefs-fn {v (fn [& args] (apply old args))}
          #(is (= :scalar-registry-redefined (:reason (contract/context input)))))))))

(deftest malformed-nat-proof-is-refused-before-emission
  (let [ctx (contract/context (input)) region (:region ctx) names (:names ctx)
        sum (fixture/target (:functions region) "sum")
        identity (fixture/target (:functions region) "identityNat")]
    (doseq [bad [(assoc-in region [:functions sum :representations 7 :proof :condition] :unconditional)
                 (assoc-in region [:functions sum :representations 1 :lane] :long-bits)
                 (assoc-in region [:functions identity :blocks 0 :operation 8] [:proof :reference])]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid represented tail proof"
                           (emit/emit-factory bad names (:literal-tags ctx) {}))))))

(defn terminal-input [operation]
  ;; Canonical producer-shape control derived from the actual subtraction row;
  ;; this changed row is a compiler test, not an additional native export.
  (let [base (input) old-target (fixture/target (:descriptors base) "sub")
        target (fixture/target (:descriptors base) operation)
        source (first (filter #(= "subtract" (last (:name %))) (fixture/read-rows "nat-region-programs.jsonl")))
        name (fixture/name-of (str "terminal-" operation))
        row (-> (walk/postwalk #(if (= old-target %) target %) source)
                (assoc :name name) (assoc-in [:ir :fdecl :f] name)
                (assoc-in [:ir :fdecl :type] (if (= operation "decEq") "uint8" "tobject"))
                (assoc-in [:ir :fdecl :body 2] (if (= operation "decEq") "uint8" "tobject")))
        [typed-name typed] (ir/lower-typed-declaration row)]
    (-> base (assoc :typed {typed-name typed}) (assoc-in [:runtime name] (second (abi/lower row))))))

(deftest terminal-nat-intrinsics-preserve-overflow-prefix-and-wrapper-locals
  (doseq [[operation examples] [["add" [[1 2] [Long/MAX_VALUE 0] [Long/MAX_VALUE 1]]]
                                ["decEq" [[0 0] [1 2] [Long/MAX_VALUE Long/MAX_VALUE]]]]
          :let [input (terminal-input operation) label (str "terminal-" operation)]]
    (contract/check-prefixes input (mapv (fn [args] {:label label :args args
                                                    :result (:result (m/run (contract/start input label args)))}) examples))
    (doseq [args examples :let [initial (contract/start input label args)
                                actual (contract/execute-plan input label initial 1000)]]
      (is (= (if (and (= operation "add") (> (+' (first args) (second args)) Long/MAX_VALUE)) :interpreted :specialized)
             (:route actual)))
      (is (= (m/run initial 1000) (:state actual))))))

(deftest nat-owner-generation-and-routing-changes-invalidate-cached-factory
  (let [input (input) initial (contract/start input "sum" [3 0])
        ctx (contract/context input) plan (execution/compile-entry ctx (:body initial))]
    (execution/force-compilation! ctx)
    (doseq [v [(ns-resolve 'prototype.mutable 'nat-rc-generation)
               (ns-resolve 'prototype.native-scalar 'native-number-generation)
               (ns-resolve 'prototype.runtime-prim 'nat-arithmetic-generation)]]
      (with-redefs-fn {v (Object.)}
        #(let [actual (contract/attempt (fn [machine] ((:execute-budget! plan) machine 1000))
                                        (execution/bind-context (u/thaw initial) ctx))]
           (is (= :interpreted (:route actual)))
           (is (= (m/run initial 1000) (:state actual))))))
    (let [v (ns-resolve 'prototype.runtime-prim 'scalar-operations)]
      (with-redefs-fn {v (assoc @v "lean_nat_add" :nat-sub)}
        #(let [actual (contract/attempt (fn [machine] ((:execute-budget! plan) machine 1000))
                                        (execution/bind-context (u/thaw initial) ctx))
               expected (contract/attempt (fn [machine] (u/run! machine 1000)) (u/thaw initial))]
           (is (= :interpreted (:route actual)))
           (is (= (:state expected) (:state actual))))))))

(deftest promotion-flushes-only-completed-chunks-before-one-funded-replay
  (let [input (input) initial (-> (contract/start input "sum" [3 (- Long/MAX_VALUE 4)])
                                (assoc :heap {0 {:kind :ctor :tag 0 :fields [] :rc 1}} :next-id 1
                                       :globals {:g {:status :ready :value 7}} :events [{:existing true}])
                                (assoc-in [:stats :allocations] 1))
        ctx (contract/context input) plan (execution/compile-entry ctx (:body initial))
        seen (atom []) original u/run!
        actual (with-redefs [u/run! (fn [machine fuel]
                                     (swap! seen conj {:steps (u/steps machine) :fuel fuel
                                                      :locals (:locals (u/freeze machine))})
                                     (original machine fuel))]
                 (contract/attempt #((:execute-budget! plan) % 1000)
                                   (execution/bind-context (u/thaw initial) ctx)))]
    (is (= [{:steps 15 :fuel 985 :locals {1 2 2 (dec Long/MAX_VALUE)}}] @seen))
    (is (= :interpreted (:route actual)))
    (is (= (m/run initial 1000) (:state actual)))
    (is (= (contract/carrier-shape (m/run initial 1000)) (contract/carrier-shape (:state actual))))))

(deftest different-arity-tail-transfer-promotes-from-the-new-current-entry
  (let [nat (data/nat-input) a (fixture/name-of "nat-A") b (fixture/name-of "nat-B")
        p #(assoc (fixture/parameter % "tobject") :borrow true)
        arg fixture/var-arg ret fixture/return-node
        row (fn [name params body] {:name name :ir {:fdecl {:f name :xs params :type "tobject" :info {} :body body}}})
        ra (row a [(p 1) (p 2)]
                ["vdecl" {:idx 3} "tagged" {:lit {:v {:num {:v 1}}}}
                 ["vdecl" {:idx 4} "tobject" {:fap {:c b :ys [(arg 2) (arg 1) (arg 3)]}} (ret 4)]])
        rb (row b [(p 1) (p 2) (p 3)]
                ["vdecl" {:idx 4} "tobject" {:fap {:c (fixture/target (:functions nat) "add") :ys [(arg 1) (arg 2)]}} (ret 4)])
        input {:runtime (into (:functions nat) (map ir/lower-declaration) [ra rb])
               :typed (into {} (map ir/lower-typed-declaration) [ra rb]) :descriptors (:descriptors nat)}]
    ;; Synthetic canonical tail facts, independent of the actual native mutual
    ;; functions that remain unsupported non-tail controls.
    (contract/check-prefixes input [{:label "nat-A" :args [Long/MAX_VALUE 1] :result (inc' Long/MAX_VALUE)}
                                    {:label "nat-A" :args [4 5] :result 9}])
    (let [initial (contract/start input "nat-A" [Long/MAX_VALUE 1]) ctx (contract/context input)
          plan (execution/compile-entry ctx (:body initial)) original u/run! seen (atom [])
          actual (with-redefs [u/run! (fn [machine fuel]
                                       (swap! seen conj {:steps (u/steps machine) :fuel fuel
                                                        :locals (:locals (u/freeze machine))})
                                       (original machine fuel))]
                   (contract/attempt #((:execute-budget! plan) % 100000000000000000000N)
                                      (execution/bind-context (u/thaw initial) ctx)))]
      (is (= [{:steps 2 :fuel 99999999999999999998N :locals {1 1 2 Long/MAX_VALUE 3 1}}] @seen))
      (is (= (m/run initial) (:state actual)))
      (is (= :interpreted (:route actual))))))
