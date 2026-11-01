(ns prototype.runtime-mvars-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.string :as str]
            [prototype.runtime-mvars :as runtime]
            [prototype.runtime-abi :as abi]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]
            [prototype.scalar :as scalar]))

(def root ["str" ["str" ["anonymous"] "Lean"] "instantiateLevelMVarsImp"])
(defn- parameter [i ty] {:x {:idx i} :ty ty :borrow false})
(defn- extern-row [name symbol arity]
  {:kind "decl" :name name :ir {:extern {:f name :xs (into [(parameter 1 "object")]
                                                                        (map #(parameter % "tobject") (range 2 (inc arity))))
                                        :type (if (= name runtime/getter) "tobject" "object")
                                        :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"] :fn symbol}}]}}}})
(defn- name-text [world name] (second (:fields (m/node world name))))
(defn- get-assignment [_ world [context name]]
  ;; A small independent association representation for the guest calls made
  ;; by the native algorithm. Actual runtime calls use the genuine Lean
  ;; PersistentHashMap helpers, never this fixture's host implementation.
  (let [fields (:fields (m/node world context)) text (name-text world name)
        found (first (filter #(= text (name-text world (first %))) (partition 2 fields)))
        world (if found (m/retain world (second found) 1) world)
        world (-> world (m/release context 1) (m/release name 1))]
    (if found (m/allocate world :ctor 1 [(second found)]) [world 0])))
(defn- assign [_ world [context name value]]
  (let [fields (:fields (m/node world context)) text (name-text world name)
        keep (remove #(= text (name-text world (first %))) (partition 2 fields))
        kept (vec (mapcat identity keep))
        world (reduce #(m/retain %1 %2 1) world kept)
        world (m/release world context 1)]
    (m/allocate world :ctor 0 (into kept [name value]))))
(def bindings
  {"test_get_lmvar" {:signature {:params [{:ty "object" :borrow false} {:ty "tobject" :borrow false}]
                                 :return-type "tobject"} :handler get-assignment}
   "test_assign_lmvar" {:signature {:params [{:ty "object" :borrow false} {:ty "tobject" :borrow false}
                                            {:ty "tobject" :borrow false}] :return-type "object"} :handler assign}})
(def functions
  {root (second (abi/lower (extern-row root "lean_instantiate_level_mvars" 2)))
   runtime/getter (second (raw/lower bindings (extern-row runtime/getter "test_get_lmvar" 2)))
   runtime/setter (second (raw/lower bindings (extern-row runtime/setter "test_assign_lmvar" 3)))})
(defn- cached [world tag fields data]
  (let [[world ref] (m/allocate world :ctor tag fields)
        layout {:objects (count fields) :usize 0 :ssize 8}
        bytes (scalar/write-bytes layout {} {:index (count fields) :offset 0 :type "uint64" :region :scalar} data)]
    [(update-in world [:heap (:id ref)] assoc :layout layout :scalar-bytes bytes) ref]))
(defn- make-name [world text] (cached world 1 [0 text] 77))
(declare make-level)
(defn- make-level [world encoded cache]
  (if-let [ref (get @cache encoded)] [(m/retain world ref 1) ref]
    (let [[op & args] (:tree encoded)]
      (if (= op "zero") [world 0]
        (let [[world fields]
              (if (contains? #{"param" "mvar"} op)
                (let [[world name] (make-name world (first args))] [world [name]])
                (reduce (fn [[world values] child]
                          (let [[world ref] (make-level world child cache)] [world (conj values ref)])) [world []] args))
              [world ref] (cached world ({"succ" 1 "max" 2 "imax" 3 "param" 4 "mvar" 5} op)
                                  fields (bigint (:data encoded)))]
          (swap! cache assoc encoded ref) [world ref])))))
(defn- encode-level [world value]
  (if (integer? value) {:tree ["zero"] :data "2221"}
    (let [n (m/node world value) fields (:fields n)
          tree (case (:tag n)
                 1 ["succ" (encode-level world (first fields))]
                 2 ["max" (encode-level world (first fields)) (encode-level world (second fields))]
                 3 ["imax" (encode-level world (first fields)) (encode-level world (second fields))]
                 4 ["param" (name-text world (first fields))]
                 5 ["mvar" (name-text world (first fields))])]
      {:tree tree :data (str (scalar/read-bytes (:layout n) (:scalar-bytes n)
                                             {:index (count fields) :offset 0 :type "uint64" :region :scalar}))})))
(defn- prepare [case]
  (let [cache (atom {})
        [world assignments] (reduce (fn [[world fields] [name value]]
                                      (let [[world n] (make-name world name)
                                            [world v] (make-level world value cache)]
                                        [world (into fields [n v])])) [(m/world functions) []] (:assignments case))
        [world context] (m/allocate world :ctor 0 assignments)
        [world input] (make-level world (:input case) cache)]
    ;; Extra owners emulate an environment retaining both inputs and make
    ;; pointer-identity/RC/fork checks independent of allocation reuse.
    [(-> world (m/retain context 1) (m/retain input 1)) context input]))

(deftest only-the-exact-owned-abi-may-use-the-guest-call-lowering
  (is (= [runtime/getter runtime/setter] (:runtime-dependencies (get functions root))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"ownership/type signature"
                       (abi/lower (assoc-in (extern-row root "lean_instantiate_level_mvars" 2)
                                            [:ir :extern :xs 1 :borrow] true))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"explicit guest-call lowering"
                       (runtime/evaluate {} {} "lean_instantiate_level_mvars" [0 0]))))

(deftest native-differential-level-instantiation-and-assignment-writeback
  (let [cases (mapv #(json/read-str % :key-fn keyword)
                    (str/split-lines (slurp "fixtures/instantiate-level-mvars-native.jsonl")))]
    (doseq [case cases backend [:reference :mutable :jvm]]
      (let [[parent context input] (prepare case)
            result (raw/call (raw/open-functions functions bindings {:backend backend}) parent root [context input])
            world (:state result) [new-context output] (:fields (m/node world (:value result)))
            assignments (into {} (map (fn [[name value]] [(name-text world name) (encode-level world value)]))
                              (partition 2 (:fields (m/node world new-context))))]
        (is (= (:result case) (encode-level world output)) (str (:label case) " " backend))
        (is (= (into {} (:finalAssignments case)) assignments) (str (:label case) " " backend))
        (is (= (:sameContext case) (= context new-context)) (:label case))
        (is (= (:sameLevel case) (= input output)) (:label case))
        (when (= "shared cache" (:label case))
          (let [[a right] (:fields (m/node world output))
                b (first (:fields (m/node world right)))]
            (is (= a b))
            (is (true? (:sharedResultChildren case)))))
        (is (not-any? :level-mvars-work (vals (:heap world))))
        (is (= (:input case) (encode-level parent input)))
        (let [released (-> world (m/release (:value result) 1) (m/release context 1) (m/release input 1))]
          (is (empty? (:heap released)) (:label case)))))))

(deftest paused-instantiation-can-resume-and-fork-with-no-hidden-traversal-state
  (let [case (->> (str/split-lines (slurp "fixtures/instantiate-level-mvars-native.jsonl"))
                  (map #(json/read-str % :key-fn keyword))
                  (filter #(= "chain writeback" (:label %))) first)]
    (doseq [backend [:reference :mutable :jvm] budget [0 1 2 4 8 16 32]]
      (let [[parent context input] (prepare case)
            session (raw/open-functions functions bindings {:backend backend :fuel budget})
            checkpoint (try (:state (raw/call session parent root [context input]))
                            (catch clojure.lang.ExceptionInfo error (:checkpoint (ex-data error))))
            session (assoc session :fuel 100000)
            a (raw/continue session checkpoint)
            b (raw/continue session checkpoint)
            [ctx output] (:fields (m/node (:state a) (:value a)))]
        (is (map? checkpoint))
        (is (= (:state a) (:state b)) (str backend " budget " budget))
        (is (= (:result case) (encode-level (:state a) output)))
        (is (not-any? :level-mvars-work (vals (get-in a [:state :heap]))))
        (is (empty? (:heap (-> (:state a) (m/release (:value a) 1)
                              (m/release context 1) (m/release input 1)))))))))

(deftest deep-universe-traversal-is-stack-safe
  (let [case (->> (str/split-lines (slurp "fixtures/instantiate-level-mvars-native.jsonl"))
                  (map #(json/read-str % :key-fn keyword))
                  (filter #(= "direct assignment" (:label %))) first)
        [world context leaf] (prepare case)
        ;; Transfer the owned leaf into a 4000-deep input. Its root carries the
        ;; hasMVar bit, so the native fast path cannot bypass this traversal.
        [world input] (reduce (fn [[world child] depth]
                                (cached world 1 [child] (+ 123 4294967296 (* 1099511627776 depth))))
                              [world leaf] (range 1 4001))]
    (doseq [backend [:reference :mutable :jvm]]
      (let [result (raw/call (raw/open-functions functions bindings {:backend backend}) world root [context input])
            after (:state result) [new-context output] (:fields (m/node after (:value result)))
            [terminal depth] (loop [x output depth 0]
                               (if (integer? x) [x depth]
                                 (recur (first (:fields (m/node after x))) (inc depth))))]
        (is (= context new-context))
        (is (= [0 4000] [terminal depth]))
        (is (not-any? :level-mvars-work (vals (:heap after))))
        ;; The saved input owner resides in leaf's 4000 parents and is consumed
        ;; by the call; prepare retains one separate leaf+context owner.
        (is (empty? (:heap (-> after (m/release (:value result) 1)
                              (m/release context 1) (m/release leaf 1)))))))))
