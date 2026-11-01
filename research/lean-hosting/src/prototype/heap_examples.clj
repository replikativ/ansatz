(ns prototype.heap-examples
  (:require [prototype.machine :as m]
            [prototype.import-ir :as ir]))

(def add-function
  {:params [0 1] :body [:let 2 [:prim :add [[:var 0] [:var 1]]] [:return [:var 2]]]})
(def inc-function
  {:params [0] :body [:let 1 [:prim :inc [[:var 0]]] [:return [:var 1]]]})

(defn functions []
  (assoc (merge (ir/load-bundle "fixtures/list-map.jsonl")
                (ir/load-bundle "fixtures/list-fold.jsonl")
                (ir/load-bundle "fixtures/list-reverse.jsonl")
                (ir/load-bundle "fixtures/tree-mirror.jsonl"))
         ::add add-function ::inc inc-function))

(defn entry [functions label]
  (or (first (filter #(and (vector? %) (= label (ir/name-label %))) (keys functions)))
      (m/fail "Missing example entry" {:label label})))

(defn prepare
  ([functions workload xs shared?] (prepare functions workload xs shared? false))
  ([functions workload xs shared? guest-callback?]
   (let [[s input] (m/guest-list (m/world functions) xs)
         s (if shared? (m/retain s input 1) s)
         [s callback] (case workload
                        :map (if guest-callback? (m/expr s [:closure ::inc []])
                                 [s (m/->Builtin :inc)])
                        :fold (m/expr s [:closure ::add []])
                        :reverse [s nil])
         target (entry functions (case workload :map "List.map._redArg"
                                             :fold "List.foldl._redArg"
                                             :reverse "List.reverse._redArg"))
         args (case workload :map [callback input] :fold [callback 0 input] :reverse [input])]
     {:initial (m/start s target args) :input input :shared? shared? :workload workload})))

(defn result-value [state workload]
  (case workload :fold (:result state) (:map :reverse) (m/list-values state (:result state))))

(defn guest-tree [state depth first-value]
  (if (zero? depth)
    (m/allocate state :ctor 0 [first-value])
    (let [[state left] (guest-tree state (dec depth) first-value)
          [state right] (guest-tree state (dec depth) (+ first-value (bit-shift-left 1 (dec depth))))]
      (m/allocate state :ctor 1 [left right]))))

(defn tree-values [state root]
  (loop [pending [root] values []]
    (if (empty? pending) values
      (let [r (peek pending) pending (pop pending) {:keys [tag fields]} (m/node state r)]
        (case tag
          0 (recur pending (conj values (first fields)))
          1 (recur (conj pending (second fields) (first fields)) values)
          (m/fail "Invalid example tree tag" {:tag tag}))))))

(defn prepare-tree [functions depth shared?]
  (let [[s input] (guest-tree (m/world functions) depth 0)
        s (if shared? (m/retain s input 1) s)]
    {:initial (m/start s (entry functions "HeapProbe.mirror") [input])
     :input input :shared? shared? :workload :mirror}))
