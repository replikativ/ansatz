(ns prototype.examples
  (:require [prototype.machine :as m]
            [prototype.import-ir :as ir]))

(defn tail-function [other]
  {:params [0]
   :body [:let 1 [:prim :zero? [[:var 0]]]
          [:case [:var 1]
           [[1 [:return [:var 0]]]
            [0 [:let 2 [:prim :dec [[:var 0]]]
                [:tail [:direct other] [[:var 2]]]]]]]]})

(defn tail-demo [n]
  (m/run (m/start (m/world {:even (tail-function :odd) :odd (tail-function :even)}) :even [n])))

(defn list-demo [shared?]
  (let [fns (ir/load-bundle "fixtures/list-map.jsonl")
        target (first (for [k (keys fns) :when (= "List.map._redArg" (ir/name-label k))] k))
        [s root] (m/guest-list (m/world fns) [1 2 3 4])
        s (if shared? (m/retain s root 1) s)
        result (m/run (m/start s target [(m/->Builtin :inc) root]))]
    {:state result :initial s :target target :input root :output (:result result)
     :values (m/list-values result (:result result))
     :original (when shared? (m/list-values result root))}))

(defn fork-demo []
  (let [s (m/world {:fork {:params [0]
                         :body [:suspend 1 [:dec [:var 0] 1 [:return [:var 1]]]]}})
        [s r] (m/resource s :test-resource)
        captured (m/run (m/start s :fork [r]))]
    {:captured captured
     :left (m/run (m/resume captured 10))
     :right (m/run (m/resume captured 20))}))

(defn export-portable! []
  (let [fns (ir/load-bundle "fixtures/list-map.jsonl")
        target (first (filter #(= "List.map._redArg" (ir/name-label %)) (keys fns)))]
    (spit "fixtures/list-map.edn" (pr-str fns))
    (spit "fixtures/entry.edn" (pr-str {:entry target}))
    (spit "fixtures/tail.edn" (pr-str {:even (tail-function :odd) :odd (tail-function :even)}))
    :exported))

(defn summary []
  (let [tail (tail-demo 100000) unique (list-demo false) shared (list-demo true)
        {:keys [captured left right]} (fork-demo)]
    {:tail {:result (:result tail) :stats (:stats tail)}
     :unique {:values (:values unique) :same-root? (= (:input unique) (:output unique))
              :stats (get-in unique [:state :stats])}
     :shared {:values (:values shared) :original (:original shared)
              :same-root? (= (:input shared) (:output shared)) :stats (get-in shared [:state :stats])}
     :fork {:results [(:result left) (:result right)]
            :captured-live (count (:heap captured))
            :events [(:events left) (:events right)]}}))
