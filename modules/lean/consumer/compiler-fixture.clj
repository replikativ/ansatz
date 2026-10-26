(ns consumer.compiler-fixture
  "Jar-only consumer data setup; no frontend/admission authority."
  (:require [clojure.data.json :as json] [clojure.java.io :as io] [clojure.string :as str]
            [prototype.runtime-abi :as abi] [prototype.import-ir :as ir]
            [prototype.machine :as m]))

(def profile {:schema "lean-block-profile/1" :producer-commit "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
              :phase :expanded-rc :word-bits 64 :layout :lean-64 :abi-generation "jar-consumer/1" :target :jvm})
(def budgets {:max-functions 16 :max-instructions 4096 :max-blocks 4096 :max-work 200000
              :max-registers 65536 :max-params 16 :max-emission 8192 :max-constants 8192 :max-chunk-cost 2048})
(defn input []
  (let [resource (or (io/resource "compiler-consumer/boxed-scalar-wrapper-programs.jsonl")
                     (throw (ex-info "Missing consumer fixture jar" {})))
        rows (mapv #(json/read-str % :key-fn keyword) (str/split-lines (slurp resource)))
        declarations (filterv #(= "decl" (:kind %)) rows)
        functions (into {} (map abi/lower) declarations)
        typed (into {} (comp (filter #(and (get-in % [:ir :fdecl]) (not= "_boxed" (last (:name %)))))
                             (map ir/lower-typed-declaration)) declarations)
        descriptors (into {} (keep #(when-let [d (abi/describe-scalar % profile)] [(:name d) d])) declarations)]
    {:functions functions :options {:typed-tail {:typed-functions typed :roots (vec (keys typed))
                                                :descriptors descriptors :profile profile :budgets budgets}}
     :targets (into {} (map (fn [name] [(last name) name])) (keys typed))}))

(defn shape [world]
  {:locals (update-vals (:locals world) class) :result (class (:result world))
   :frames (mapv #(update-vals (:locals %) class) (:frames world))
   :joins (update-vals (:joins world) #(update-vals (:locals %) class))})
