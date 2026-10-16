(ns prototype.portable
  (:require [cljs.reader :as reader]
            [prototype.machine :as m]))

(defn check! [condition label]
  (when-not condition (throw (js/Error. (str "Failed: " label)))))

(defn -main []
  (let [fs (js/require "fs")
        functions (reader/read-string (.readFileSync fs "fixtures/list-map.edn" "utf8"))
        target (get (reader/read-string (.readFileSync fs "fixtures/entry.edn" "utf8")) :entry)
        [s root] (m/guest-list (m/world functions) [1 2 3 4])
        shared-input (m/retain s root 1)
        unique (m/run (m/start s target [(m/->Builtin :inc) root]))
        shared (m/run (m/start shared-input target [(m/->Builtin :inc) root]))
        tail-functions (reader/read-string (.readFileSync fs "fixtures/tail.edn" "utf8"))
        tail (m/run (m/start (m/world tail-functions) :even [100000]))
        [f resource] (m/resource (m/world {:fork {:params [0]
                                                :body [:suspend 1 [:dec [:var 0] 1 [:return [:var 1]]]]}}) :fork-resource)
        captured (m/run (m/start f :fork [resource]))
        left (m/run (m/resume captured 10)) right (m/run (m/resume captured 20))
        host (m/run (m/start (m/world {:host {:params [0] :body [:host "demo" [[:var 0]] 1 [:return [:var 1]]]}})
                             :host [42]))]
    (check! (= [2 3 4 5] (m/list-values unique (:result unique))) :unique-map)
    (check! (= [2 3 4 5] (m/list-values shared (:result shared))) :shared-map)
    (check! (= [1 2 3 4] (m/list-values shared root)) :preserve-input)
    (check! (= root (:result unique)) :reuse-root)
    (check! (not= root (:result shared)) :copy-shared)
    (check! (= :done (:status tail)) :tail-done)
    (check! (= 0 (:result tail)) :tail-result)
    (check! (= 0 (get-in tail [:stats :max-frames])) :tail-space)
    (check! (= [10 20] [(:result left) (:result right)]) :fork-results)
    (check! (= [[:released :fork-resource]] (:events left) (:events right)) :fork-release)
    (check! (= 1 (count (:heap captured))) :snapshot-preserved)
    (check! (empty? (:events captured)) :snapshot-no-effects)
    (check! (= [1 2 3 4] (m/list-values s root)) :unique-store-snapshot-isolation)
    (check! (= [2 3 4 5] (m/list-values (m/run (m/start s target [(m/->Builtin :inc) root])) root))
            :unique-store-second-branch)
    (check! (= 6 (m/scalar :add [2 4])) :exact-addition)
    (check! (= 0 (m/scalar :add [9007199254740991 -9007199254740991])) :addition-cancellation)
    (check! (try (m/scalar :add [9007199254740991 1]) false
                 (catch js/Error _ true)) :addition-overflow-rejected)
    (check! (= {:symbol "demo" :arguments [42] :dest 1} (:host-request host)) :host-boundary-data)
    (check! (= [10 20] (mapv #(:result (m/run (m/resume host %))) [10 20])) :host-independent-resumes)
    (check! (= :host-call (:status host)) :host-snapshot-retained)
    (let [[world box] (m/box-value (m/world {}) "uint64" 9007199254740991)
          slot {:index 0 :offset 0 :type "uint64" :region :scalar}
          child (m/run (m/start (assoc world :functions {:write {:params [0] :body [:scalar-set [:var 0] slot [:imm 7] [:return [:var 0]]]}})
                                :write [box]))]
      (check! (= 9007199254740991 (m/unbox-value world "uint64" box)) :scalar-wide-exact)
      (check! (= 7 (m/unbox-value child "uint64" box)) :scalar-child-update)
      (check! (= 9007199254740991 (m/unbox-value world "uint64" box)) :scalar-parent-isolation)
      (check! (= 4294967295 (second (m/box-value (m/world {}) "uint32" 4294967295))) :scalar-immediate-uint32)
      (check! (try (m/box-value world "uint64" 9007199254740992) false
                   (catch js/Error _ true)) :scalar-unsafe-number-rejected))
    (println (pr-str {:platform :node :checks 25 :unique (:stats unique)
                     :shared (:stats shared) :tail (:stats tail)}))))

(set! *main-cli-fn* -main)
