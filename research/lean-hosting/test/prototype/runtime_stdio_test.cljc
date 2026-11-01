(ns prototype.runtime-stdio-test
  (:require [prototype.machine :as m]
            [prototype.runtime-io :as io]
            [prototype.runtime-task :as task]
            #?(:clj [prototype.stdio :as stdio])
            #?(:clj [prototype.mutable :as u])
            #?(:clj [prototype.lazy-runtime :as lazy])
            #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])))

(def backends #?(:clj [:reference :mutable :jvm] :cljs [:reference]))
(defn method-name [i] ["str" ["anonymous"] (str "stream-method-" i)])
(def table
  (merge
   (into {} (for [[symbol [_ swap?]] io/stdio-symbols
                  :let [arity (if swap? 2 1) params (vec (range 1 (inc arity))) dest (inc arity)]]
              [symbol {:params params :body [:let dest [:runtime symbol (mapv #(vector :var %) params)] [:return [:var dest]]]}]))
   {(method-name 0) {:params [1 2] :body [:let 3 [:ctor 0 [[:imm 0]]] [:return [:var 3]]]}
    (method-name 1) {:params [1 2 3] :body [:let 4 [:runtime "lean_mk_empty_byte_array" [[:imm 0]]]
                                         [:let 5 [:ctor 0 [[:var 4]]] [:return [:var 5]]]]}
    (method-name 2) {:params [1 2 3] :body [:dec [:var 2] 1 [:let 4 [:ctor 0 [[:imm 0]]] [:return [:var 4]]]]}
    (method-name 3) {:params [1 2] :body [:let 3 [:ctor 0 [[:var 1]]] [:return [:var 3]]]}
    (method-name 4) {:params [1 2 3] :body [:let 4 [:ctor 0 [[:imm 0]]] [:return [:var 4]]]}
    (method-name 5) {:params [1 2] :body [:return [:imm 0]]}
    "stream-line" {:params [1 2] :body [:let 3 [:project [:var 1] 3]
                                        [:inc [:var 3] 1 [:tail [:closure [:var 3]] [[:var 2]]]]]}
    "spawn" {:params [1 2 3 4] :body (task/registration-body "lean_io_as_task" [1 2 3 4] 5)}
    "mapIO" {:params [1 2 3 4 5 6 7] :body (task/registration-body "lean_io_map_task" [1 2 3 4 5 6 7] 8)}
    "pure" {:params [1 2] :body [:let 3 [:runtime "lean_task_pure" [[:var 1] [:var 2]]] [:return [:var 3]]]}
    task/get-target {:params [1 2] :body (task/get-body 2 3)}
    "get-worker-out" {:params [1] :body [:let 2 [:runtime "lean_get_stdout" [[:var 1]]] [:return [:var 2]]]}
    "get-sync-out" {:params [1 2] :body [:let 3 [:runtime "lean_get_stdout" [[:var 2]]] [:return [:var 3]]]}}))

(defn run [backend world target args]
  (let [world (m/start world target args)]
    #?(:clj (case backend :reference (m/run world 100000)
                          :mutable (u/freeze (u/run! (u/thaw world) 100000))
                          :jvm (u/freeze (lazy/run! (lazy/open-program (:functions world)) (u/thaw world) 100000)))
       :cljs (m/run world 100000))))
(defn stream [world label]
  (let [[world methods] (reduce (fn [[world methods] i]
                                (let [[world method] (m/expr world [:closure (method-name i) [[:imm label]]])]
                                  [world (conj methods method)])) [world []] (range 6))]
    (m/allocate world :ctor 0 methods)))
(defn configured []
  (reduce (fn [world channel]
            (let [[world stream] (stream world (name channel))]
              (assoc-in world [:stdio-runtime :defaults channel] stream)))
          (m/world table) [:stdin :stdout :stderr]))

(deftest standard-stream-get-and-swap-transfer-the-right-owners
  (doseq [backend backends channel [:stdin :stdout :stderr]]
    (let [get-symbol (str "lean_get_" (name channel)) set-symbol (str "lean_get_set_" (name channel))
          before (configured) default (get-in before [:stdio-runtime :defaults channel])
          got (run backend before get-symbol [m/erased])
          [world replacement] (stream got "replacement")
          ;; Drop getter owner; retain only process-default + thread slot.
          world (m/release world (:result got) 1)
          swapped (run backend world set-symbol [replacement m/erased])
          old (:result swapped)
          restored (run backend swapped set-symbol [old m/erased])
          returned (:result restored)]
      (is (= default (:result got)))
      (is (= 3 (:rc (m/node got default))))
      (is (= default old))
      (is (= replacement (get-in swapped [:stdio-runtime :threads :main channel])))
      (is (= 1 (:rc (m/node swapped replacement))))
      (is (= replacement returned))
      (is (= default (get-in restored [:stdio-runtime :threads :main channel])))
      (is (= 2 (:rc (m/node restored default))))
      (is (not (contains? (:heap (m/release restored returned 1)) (:id replacement))))
      (is (nil? (get-in before [:stdio-runtime :threads]))))))

(deftest stream-methods-are-still-visible-guest-closures
  (doseq [backend backends]
    (let [world (run backend (configured) "lean_get_stdin" [m/erased]) stream (:result world)
          after (run backend world "stream-line" [stream m/erased]) result (:result after)]
      (is (= :ctor (:kind (m/node after stream))))
      (is (= 0 (:tag (m/node after result))))
      (is (= ["stdin"] (:fields (m/node after result))))
      (is (= 1 (:rc (m/node after (nth (:fields (m/node after stream)) 3))))))))

(deftest unconfigured-or-invalid-streams-fail-without-fabricated-handles
  (doseq [backend backends]
    (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"Missing guest standard stream"
          (run backend (m/world table) "lean_get_stdin" [m/erased])))
    (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"FS.Stream"
          (run backend (configured) "lean_get_set_stdin" [0 m/erased])))))

(deftest swaps-fork-without-changing-the-parent-or-other-streams
  (doseq [backend backends]
    (let [parent (configured) [world left-stream] (stream parent "left") [world right-stream] (stream world "right")
          left (run backend world "lean_get_set_stdout" [left-stream m/erased])
          right (run backend world "lean_get_set_stdout" [right-stream m/erased])]
      (is (= left-stream (get-in left [:stdio-runtime :threads :main :stdout])))
      (is (= right-stream (get-in right [:stdio-runtime :threads :main :stdout])))
      (is (nil? (get-in parent [:stdio-runtime :threads])))
      (is (= (get-in parent [:stdio-runtime :defaults :stderr]) (get-in left [:stdio-runtime :defaults :stderr]))))))

(deftest async-workers-use-default-streams-and-sync-continuations-share-caller-streams
  (doseq [backend backends]
    (let [world (configured) default (get-in world [:stdio-runtime :defaults :stdout])
          [world redirected] (stream world "parent-only")
          changed (run backend world "lean_get_set_stdout" [redirected m/erased])
          world (m/release changed (:result changed) 1)
          [world closure] (m/expr world [:closure "get-worker-out" []])
          spawned (run backend world "spawn" [m/erased closure 0 m/erased])
          job (:result spawned)
          worker (run backend spawned task/get-target [m/erased job])
          pure (run backend worker "pure" [m/erased 0])
          [world callback] (m/expr pure [:closure "get-sync-out" []])
          mapped (run backend world "mapIO" [m/erased m/erased callback (:result pure) 0 1 m/erased])
          sync (run backend mapped task/get-target [m/erased (:result mapped)])]
      (is (= default (:result worker)))
      (is (= redirected (:result sync)))
      (is (= redirected (get-in sync [:stdio-runtime :threads :main :stdout])))
      (is (= #{:main} (set (keys (get-in sync [:stdio-runtime :threads])))))
      (is (= [] (get-in sync [:task-runtime :active]))))))

#?(:clj
   (deftest memory-seeding-uses-guest-ofbuffer-and-retains-host-buffer-roots
     (let [invocations (atom [])
           invoke (fn [world target [reference]]
                    (swap! invocations conj target)
                    (is (= :ref (:kind (m/node world reference))))
                    ;; A test constructor owns the argument in six guest methods.
                    (let [world (m/retain world reference 5)
                          [world methods] (reduce (fn [[w fs] i]
                                                    (let [[w f] (m/expr w [:closure (method-name i) [[:imm reference]]])]
                                                      [w (conj fs f)])) [world []] (range 6))]
                      (m/allocate world :ctor 0 methods)))
           seeded (stdio/seed-memory (m/world table) invoke {:stdin [206 187 10]})
           world (:world seeded)
           stdin (get-in seeded [:buffers :stdin])
           buffer (m/node world (first (:fields (m/node world stdin))))
           bytes (m/node world (first (:fields buffer)))]
       (is (= (repeat 3 stdio/of-buffer-target) @invocations))
       (is (= [206 187 10] (:bytes bytes)))
       (is (= #{:stdin :stdout :stderr} (set (keys (:buffers seeded)))))
       (let [released (reduce #(m/release %1 %2 1) (dissoc world :stdio-runtime)
                              (concat (vals (get-in world [:stdio-runtime :defaults])) (vals (:buffers seeded))))]
         (is (empty? (:heap released))))
       (is (thrown-with-msg? clojure.lang.ExceptionInfo #"already configured"
             (stdio/seed-memory world invoke))))))
