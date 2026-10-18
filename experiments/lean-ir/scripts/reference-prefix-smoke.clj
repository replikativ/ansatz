;; Definitions only. No tests, benchmarks, runtime Var replacement, guest work,
;; print setting changes, or native-resource lifetime changes occur on load.
(ns prototype.reference-prefix-smoke-draft
  (:require [prototype.machine :as m]
            [prototype.native-scalar :as native]
            [prototype.examples :as ex]))

(defn- check! [okay context]
  ;; NEVER embed worlds/results/Exprs in assertion output or ex-data.
  (when-not okay (throw (ex-info "Reference-prefix smoke mismatch" context))))
(defn- literal-chain [n continuation]
  (reduce (fn [body i] [:let (+ 10 i) [:literal i] body]) continuation (range n)))
(defn- fixture-worlds []
  (let [tail (m/start (m/world {:even (ex/tail-function :odd) :odd (ex/tail-function :even)}) :even [120])
        list-a (ex/list-demo false) list-b (ex/list-demo true)
        list-start (fn [{:keys [initial target input]}]
                     (m/start initial target [(m/->Builtin :inc) input]))
        resource-functions {:resource {:params [1] :body (literal-chain 650 [:dec [:var 1] 1 [:return [:imm 42]]])}}
        [resource-world resource] (m/resource (m/world resource-functions) "prefix-owned")
        native-functions {:native {:params []
                                   :body [:let 1 [:runtime "lean_uint32_add"
                                                  [[:imm (native/native-scalar 4294967295)]
                                                   [:imm (native/native-scalar 2)]]]
                                          [:return [:var 1]]]}}
        task-functions {:task {:params []
                               :body [:let 1 [:runtime "lean_task_pure" [[:imm m/erased] [:imm 42]]]
                                      [:let 2 [:runtime "lean_task_get_own" [[:imm m/erased] [:var 1]]]
                                       [:return [:var 2]]]]}}
        host-functions {:host {:params [] :body (literal-chain 300
                                                   [:host "smoke_unexecuted_callback" [] 900 [:return [:var 900]]])}}]
    {:tail tail :list (list-start list-a) :shared-list (list-start list-b)
     :resource (m/start resource-world :resource [resource])
     :native-scalar (m/start (m/world native-functions) :native [])
     :task (m/start (m/world task-functions) :task [])
     :unstarted-host (m/start (m/world host-functions) :host [])}))

(defn smoke!
  "Compare exact SMALL worlds against captured original run-boundary. The
   candidate has signature [session world fuel prefix-limit]. No host handlers
   are dispatched. Throws only scalar fixture/fuel/prefix context on mismatch."
  [original candidate]
  (let [checks (atom 0)]
    (doseq [[label world] (fixture-worlds)
            fuel [0 1 255 256 257 600 2000]
            prefix [0 1 256]]
      (let [session {:backend :mutable :functions (:functions world)}
            expected (original session world fuel)
            actual (candidate session world fuel prefix)
            context {:fixture label :fuel fuel :prefix prefix
                     :expected-status (:status expected) :actual-status (:status actual)
                     :expected-steps (get-in expected [:stats :steps])
                     :actual-steps (get-in actual [:stats :steps])}]
        (check! (= expected actual) context)
        (swap! checks inc)))
    {:status :pass :checks @checks :fixtures 7 :host-handler-executions 0}))

(defn microbenchmark!
  "Pure static 50-let helper over an EXACT borrowed full heap. Synthetic function
   is confined to a new function-map branch; no host callbacks or heap operations.
   Pass original/candidate explicitly, rounds 1..20. Returns scalar timings only.
   No warm/cold/JIT throughput claim; no resource close, source access or GC."
  [original candidate borrowed-world rounds]
  (check! (and (integer? rounds) (<= 1 rounds 20)) {:reason :invalid-round-count})
  (let [name ["str" ["anonymous"] "referencePrefixPureMicrobenchmark"]
        _ (check! (not (contains? (:functions borrowed-world) name)) {:reason :synthetic-name-collision})
        function {:params [] :body (literal-chain 50 [:return [:imm 42]])}
        functions (assoc (:functions borrowed-world) name function)
        started (m/start (assoc borrowed-world :functions functions) name [])
        session {:backend :mutable :functions functions}
        sample (fn [run]
                 (let [t (System/nanoTime) result (run) elapsed (/ (- (System/nanoTime) t) 1e6)]
                   (check! (and (= :done (:status result)) (= 42 (:result result))
                                (= 51 (- (get-in result [:stats :steps]) (get-in started [:stats :steps])))
                                (= (:heap started) (:heap result))
                                (= (:events started) (:events result))
                                (= (:globals started) (:globals result)))
                           {:reason :pure-microbenchmark-result :status (:status result)})
                   elapsed))
        samples (mapv (fn [round]
                        {:round round
                         :original-ms (sample #(original session started 2000))
                         :prefix256-ms (sample #(candidate session started 2000 256))}) (range rounds))]
    {:scope :borrowed-full-heap-pure-50-let-observation
     :rounds rounds :guest-steps-per-sample 51 :heap-objects (count (:heap started))
     :samples samples :includes-bootstrap false :includes-host-handler false
     :source-closed false :original-world-mutated false}))
