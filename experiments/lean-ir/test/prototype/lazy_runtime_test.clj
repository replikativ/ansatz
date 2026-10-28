(ns prototype.lazy-runtime-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.block-compile :as b]
            [prototype.fingerprint :as fingerprint]
            [prototype.code-provenance :as provenance]
            [clojure.edn :as edn]
            [prototype.import-ir :as ir]
            [prototype.lazy-runtime :as lazy]
            [prototype.heap-examples :as h]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.region-compile-test :as regions]))

(defn check-fuels [functions initial]
  (let [program (lazy/open-program functions) completed (m/run initial)]
    (is (zero? (:compiled (lazy/summary program))))
    (doseq [fuel (range (+ 2 (get-in completed [:stats :steps])))]
      (let [machine (lazy/run! program (u/thaw initial) fuel) captured (u/freeze machine)]
        (is (= (m/run initial fuel) captured))
        (when (= :paused (:status captured))
          (is (= completed (u/freeze (lazy/run! program (u/resume! machine nil)))))
          (is (= completed (m/run (m/resume captured nil)))))))
    completed))

(defn cache-sizes [program]
  (assoc (select-keys (lazy/summary program) [:compiled :cache-hits :dispatch-blocks :cached-blocks])
         :identities (.size ^java.util.IdentityHashMap (:identity-dispatch program))
         :keys (.size ^java.util.IdentityHashMap (:identity-keys program))
         :visits (.size ^java.util.IdentityHashMap (:visits program))
         :source-bodies (.size ^java.util.IdentityHashMap (:source-bodies program))))

(deftest runtime-publication-continuations-never-enter-code-caches
  (doseq [functions [{:entry {:params [] :body [:global :g :init]}
                     :init {:params [] :body [:return [:imm 42]]}}
                    {:entry {:params [] :body [:begin-init :g :init [] "object"]}
                     :init {:params [] :body [:let 0 [:ctor 0 [[:imm 42]]] [:return [:var 0]]]}}]]
    (let [program (lazy/open-program functions)
          initial (m/start (m/world functions) :entry [])
          completed (check-fuels functions initial)
          original fingerprint/key
          run #(u/freeze (lazy/run! program (u/thaw initial)))]
      (is (= 42 (:result completed)))
      (with-redefs [fingerprint/key
                    (fn [body]
                      (when (and (vector? body)
                                 (contains? #{:publish-global :publish-io-global} (first body)))
                        (throw (ex-info "Runtime publisher was hashed" {})))
                      (original body))]
        (is (= completed (run)))
        (let [before (cache-sizes program)]
          (dotimes [_ 10] (is (= completed (run))))
          (is (= before (cache-sizes program))))))))

(deftest overapplication-surplus-values-never-become-code
  (let [functions {:entry {:params [0]
                           :body [:let 1 [:closure :first []]
                                  [:tail [:closure [:var 1]] [[:imm 0] [:var 0]]]]}
                   :first {:params [0] :body [:let 1 [:closure :identity []] [:return [:var 1]]]}
                   :identity {:params [0] :body [:return [:var 0]]}}
        [world ref] (m/resource (m/world functions) :surplus)
        initial (m/start world :entry [ref])
        completed (check-fuels functions initial)
        program (lazy/open-program functions)
        original fingerprint/key
        run #(u/freeze (lazy/run! program (u/thaw initial)))]
    (is (= ref (:result completed)))
    (with-redefs [fingerprint/key
                  (fn [body]
                    (when (and (vector? body) (= :tail (first body))
                               (= :imm (first (first (nth body 2 nil))))
                               (m/ref? (second (first (nth body 2 nil)))))
                      (throw (ex-info "Surplus guest value was hashed as code" {})))
                    (original body))]
      (is (= completed (run)))
      (let [before (cache-sizes program)]
        (dotimes [_ 10] (is (= completed (run))))
        (is (= before (cache-sizes program)))))))

(deftest cached-source-provenance-keeps-equivalent-multi-region-reuse
  (let [functions {:entry {:params [] :body [:call 0 [:direct :worker] []
                                           [:let 1 [:literal 99] [:return [:var 1]]]]}
                   :worker {:params [] :body [:return [:imm 42]]}}
        original-continuation (get-in functions [:entry :body 4])
        cache (lazy/code-cache)
        first-program (lazy/open-program functions {} cache)
        run #(u/freeze (lazy/run! % (u/thaw (m/start (m/world (:functions %)) :entry []))))]
    (is (= 99 (:result (run first-program))))
    (let [independent (edn/read-string (pr-str functions))
          second-program (lazy/open-program independent {} cache)]
      (is (not (.containsKey ^java.util.IdentityHashMap (:source-bodies second-program) original-continuation)))
      (is (= 99 (:result (run second-program))))
      (is (.containsKey ^java.util.IdentityHashMap (:source-bodies second-program) original-continuation))
      (is (zero? (:compiled (lazy/summary second-program))))
      (is (= 3 (:cache-hits (lazy/summary second-program)))))))

(deftest source-discovery-is-nonvalidating-and-does-not-walk-literals
  (let [hashed (atom 0)
        opaque-op (reify Object (hashCode [_] (swap! hashed inc) (throw (ex-info "Unexpected hash" {}))))
        literal [:return [:imm :data]]
        functions {:entry {:params [] :body [:let 0 [:literal literal] [:return [:var 0]]]}
                   :unused {:params [] :body [opaque-op]}}
        program (lazy/open-program functions)
        index (:source-bodies program)]
    (is (zero? @hashed))
    (is (not (.containsKey ^java.util.IdentityHashMap index literal)))
    (is (identical? index (provenance/admit-body! index literal)))
    (is (.containsKey ^java.util.IdentityHashMap index literal)))
  (let [functions {:entry {:params [] :body [:return [:imm 42]]}}
        program (lazy/open-program functions)
        copied (edn/read-string (pr-str (get-in functions [:entry :body])))
        initial (assoc (m/start (m/world functions) :entry []) :body copied)]
    (with-redefs [fingerprint/key (fn [& _] (throw (ex-info "Copied runtime PC was hashed" {})))]
      (is (= (m/run initial) (u/freeze (lazy/run! program (u/thaw initial))))))
    (is (zero? (:compiled (lazy/summary program))))))

(deftest real-ir-pauses-and-suspension-forks
  (let [functions (h/functions)]
    (doseq [shared? [false true] workload [:map :fold :reverse]]
      (check-fuels functions (:initial (h/prepare functions workload [1 2 3 4] shared? true)))))
  (doseq [functions [regions/nested regions/captured-call regions/recursive]]
    (let [initial (m/start (m/world functions) :entry (if (= functions regions/nested) [3 4] [3]))
          captured (check-fuels functions initial)]
      (when (= :suspended (:status captured))
        (let [program (lazy/open-program functions) parent (u/thaw captured)]
          (doseq [answer [10 20]]
            (is (= (m/run (m/resume captured answer))
                   (u/freeze (lazy/run! program (u/resume! (u/thaw captured) answer))))))
          (is (= captured (u/freeze parent))))))))

(deftest unvisited-declarations-are-not-compiled
  (let [functions {:entry {:params [] :body [:return [:imm 42]]}
                   :unused {:params [] :body [:unsupported]}}
        program (lazy/open-program functions)
        initial (m/start (m/world functions) :entry [])]
    (lazy/run! program (u/thaw initial) 0)
    (is (zero? (:compiled (lazy/summary program))))
    (is (= (m/run initial) (u/freeze (lazy/run! program (u/thaw initial)))))
    (is (= 1 (:compiled (lazy/summary program))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported"
                         (lazy/run! program (u/thaw (m/start (m/world functions) :unused [])))))))

(deftest edits-reuse-caller-code-without-stale-callees
  (let [functions {:entry {:params [] :body [:tail [:direct :value] []]}
                   :value {:params [] :body [:return [:imm 10]]}}
        cache (lazy/code-cache)
        old (lazy/open-program functions {} cache)
        run #(u/freeze (lazy/run! % (u/thaw (m/start (m/world (:functions %)) :entry []))))
        before (run old)
        edited (assoc-in functions [:value :body] [:return [:imm 20]])
        new (lazy/open-program edited {} cache)
        after (run new)]
    (is (= 10 (:result before)))
    (is (= 20 (:result after)))
    (is (= 1 (:compiled (lazy/summary new))))
    (is (= 1 (:cache-hits (lazy/summary new))))
    (is (= before (run old)))
    ;; Only the tail target's shape affects this entry, not unrelated arities.
    (let [unrelated (lazy/open-program (assoc edited :unused {:params [0] :body [:unsupported]}) {} cache)]
      (is (= 20 (:result (run unrelated))))
      (is (zero? (:compiled (lazy/summary unrelated)))))
    (is (not= (b/runtime-block-key functions (get-in functions [:entry :body]) {:lexical-joins true})
              (b/runtime-block-key (assoc-in functions [:value :params] [0])
                                   (get-in functions [:entry :body]) {:lexical-joins true})))
    (is (not= (b/runtime-block-key functions [:return [:imm 0]] {})
              (b/runtime-block-key functions [:return [:imm 0]] {:direct-linking true})))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"does not match"
                         (lazy/run! old (u/thaw (m/start (m/world edited) :entry [])))))))

(deftest selective-real-ir-lowering
  (let [catalogue (ir/index-bundles ["fixtures/list-map.jsonl" "fixtures/list-fold.jsonl"])
        eager (ir/load-bundle "fixtures/list-map.jsonl")
        root (h/entry eager "List.map")
        selected (ir/load-closure catalogue [root])]
    (is (= eager selected))
    (let [target (h/entry eager "List.map._redArg")
          functions (ir/load-closure catalogue [target])
          [world input] (m/guest-list (m/world functions) [1 2 3 4])
          initial (m/start world target [(m/->Builtin :inc) input])
          result (u/freeze (lazy/run! (lazy/open-program functions) (u/thaw initial)))]
      (is (= (m/run initial) result))
      (is (= [2 3 4 5] (m/list-values result (:result result)))))
    (let [name ["str" ["anonymous"] "unsupported"]
          catalogue (assoc-in catalogue [:declarations name]
                              {:name name :kind "decl" :ir {:extern {}}})]
      (is (= selected (ir/load-closure catalogue [root])))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Missing body or extern"
                           (ir/load-closure catalogue [name]))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Missing declaration dependency"
                         (ir/load-closure (assoc catalogue :declarations {}) [root])))))

(deftest cache-reload-guard-and-profile-boundaries
  (let [functions {:entry {:params [] :body [:return [:imm 0]]}}
        program (lazy/open-program functions)
        initial (m/start (m/world functions) :entry [])]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Reopen lazy program"
                         (lazy/run! (assoc program :generation (Object.)) (u/thaw initial))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Lazy prototype"
                         (lazy/open-program functions {:leaf-calls true})))))

(deftest total-emission-budget-caches-a-progressing-wide-case-boundary
  (let [body [:case [:var 0]
              (mapv (fn [i] [i [:dec [:var 1] 1 [:suspend 2 [:return [:imm i]]]]]) (range 600))]
        functions {:entry {:params [0 1] :body body}}
        cache (lazy/code-cache) program (lazy/open-program functions {} cache)]
    (doseq [selected [0 299 599]]
      (let [[w resource] (m/resource (m/world functions) :selected-branch)
            initial (m/start w :entry [selected resource])
            completed (m/run initial)]
        (doseq [fuel (range 6)]
          (let [expected (m/run initial fuel) mutable (u/freeze (u/run! (u/thaw initial) fuel))
                actual (u/freeze (lazy/run! program (u/thaw initial) fuel))]
            (is (= expected mutable actual))
            (when (= :suspended (:status actual))
              (doseq [answer [17 23]]
                (let [done (u/freeze (lazy/run! program (u/resume! (u/thaw actual) answer)))]
                  (is (= (m/run (m/resume actual answer)) done))
                  (is (= selected (:result done))))))))
        (let [one (u/freeze (lazy/run! program (u/thaw initial) 1))
              block (get @cache (b/runtime-block-key functions body (:options program)))]
          (is (= (m/run initial 1) one))
          (is (not= body (:body one)))
          (is (= 1 (:max-cost block)))
          (is (= :emission-budget (:fallback block)))
          (is (= :suspended (:status completed))))))
    (let [again (lazy/open-program functions {} cache)
          [w r] (m/resource (m/world functions) :again)]
      (lazy/run! again (u/thaw (m/start w :entry [299 r])) 1)
      (is (zero? (:compiled (lazy/summary again))))
      (is (= 1 (:cache-hits (lazy/summary again)))))))

(deftest aggregate-branches-and-lexical-captures-preserve-fuel-frames-and-owners
  (let [branches [:case [:var 0]
                  (mapv (fn [i] [i [:call 4 [:direct :worker] [[:imm i]] [:jump (+ 100 i) [[:var 4]]]]]) (range 12))]
        shadowed [:let 10 [:literal 1000] branches]
        joined (reduce (fn [body i]
                         [:join (+ 100 i) [1]
                          [:let 2 [:prim :add [[:var 10] [:var 1]]]
                           [:dec [:var 5] 1 [:suspend 3 [:return [:var 2]]]]]
                          body]) shadowed (reverse (range 12)))
        body (reduce (fn [body i] [:let i [:literal i] body]) joined (reverse (range 10 70)))
        functions {:entry {:params [0 5] :body body} :worker {:params [0] :body [:return [:var 0]]}}
        program (lazy/open-program functions)]
    (doseq [selected [0 6 11]]
      (let [[w resource] (m/resource (m/world functions) :joined-branch)
            initial (m/start w :entry [selected resource])]
        (doseq [fuel [0 1 20 59 60 64 72 73 74 75 76 77 79 100]]
          (let [reference (m/run initial fuel)
                mutable (u/freeze (u/run! (u/thaw initial) fuel))
                compiled (u/freeze (lazy/run! program (u/thaw initial) fuel))]
            (is (= reference mutable compiled))
            (when (= :paused (:status compiled))
              (is (= (m/run initial) (u/freeze (lazy/run! program (u/resume! (u/thaw compiled) nil))))))))))
    (let [[w resource] (m/resource (m/world functions) :suspended-parent)
          captured (u/freeze (lazy/run! program (u/thaw (m/start w :entry [11 resource]))))]
      (is (= :suspended (:status captured)))
      (doseq [answer [1 2]]
        (let [result (u/freeze (lazy/run! program (u/resume! (u/thaw captured) answer)))]
          (is (= (m/run (m/resume captured answer)) result))
          (is (= 21 (:result result)))
          (is (= captured (u/freeze (u/thaw captured)))))))
    (is (some #(< (:region-limit %) 128) (vals @(:cache program))))))

(deftest method-size-backstop-does-not-mask-other-compiler-errors
  (let [body [:return [:imm 7]] functions {:entry {:params [] :body body}}
        observer-calls (atom 0) original-step u/step!
        compiled (with-redefs [clojure.core/eval (fn [_] (throw (IndexOutOfBoundsException. "Method code too large!")))
                               u/step! (fn [machine] (swap! observer-calls inc) (original-step machine))]
                   (b/compile-runtime-block functions body {:lexical-joins true}))
        initial (m/start (m/world functions) :entry [])
        machine (u/thaw initial)]
    (is (= :jvm-method-size (:fallback compiled)))
    (is (= 1 (:max-cost compiled)))
    ((:execute! compiled) machine)
    (is (zero? @observer-calls))
    (is (= (m/run initial 1) (u/freeze machine)))
    (let [sentinel (IndexOutOfBoundsException. "Different compiler bug")
          actual (try (with-redefs [clojure.core/eval (fn [_] (throw sentinel))]
                        (b/compile-runtime-block functions body {:lexical-joins true}))
                      (catch Throwable t t))]
      (is (identical? sentinel actual)))))

(deftest actual-hosted-frontend-continuation-fits-bounded-regions
  ;; Captured from actual PreludeIdentity.lean compilation before the size fix:
  ;;293IR instructions,25binarycases,20joins; old emitter hit the64KiB limit.
  (let [body (edn/read-string (slurp "fixtures/jvm-method-size-continuation.edn"))
        block (b/compile-runtime-block {} body {:lexical-joins true})]
    (is (fn? (:execute! block)))
    (is (or (:fallback block) (< (:region-limit block) 128)))
    (is (<= 1 (:max-cost block) 128))))

(deftest optional-hotness-compiles-only-after-positive-progress
  (let [functions {:entry {:params [] :body [:return [:imm 42]]}}
        initial (m/start (m/world functions) :entry [])
        cache (lazy/code-cache)
        program (lazy/open-program functions {:compile-threshold 3} cache)
        run #(u/freeze (lazy/run! % (u/thaw initial)))]
    (is (= (m/run initial 0) (u/freeze (lazy/run! program (u/thaw initial) 0))))
    (doseq [_ (range 2)]
      (is (= (m/run initial) (run program)))
      (is (empty? @cache)))
    (is (= 2 (:interpreted-steps (lazy/summary program))))
    (is (zero? (:dispatch-blocks (lazy/summary program))))
    (is (= (m/run initial) (run program)))
    (is (= 1 (:compiled (lazy/summary program))))
    (is (= 1 (count @cache)))
    (let [warm (lazy/open-program functions {:compile-threshold 100} cache)]
      (is (= (m/run initial) (run warm)))
      (is (= 1 (:cache-hits (lazy/summary warm))))
      (is (zero? (:compiled (lazy/summary warm))))
      (is (nil? (:interpreted-steps (lazy/summary warm))))))
  (doseq [threshold [0 -1 nil 1.5 "64" 2147483648N]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"compilation threshold"
                         (lazy/open-program {} {:compile-threshold threshold})))))

(deftest cold-interpretation-preserves-fuel-ownership-and-forks
  (doseq [functions [regions/nested regions/captured-call regions/recursive]]
    (let [initial (m/start (m/world functions) :entry (if (= functions regions/nested) [3 4] [3]))
          completed (m/run initial)
          program (lazy/open-program functions {:compile-threshold 1000000})]
      (doseq [fuel (range (+ 2 (get-in completed [:stats :steps])))]
        (let [machine (lazy/run! program (u/thaw initial) fuel)
              snapshot (u/freeze machine)]
          (is (= (m/run initial fuel) snapshot))
          (when (= :paused (:status snapshot))
            (is (= completed (u/freeze (lazy/run! program (u/resume! machine nil))))))
          (when (= :suspended (:status snapshot))
            (doseq [answer [10 20]]
              (is (= (m/run (m/resume snapshot answer))
                     (u/freeze (lazy/run! program (u/resume! (u/thaw snapshot) answer)))))))))
      (is (zero? (:compiled (lazy/summary program))))))
  (let [functions (h/functions)
        initial (:initial (h/prepare functions :map [1 2 3 4] true true))
        program (lazy/open-program functions {:compile-threshold 64})
        machine (u/thaw initial)]
    (lazy/step-region! program machine)
    (is (= (m/run initial 1) (assoc (u/freeze machine) :status :paused)))
    (is (= (m/run initial) (u/freeze (lazy/run! program machine))))))

(deftest promotion-during-resource-workload-keeps-exact-fuel
  (let [functions (h/functions)
        initial (:initial (h/prepare functions :map [1 2 3 4] true true))
        completed (m/run initial)
        program (lazy/open-program functions {:compile-threshold 2})]
    (doseq [fuel (range (+ 2 (get-in completed [:stats :steps])))]
      (let [machine (lazy/run! program (u/thaw initial) fuel)
            snapshot (u/freeze machine)]
        (is (= (m/run initial fuel) snapshot))
        (when (= :paused (:status snapshot))
          (is (= completed (u/freeze (lazy/run! program (u/resume! machine nil))))))))
    (is (pos? (:compiled (lazy/summary program))))
    (is (pos? (:interpreted-steps (lazy/summary program))))))

(defn with-isolated-hints [f]
  (with-redefs-fn {#'lazy/shared-hints (#'lazy/hint-table)} f))

(deftest cold-identities-delay-content-work-but-warm-identities-reuse-immediately
  (with-isolated-hints
    (fn []
      (let [body [:return [:imm 42]]
            functions {:entry {:params [] :body body}}
            cache (lazy/code-cache)
            program (lazy/open-program functions {:compile-threshold 3} cache)
            run #(u/freeze (lazy/run! % (u/thaw (m/start (m/world (:functions %)) :entry []))))
            original fingerprint/key]
        (with-redefs [fingerprint/key (fn [value]
                                       (when (identical? value body)
                                         (throw (ex-info "Cold body was hashed" {})))
                                       (original value))
                      b/runtime-block-key (fn [& _] (throw (ex-info "Cold tail targets were scanned" {})))]
          (dotimes [_ 2] (is (= 42 (:result (run program))))))
        (is (= 42 (:result (run program))))
        (let [warm (lazy/open-program functions {:compile-threshold 64} cache)]
          (with-redefs [fingerprint/key (fn [& _] (throw (ex-info "Identity hit was hashed" {})))
                        b/runtime-block-key (fn [& _] (throw (ex-info "Identity hit was scanned" {})))]
            (is (= 42 (:result (run warm)))))
          (is (= 1 (:cache-hits (lazy/summary warm))))
          (is (nil? (:interpreted-steps (lazy/summary warm)))))
        (let [equivalent (edn/read-string (pr-str body))
              fresh (lazy/open-program (assoc-in functions [:entry :body] equivalent)
                                       {:compile-threshold 3} cache)]
          (is (not (identical? body equivalent)))
          (dotimes [_ 2] (is (= 42 (:result (run fresh)))))
          (is (zero? (:cache-hits (lazy/summary fresh))))
          (is (= 42 (:result (run fresh))))
          (is (= 1 (:cache-hits (lazy/summary fresh))))
          (is (zero? (:compiled (lazy/summary fresh)))))))))

(deftest identity-hints-check-cache-options-generation-and-tail-arities
  (with-isolated-hints
    (fn []
      (let [body [:tail [:direct :value] [[:imm 7]]]
            functions {:entry {:params [] :body body}
                       :value {:params [0] :body [:return [:var 0]]}}
            cache (lazy/code-cache)
            first-program (lazy/open-program functions {} cache)]
        (is (map? (#'lazy/block! first-program body)))
        (let [warm (lazy/open-program functions {:compile-threshold 64} cache)]
          (is (map? (#'lazy/block! warm body))))
        (doseq [[f opts c] [[functions {:lexical-joins false} cache]
                            [functions {:direct-linking (not (get-in first-program [:options :direct-linking]))} cache]
                            [(assoc-in functions [:value :params] [0 1]) {} cache]
                            [functions {} (lazy/code-cache)]]]
          (let [program (lazy/open-program f (assoc opts :compile-threshold 64) c)]
            (is (nil? (#'lazy/block! program body)))
            (is (zero? (:cache-hits (lazy/summary program))))))
        (with-redefs-fn {#'b/generation (Object.)}
          #(let [program (lazy/open-program functions {:compile-threshold 64} cache)]
             (is (nil? (#'lazy/block! program body)))))
        (reset! cache {})
        (let [program (lazy/open-program functions {:compile-threshold 64} cache)]
          (is (nil? (#'lazy/block! program body)))
          (is (empty? @cache)))))))

(deftest identity-hints-have-only-weak-body-and-key-edges-and-bounded-cleanup
  (with-isolated-hints
    (fn []
      (let [body [:return [:imm (Object.)]]
            functions {:entry {:params [] :body body}}
            cache (lazy/code-cache)
            program (lazy/open-program functions {} cache)
            _ (#'lazy/block! program body)
            table @#'lazy/shared-hints
            buckets (:buckets table)
            entry (first (first (vals buckets)))
            body-reference (first entry)
            key-reference (first (second entry))]
        (is (instance? java.lang.ref.WeakReference body-reference))
        (is (instance? java.lang.ref.WeakReference key-reference))
        (is (identical? body (.get ^java.lang.ref.WeakReference body-reference)))
        (is (identical? (key (first @cache)) (.get ^java.lang.ref.WeakReference key-reference)))
        ;; Simulate GC deterministically; no dependence on JVM collection timing.
        (.clear ^java.lang.ref.WeakReference key-reference)
        (let [fresh (lazy/open-program functions {:compile-threshold 64} cache)]
          (is (nil? (#'lazy/block! fresh body))))
        (.clear ^java.lang.ref.WeakReference body-reference)
        (.enqueue ^java.lang.ref.WeakReference body-reference)
        (is (nil? (#'lazy/hint-keys body)))
        (is (zero? @(:size table)))
        (is (.isEmpty ^java.util.HashMap buckets))
        (with-redefs-fn {#'lazy/hint-limit 1}
          #(do (#'lazy/remember-hint! [:return [:imm 1]] (Object.))
               (#'lazy/remember-hint! [:return [:imm 2]] (Object.))))
        (is (zero? @(:size table)))
        (is (.isEmpty ^java.util.HashMap buckets))))))
