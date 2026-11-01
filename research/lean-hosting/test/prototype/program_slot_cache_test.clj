(ns prototype.program-slot-cache-test
  "Storage-proof regressions, not executable/kernel authority. These isolated
   tests inspect the weak cache and instrument host sizing without running a
   live frontend or redefining any Var in an application process."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [prototype.slot-count :as slots]
            [prototype.program-install :as install]
            [prototype.program-install-test :as install-test]
            [prototype.machine :as m]
            [prototype.mutable :as mutable])
  (:import [java.lang.ref WeakReference]
           [java.util HashMap]
           [clojure.lang APersistentVector APersistentMap]))

(defn- cache-atom [] @#'slots/program-cache)
(defn- cached [program]
  (some #(when (identical? program (.get ^WeakReference (:program %))) %) @(cache-atom)))
(defn- function [width] {:params [] :body [:return [:var (dec width)]]})
(defn- program [width] {:entry (function width)})
(use-fixtures :each
  (fn [f]
    (let [saved @(cache-atom)]
      (reset! (cache-atom) [])
      (try (f) (finally (reset! (cache-atom) saved))))))
(defn- with-program-scans [f]
  (let [original @#'slots/measure-program calls (atom [])]
    (with-redefs-fn {#'slots/measure-program (fn [functions reuse?]
                                            (swap! calls conj functions)
                                            (original functions reuse?))}
      #(f calls))))

(deftest alternation-reuses-both-exact-program-identities
  (let [a (program 7) b (program 19)]
    (with-program-scans
      (fn [calls]
        (doseq [_ (range 4)]
          (is (= 7 (slots/program-slots a)))
          (is (= 19 (slots/program-slots b))))
        (is (= 2 (count @calls)))
        (is (identical? a (first @calls)))
        (is (identical? b (second @calls)))))
    (is (= #{:program :slots} (set (keys (cached a)))))
    (is (instance? WeakReference (:program (cached a))))
    (is (= 7 (:slots (cached a))))))

(deftest bounds-and-cleared-referents-do-not-retain-program-history
  (let [programs (mapv program (range 2 20))]
    (doseq [p programs] (slots/program-slots p))
    (is (= 16 (count @(cache-atom))))
    (is (nil? (cached (first programs))))
    (doseq [entry @(cache-atom)]
      (is (= #{:program :slots} (set (keys entry))))
      (is (instance? WeakReference (:program entry)))
      (is (integer? (:slots entry))))
    (let [last-program (peek programs) entry (cached last-program)]
      (.clear ^WeakReference (:program entry))
      (slots/program-slots last-program)
      (is (not (identical? entry (cached last-program)))))
    (is (<= (count @(cache-atom)) 16))))

(deftest append-constructs-and-measures-only-the-final-small-delta
  (let [base (program 7) additions {:second (function 29)}]
    (slots/program-slots base)
    (with-program-scans
      (fn [calls]
        (let [result (slots/append-functions base additions)]
          (is (= (merge base additions) result))
          (is (identical? (:entry base) (:entry result)))
          (is (= 29 (:slots (cached result))))
          (is (= 29 (slots/program-slots result)))
          (is (= 1 (count @calls)))
          (is (identical? additions (first @calls)))
          (is (= 7 (slots/program-slots base)))
          (is (= 1 (count @calls))))))))

(deftest unknown-base-replacements-removals-and-fake-metadata-need-exact-sizing
  (let [base (program 100) new {:second (function 3)}
        unknown (slots/append-functions base new)]
    (is (nil? (cached unknown)))
    (is (= 100 (slots/program-slots unknown)))
    (slots/program-slots base)
    (let [replacement (slots/append-functions base {:entry (function 2)})
          removal (dissoc unknown :entry)
          independent (with-meta (into {} unknown) {:program-slots 1})]
      (is (nil? (cached replacement)))
      (is (nil? (cached removal)))
      (is (nil? (cached independent)))
      (is (= 2 (slots/program-slots replacement)))
      (is (= 3 (slots/program-slots removal)))
      (is (= 100 (slots/program-slots independent)))
      (is (= 100 (slots/program-slots base))))))

(deftest failed-addition-never-publishes-a-partial-width
  (let [base (program 7)]
    (slots/program-slots base)
    (doseq [bad [{:params (object-array [0]) :body [:return [:imm 0]]}
                 {:params [] :body [:return [:imm (int-array [0])]]}
                 {:params [] :body [:return [:imm (seq (object-array [0]))]]}]]
      (let [before @(cache-atom)]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"immutable|mutable"
                             (slots/append-functions base {:bad bad})))
        (is (= (mapv :slots before) (mapv :slots @(cache-atom))))
        (is (= 7 (slots/program-slots base)))))
    (doseq [[a b] [[(HashMap.) {}] [{} (HashMap.)]]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"immutable function maps"
                           (slots/append-functions a b))))))

(defn- mutable-vector-view [cell]
  (let [custom (proxy [APersistentVector] []
                 (count [] (count @cell))
                 (nth [index] (nth @cell index)))]
    (clojure.lang.APersistentVector$SubVector. nil custom 0 (count @cell))))
(defn- custom-map-view [cell]
  (proxy [APersistentMap] []
    (count [] (count @cell))
    (seq [] (seq @cell))
    (valAt ([key] (get @cell key)) ([key missing] (get @cell key missing)))))

(deftest subvector-and-nested-custom-collections-never-get-reusable-proofs
  (let [cell (atom [:return [:var 8]]) body (mutable-vector-view cell)
        f {:params [] :body body} p {:entry f}]
    (is (= 9 (slots/program-slots p)))
    (is (nil? (cached p)))
    (reset! cell [:return [:var 77]])
    (is (= 78 (slots/program-slots p)))
    (is (= 78 (slots/function-slots f)))
    (is (nil? (cached p))))
  (let [base (program 3) cell (atom {:nested [:var 10]})
        custom (custom-map-view cell)
        f {:params [] :body [:return [:imm custom]]}]
    (slots/program-slots base)
    (let [extended (slots/append-functions base {:view f})]
      (is (nil? (cached extended)))
      (is (= 11 (slots/program-slots extended)))
      (reset! cell {:nested [:var 80]})
      (is (= 81 (slots/program-slots extended)))
      (is (nil? (cached extended))))))

(deftest custom-program-maps-keep-their-exact-fallback
  (let [base (sorted-map :entry (function 31))]
    (is (= 31 (slots/program-slots base)))
    (is (nil? (cached base)))
    (let [extended (slots/append-functions base {:second (function 52)})]
      (is (= (merge base {:second (function 52)}) extended))
      (is (nil? (cached extended)))
      (is (= 52 (slots/program-slots extended)))
      (is (nil? (cached extended))))))

(deftest native-installer-publishes-exact-delta-and-warm-width
  (let [old (program 41)
        candidate @install-test/initial-bundle]
    (slots/program-slots old)
    (with-program-scans
      (fn [calls]
        (let [installed (install/install (m/world old) candidate)
              functions (get-in installed [:world :functions])
              added (:new-functions installed)]
          (is (= #{install-test/answer install-test/boxed} (set (keys added))))
          (is (= (merge old added) functions))
          (is (identical? (:entry old) (:entry functions)))
          (is (some? (cached functions)))
          (is (= (slots/program-slots functions (slots/cache)) (slots/program-slots functions)))
          ;; The only global-cache miss work during install was the final delta;
          ;; the explicit custom-cache comparison above also measures the program.
          (is (= 2 (count @calls)))
          (is (identical? added (first @calls)))
          (is (= 42 (:result (m/run (m/start (:world installed) install-test/boxed [m/erased 42]) 100))))
          (is (= 42 (:result (mutable/freeze (mutable/run! (mutable/thaw
                          (m/start (:world installed) install-test/boxed [m/erased 42])) 100))))))))))

(deftest final-global-and-io-wrappers-participate-in-the-propagated-width
  (let [n (fn [s] ["str" ["anonymous"] s])
        root (n "newEntry") io-name (n "newIO")
        io-f (with-meta {:params [] :body [:return [:imm 0]]} {:runtime-param-types []})
        old {io-name io-f}
        row {:kind "decl" :name root :sourceLocal true :runtime {:role "ordinary"}
             :ir {:fdecl {:f root :xs [] :type "tobject" :body ["ret" "erased"]}}}
        manifest (-> (first (:manifests @install-test/initial-bundle))
                     (assoc :requestedRoots [root] :entryPoints [{:name root :boxedTarget root}])
                     (assoc-in [:initializationPlan :actions]
                               [{:meta false :action {:kind "io" :name io-name :target io-name}}]))
        candidate {:manifests [manifest] :declarations {root row}}]
    (slots/program-slots old)
    (let [installed (install/install (m/world old) candidate)
          added (:new-functions installed) final-functions (get-in installed [:world :functions])
          wrapper ["str" io-name "_ansatz_io_initializer"]]
      (is (= #{root wrapper} (set (keys added))))
      (is (= :begin-init (get-in added [wrapper :body 0])))
      (is (identical? (get added wrapper) (get final-functions wrapper)))
      (is (identical? io-f (get final-functions io-name)))
      (is (= (slots/program-slots final-functions (slots/cache)) (:slots (cached final-functions))))))
  ;; Genuine nullary-global fixture generates both runtime wrapper and its
  ;; unwrapped initializer, rather than propagating the pre-wrapper body width.
  (let [old (program 6)]
    (slots/program-slots old)
    (let [installed (install/install (m/world old) (slurp "fixtures/runtime-compiled-nullary.jsonl"))
          added (:new-functions installed) p (get-in installed [:world :functions])
          wrapper ["str" install-test/answer "_ansatz_global_initializer"]]
      (is (contains? added wrapper))
      (is (= :global (get-in added [install-test/answer :body 0])))
      (is (= (slots/program-slots p (slots/cache)) (:slots (cached p)))))))

(defn- base-with-cache-state [cache-state]
  (let [base (program 7)
        _ (when (not= cache-state :cold) (slots/program-slots base))
        fillers (when (= cache-state :evicted)
                  (mapv (fn [width] (let [p (program width)] (slots/program-slots p) p)) (range 20 37)))]
    (is (if (= cache-state :warm) (some? (cached base)) (nil? (cached base))))
    [base fillers]))

(deftest eager-final-addition-validation-does-not-depend-on-cache-state
  (doseq [bad [{:params (object-array [0]) :body [:return [:imm 0]]}
               {:params [] :body [:return [:imm (int-array [0])]]}
               {:params [] :body [:host "missing-destination"]}
               {:params [] :body [:join 2]}]]
    (let [failures
          (for [cache-state [:cold :warm :evicted]]
            (let [[base fillers] (base-with-cache-state cache-state)]
              (try (slots/append-functions base {:bad bad}) :unexpected-success
                   (catch Exception error [(class error) (.getMessage error)])
                   (finally (java.lang.ref.Reference/reachabilityFence fillers)))))]
      (is (not-any? #{:unexpected-success} failures))
      (is (apply = failures))))
  ;; Even a replacement or custom-map fallback validates final additions now;
  ;; it cannot silently admit a mutable program merely because no proof propagates.
  (doseq [base [(program 7) (sorted-map :entry (function 7))]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"mutable program collections"
                         (slots/append-functions base {:entry {:params [] :body [:return [:imm (int-array [0])]]}})))))

(deftest global-proof-and-append-never-hash-deep-code-or-body-values
  (let [poison (proxy [Object] [] (hashCode [] (throw (AssertionError. "Body hash is forbidden"))))
        body (loop [n 10000 body [:return [:var 88]]]
               (if (zero? n) body (recur (dec n) [:let 1 [:literal poison] body])))
        base (program 3) addition {:deep {:params [] :body body}}]
    (slots/program-slots base)
    (let [extended (slots/append-functions base addition)]
      (is (= 89 (slots/program-slots extended)))
      (is (= 3 (slots/program-slots base)))
      (is (= 89 (:slots (cached extended)))))))

(defn- extern-candidate [root]
  (let [all ["str" ["anonymous"] "all"]
        row {:kind "decl" :name root :sourceLocal true :runtime {:role "ordinary"}
             :ir {:extern {:f root :xs [] :type "tobject"
                           :ext {:entries [{:standard {:backend all :fn "slot_test_extern"}}]}}}}]
    {:manifests [(assoc (first (:manifests @install-test/initial-bundle))
                        :requestedRoots [root] :entryPoints [{:name root :boxedTarget root}])]
     :declarations {root row}}))

(deftest installer-rejects-invalid-trusted-lowering-independent-of-cache-state
  (let [root ["str" ["anonymous"] "badTrustedBody"] candidate (extern-candidate root)]
    (doseq [bad [{:params [] :body [:return [:imm (int-array [0])]]}
                 {:params [] :body [:host "missing-destination"]}]]
      (let [failures
            (for [cache-state [:cold :warm :evicted]]
              (let [[base fillers] (base-with-cache-state cache-state) world (m/world base)]
                (try
                  (install/install world candidate {:lower-extern (fn [_] [root bad])})
                  :unexpected-success
                  (catch Exception error [(class error) (.getMessage error)])
                  (finally (java.lang.ref.Reference/reachabilityFence fillers)))))]
        (is (not-any? #{:unexpected-success} failures))
        (is (apply = failures))
        (is (not-any? #(contains? (.get ^WeakReference (:program %)) root) @(cache-atom)))))))

(deftest rewritten-global-target-carries-the-highest-register
  (let [root ["str" ["anonymous"] "wideGlobal"] target ["str" root "_ansatz_global_initializer"]
        base (program 3)
        lowered {:params [] :global-role :value :body [:let 500 [:literal 42] [:return [:var 500]]]}]
    (slots/program-slots base)
    (let [installed (install/install (m/world base) (extern-candidate root)
                                     {:lower-extern (fn [_] [root lowered])})
          final (get-in installed [:world :functions])]
      (is (= :global (get-in final [root :body 0])))
      (is (= :let (get-in final [target :body 0])))
      (is (= 501 (:slots (cached final))))
      (is (= 501 (slots/program-slots final)))
      (is (= 42 (:result (m/run (m/start (:world installed) root []) 100)))))))
