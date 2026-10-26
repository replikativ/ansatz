(ns prototype.typed-blocks-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.java.io :as io]
            [prototype.typed-blocks :as b]
            [prototype.import-ir :as ir]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.lazy-runtime :as lazy]))

(def profile {:schema "lean-block-profile/1" :producer-commit "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
              :phase :expanded-rc :word-bits 64 :layout :lean-64
              :abi-generation "ansatz-runtime/1" :target :jvm})
(def budgets {:max-functions 30 :max-instructions 2000 :max-blocks 3000 :max-work 50000 :max-registers 2000})
(defn name-of [s] ["str" ["anonymous"] s])
(defn p [id ty] {:x {:idx id} :ty ty :borrow false})
(defn arg [id] {:var {:id {:idx id}}})
(defn ret [id] ["ret" (arg id)])
(defn row [label params result body]
  {:name (name-of label) :ir {:fdecl {:f (name-of label) :xs params :type result :info {} :body body}}})
(defn selected [rows] (into {} (map ir/lower-typed-declaration) rows))
(defn prepare [fs roots] (b/prepare-unit fs (mapv name-of roots) profile {} budgets))
(defn invalid? [f] (try (f) false (catch clojure.lang.ExceptionInfo e (:typed-block-validation (ex-data e)))))
(def callee (row "callee" [(p 0 "uint8")] "uint8" (ret 0)))
(def tail-row (row "tail" [(p 0 "uint8")] "uint8"
                   ["vdecl" {:idx 1} "uint8" {:fap {:c (name-of "callee") :ys [(arg 0)]}} (ret 1)]))
(def main-row
  (row "main" [(p 0 "uint8") (p 1 "uint8")] "uint8"
       ["jdecl" {:idx 2} [(p 3 "uint8") (p 4 "uint8")] (ret 3)
        ["case" (name-of "UInt8") {:idx 0} "uint8"
         [["ctor" {:cidx 0}
           ["vdecl" {:idx 5} "uint8" {:lit {:v {:num {:v 9}}}}
            ["vdecl" {:idx 6} "uint8" {:fap {:c (name-of "callee") :ys [(arg 5)]}}
             ["jmp" {:idx 2} [(arg 6) (arg 1)]]]]]
          ["default" ["jmp" {:idx 2} [(arg 1) (arg 0)]]]]]]))

(deftest typed-canonical-blocks-and-tail-origins
  (let [fs (selected [callee main-row tail-row]) {:keys [status unit]} (prepare fs ["main" "tail"])
        f (get-in unit [:functions (name-of "main")])
        tail (get-in unit [:functions (name-of "tail")])
        join (first (filter #(= :join (get-in % [:terminator :op])) (:blocks f)))
        jump (first (filter #(= :jump (get-in % [:terminator :op])) (:blocks f)))]
    (is (= :ready status))
    (is (= 3 (count (:functions unit))))
    (is (= {0 "uint8" 1 "uint8"} (get-in join [:terminator :join :captures])))
    (is (= [3 4] (mapv :id (get-in join [:terminator :join :params]))))
    (is (= :simultaneous (get-in jump [:terminator :transfer])))
    (is (= :canonical-registers (get-in join [:params :kind])))
    (is (= 1 (count (:instructions tail))))
    (is (= 2 (count (get-in tail [:origins 0 :producer-node-ids]))))
    (is (= (get-in fs [(name-of "tail") :body]) (b/legacy-body tail)))
    (is (= (get-in fs [(name-of "main") :typed-ir :source-key]) (:source-key f)))))

(def ^:dynamic *jvm-program* nil)
(defn backend-run [backend fs initial fuel]
  (case backend
    :reference (m/run initial fuel)
    :mutable (u/freeze (u/run! (u/thaw initial) fuel))
    :jvm (u/freeze (lazy/run! (or *jvm-program* (lazy/open-program fs)) (u/thaw initial) fuel))))

(deftest actual-table-reconstruction-every-prefix-and-saved-siblings
  (let [fs (selected [callee main-row tail-row]) unit (:unit (prepare fs ["main" "tail"]))
        rebuilt (reduce-kv (fn [fs name f] (assoc-in fs [name :body] (b/legacy-body f))) fs (:functions unit))]
    (is (= fs rebuilt))
    (binding [*jvm-program* (lazy/open-program rebuilt)]
     (doseq [[label args] [["main" [0 7]] ["main" [1 8]] ["tail" [13]]]
            fuel (range 12)]
      (let [initial (m/start (m/world fs) (name-of label) args)
            expected (m/run initial fuel)]
        (doseq [backend [:reference :mutable :jvm]]
          (let [actual (backend-run backend rebuilt (m/start (m/world rebuilt) (name-of label) args) fuel)]
            (is (= expected actual))
            (when (= :paused (:status actual))
              (let [saved actual left (backend-run backend rebuilt (m/resume saved nil) 30)
                    right (backend-run backend rebuilt (m/resume saved nil) 30)]
                (is (= (m/run initial) left right))
                (is (= expected saved)))))))))))

(deftest lexical-invalidity-and-malformed-shapes
  (doseq [r [(row "bad" [(p 0 "uint8")] "uint8" (ret 9))
             (row "bad" [(p 0 "uint8")] "uint8" ["jdecl" {:idx 1} [] ["jmp" {:idx 1} []] (ret 0)])
             (row "bad" [(p 0 "uint8")] "uint8" ["jdecl" {:idx 1} [(p 0 "uint8")] (ret 0) (ret 0)])
             (row "bad" [(p 0 "uint8")] "uint8" ["vdecl" {:idx 1} "uint8" {:fap {:c (name-of "callee") :ys []}} (ret 1)])]]
    (is (invalid? #(prepare (selected [callee r]) ["bad"]))))
  (let [fs (selected [callee]) n (name-of "callee")]
    (doseq [body [[:return [:var 0 :extra]] [:return [:var 0] :extra]]]
      (is (invalid? #(prepare (assoc-in fs [n :body] body) ["callee"]))))))

(deftest optimization-fallback-is-not-source-rejection
  (doseq [[r reason] [[(row "unsupported" [(p 0 "object")] "object"
                            ["vdecl" {:idx 1} "uint8" {:isShared {:x {:idx 0}}} (ret 0)]) :unsupported-literal]
                      [(row "unsupported" [(p 0 "uint8")] "uint64" (ret 0)) :type-compatibility]
                      [(row "unsupported" [] "uint8" ["vdecl" {:idx 0} "uint8" {:lit {:v {:num {:v 256}}}} (ret 0)]) :literal-range]
                      [(row "unsupported" [(p 0 "uint64")] "uint64"
                            ["case" (name-of "UInt64") {:idx 0} "uint64" [["default" (ret 0)]]]) :non-scalar-case]]]
    (is (= reason (:reason (prepare (selected [r]) ["unsupported"])))))
  (let [fs (selected [callee])]
    (is (= :missing-companion (:reason (prepare (update fs (name-of "callee") dissoc :typed-ir) ["callee"]))))))

(deftest bounded-demand-and-deep-stack-safe-reconstruction
  (let [fs (assoc (selected [callee]) (name-of "unrequested") {:typed-ir :invalid})]
    (is (= :ready (:status (prepare fs ["callee"]))))
  (doseq [[key limit] [[:max-functions 1] [:max-instructions 1] [:max-blocks 1] [:max-work 1]]]
    (is (= :budget (:reason (b/prepare-unit (selected [main-row callee]) [(name-of "main")] profile {} (assoc budgets key limit))))))
  (is (= :register-budget (:reason (b/prepare-unit (selected [(row "callee" [(p 1 "uint8")] "uint8" (ret 1))]) [(name-of "callee")] profile {} (assoc budgets :max-registers 1)))))
  (let [body (reduce (fn [body id] ["vdecl" {:idx id} "uint8" {:lit {:v {:num {:v 1}}}} body]) (ret 0) (range 1 1001))
        fs (selected [(row "deep" [(p 0 "uint8")] "uint8" body)])
        result (prepare fs ["deep"]) f (get-in result [:unit :functions (name-of "deep")])]
    (is (= :ready (:status result)))
    (is (= 1001 (count (:instructions f))))
    ;; Equality itself recursively walks vectors; compare stack-safely through
    ;; a second bounded preparation rather than a deep structural = call.
    (is (= 1001 (count (:instructions (get-in (prepare (assoc-in fs [(name-of "deep") :body] (b/legacy-body f)) ["deep"])
                                              [:unit :functions (name-of "deep")]))))))))

(deftest intrinsic-boundaries-retain-exact-demanded-descriptors
  (let [fs (selected [tail-row]) desc {:params [{:id 0 :type "uint8" :borrow false}]
                                     :result-type "uint8" :generation "test/1" :extern "lean_test_identity"}
        r (b/prepare-unit fs [(name-of "tail")] profile {(name-of "callee") desc (name-of "unused") :invalid} budgets)]
    (is (= :ready (:status r)))
    (is (= {(name-of "callee") desc} (get-in r [:unit :intrinsics])))
    (is (= :tail (get-in r [:unit :functions (name-of "tail") :blocks 0 :terminator :op])))))

(deftest actual-selected-producer-scalar-declarations
  (let [path (io/file "fixtures/scalar.jsonl") path (if (.exists path) path (io/file "experiments/lean-ir/fixtures/scalar.jsonl"))
        rows (with-open [r (io/reader path)]
               (into [] (comp (map #(json/read-str % :key-fn keyword))
                              (filter #(and (:name %) (contains? #{"ScalarProbe.identity8" "ScalarProbe.identity64"} (ir/name-label (:name %))))))
                     (line-seq r)))
        fs (selected rows) result (b/prepare-unit fs (vec (keys fs)) profile {} budgets)]
    (is (= 2 (count rows)))
    (is (= :ready (:status result)))
    (doseq [[name f] (get-in result [:unit :functions])]
      (is (= (get-in fs [name :body]) (b/legacy-body f))))))

(deftest bounded-shared-terminal-dag-and-distinct-binding-sites
  (let [leaf (ret 0)
        body (nth (iterate #(vector "case" (name-of "UInt8") {:idx 0} "uint8"
                                    [["ctor" {:cidx 0} %] ["default" %]]) leaf) 27)
        fs (selected [(row "dag" [(p 0 "uint8")] "uint8" body)])
        r (b/prepare-unit fs [(name-of "dag")] profile {} (assoc budgets :max-blocks 100))]
    (is (= :budget (:reason r)))
    (is (= :max-blocks (get-in r [:details :budget]))))
  (let [leaf (ret 0) fs (selected [(row "shared" [(p 0 "uint8")] "uint8"
                                      ["case" (name-of "UInt8") {:idx 0} "uint8"
                                       [["ctor" {:cidx 0} leaf] ["default" leaf]]])])
        f (get-in (prepare fs ["shared"]) [:unit :functions (name-of "shared")])]
    (is (= 2 (count (:instructions f))))
    (is (= 3 (count (:blocks f))))
    (is (= [1 1] (get-in f [:instructions 0 :children]))))
  (let [shared ["vdecl" {:idx 1} "uint8" {:lit {:v {:num {:v 2}}}} (ret 0)]
        fs (selected [(row "bad" [(p 0 "uint8")] "uint8"
                           ["case" (name-of "UInt8") {:idx 0} "uint8"
                            [["ctor" {:cidx 0} shared] ["default" shared]]])])]
    (is (invalid? #(prepare fs ["bad"])))))

(defn graph-tuples [function]
  (mapv (fn [{:keys [id pc terminator]}]
          [id pc (:op terminator)
           (case (:op terminator)
             :join [(get-in terminator [:join :block]) (:block terminator)]
             :case (mapv (fn [[tag edge]] [tag (:block edge)]) (:alternatives terminator))
             (:next :call :jump) (:block terminator)
             nil)]) (:blocks function)))

(defn check-graph [function]
  (let [blocks (:blocks function) table (:instructions function)
        pc-of #(get-in blocks [% :pc])
        declarations (into {} (keep (fn [block] (let [t (:terminator block)]
                                                (when (= :join (:op t)) [(:join-id t) (:join t)])))) blocks)]
    (doseq [{:keys [pc scope params ops terminator]} blocks]
      (let [[op a b c] (get-in table [pc :form]) children (get-in table [pc :children]) t terminator]
        (is (= {:kind :canonical-registers :types scope} params))
        (case op
          :let (do (is (= [{:pc pc :op :literal :id a :type (get-in blocks [(:block t) :scope a]) :value (second b)}] ops))
                   (is (= :next (:op t)))
                   (is (= {:kind :identity-registers} (:args t)))
                   (is (= children [(pc-of (:block t))])))
          :call (do (is (= [:call a b c] [(:op t) (:dest t) (:target t) (:args t)]))
                    (is (= children [(pc-of (:block t))]))
                    (is (= (assoc scope a (:type t)) (get-in blocks [(:block t) :scope])))
                    (is (= {:kind :call-result :dest a :preserve :identity-registers} (:continuation-args t))))
          :tail (is (= [:tail a b] [(:op t) (:target t) (:args t)]))
          :return (is (= [:return a] [(:op t) (:value t)]))
          :case (do (is (= a (:value t)))
                    (is (= (mapv first b) (mapv first (:alternatives t))))
                    (is (= children (mapv (fn [[_ edge]] (pc-of (:block edge))) (:alternatives t)))))
          :join (let [j (:join t)]
                  (is (= a (:join-id t))) (is (= b (mapv :id (:params j))))
                  (is (= children [(pc-of (:block j)) (pc-of (:block t))]))
                  (is (= scope (:captures j)))
                  (is (= (into scope (map (juxt :id :type)) (:params j)) (get-in blocks [(:block j) :scope])))
                  (is (= scope (get-in blocks [(:block t) :scope]))))
          :jump (let [j (get declarations a)]
                  (is (= a (:join-id t))) (is (= b (:args t)))
                  (is (= (:block j) (:block t))) (is (= (:captures j) (:captures t)))
                  (is (= :simultaneous (:transfer t)))))))))

(deftest block-graph-has-independent-canonical-edge-oracle
  (let [fs (selected [main-row callee tail-row]) unit (:unit (prepare fs ["main" "tail"]))
        main (get-in unit [:functions (name-of "main")])]
    (is (= [[0 0 :join [1 2]] [1 1 :return nil] [2 2 :case [[0 3] [:default 4]]]
            [3 3 :next 5] [4 4 :jump 1] [5 5 :call 6] [6 6 :jump 1]] (graph-tuples main)))
    (is (= {0 "uint8" 1 "uint8" 5 "uint8"} (get-in main [:blocks 5 :scope])))
    (is (= {0 "uint8" 1 "uint8" 5 "uint8" 6 "uint8"} (get-in main [:blocks 6 :scope])))
    (doseq [[_ f] (:functions unit)] (check-graph f))))

(deftest nested-join-captures-and-outer-scope
  (let [r (row "nested" [(p 0 "uint8")] "uint8"
               ["jdecl" {:idx 1} [(p 2 "uint8")] (ret 2)
                ["vdecl" {:idx 3} "uint8" {:lit {:v {:num {:v 9}}}}
                 ["jdecl" {:idx 4} [(p 5 "uint8")] ["jmp" {:idx 1} [(arg 5)]]
                  ["jmp" {:idx 4} [(arg 3)]]]]])
        fs (selected [r]) result (prepare fs ["nested"])
        f (get-in result [:unit :functions (name-of "nested")])
        joins (filter #(= :join (get-in % [:terminator :op])) (:blocks f))]
    (is (= :ready (:status result)))
    (is (= [[0 0 :join [1 2]] [1 1 :return nil] [2 2 :next 3] [3 3 :join [4 5]]
            [4 4 :jump 1] [5 5 :jump 4]] (graph-tuples f)))
    (check-graph f)
    (is (= [{0 "uint8"} {0 "uint8" 3 "uint8"}]
           (mapv #(get-in % [:terminator :join :captures]) joins)))
    (let [rebuilt (assoc-in fs [(name-of "nested") :body] (b/legacy-body f))]
      (doseq [fuel (range 8)]
        (is (= (m/run (m/start (m/world fs) (name-of "nested") [4]) fuel)
               (m/run (m/start (m/world rebuilt) (name-of "nested") [4]) fuel)))))))

(deftest malformed-companions-and-case-profiles
  (let [fs (selected [callee]) n (name-of "callee")]
    (doseq [[path value] [[[:typed-ir :nodes 0 :op] :jmp]
                         [[:typed-ir :root] 20]
                         [[:typed-ir :source-key] ["invalid" #{}]]
                         [[:typed-ir :source-key] [(apply str (repeat 64 "a")) #{(Object.)}]]]]
      (is (invalid? #(prepare (assoc-in fs (into [n] path) value) ["callee"])))))
  (doseq [alts [[["default" (ret 0)] ["ctor" {:cidx 0} (ret 0)]]
                [["ctor" {:cidx 0} (ret 0)] ["ctor" {:cidx 0} (ret 0)]]]]
    (let [fs (selected [(row "case" [(p 0 "uint8")] "uint8" ["case" (name-of "UInt8") {:idx 0} "uint8" alts])])]
      (is (= :unsupported-case-profile (:reason (prepare fs ["case"])))))))
