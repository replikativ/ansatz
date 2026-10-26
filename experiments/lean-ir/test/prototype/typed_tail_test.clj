(ns prototype.typed-tail-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.java.io :as io]
            [clojure.data.json :as json]
            [prototype.machine :as m]
            [pattern.nanopass.dialect :as dialect]
            [prototype.typed-tail :as tail]
            [prototype.typed-blocks :as blocks]
            [prototype.scalar-wrapper-test :as fixture]
            [prototype.import-ir :as ir]
            [prototype.runtime-abi :as abi]))

(def budgets {:max-functions 16 :max-instructions 4096 :max-blocks 4096 :max-work 200000
              :max-registers 65536 :max-params 16 :max-emission 8192 :max-constants 8192 :max-chunk-cost 2048})
(def fixture-dir
  (first (filter #(.exists (io/file % "typed-tail-programs.jsonl"))
                 [(io/file "fixtures") (io/file "experiments/lean-ir/fixtures")
                  (io/file (.getParentFile (.getParentFile (.getParentFile (.getAbsoluteFile (io/file *file*))))) "fixtures")])))
(defn read-rows [file]
  (with-open [r (io/reader (io/file fixture-dir file))]
    (into [] (map #(json/read-str % :key-fn keyword)) (line-seq r))))
(defn bundle [file]
  (let [rows (rest (read-rows file))]
    {:runtime (into {} (map abi/lower) rows)
     :typed (into {} (comp (filter #(get-in % [:ir :fdecl])) (map ir/lower-typed-declaration)) rows)
     :descriptors (into {} (keep (fn [row] (when-let [d (abi/describe-scalar row fixture/profile)] [(:name d) d]))) rows)}))
(defn prepare [{:keys [runtime typed descriptors]}]
  (tail/prepare-region runtime typed (vec (keys typed)) descriptors fixture/profile budgets))
(defn target [fs label] (first (filter #(= label (last %)) (keys fs))))
(defn name-of [s] ["str" ["anonymous"] s])
(defn parameter [id ty] {:x {:idx id} :ty ty :borrow false})
(defn var-arg [id] {:var {:id {:idx id}}})
(defn return-node [id] ["ret" (var-arg id)])
(defn row [label body]
  {:name (name-of label) :ir {:fdecl {:f (name-of label) :xs [(parameter 0 "uint64")]
                                     :type "uint64" :info {} :body body}}})
(defn small-bundle [r]
  {:runtime (into {} [(ir/lower-declaration r)]) :typed (into {} [(ir/lower-typed-declaration r)]) :descriptors {}})

(deftest pattern-lowering-shapes-and-domain-separation
  (let [o [(name-of "test") 0]
        forms [[:literal o 1 "uint64" 7]
               [:intrinsic o 2 "uint64" :unsigned64 :add (name-of "add") [[:var 0] [:var 1]] :unsigned-bigint]
               [:case o [[:var 0]] [[0 1] [:default 2]]]
               [:tail o (name-of "test") [[:var 0]]]
               [:tail-intrinsic o "uint8" :unsigned64 :eq (name-of "eq") [[:var 0] [:var 1]] :long]
               [:return o [[:var 0]]]]]
    (doseq [form forms]
      (is (dialect/valid? tail/TypedTailOp form))
      (is (dialect/valid? tail/RepresentedTailOp (tail/lower-operation! form))))
    (is (= [:literal o 1 [:repr "uint64" :long-bits] 7 [:carrier :literal]] (tail/lower-operation! (first forms))))
    (doseq [bad [(assoc-in (first forms) [2] -1)
                 (assoc-in (second forms) [4] :signed64)
                 (assoc-in (second forms) [5] :mul)]]
      (is (thrown? clojure.lang.ExceptionInfo (tail/lower-operation! bad)))))
  (is (nil? (find-ns 'pattern.llvm)))
  (is (nil? (find-ns 'pattern.llvm.graph))))

(deftest actual-sums-typed-origin-traces-costs-and-semantic-keys
  (let [input (bundle "scalar-wrapper-programs.jsonl") result (prepare input) region (:region result)]
    (is (= :ready (:status result)))
    (is (= 2 (count (:functions region))))
    (is (= 6 (count (:descriptors region))))
    (is (= #{13} (set (map :max-cost (vals (:functions region))))))
    (is (= 2 (count (:components region))))
    (doseq [[name f] (:functions region)]
      (is (= (get-in (:runtime input) [name :body])
             (blocks/legacy-body {:entry-pc (:entry-pc f) :instructions (:canonical-instructions f)})))
      (is (empty? (second (get-in region [:typed-code-keys name]))))
      (doseq [b (:blocks f)]
        (is (= (:cost b) (count (:trace b))))
        (is (dialect/valid? tail/RepresentedTailOp (:operation b)))
        (when (= :intrinsic (first (:typed-operation b)))
          (is (= 3 (:cost b)))
          (is (= 1 (:logical-frame-peak b)))
          (is (= [:call :runtime :return] (mapv :event (:trace b)))))))
    (is (empty? (second (:key region))))))

(defn reason [input] (:reason (prepare input)))

(deftest actual-mutual-tail-and-other-shapes-are-generic
  (let [input (bundle "typed-tail-programs.jsonl")
        result (prepare input)
        region (:region result)
        fs (:functions region)
        a (target fs "bounceA") b (target fs "bounceB")
        constant (get fs (target fs "constant64"))
        identity (get fs (target fs "identity64"))]
    (is (= :ready (:status result)))
    (is (= 7 (count fs)))
    (is (some #{#{a b}} (map set (:components region))))
    (is (= [2 3] (mapv #(count (:params (get fs %))) [a b])))
    (is (= :return (first (:typed-operation (first (:blocks identity))))))
    (is (some #(= :literal (get-in % [:carrier :kind])) (:blocks constant)))
    (doseq [label ["terminalAdd" "terminalEq"]]
      (let [f (get fs (target fs label))
            b (first (:blocks f))
            origin-ids (get-in f [:origins (:pc b) :producer-node-ids])]
        (is (= :tail-intrinsic (first (:typed-operation b))))
        (is (= 3 (:cost b)))
        (is (zero? (:logical-frame-peak b)))
        (is (= 2 (count origin-ids)))))
    ;; Reference execution checks native fixtures; the new graph is not executed.
    (let [path (io/file fixture-dir "typed-tail-program-values.json")
          cases (:cases (json/read-str (slurp path) :key-fn keyword))]
      (is (= 9 (count cases)))
      (doseq [{:keys [function args result]} cases]
        (let [start (m/start (m/world (:runtime input)) (target fs function) (mapv fixture/carrier args))]
          (is (= (bigint result) (:result (m/run start)))))))))

(deftest installed-code-and-descriptor-profile-proof
  (let [input (bundle "scalar-wrapper-programs.jsonl")
        [name _] (first (:descriptors input))
        bad (assoc-in input [:runtime name :body] [:return [:imm 0]])
        bad-profile (assoc-in input [:descriptors name :profile :abi-generation] "other/2")
        unused (name-of "unused")
        d (-> (get-in input [:descriptors name])
              (assoc :name unused) (assoc-in [:profile :abi-generation] "other/2"))
        unused-input (assoc-in input [:descriptors unused] d)]
    (is (= :runtime-code-mismatch (reason bad)))
    (is (= :descriptor-profile-mismatch (reason bad-profile)))
    (is (= :ready (:status (prepare unused-input)))))
  (let [body ["vdecl" {:idx 1} "uint64" {:lit {:v {:num {:v 7}}}} (return-node 1)]
        input (small-bundle (row "constant" body))
        name (name-of "constant")
        changed (assoc-in input [:runtime name :body 2 1] 7N)]
    (is (= (get-in input [:runtime name :body]) (get-in changed [:runtime name :body])))
    (is (= :runtime-code-mismatch (reason changed)))))

(deftest owner-free-boundaries-and-metadata
  (let [input (small-bundle (row "identity" (return-node 0)))
        name (name-of "identity") owner (Object.)
        original (get-in input [:typed name])
        altered (assoc-in input [:typed name] (with-meta original {:owner owner}))
        result (prepare altered) region (:region result)]
    (is (= :ready (:status result)))
    (let [extra (-> input (assoc-in [:runtime :unrequested] owner) (assoc-in [:typed :unrequested] owner))
          chosen (tail/prepare-region (:runtime extra) (:typed extra) [name] {} fixture/profile budgets)]
      (is (= :ready (:status chosen)))
      (is (= #{name} (set (keys (get-in chosen [:region :dependencies]))))))
    (is (nil? (meta (get-in region [:dependencies name]))))
    (is (empty? (second (:key region))))
    (is (= :opaque-code-data (reason (assoc-in input [:typed name :opaque] owner))))
    (doseq [index [2 4 5]]
      (let [args [(:runtime input) (:typed input) [name] {} fixture/profile budgets]
            changed (assoc args index (with-meta (nth args index) {:owner owner}))
            result (apply tail/prepare-region changed)]
        (is (= :opaque-code-data (:reason result)))))))

(deftest unsupported-control-and-malformed-scopes-remain-explicit
  ;; M2 now preserves these facts; scalar representation must decline BEFORE
  ;; Pattern sees an unsupported RC operation or object-family literal.
  (doseq [[body expected] [[["inc" {:idx 0} 1 true false (return-node 0)] :unsupported-rc]
                           [["vdecl" {:idx 1} "tagged" {:lit {:v {:num {:v 7}}}} (return-node 0)] :non-scalar-local]]]
    (let [input (small-bundle (row "new-facts" body)) calls (atom 0)]
      (with-redefs [tail/lower-operation! (fn [_] (swap! calls inc) (throw (ex-info "Pattern should not run" {})))]
        (is (= expected (reason input))))
      (is (zero? @calls))))
  (let [joined ["jdecl" {:idx 1} [(parameter 2 "uint64")] (return-node 2)
                ["jmp" {:idx 1} [(var-arg 0)]]]
        input (small-bundle (row "join" joined))]
    (is (= :unsupported-control (reason input))))
  (is (thrown? clojure.lang.ExceptionInfo
               (prepare (small-bundle (row "invalid" (return-node 99))))))
  (let [identity (row "callee" (return-node 0))
        caller (row "caller" ["vdecl" {:idx 1} "uint64"
                               {:fap {:c (name-of "callee") :ys [(var-arg 0)]}}
                               ["vdecl" {:idx 2} "uint64" {:lit {:v {:num {:v 1}}}} (return-node 2)]])
        input {:runtime (into {} (map ir/lower-declaration) [identity caller])
               :typed (into {} (map ir/lower-typed-declaration) [identity caller]) :descriptors {}}]
    (is (= :non-intrinsic-call (reason input)))))

(deftest work-cost-constant-and-parameter-limits
  (let [input (bundle "scalar-wrapper-programs.jsonl")]
    (doseq [[key n] [[:max-work 1] [:max-constants 1] [:max-emission 1]
                    [:max-chunk-cost 1] [:max-params 1]]]
      (let [result (tail/prepare-region (:runtime input) (:typed input) (vec (keys (:typed input)))
                                        (:descriptors input) fixture/profile (assoc budgets key n))]
        (is (= :fallback (:status result))))))
  (let [body (reduce (fn [body id] ["vdecl" {:idx id} "uint64" {:lit {:v {:num {:v 1}}}} body])
                     (return-node 0) (range 1 1001))
        result (prepare (small-bundle (row "deep" body)))
        f (get-in result [:region :functions (name-of "deep")])]
    (is (= :ready (:status result)))
    (is (= 1001 (:max-cost f)))
    (is (= 1001 (count (:blocks f))))
    (is (empty? (second (get-in result [:region :key]))))))

(deftest bounded-natural-id-carriers-remain-compatible
  (let [r (assoc-in (row "bigint-id" (return-node 0N)) [:ir :fdecl :xs 0 :x :idx] 0N)
        result (prepare (small-bundle r))]
    (is (= :ready (:status result)))
    (is (= 0N (get-in result [:region :functions (name-of "bigint-id") :params 0 :id])))))
