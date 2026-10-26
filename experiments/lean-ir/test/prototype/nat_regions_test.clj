(ns prototype.nat-regions-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.nat-preparation-test :as fixture]
            [prototype.scalar-wrapper-test :as scalar-fixture]
            [prototype.runtime-abi :as abi]
            [prototype.scalar-wrapper :as wrapper]
            [prototype.typed-tail :as tail]
            [prototype.typed-tail-execution-test]))

(defn nat-input []
  (let [names (set (map #(fixture/name-of "Nat" %) ["add" "sub" "decEq"]))
        rows (fixture/actual-rows "module-import-bulk.jsonl" names)]
    {:rows rows :functions (into {} (map abi/lower) (vals rows))
     :descriptors (into {} (map (fn [[name row]] [name (abi/describe-scalar row scalar-fixture/profile)])) rows)}))

(deftest actual-nat-descriptors-and-guarded-operation-data
  (let [{:keys [descriptors]} (nat-input)]
    (is (= 3 (count descriptors)))
    (doseq [[name d] descriptors]
      (is (= d (abi/validate-scalar-description! d)))
      (is (= :nat (:domain d)))
      (is (= :nonnegative-long (:lane d)))
      (is (= "nat-wrapper/1" (:semantic-generation d)))
      (is (= [true true] (mapv :borrow (:params d))))
      (is (= ["tobject" "tobject"] (mapv :type (:params d))))
      (is (= :long (:result-carrier (abi/scalar-operation (:extern d)))))
      (is (= (if (= "decEq" (last name)) "uint8" "tobject") (:result-type d))))
    (is (= :nat-sub (:runtime-operation (abi/scalar-operation "lean_nat_sub"))))
    (is (nil? (abi/scalar-operation "lean_nat_abs")))))

(deftest nat-descriptors-do-not-enter-the-wrapping-unsigned-tier
  (let [{:keys [functions descriptors]} (nat-input)
        options (wrapper/prepare-options {:scalar-wrappers descriptors})]
    (doseq [[name _] descriptors :let [body (get-in functions [name :body])]]
      (is (nil? (wrapper/descriptor-for functions body options)))
      (is (nil? (wrapper/extension-key functions body options)))
      (is (nil? (wrapper/compile-wrapper functions body options))))))

(deftest nat-and-unsigned-descriptor-generations-stay-distinct
  (let [d (get-in (nat-input) [:descriptors (fixture/name-of "Nat" "add")])]
    (doseq [bad [(assoc d :domain :unsigned64) (assoc d :lane :long-bits)
                 (assoc d :semantic-generation "unsigned-wrapper/1")
                 (assoc d :semantic-generation "unsigned-wrapper/2")
                 (assoc-in d [:params 0 :borrow] false)]]
      (is (thrown? clojure.lang.ExceptionInfo (abi/validate-scalar-description! bad)))))
  (doseq [[_ d] @scalar-fixture/descriptions]
    (is (= d (abi/validate-scalar-description! d)))
    (is (= (assoc d :semantic-generation "unsigned-wrapper/1")
           (abi/validate-scalar-description! (assoc d :semantic-generation "unsigned-wrapper/1"))))))

(deftest pattern-nat-forms-keep-domain-and-lane-explicit
  (let [origin [(fixture/name-of "test") 0]
        operands [[:var 0] [:var 1]]
        forms [[:nat-literal origin 2 "tagged" 1]
               [:intrinsic origin 3 "tobject" :nat :add (fixture/name-of "Nat" "add") operands :long]
               [:intrinsic origin 4 "uint8" :nat :eq (fixture/name-of "Nat" "decEq") operands :long]
               [:rc origin :inc 0 1 true false "tobject"]]]
    (is (= [:literal origin 2 [:repr "tagged" :nonnegative-long] 1 [:carrier :literal]]
           (tail/lower-operation! (nth forms 0))))
    (is (= [:repr "tobject" :nonnegative-long] (nth (tail/lower-operation! (nth forms 1)) 3)))
    (is (= [:repr "uint8" :long-bits] (nth (tail/lower-operation! (nth forms 2)) 3)))
    (is (= [:rc origin :inc 0 1 true false [:repr "tobject" :nonnegative-long] [:proof :nonreference]]
           (tail/lower-operation! (nth forms 3))))))

(defn nat-program [] (prototype.typed-tail-test/bundle "nat-region-programs.jsonl"))
(defn fast-roots [input]
  (filterv #(contains? #{"sum" "identityNat" "constantNat" "subtract"} (last %)) (vec (keys (:typed input)))))
(defn prepare-program [input roots]
  (tail/prepare-region (:runtime input) (:typed input) roots (:descriptors input)
                       scalar-fixture/profile prototype.typed-tail-test/budgets))

(deftest actual-nat-data-records-per-function-refinements-and-canonical-traces
  (let [input (nat-program) result (prepare-program input (fast-roots input)) region (:region result)
        name #(prototype.typed-tail-test/target (:typed input) %)
        sum (get-in region [:functions (name "sum")])
        identity (get-in region [:functions (name "identityNat")])
        constant (get-in region [:functions (name "constantNat")])
        subtract (get-in region [:functions (name "subtract")])]
    (is (= :ready (:status result)))
    (is (= "lean-represented-tail/2" (:schema region)))
    (is (= "typed-tail/2" (:preparation-generation region)))
    (is (= 4 (count (:functions region))))
    (is (= 3 (count (:descriptors region))))
    (is (= [15 2 2 3] (mapv :max-cost [sum identity constant subtract])))
    (is (= [false false] (mapv :borrow (:params sum))))
    (is (= [true] (mapv :borrow (:params identity))))
    (is (= :entry-guard (get-in sum [:representations 2 :proof :kind])))
    (is (= :literal (get-in constant [:representations 2 :proof :kind])))
    (is (= "tagged" (get-in constant [:representations 2 :ir-type])))
    (is (= :entry-guard (get-in constant [:representations 1 :proof :kind])))
    (is (= [0 Long/MAX_VALUE] (get-in constant [:representations 1 :proof :range])))
    (is (= :checked-small-add (get-in sum [:representations 7 :proof :condition])))
    (is (= [:proof :nonreference] (last (:operation (first (:blocks identity))))))
    (is (= [:inc :return] (mapv :event (mapcat :trace (:blocks identity)))))
    (doseq [[name f] (:functions region)]
      (is (= (get-in input [:runtime name :body])
             (prototype.typed-blocks/legacy-body {:entry-pc (:entry-pc f) :instructions (:canonical-instructions f)})))
      (is (every? #(= (:cost %) (count (:trace %))) (:blocks f))))))

(deftest actual-borrowed-mutual-calls-remain-unsupported-nontail-controls
  (let [input (nat-program)]
    (doseq [label ["bounceA" "bounceB"]]
      (is (= :non-intrinsic-call (:reason (prepare-program input [(prototype.typed-tail-test/target (:typed input) label)])))))))

(deftest nat-literal-and-rc-count-refusal-precedes-typed-code-fingerprints
  (let [huge (.shiftLeft java.math.BigInteger/ONE 8192)
        rows [(prototype.typed-tail-test/row "literal"
                ["vdecl" {:idx 1} "tagged" {:lit {:v {:num {:v huge}}}} (prototype.typed-tail-test/return-node 0)])
              (fixture/rc-row false)]
        literal-input (prototype.typed-tail-test/small-bundle (first rows))
        rc-row (assoc-in (second rows) [:ir :fdecl :body 2] huge)
        calls (atom 0)]
    (with-redefs [prototype.typed-ir/typed-code-key (fn [& _] (swap! calls inc) (throw (ex-info "Fingerprint should not run" {})))]
      (is (= :unsupported-nat-literal (:reason (prepare-program literal-input (vec (keys (:typed literal-input)))))))
      ;; The existing typed-companion boundary already limits producer counts.
      (is (thrown? clojure.lang.ExceptionInfo (prototype.typed-tail-test/small-bundle rc-row))))
    (is (zero? @calls))))

(deftest data-only-nat-units-decline-before-factory-while-unsigned-execution-remains
  (let [input (nat-program) roots (fast-roots input)
        config {:typed-functions (:typed input) :roots roots :descriptors (:descriptors input)
                :profile scalar-fixture/profile :budgets prototype.typed-tail-test/budgets}
        called (atom 0)]
    (with-redefs [prototype.typed-tail-emit/emit-factory (fn [& _] (swap! called inc) (throw (ex-info "Factory should not run" {})))]
      (is (= {:status :fallback :reason :unsupported-represented-schema}
             (prototype.typed-tail-execution/prepare-context (:runtime input) config {})))
      (let [name (prototype.typed-tail-test/target (:typed input) "sum")
            initial (prototype.machine/start (prototype.machine/world (:runtime input)) name [10 0])
            program (prototype.lazy-runtime/open-program (:runtime input) {:typed-tail config})
            actual (prototype.mutable/freeze (prototype.lazy-runtime/run! program (prototype.mutable/thaw initial) 1000))]
        (is (= (prototype.machine/run initial) actual))))
    (is (zero? @called)))
  (let [input (prototype.typed-tail-test/bundle "scalar-wrapper-programs.jsonl")]
    (is (= "lean-represented-tail/1" (get-in (prepare-program input (vec (keys (:typed input)))) [:region :schema])))
    (is (= :specialized (:route (prototype.typed-tail-execution-test/execute-plan input "sum64"
                                (prototype.typed-tail-execution-test/start input "sum64" [2 0]) 100))))))

(deftest unused-nat-descriptors-preserve-unsigned-unit-key-and-route
  (let [unsigned (prototype.typed-tail-test/bundle "scalar-wrapper-programs.jsonl")
        nat (nat-input)
        mixed (-> unsigned (update :runtime merge (:functions nat))
                  (update :descriptors merge (:descriptors nat)))
        roots (vec (keys (:typed unsigned)))
        before (:region (prepare-program unsigned roots)) after (:region (prepare-program mixed roots))]
    (is (= "lean-represented-tail/1" (:schema after)))
    (is (= (:key before) (:key after)))
    (is (= (:descriptors before) (:descriptors after)))
    (is (= :specialized (:route (prototype.typed-tail-execution-test/execute-plan mixed "sum64"
                                 (prototype.typed-tail-execution-test/start mixed "sum64" [2 0]) 100))))))

(deftest positive-nat-cross-tail-transfers-are-simultaneous-and-scoped-per-function
  ;; Synthetic producer IR tests the general data rule. Native borrowed mutual
  ;; fixtures remain unsupported because they contain real post-call decs.
  (let [a (fixture/name-of "tail-A") b (fixture/name-of "tail-B")
        p (fn [id type] (assoc (prototype.typed-blocks-test/p id type) :borrow true))
        arg prototype.typed-blocks-test/arg ret prototype.typed-blocks-test/ret
        row prototype.typed-blocks-test/row
        ra (row "tail-A" [(p 1 "tobject") (p 2 "tobject")] "tobject"
                ["vdecl" {:idx 3} "tagged" {:lit {:v {:num {:v 3}}}}
                 ["vdecl" {:idx 4} "tobject" {:fap {:c b :ys [(arg 2) (arg 1) (arg 3)]}} (ret 4)]])
        rb (row "tail-B" [(p 1 "tobject") (p 2 "tobject") (p 3 "tobject")] "tobject"
                ["vdecl" {:idx 4} "tobject" {:fap {:c a :ys [(arg 2) (arg 1)]}} (ret 4)])
        input {:runtime (into {} (map prototype.import-ir/lower-declaration) [ra rb])
               :typed (into {} (map prototype.import-ir/lower-typed-declaration) [ra rb]) :descriptors {}}
        result (prepare-program input [a]) fs (get-in result [:region :functions])
        ta (:operation (last (get-in fs [a :blocks]))) tb (:operation (first (get-in fs [b :blocks])))]
    (is (= :ready (:status result)))
    (is (= "lean-represented-tail/2" (get-in result [:region :schema])))
    (is (= [b [[:var 2] [:var 1] [:var 3]] :simultaneous-carriers] (subvec ta 2)))
    (is (= [a [[:var 2] [:var 1]] :simultaneous-carriers] (subvec tb 2)))
    (is (= :literal (get-in fs [a :representations 3 :proof :kind])))
    (is (= :entry-guard (get-in fs [b :representations 3 :proof :kind])))
    (is (some #{#{a b}} (map set (get-in result [:region :components]))))
    (let [bad (assoc-in fs [a :representations 3 :lane] :long-bits)
          reason (try ((ns-resolve 'prototype.typed-tail 'check-tail-representations!) bad (fn [& _]))
                      nil (catch clojure.lang.ExceptionInfo e (:prototype.typed-tail/fallback (ex-data e))))]
      (is (= :nat-tail-representation reason)))
    (let [nat (nat-input) target (fixture/name-of "Nat" "add")
          r (row "unsupported-reference" [(p 1 "object") (p 2 "tobject")] "tobject"
                 ["vdecl" {:idx 3} "tobject" {:fap {:c target :ys [(arg 1) (arg 2)]}} (ret 3)])
          input {:runtime (into (:functions nat) [(prototype.import-ir/lower-declaration r)])
                 :typed (into {} [(prototype.import-ir/lower-typed-declaration r)]) :descriptors (:descriptors nat)}]
      (is (= :non-scalar-signature (:reason (prepare-program input (vec (keys (:typed input))))))))))
