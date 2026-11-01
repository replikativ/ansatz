(ns prototype.typed-ir-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.data.json :as json]
            [clojure.java.io :as io]
            [prototype.import-ir :as ir]
            [prototype.typed-ir :as typed]
            [prototype.fingerprint :as fp]
            [prototype.slot-count :as slots]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.lazy-runtime :as lazy]))

(defn- parameter [id ty borrow] {:x {:idx id} :ty ty :borrow borrow})
(defn- row [body]
  {:name ["str" ["anonymous"] "test"]
   :ir {:fdecl {:f ["str" ["anonymous"] "test"] :xs [(parameter 0 "uint64" false)]
                :type "uint64" :info {} :body body}}})
(def return-node ["ret" {:var {:id {:idx 0}}}])
(defn- facts [row] (:typed-ir (second (ir/lower-typed-declaration row))))
(defn- outcome [f]
  (try [:ok (f)] (catch Throwable t [:error (class t) (.getMessage t) (ex-data t)])))

(deftest demand-only-preserves-executable-shape-and-slot-count
  (let [r (row ["vdecl" {:idx 4} "uint64" {:lit {:v {:num {:v 7}}}} return-node])
        [name legacy] (ir/lower-declaration r) [typed-name selected] (ir/lower-typed-declaration r)
        c (:typed-ir selected)]
    (is (= name typed-name))
    (is (= legacy (dissoc selected :typed-ir)))
    (is (= (meta legacy) (meta selected)))
    (is (not (contains? legacy :typed-ir)))
    (is (= "lean-typed-companion/1" (:schema c)))
    (is (= :producer-ir (:node-space c)))
    (is (= {:params [{:id 0 :type "uint64" :borrow false}] :result-type "uint64"} (:signature c)))
    (is (= (slots/function-slots legacy) (slots/function-slots selected)))
    (is (= (slots/function-slots legacy)
           (slots/function-slots (assoc-in selected [:typed-ir :nodes 0 :source-site] 1000000))))))

(deftest producer-graph-preserves-lexical-facts-and-tail-origin
  (let [r (row ["jdecl" {:idx 9} [(parameter 3 "object" true)] return-node
                ["case" ["str" ["anonymous"] "UInt64"] {:idx 0} "uint64"
                 [["default" ["inc" {:idx 0} 1 true false return-node]]]]])
        c (facts r) nodes (:nodes c)]
    (is (= 4 (count nodes)))
    (is (= {:op :jdecl :join-id 9 :params [{:id 3 :type "object" :borrow true}]
            :children [0 2]} (peek nodes)))
    (is (= {:op :inc :id 0 :count 1 :check true :persistent false :children [0]} (nth nodes 1)))
    (is (= "uint64" (:type (nth nodes 2))))
    (is (= ["str" ["anonymous"] "UInt64"] (:name (nth nodes 2)))))
  (let [r (row ["vdecl" {:idx 0} "uint64"
                {:fap {:c ["str" ["anonymous"] "callee"] :ys ["erased"]}} return-node])
        selected (second (ir/lower-typed-declaration r))]
    (is (= :tail (first (:body selected))))
    (is (= [:ret :vdecl] (mapv :op (get-in selected [:typed-ir :nodes]))))))

(deftest source-and-typed-keys-include-erased-facts-and-profile
  (let [r (row return-node) changed (assoc-in r [:ir :fdecl :xs 0 :borrow] true)
        a (second (ir/lower-typed-declaration r)) b (second (ir/lower-typed-declaration changed))
        legacy-key #(fp/key (select-keys % [:params :body]))]
    (is (= (legacy-key a) (legacy-key b)))
    (is (not= (get-in a [:typed-ir :source-key]) (get-in b [:typed-ir :source-key])))
    (is (not= (typed/typed-code-key a {:word-bits 64}) (typed/typed-code-key b {:word-bits 64})))
    (is (not= (typed/typed-code-key a {:word-bits 64}) (typed/typed-code-key a {:word-bits 32})))
    (doseq [path [[:ir :fdecl :type] [:ir :fdecl :xs 0 :ty]]]
      (is (not= (:source-key (facts r)) (:source-key (facts (assoc-in r path "object"))))))
    (is (= (:source-key (facts r)) (:source-key (facts (json/read-str (json/write-str r) :key-fn keyword)))))))

(deftest malformed-types-parameters-and-shapes-are-rejected
  (is (= (outcome #(ir/type! "bad")) (outcome #(typed/type! "bad"))))
  (doseq [r [(assoc-in (row return-node) [:ir :fdecl :xs] [(parameter 0 "uint64" false) (parameter 0 "uint64" true)])
             (assoc-in (row return-node) [:ir :fdecl :xs 0 :borrow] nil)
             (assoc-in (row return-node) [:ir :fdecl :xs 0 :x :idx] -1)
             (row ["vdecl" {:idx 1} "bad" {} return-node])
             (row ["jdecl" {:idx 1} [(parameter 0 "object" false) (parameter 0 "object" false)] return-node return-node])
             (row ["inc" {:idx 0} 1 nil false return-node])
             (row ["ret"])
             (row ["case" ["anonymous"] {:idx 0} "object" [["unknown" return-node]]])]]
    (is (= :error (first (outcome #(ir/lower-typed-declaration r)))))))

(deftest identity-memoized-source-dag-and-deep-chain
  (let [dag (nth (iterate #(vector "jdecl" {:idx 1} [] % %) return-node) 30)
        c (typed/companion (get-in (row dag) [:ir :fdecl]))]
    ;; A structural source hash would expand this to over a billion leaves.
    (is (= 31 (count (:nodes c))))
    (is (= [29 29] (:children (peek (:nodes c)))))
    (let [selected (second (ir/lower-typed-declaration (row dag)))]
      (is (= (typed/typed-code-key selected {}) (typed/typed-code-key selected {}))))
    (is (empty? (second (:source-key c)))))
  (let [chain (reduce (fn [b _] ["del" {:idx 0} b]) return-node (range 10000))
        c (typed/companion (get-in (row chain) [:ir :fdecl]))]
    (is (= 10001 (count (:nodes c))))
    (is (= 10000 (:root c)))))

(deftest actual-producer-fixtures-retain-legacy-functions
  (doseq [fixture ["list-reverse.jsonl" "list-map.jsonl"]]
    (let [path (io/file "fixtures" fixture)
          path (if (.exists path) path (io/file "experiments/lean-ir/fixtures" fixture))
          rows (with-open [r (io/reader path)]
                 (doall (map #(json/read-str % :key-fn keyword) (line-seq r))))]
      (doseq [r rows :when (get-in r [:ir :fdecl])]
        (let [[name legacy] (ir/lower-declaration r) [typed-name selected] (ir/lower-typed-declaration r)]
          (is (= name typed-name))
          (is (= legacy (dissoc selected :typed-ir)))
          (is (= (meta legacy) (meta selected)))
          (is (= (slots/function-slots legacy) (slots/function-slots selected))))))))

(deftest typed-keys-cover-global-behavior-and-executable-replacement
  (let [a (second (ir/lower-typed-declaration (row return-node)))
        key #(typed/typed-code-key % {:word-bits 64})]
    (doseq [[field value] [[:runtime-initializer ["str" ["anonymous"] "init"]]
                           [:global-role "value"] [:result-type "object"]
                           [:body [:return [:imm 42]]]]]
      (is (not= (key a) (key (assoc a field value)))))
    (let [r (row ["inc" {:idx 0} 1 true false return-node])
          changed (assoc-in r [:ir :fdecl :body 3] false)]
      (is (= (ir/lower-declaration r) (ir/lower-declaration changed)))
      (is (not= (key (second (ir/lower-typed-declaration r)))
                (key (second (ir/lower-typed-declaration changed))))))))

(deftest malformed-source-leaves-never-become-opaque-keys
  (doseq [body [["ret" {:var {:id {:idx -1}}}]
                ["jmp" {:idx 0} [{:var {:id {:idx -1}}}]]
                ["vdecl" {:idx 0} "object" {:proj {:x {:idx 0} :i -1}} return-node]
                ["vdecl" {:idx 0} "object" {:sproj {:x {:idx 0} :n 0 :offset -1}} return-node]
                ["vdecl" {:idx 0} "object" {:lit {:v {:num {:v -1}}}} return-node]
                ["vdecl" {:idx 0} "object" {:lit {:v {:num {:v 1} :str {:v "x"}}}} return-node]
                ["case" ["not-a-name"] {:idx 0} "object" [["default" return-node]]]]]
    (is (= :error (first (outcome #(typed/companion (get-in (row body) [:ir :fdecl])))))))
  (let [opaque (proxy [java.math.BigInteger] ["3"])]
    (is (= :error (first (outcome #(typed/companion
                                  (assoc-in (get-in (row return-node) [:ir :fdecl]) [:info :opaque] opaque))))))))

(deftest selected-companion-does-not-change-evaluation-or-default-demand
  (let [r (row return-node) [name legacy] (ir/lower-declaration r)
        [_ selected] (ir/lower-typed-declaration r)
        run #(m/run (m/start (m/world {name %}) name [41]))
        original (run legacy) chosen (run selected)]
    (is (= 41 (:result original) (:result chosen)))
    ;; The selected function image intentionally contains facts; every other
    ;; World field, including final PC/locals/stats/heap, is unchanged.
    (is (= original (update-in chosen [:functions name] dissoc :typed-ir)))
    (doseq [backend [:mutable :jvm] fuel [0 1]]
      (let [run (fn [function]
                  (let [functions {name function}
                        machine (u/thaw (m/start (m/world functions) name [41]))]
                    (u/freeze (case backend
                                :mutable (u/run! machine fuel)
                                :jvm (lazy/run! (lazy/open-program functions) machine fuel)))))
            before (run legacy) after (run selected)]
        (is (= before (update-in after [:functions name] dissoc :typed-ir)))))
    (with-redefs [typed/companion (fn [_] (throw (AssertionError. "eager companion")))]
      (is (= [name legacy] (ir/lower-declaration r))))))
