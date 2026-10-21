(ns prototype.runtime-expr-bvars-test
  (:require [clojure.test :refer [deftest is]] [clojure.data.json :as json] [clojure.string :as str]
            [clojure.walk :as walk] [prototype.machine :as m] [prototype.raw-interop :as raw]
            [prototype.runtime-prim :as prim] [prototype.runtime-abi :as abi] [prototype.runtime-expr-bvars :as bvars]
            [prototype.runtime-expr-transform :as transform]
            [prototype.runtime-expr-transform-test :as transform-test]
            [prototype.runtime-expr-replace-test :as replace-test]))
(def ops replace-test/ops)
(defn nat [w s]
  (let [n (bigint s)]
    (if (<= n 9223372036854775807N) [w n]
      (let [[w r] (m/allocate w :mpz 250 [])] [(assoc-in w [:heap (:id r) :integer] n) r]))))
(defn run-case [backend w symbol args]
  (let [params (vec (range 1 (inc (count args)))) dest (inc (count args))
        functions {:test {:params params :body [:let dest [:runtime symbol (mapv #(vector :var %) params)] [:return [:var dest]]]}}
        session (raw/open-functions functions {} {:backend backend}) original prim/evaluate]
    (with-redefs [prim/evaluate (fn [ops w symbol args]
                                (if (contains? bvars/supported-symbols symbol) (bvars/evaluate ops w symbol args)
                                  (original ops w symbol args)))]
      (raw/call session (assoc w :functions functions) :test args))))
(deftest native-query-and-lowering-cache-depth-shape-and-pointer-differential
  (let [rows (mapv #(json/read-str % :key-fn keyword) (str/split-lines (slurp "fixtures/runtime-expr-bvars.jsonl")))]
    (is (= 190 (count rows)))
    (doseq [row rows backend [:reference :mutable :jvm]]
      (let [cache (atom {})
            [w root] (with-bindings {#'transform-test/*build-cache* cache}
                       (transform-test/build (m/world {}) (:input row)))
            [w params] (reduce (fn [[w out] s] (let [[w v] (nat w s)] [w (conj out v)])) [w []] (:params row))
            result (run-case backend w (:symbol row) (into [root] params))
            next (:state result) value (:value result)]
        (if (= "lean_expr_has_loose_bvar" (:symbol row))
          (do (is (= (if (:result row) 1 0) value) [backend (:label row)])
              (is (= (:heap w) (:heap next))))
          (do (is (= (:sameRoot row) (= root value)) [backend (:label row)])
              (is (= (walk/postwalk #(if (map? %) (dissoc % :nodeId) %) (:output row))
                     (transform-test/normalized next value)) [backend (:label row)])
              (replace-test/assert-native-sharing next value (:output row) (atom @cache))
              (is (= (:heap w) (:heap (m/release next value 1))))))))))
(deftest pure-query-does-not-allocate-or-retain-and-lowering-forks-are-isolated
  (let [[w b] (transform/make-bvar ops (m/world {}) 3)
        [w root] (replace-test/app w b b)
        [same yes] (bvars/evaluate ops w "lean_expr_has_loose_bvar" [root 3])
        [same no] (bvars/evaluate ops same "lean_expr_has_loose_bvar" [root 2])
        [left a] (bvars/evaluate ops w "lean_expr_lower_loose_bvars" [root 2 1])
        [right b] (bvars/evaluate ops w "lean_expr_lower_loose_bvars" [root 2 1])]
    (is (identical? w same)) (is (= 1 yes)) (is (= 0 no))
    (is (= left right)) (is (= a b))
    (is (apply = (:fields (m/node left a))))
    (is (= (:heap w) (:heap (m/release left a 1))))))
(deftest deep-lowering-keeps-the-host-stack-bounded
  (let [[w b] (transform/make-bvar ops (m/world {}) 2)
        [w root] (loop [w w root b n 3000]
                   (if (zero? n) [w root]
                     (let [[w a] (replace-test/app w root b)] (recur w a (dec n)))))
        [next yes] (bvars/evaluate ops w "lean_expr_has_loose_bvar" [root 2])
        [next result] (bvars/evaluate ops next "lean_expr_lower_loose_bvars" [root 1 1])]
    (is (= 1 yes))
    (is (= 3000 (loop [v result n 0]
                  (let [node (m/node next v)] (if (= 5 (:tag node)) (recur (first (:fields node)) (inc n)) n)))))
    (is (= 1 (first (:fields (m/node next (second (:fields (m/node next result))))))))
    (is (= (:heap w) (:heap (m/release next result 1))))))
(deftest pinned-abi-lowers-and-executes-through-the-real-dispatcher
  (doseq [symbol ["lean_expr_has_loose_bvar" "lean_expr_lower_loose_bvars"]
          backend [:reference :mutable :jvm]]
    (let [arity (get-in bvars/supported-symbols [symbol :arity])
          name ["str" ["anonymous"] symbol]
          row {:kind "decl" :name name
               :ir {:extern {:f name :type (if (= arity 2) "uint8" "object")
                             :xs (mapv (fn [i] {:x {:idx i} :ty (if (= i 1) "object" "tobject") :borrow true})
                                       (range 1 (inc arity)))
                             :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"] :fn symbol}}]}}}}
          [target function] (abi/lower row)
          session (raw/open-functions {target function} {} {:backend backend})
          [w root] (transform/make-bvar ops (m/world {target function}) 3)
          args (if (= arity 2) [root 3] [root 2 1])
          {:keys [state value]} (raw/call session w target args)]
      (is (= arity (get-in prim/supported-symbols [symbol :arity])))
      (is (= symbol (:runtime-extern function)))
      (if (= arity 2)
        (is (= 1 value))
        (is (= [2] (:fields (m/node state value)))))
      (is (= (:heap w) (:heap (if (= arity 2) state (m/release state value 1)))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unrecognized raw runtime ownership/type signature"
            (abi/lower (assoc-in row [:ir :extern :xs 0 :borrow] false)))))))
