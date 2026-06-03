(ns ansatz.reducers-test
  (:require [ansatz.reducers :as r]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [clojure.test :refer [deftest is]]))

(def ^:private init-medium-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(defn- require-env []
  (or @init-medium-env
      (throw (ex-info "test-data/init-medium.ndjson not found" {}))))

(r/defpipeline odd-squares
  (map inc)
  (filter odd?)
  (map #(* % %)))

(deftest pipeline-compiles-to-transducer
  (let [pipeline (-> r/empty
                     (r/map inc)
                     (r/filter even?)
                     (r/flat-map (fn [x] [x (* 10 x)])))]
    (is (identical? (r/xform pipeline) (r/xform pipeline))
        "compiled xform is cached on the pipeline value")
    (is (= [2 20 4 40]
           (r/into [] pipeline [0 1 2 3])))
    (is (= 66
           (r/transduce pipeline + 0 [0 1 2 3])))
    (is (= [2 20 4 40]
           (vec (r/eduction pipeline [0 1 2 3]))))
    (is (= {:steps [{:op :map :fold-safe? true}
                    {:op :filter :fold-safe? true}
                    {:op :mapcat :fold-safe? true}]
            :fold-safe? true}
           (r/explain pipeline)))))

(deftest compose-preserves-left-to-right-order
  (let [pipeline (r/compose (r/map inc)
                            (r/filter odd?)
                            (r/map #(* % %)))]
    (is (= [1 9 25]
           (r/into [] pipeline [0 1 2 3 4])))))

(deftest pipeline-macro-accepts-clojure-transducer-shape
  (let [pipeline (r/pipeline
                  (map inc)
                  (filter odd?)
                  (mapcat (fn [x] [x (- x)])))]
    (is (= [1 -1 3 -3 5 -5]
           (r/into [] pipeline [0 1 2 3 4]))))
  (is (= [1 9 25]
         (r/into [] odd-squares [0 1 2 3 4]))))

(deftest lawful-fold-map-matches-sequential-transduce
  (let [xs (vec (range 1000))
        pipeline (-> r/empty
                     (r/map inc)
                     (r/filter #(not (zero? (mod % 3)))))
        value-f #(* % %)
        expected (r/transduce pipeline
                              (fn
                                ([] 0)
                                ([x] x)
                                ([acc x] (+ acc (value-f x))))
                              xs)]
    (doseq [grain [1 2 17 512]]
      (is (= expected
             (r/fold-map pipeline r/nat-add value-f xs {:grain grain}))
          (str "grain=" grain)))))

(deftest convenience-terminals-map-to-lawful-folds
  (let [xs (vec (range 10))
        pipeline (r/pipeline (map inc) (filter odd?))]
    (is (= 25
           (r/sum pipeline r/nat-add xs {:grain 2})))
    (is (= 25
           (r/sum-seq pipeline r/nat-add xs)))
    (is (= 55
           (r/sum-by r/empty r/nat-add inc xs {:grain 2})))
    (is (= 55
           (r/sum-by-seq r/empty r/nat-add inc xs)))
    (is (= {0 5, 1 5}
           (r/frequencies r/empty r/nat-add #(mod % 2) xs {:grain 2})))
    (is (= {0 5, 1 5}
           (r/frequencies-seq r/empty r/nat-add #(mod % 2) xs)))))

(deftest group-by-uses-value-monoid
  (let [xs (vec (range 1 31))
        pipeline (r/filter #(<= % 20))
        actual (r/group-by pipeline r/nat-add #(mod % 4) (constantly 1) xs {:grain 3})]
    (is (= {0 5, 1 5, 2 5, 3 5} actual))))

(deftest unsafe-monoid-is-rejected-by-lawful-fold
  (let [bad-spec (r/monoid-spec
                  {:name :bad/add
                   :unit-fn (constantly 0)
                   :combine +
                   :laws {:assoc 'Nat.add_assoc}})]
    (is (false? (r/lawful? bad-spec)))
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"Parallel fold requires a lawful MonoidSpec"
         (r/fold-map r/empty bad-spec identity [1 2 3])))
    (is (= 6
           (r/unchecked-fold-map r/empty (constantly 0) + identity [1 2 3]
                                 {:grain 1})))))

(deftest kernel-validates-monoid-law-certificates
  (let [env (require-env)
        checked (r/checked env r/nat-add)]
    (is (r/lawful? checked))
    (is (r/kernel-lawful? checked))
    (is (= 10
           (r/fold-map-checked r/empty checked identity [1 2 3 4]
                               {:grain 1})))
    (is (= 10
           (r/sum-checked r/empty checked [1 2 3 4]
                          {:grain 1})))
    (is (= 10
           (r/sum-seq-checked r/empty checked [1 2 3 4])))
    (is (= {0 2, 1 2}
           (r/group-by-checked r/empty checked #(mod % 2) (constantly 1)
                               [1 2 3 4]
                               {:grain 1})))
    (is (= {0 2, 1 2}
           (r/group-by-seq-checked r/empty checked #(mod % 2) (constantly 1)
                                   [1 2 3 4])))
    (is (= {0 2, 1 2}
           (r/frequencies-checked r/empty checked #(mod % 2)
                                  [1 2 3 4]
                                  {:grain 1})))
    (is (= {0 2, 1 2}
           (r/frequencies-seq-checked r/empty checked #(mod % 2)
                                      [1 2 3 4])))
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"Kernel-checked fold requires validate-monoid-spec"
         (r/fold-map-checked r/empty r/nat-add identity [1 2 3])))))

(deftest kernel-validation-rejects-mismatched-law-type
  (let [env (require-env)
        bad-spec (r/monoid-spec
                  {:name :bad/nat-add
                   :unit-fn (:unit-fn r/nat-add)
                   :combine (:combine r/nat-add)
                   :laws (assoc (:laws r/nat-add)
                                :right-identity 'Nat.zero_add)
                   :metadata (:metadata r/nat-add)})]
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"Kernel law type does not match MonoidSpec"
         (r/validate-monoid-spec env bad-spec)))))
