(ns prototype.imported-kernel-performance-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.imported-kernel :as imported]
            [prototype.imported-kernel-test :as fixture]
            [prototype.module-store :as store]
            [prototype.machine :as m]))

(deftest module-name-validation-does-not-discard-full-projections
  (let [loaded (fixture/loaded) calls (atom 0) project imported/project-constant]
    (with-redefs [imported/project-constant (fn [& args] (swap! calls inc) (apply project args))]
      (let [certificate (imported/verify-module-data (:world loaded)
                                                    (concat (:roots loaded) (:roots loaded)) fixture/policy)]
        (is (= 17 (count (:constants certificate)))))
      (is (= 17 @calls)))))

(defn- associate-counted [world values certificate]
  (let [[world root] (m/allocate world :ctor 0 [])
        calls (atom 0) project imported/project-constant]
    (with-redefs [imported/project-constant (fn [& args] (swap! calls inc) (apply project args))]
      (let [result (imported/associate-checked (fixture/context root values 1)
                                              world root fixture/helper-names certificate)]
        [result @calls]))))

(deftest immutable-source-reuse-requires-exact-source-and-reference-identity
  (let [a (store/load-file (m/world {}) "fixtures/imported-kernel-native.jsonl")
        b (store/load-file (m/world {}) "fixtures/imported-kernel-native.jsonl")]
    (try
      (let [world (:world a) values (vec (mapcat #(map :guest (imported/module-constants world %)) (:roots a)))
            certificate (imported/verify-constants world values fixture/policy)
            [associated calls] (associate-counted world values certificate)
            ;; Same exact IDs and content in a separately validated source are
            ;; deliberately reprojected; content equality cannot authorize reuse.
            [_ replaced-calls] (associate-counted (:world b) values certificate)]
        (is (identical? (:source a) (first (:projection-sources certificate))))
        (is (= 0 calls))
        (is (= 17 replaced-calls))
        ;; Source membership alone is insufficient: another source could shadow
        ;; the root OR only a descendant in its range. Conservatively disable
        ;; reuse for every multi-source world and multi-source certificate.
        (doseq [sources [[(:source b) (:source a)] [(:source a) (:source b)]]]
          (let [overlap (assoc world :native-imports sources)
                [_ calls] (associate-counted overlap values certificate)]
            (is (= 17 calls))))
        (let [overlap (assoc world :native-imports [(:source a) (:source b)])
              multi-certificate (imported/verify-constants overlap values fixture/policy)
              [_ calls] (associate-counted world values multi-certificate)]
          (is (empty? (:projection-sources multi-certificate)))
          (is (= 17 calls)))
        (is (= 1 (count (:kernel-environments associated))))
        (is (nil? (:kernel-environments world)))
        ;; Native heap shadows invalidate the shortcut and fail through node's
        ;; ordinary imported-range collision guard.
        (is (thrown? clojure.lang.ExceptionInfo
              (associate-counted (assoc-in world [:heap (:id (first values))]
                                           {:kind :ctor :tag 0 :fields [] :rc 1}) values certificate)))
        (.close ^java.io.Closeable (:source a))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"source is closed"
              (associate-counted world values certificate))))
      (finally (.close ^java.io.Closeable (:source a))
               (.close ^java.io.Closeable (:source b))))))

(deftest eager-and-local-values-still-reproject
  (let [loaded (fixture/loaded) world (:world loaded) values (fixture/values loaded)
        certificate (imported/verify-constants world values fixture/policy)
        [_ calls] (associate-counted world values certificate)]
    (is (empty? (:projection-sources certificate)))
    (is (= 17 calls))))

(defn- verify-counted [world values options]
  (let [calls (atom 0) project imported/project-constant
        result (with-redefs [imported/project-constant (fn [& args] (swap! calls inc) (apply project args))]
                 (imported/verify-constants world values options))]
    [result @calls]))

(deftest trusted-certificate-reuses-only-immutable-projections-and-rechecks-entire-environment
  (let [loaded (store/load-file (m/world {}) "fixtures/imported-kernel-native.jsonl")]
    (try
      (let [world (:world loaded)
            values (vec (mapcat #(map :guest (imported/module-constants world %)) (:roots loaded)))
            certificate (imported/verify-constants world values fixture/policy)
            options (assoc fixture/policy :projection-certificate certificate)
            [checked calls] (verify-counted world values options)]
        (is (= 0 calls))
        (is (= 17 (count (:constants checked))))
        (is (= (:constants certificate) (:constants checked)))
        (is (not (identical? (:env certificate) (:env checked))))
        (doseq [[name ci] (:projected certificate)]
          (is (identical? ci (get (:projected checked) name))))
        (is (identical? (:source loaded) (first (:projection-sources checked))))
        (is (nil? (:kernel-environments world)))
        ;; Cached checked Java values grant no axiom/unsafe policy or dependency
        ;; admission in the NEW environment; the entire checker still runs.
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"axiom admission"
              (imported/verify-constants world values {:allow-unsafe? true :projection-certificate certificate})))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unsafe/partial"
              (imported/verify-constants world values {:allow-axioms? true :projection-certificate certificate})))
        (let [a-name (some #(when (= "A" (str %)) %) (keys (:constants certificate)))
              a (get (:constants certificate) a-name)
              without-a (filterv #(not= a %) values)]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unresolved"
                (imported/verify-constants world without-a options)))
          ;; Same name and even identical payload does not authorize a different
          ;; guest CI reference. Only this local wrapper is freshly projected.
          (let [node (m/node world a)
                [local-world replacement] (m/allocate world :ctor (:tag node) (:fields node))
                replaced (mapv #(if (= a %) replacement %) values)
                [local-certificate calls] (verify-counted local-world replaced options)]
            (is (= 1 calls))
            (is (= replacement (get (:constants local-certificate) a-name)))
            (is (not (identical? (get (:projected certificate) a-name)
                                (get (:projected local-certificate) a-name)))))
          ;; The certificate is explicit HOST authority, but accidental mutation
          ;; of its projected map cannot substitute another Java CI.
          (let [other (first (remove #(= a-name (key %)) (:projected certificate)))
                forged (assoc-in certificate [:projected a-name] (val other))]
            (is (thrown-with-msg? clojure.lang.ExceptionInfo #"checked Java environment"
                  (imported/verify-constants world values (assoc options :projection-certificate forged))))))
        (is (= world (:world loaded))))
      (finally (.close ^java.io.Closeable (:source loaded))))))

(deftest projection-reuse-rejects-source-replacement-descendant-shadows-and-closed-stores
  (let [a (store/load-file (m/world {}) "fixtures/imported-kernel-native.jsonl")
        b (store/load-file (m/world {}) "fixtures/imported-kernel-native.jsonl")]
    (try
      (let [world (:world a)
            values (vec (mapcat #(map :guest (imported/module-constants world %)) (:roots a)))
            certificate (imported/verify-constants world values fixture/policy)
            options (assoc fixture/policy :projection-certificate certificate)]
        (let [[_ calls] (verify-counted (:world b) values options)]
          (is (= 17 calls)))
        (doseq [sources [[(:source a) (:source b)] [(:source b) (:source a)]]]
          (let [[_ calls] (verify-counted (assoc world :native-imports sources) values options)]
            (is (= 17 calls))))
        ;; The CI root is untouched. Shadow only a descendant in its closed
        ;; Store range: reuse must not skip this collision by trusting root ID.
        (let [descendant (first (:fields (m/node world (first values))))
              shadowed (assoc-in world [:heap (:id descendant)] {:kind :ctor :tag 0 :fields [] :rc 1})]
          (is (thrown? clojure.lang.ExceptionInfo (imported/verify-constants shadowed values options))))
        (.close ^java.io.Closeable (:source a))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"source is closed"
              (imported/verify-constants world values options))))
      (finally (.close ^java.io.Closeable (:source a))
               (.close ^java.io.Closeable (:source b))))))
