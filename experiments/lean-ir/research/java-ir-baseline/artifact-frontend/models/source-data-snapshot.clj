(ns source-data-snapshot-checks-v1
  "Storage mutation models; actual Node realm guards remain runtime validation."
  (:require [clojure.test :refer [deftest is run-tests]]
            [ansatz.research.ir.source-data-snapshot :as snapshot]))
(defn node [children]
  (atom {:tag 0 :array? false :bytes? false :metadata-kind nil :capacity (count children)
         :logical-size (count children) :children (vec children) :scalars (byte-array 0)}))
(defn model [f]
  (with-redefs-fn
    {#'snapshot/sample
     (fn [_ n]
       (let [s @n]
         (when (or (:dead s) (:ref s) (:task s) (:closure s)) (throw (ex-info "Modeled invalid Node" {})))
         (assoc s :node n :children (if (:array? s) (subvec (:children s) 0 (:logical-size s)) (:children s))
                  :scalars (aclone ^bytes (:scalars s)))))}
    #(f {:basis {:node-class clojure.lang.Atom} :engine (Object.)})))
(deftest captures-aliases-and-all-import-extra-extension-subgraphs
  (model
    (fn [{:keys [basis engine]}]
      (let [import (node ["Init.Prelude"]) extras (node ["helper"])
            extension-child (node [7]) entries (node [(node ["extension" extension-child])])
            root (node [import extras entries extras]) witness (snapshot/capture! basis engine [root])]
        (is (identical? witness (snapshot/validate! witness)))
        (is (= 6 (count (:records witness))))
        (doseq [[target update!] [[import #(swap! % assoc :children ["Other"])]
                                  [extras #(swap! % assoc :children ["changed"])]
                                  [extension-child #(swap! % assoc :children [8])]
                                  [entries #(swap! % assoc :children [])]]]
          (let [old @target]
            (update! target)
            (is (thrown? Exception (snapshot/validate! witness)))
            (reset! target old)))))))
(deftest checks-flags-scalars-child-order-and-node-alias-identity
  (model
    (fn [{:keys [basis engine]}]
      (let [child (node [1]) root (node [child "Name"])
            _ (swap! root assoc :scalars (byte-array [0 0 0 0 0 0 0 0]))
            witness (snapshot/capture! basis engine [root]) initial @root]
        (doseq [changed [(assoc initial :scalars (byte-array [1 0 0 0 0 0 0 0]))
                         (assoc initial :scalars (byte-array [0 0 0 0 0 0 0 1]))
                         (assoc initial :children ["Name" child])
                         (assoc initial :children [(node [1]) "Name"])
                         (assoc initial :tag 1) (assoc initial :array? true)
                         (assoc initial :metadata-kind ::unknown)]]
          (reset! root changed)
          (is (thrown? Exception (snapshot/validate! witness))))
        (reset! root (assoc initial :rc 9 :pointer-annotation :new :logical-sharing true))
        (is (identical? witness (snapshot/validate! witness)))))))
(deftest logical-array-and-byte-array-extent-remain-fixed
  (model
    (fn [{:keys [basis engine]}]
      (let [array (node [1 2 3]) _ (swap! array assoc :array? true :logical-size 1 :metadata-kind ::array)
            witness (snapshot/capture! basis engine [array])]
        (swap! array assoc :logical-size 2)
        (is (thrown? Exception (snapshot/validate! witness))))
      (let [bytes (node []) _ (swap! bytes assoc :tag 248 :bytes? true :metadata-kind ::bytes
                                               :logical-size 1 :scalars (byte-array [5 0 0]))
            witness (snapshot/capture! basis engine [bytes])]
        (swap! bytes assoc :logical-size 2)
        (is (thrown? Exception (snapshot/validate! witness)))
        (swap! bytes assoc :logical-size 1 :scalars (byte-array [6 0 0]))
        (is (thrown? Exception (snapshot/validate! witness)))))))
(deftest cycles-effectful-nodes-and-explicit-bounds-reject-before-publication
  (model
    (fn [{:keys [basis engine]}]
      (let [root (node [])]
        (swap! root assoc :children [root])
        (is (thrown? Exception (snapshot/capture! basis engine [root]))))
      (doseq [key [:ref :task :closure :dead]]
        (let [root (node [])]
          (swap! root assoc key true)
          (is (thrown? Exception (snapshot/capture! basis engine [root])))))
      (with-redefs [snapshot/limits (assoc snapshot/limits :nodes 1)]
        (is (thrown? Exception (snapshot/capture! basis engine [(node [(node [])])])))))))
(deftest extensible-integer-is-rejected-without-invoking-its-conversion
  (let [calls (atom 0)
        mutable (proxy [java.math.BigInteger] ["1"] (bitLength [] (swap! calls inc) 1))]
    (is (thrown? Exception (snapshot/capture! {:node-class clojure.lang.Atom} (Object.) [mutable])))
    (is (zero? @calls))))
(deftest object-lane-snapshot-rejects-unboxed-scalar-dtos
  (doseq [value [(Integer/valueOf 1) (Short/valueOf (short 1)) (Byte/valueOf (byte 1))
                 (Float/valueOf (float 1)) (Double/valueOf (double 1))]]
    (is (thrown? Exception (snapshot/capture! {:node-class clojure.lang.Atom} (Object.) [value])))))
(defn check! [] (run-tests 'source-data-snapshot-checks-v1))
