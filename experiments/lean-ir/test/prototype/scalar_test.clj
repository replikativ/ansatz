(ns prototype.scalar-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.scalar :as scalar]
            [prototype.import-ir :as ir]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.block-compile :as blocks]
            [prototype.lazy-runtime :as lazy]))

(def functions (delay (ir/load-bundle "fixtures/scalar.jsonl")))
(defn target [label] (first (filter #(= label (ir/name-label %)) (keys @functions))))
(def max64 18446744073709551615N)
(def values [7 4294967297 255 4294967295 max64])
(defn run [backend program initial fuel]
  (case backend
    :reference (m/run initial fuel)
    :mutable (u/freeze (u/run! (u/thaw initial) fuel))
    :eager (u/freeze (blocks/run! program (u/thaw initial) fuel))
    :lazy (u/freeze (lazy/run! program (u/thaw initial) fuel))))
(defn backends []
  [[:reference nil] [:mutable nil] [:eager (blocks/compile-program @functions nil {:lexical-joins true})]
   [:lazy (lazy/open-program @functions)]])

(defn check-fuels [initial]
  (let [expected (m/run initial) steps (get-in expected [:stats :steps])
        start (get-in initial [:stats :steps])]
    (doseq [[backend program] (backends) fuel (range (+ 2 (- steps start)))]
      (let [paused (run backend program initial fuel)]
        (is (= (m/run initial fuel) paused))
        (when (= :paused (:status paused))
          (is (= expected (run backend program (m/resume paused nil) 100000))))))
    expected))

(deftest mixed-constructor-native-values-and-every-fuel-boundary
  (let [initial (m/start (m/world @functions) (target "ScalarProbe.makePacket") values)
        result (check-fuels initial) root (:result result)]
    (is (= {:objects 1 :usize 1 :ssize 13} (:layout (m/node result root))))
    (doseq [[name expected] (map vector ["ScalarProbe.readWord" "ScalarProbe.readSmall" "ScalarProbe.readMedium" "ScalarProbe.readWide"] (rest values))]
      (is (= expected (:result (check-fuels (m/start result (target name) [root]))))))))

(deftest shared-and-unique-scalar-update-and-fork-isolation
  (let [parent (m/run (m/start (m/world @functions) (target "ScalarProbe.makePacket") values))
        root (:result parent)]
    (doseq [shared? [false true]]
      (let [world (if shared? (m/retain parent root 1) parent)
            result (check-fuels (m/start world (target "ScalarProbe.replaceSmall") [root 3]))
            updated (:result result)]
        (is (= (not shared?) (= root updated)))
        (is (= 255 (:result (m/run (m/start parent (target "ScalarProbe.readSmall") [root])))))
        (is (= 3 (:result (m/run (m/start result (target "ScalarProbe.readSmall") [updated])))))
        (is (= max64 (:result (m/run (m/start result (target "ScalarProbe.readWide") [updated])))))
        (when shared?
          (is (= 255 (:result (m/run (m/start result (target "ScalarProbe.readSmall") [root]))))))))
    (let [program (lazy/open-program @functions)
          make-child #(u/thaw (m/start parent (target "ScalarProbe.replaceSmall") [root %]))
          left (u/freeze (lazy/run! program (make-child 3)))
          right (u/freeze (lazy/run! program (make-child 4)))]
      (is (= 3 (:result (m/run (m/start left (target "ScalarProbe.readSmall") [root])))))
      (is (= 4 (:result (m/run (m/start right (target "ScalarProbe.readSmall") [root])))))
      (is (= 255 (:result (m/run (m/start parent (target "ScalarProbe.readSmall") [root]))))))))

(deftest boxing-allocation-ownership-and-closure-application
  (doseq [[type suffix value allocated?] [["uint8" "8" 255 false] ["uint16" "16" 65535 false] ["uint32" "32" 4294967295 false]
                                         ["uint64" "64" max64 true] ["usize" "Size" max64 true]]]
    (let [[world boxed] (m/box-value (m/world @functions) type value)
          result (check-fuels (m/start world (target (str "ScalarProbe.identity" suffix "._boxed")) [boxed]))]
      (is (= value (m/unbox-value result type (:result result))))
      (is (= allocated? (m/ref? (:result result))))
      (is (= (if allocated? 1 0) (count (:heap result))))))
  (let [[world closure] (m/expr (m/world @functions) [:closure (target "ScalarProbe.identity64._boxed") []])
        result (check-fuels (m/start world (target "ScalarProbe.apply64") [closure max64]))]
    (is (= max64 (:result result)))
    (is (empty? (:heap result)))))

(deftest scalar-storage-rejects-uninitialized-out-of-bounds-and-shared-writes
  (doseq [layout [{:objects 256 :usize 0 :ssize 1} {:objects 0 :usize 128 :ssize 0}]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Invalid scalar constructor layout" (scalar/layout! layout))))
  (let [layout {:objects 1 :usize 1 :ssize 13}
        slot {:index 2 :offset 0 :type "uint64" :region :scalar}
        [world root] (m/scalar-constructor (m/world {}) 0 [7] layout)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"uninitialized" (m/read-scalar-node (m/node world root) slot)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"outside constructor" (m/write-scalar-node (m/node world root) (assoc slot :offset 6) 1)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"outside constructor" (m/write-scalar-node (m/node world root) (assoc slot :offset 1 :type "uint32") 1)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unique scalar" (m/write-scalar-node (m/node (m/retain world root 1) root) slot 1)))
    (doseq [[type value] [["uint8" 256] ["uint16" -1] ["uint32" 4294967296] ["uint64" 18446744073709551616N]]]
      (is (thrown? clojure.lang.ExceptionInfo (m/box-value world type value))))
    (let [written (m/write-scalar-node (m/node world root) slot 72623859790382856)]
      (is (= [8 7 6 5 4 3 2 1] (mapv (:scalar-bytes written) (range 16 24))))
      (is (= 84281096 (m/read-scalar-node written (assoc slot :type "uint32")))))
    (let [[world boxed] (m/box-value world "uint64" max64)]
      (is (= max64 (m/unbox-value world "usize" boxed))))
    (let [[world boxed] (m/box-value world "usize" max64)]
      (is (= max64 (m/unbox-value world "uint64" boxed))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported" (ir/type! "float128")))))

(deftest explicit-runtime-profile-is-checked
  (let [manifest {:schema "lean-ir-probe/1" :leanVersion "4.33.1"
                  :runtimeProfile {:wordBits 64 :target "x86_64-unknown-linux-gnu"}}]
    (is (= manifest (ir/validate-manifest! manifest)))
    (doseq [profile [{:wordBits 32 :target "i686-unknown-linux-gnu"}
                     {:wordBits 64 :target "powerpc64-unknown-linux-gnu"}
                     {:wordBits 64 :target "x86_64-windows-msvc"}]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported runtime profile"
                            (ir/validate-manifest! (assoc manifest :runtimeProfile profile))))))
  (let [catalogue (ir/index-bundles ["fixtures/scalar.jsonl"])
        legacy (update catalogue :manifests #(mapv (fn [m] (dissoc m :runtimeProfile)) %))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"requires explicit runtime profile"
                          (ir/load-closure legacy [(target "ScalarProbe.readWide")])))))

(deftest ieee-boxes-preserve-bytes-and-execution-boundaries
  (doseq [[type value expected]
          [["float" 1.5 4609434218613702656N]
           ["float" -0.0 9223372036854775808N]
           ["float32" 1.5 1069547520]
           ["float32" -0.0 2147483648]
           ["float" (scalar/float-from-bytes "float" [1 0 0 0 0 0 240 127]) 9218868437227405313N]]]
    (let [slot {:index 0 :offset 0 :type (if (= type "float") "uint64" "uint32") :region :scalar}
          functions {:bits {:params [] :body [:let 0 [:literal value]
                                             [:let 1 [:box type [:var 0]]
                                              [:let 2 [:scalar-get [:var 1] slot]
                                               [:dec [:var 1] 1 [:return [:var 2]]]]]]}}
          initial (m/start (m/world functions) :bits [])
          eager (blocks/compile-program functions nil {:lexical-joins true})
          demand (lazy/open-program functions)]
      (is (= expected (:result (m/run initial))))
      (doseq [[backend program] [[:reference nil] [:mutable nil] [:eager eager] [:lazy demand]]
              fuel (range 7)]
        (let [paused (run backend program initial fuel)]
          (is (= (m/run initial fuel) paused))
          (when (= :paused (:status paused))
            (is (= (m/run initial) (run backend program (m/resume paused nil) 100)))))))))
