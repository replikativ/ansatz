(ns prototype.runtime-expr-order-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.data.json :as json]
            [prototype.runtime-expr :as expr]
            [prototype.runtime-abi :as abi]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.lazy-runtime :as lazy]
            [prototype.block-compile :as blocks]
            [prototype.scalar :as scalar]))

(def ops {:ref? m/ref? :node m/node})
(def fixture-sha "7461e7415d05cc5deaf016a287b2a4cae00d81608ecf04ca37e1d0b22228ae98")
(defn- fixture []
  (let [bytes (java.nio.file.Files/readAllBytes (.toPath (java.io.File. "fixtures/expr-order-native.json")))
        digest (.formatHex (java.util.HexFormat/of)
                 (.digest (java.security.MessageDigest/getInstance "SHA-256") bytes))]
    (assert (= fixture-sha digest))
    (json/read-str (String. bytes java.nio.charset.StandardCharsets/UTF_8) :key-fn keyword)))

(defn- cases []
  (let [world (atom (m/world {})) roots (atom [])]
    (letfn [(byte [tag value]
              (let [[state ref] (m/allocate @world :ctor tag [])
                    layout {:objects 0 :usize 0 :ssize 1}
                    bytes (scalar/write-bytes layout {} {:index 0 :offset 0 :type "uint8" :region :scalar} value)]
                (reset! world (update-in state [:heap (:id ref)] assoc :layout layout :scalar-bytes bytes)) ref))
            (plain [tag fields]
              (let [state (reduce #(m/retain %1 %2 1) @world fields)
                    [state value] (m/allocate state :ctor tag fields)]
                (reset! world state) value))
            (word [tag fields data annotation]
              (let [value (plain tag fields)
                    layout {:objects (count fields) :usize 0 :ssize (if annotation 9 8)}
                    bytes (scalar/write-bytes layout {} {:index (count fields) :offset 0 :type "uint64" :region :scalar} data)
                    bytes (if annotation (scalar/write-bytes layout bytes {:index (count fields) :offset 8 :type "uint8" :region :scalar} annotation) bytes)]
                (swap! world update-in [:heap (:id value)] assoc :layout layout :scalar-bytes bytes)
                value))
            (add [name value] (swap! roots conj [name value]))]
      (let [nx (word 1 [0 "x"] 0 nil) ny (word 1 [0 "y"] 0 nil)
            nnum (word 2 [0 2] 0 nil)
            [state huge] (m/allocate @world :mpz nil [])
            _ (reset! world (assoc-in state [:heap (:id huge) :integer] 73786976294838206464N))
            nhuge (word 2 [0 huge] 0 nil) nxs (word 1 [nx "a"] 0 nil)
            b0 (word 0 [0] 0 nil) b1 (word 0 [1] 0 nil) bx (word 0 [0] 4294967295N nil)
            px (word 4 [nx] 0 nil) py (word 4 [ny] 0 nil) mx (word 5 [nx] 0 nil)
            succ (word 1 [0] 1099511627776N nil) deep (word 1 [succ] 2199023255552N nil)
            maxxy (word 2 [px py] 1099511627776N nil) maxyx (word 2 [py px] 1099511627776N nil)
            imax (word 3 [px py] 1099511627776N nil)]
        (add "bvar0" b0) (add "bvar1" b1) (add "bvar0-highhash" bx) (add "bvar0-highbits" (word 0 [0] 1095216660480N nil))
        (add "fvar-x" (word 1 [nx] 0 nil)) (add "fvar-y" (word 1 [ny] 0 nil))
        (add "fvar-num" (word 1 [nnum] 0 nil)) (add "fvar-huge" (word 1 [nhuge] 0 nil))
        (add "fvar-prefix" (word 1 [nxs] 0 nil)) (add "mvar-x" (word 2 [nx] 0 nil))
        (doseq [[label value] [["zero" 0] ["param-x" px] ["param-y" py] ["mvar-x" mx]
                              ["succ" succ] ["deep" deep] ["max-xy" maxxy] ["max-yx" maxyx] ["imax" imax]]]
          (add (str "sort-" label) (word 3 [value] 0 nil)))
        (add "const-x-empty" (word 4 [nx 0] 0 nil)) (add "const-y-empty" (word 4 [ny 0] 0 nil))
        (add "const-x-levelx" (word 4 [nx (plain 1 [px 0])] 0 nil))
        (add "const-x-levely" (word 4 [nx (plain 1 [py 0])] 0 nil))
        (add "const-x-levelxy" (word 4 [nx (plain 1 [px (plain 1 [py 0])])] 0 nil))
        (add "app-01" (word 5 [b0 b1] 0 nil)) (add "app-10" (word 5 [b1 b0] 0 nil))
        (add "app-00" (word 5 [b0 b0] 0 nil))
        (add "lam-x" (word 6 [nx b0 b1] 0 0)) (add "lam-y-info" (word 6 [ny b0 b1] 0 2))
        (add "lam-domain" (word 6 [nx b1 b0] 0 0)) (add "lam-body" (word 6 [nx b0 b0] 0 0))
        (add "forall" (word 7 [nx b0 b1] 0 0))
        (add "let-false" (word 8 [nx b0 b0 b1] 0 0)) (add "let-true" (word 8 [nx b0 b0 b1] 0 1))
        (add "let-name" (word 8 [ny b0 b0 b1] 0 0)) (add "let-type" (word 8 [nx b1 b0 b1] 0 0))
        (add "let-value" (word 8 [nx b0 b1 b1] 0 0)) (add "let-body" (word 8 [nx b0 b0 b0] 0 0))
        (add "nat-lit0" (word 9 [(plain 0 [0])] 0 nil)) (add "nat-lit-huge" (word 9 [(plain 0 [huge])] 0 nil))
        (add "str-lit-a" (word 9 [(plain 1 ["a"])] 0 nil))
        (add "str-lit-unicode" (word 9 [(plain 1 ["𐀀"])] 0 nil))
        (add "str-lit-private" (word 9 [(plain 1 ["\uE000"])] 0 nil))
        (let [kint0 (plain 1 [(plain 0 [nx (plain 4 [0])]) 0])
              kint1 (plain 1 [(plain 0 [nx (plain 4 [1])]) 0])
              knat0 (plain 1 [(plain 0 [nx (plain 3 [0])]) 0])
              knat1 (plain 1 [(plain 0 [nx (plain 3 [1])]) 0])
              md0 (word 10 [kint0 b0] 0 nil) md1 (word 10 [kint1 b0] 0 nil)]
          (add "mdata-empty" (word 10 [0 b0] 0 nil)) (add "mdata-nat0" (word 10 [knat0 b0] 0 nil))
          (add "mdata-nat1" (word 10 [knat1 b0] 0 nil)) (add "mdata-body" (word 10 [knat0 b1] 0 nil))
          (add "mdata-int0" md0) (add "mdata-int1" md1)
          (add "app-incomparable-0" (word 5 [md0 b0] 0 nil))
          (add "app-incomparable-1" (word 5 [md1 b1] 0 nil)))
        (let [meta (fn [value] (word 10 [(plain 1 [(plain 0 [nx value]) 0]) b0] 0 nil))]
          (add "mdata-string-a" (meta (plain 0 ["a"]))) (add "mdata-string-b" (meta (plain 0 ["b"])))
          (add "mdata-bool-false" (meta (byte 1 0))) (add "mdata-bool-true" (meta (byte 1 1)))
          (add "mdata-name-x" (meta (plain 2 [nx]))) (add "mdata-name-y" (meta (plain 2 [ny])))
          (add "mdata-syntax-missing" (meta (plain 5 [0])))
          (add "mdata-syntax-atom" (meta (plain 5 [(plain 2 [0 "atom"])]))))
        (doseq [i [0 1]]
          (add (str "mdata-int-tail" i)
            (word 10 [(plain 1 [(plain 0 [nx (plain 4 [i])])
                               (plain 1 [(plain 0 [ny (plain 3 [i])]) 0])]) b0] 0 nil)))
        (add "proj-x0" (word 11 [nx 0 b0] 0 nil)) (add "proj-y0" (word 11 [ny 0 b0] 0 nil))
        (add "proj-x1" (word 11 [nx 1 b0] 0 nil)) (add "proj-body" (word 11 [nx 0 b1] 0 nil)))
      {:world @world :names (mapv first @roots) :roots (mapv second @roots)})))

(defn- extern-row [symbol]
  (let [name ["str" ["anonymous"] symbol]]
    {:name name :ir {:extern {:f name :xs [{:x {:idx 0} :ty "object" :borrow true}
                                          {:x {:idx 1} :ty "object" :borrow true}]
                             :type "uint8" :ext {:entries [{:standard {:backend ["str" ["anonymous"] "c"] :fn symbol}}]}}}}))

(deftest native-all-pairs-order-is-exact-and-borrowed
  (let [{:keys [world names roots]} (cases) native (fixture)]
    (is (= names (:names native)))
    (is (= 65 (count roots)))
    (is (= 4225 (count (:comparisons native))))
    (doseq [[a b quick structural] (:comparisons native)
            [symbol expected] [["lean_expr_quick_lt" quick] ["lean_expr_lt" structural]]]
      (let [[after actual] (expr/evaluate ops world symbol [(roots a) (roots b)])]
        (is (identical? world after))
        (is (= expected actual) (str symbol " " (names a) " / " (names b)))))))

(deftest actual-abi-all-backends-and-fuel-boundaries
  (let [{:keys [world roots names]} (cases)
        functions (into {} (map #(abi/lower (extern-row %))) ["lean_expr_quick_lt" "lean_expr_lt"])
        world (assoc world :functions functions)
        eager (blocks/compile-program functions nil {:lexical-joins true :compact-registers true})
        demand (lazy/open-program functions {:compile-threshold 2})
        selected (take-nth 137 (:comparisons (fixture)))]
    (doseq [[a b quick structural] selected
            [symbol expected] [["lean_expr_quick_lt" quick] ["lean_expr_lt" structural]]
            :let [initial (m/start world ["str" ["anonymous"] symbol] [(roots a) (roots b)])]
            fuel [0 1 2 3]]
      (let [reference (m/run initial fuel)]
        (is (= reference (u/freeze (u/run! (u/thaw initial) fuel))))
        (is (= reference (u/freeze (lazy/run! demand (u/thaw initial) fuel))))
        (is (= reference (u/freeze (blocks/run! eager (u/thaw initial) fuel))))
        (when (= :done (:status reference)) (is (= expected (:result reference))))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"ownership/type"
          (abi/lower (assoc-in (extern-row "lean_expr_quick_lt") [:ir :extern :xs 0 :borrow] false))))))

(deftest deep-collisions-are-stack-safe-and-invalid-cycles-trap
  (let [{:keys [world roots]} (cases)
        b0 (roots 0) b1 (roots 1)
        layout {:objects 2 :usize 0 :ssize 8}
        word (fn [world fields]
               (let [[world value] (m/scalar-constructor world 5 fields layout)
                     bytes (scalar/write-bytes layout {} {:index 2 :offset 0 :type "uint64" :region :scalar} 0)]
                 [(assoc-in world [:heap (:id value) :scalar-bytes] bytes) value]))
        [world left right] (loop [n 3000 world world left b0 right b1]
                             (if (zero? n) [world left right]
                               (let [[world left] (word world [b0 left])
                                     [world right] (word world [b0 right])]
                                 (recur (dec n) world left right))))]
    (is (= [world 1] (expr/evaluate ops world "lean_expr_quick_lt" [left right])))
    (is (= [world 0] (expr/evaluate ops world "lean_expr_quick_lt" [right left])))
    (let [cyclic (-> world (assoc-in [:heap (:id left) :fields] [b0 left])
                           (assoc-in [:heap (:id right) :fields] [b0 right]))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Cyclic"
            (expr/evaluate ops cyclic "lean_expr_quick_lt" [left right]))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"arity"
          (expr/evaluate ops world "lean_expr_quick_lt" [left])))))
