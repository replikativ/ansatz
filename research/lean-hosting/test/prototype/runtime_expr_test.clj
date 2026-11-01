(ns prototype.runtime-expr-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.runtime-expr :as runtime]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.scalar :as scalar]))

(def ops {:ref? m/ref? :node m/node})
(defn evaluate [world symbol args] (runtime/evaluate ops world symbol args))
(defn- cache-node
  ([world tag fields data] (cache-node world tag fields data nil))
  ([world tag fields data annotation]
   (let [[world value] (m/allocate world :ctor tag fields)
         layout {:objects (count fields) :usize 0 :ssize (if (nil? annotation) 8 9)}
         bytes (scalar/write-bytes layout {} {:index (count fields) :offset 0 :type "uint64" :region :scalar} data)
         bytes (if (nil? annotation) bytes
                 (scalar/write-bytes layout bytes {:index (count fields) :offset 8 :type "uint8" :region :scalar} annotation))]
     [(update-in world [:heap (:id value)] assoc :layout layout :scalar-bytes bytes) value])))
(defn- name-node [world text] (cache-node world 1 [0 text] 77))
(defn- byte-node [world tag fields byte]
  (let [[world value] (m/allocate world :ctor tag fields)
        layout {:objects (count fields) :usize 0 :ssize 1}
        bytes (scalar/write-bytes layout {} {:index (count fields) :offset 0 :type "uint8" :region :scalar} byte)]
    [(update-in world [:heap (:id value)] assoc :layout layout :scalar-bytes bytes) value]))
(defn- expr [world tag fields & [annotation]] (cache-node world tag fields 123 annotation))
(defn- level [world tag fields depth]
  (cache-node world tag fields (second (evaluate world "lean_level_mk_data"
                                                [123 depth (if (= tag 5) 1 0) (if (= tag 4) 1 0)]))))
(defn- compare-both [world left right expected]
  (is (= [world (first expected)] (evaluate world "lean_expr_eqv" [left right])))
  (is (= [world (second expected)] (evaluate world "lean_expr_equal" [left right]))))

(deftest pinned-native-cache-data-oracles
  ;; Obtained from the installed 4.33.1 native implementations through --run.
  ;; mkAppData inputs are unsafeCast UInt64→Expr.Data so all64bits reach C++.
  (doseq [[symbol args expected]
          [["lean_expr_mk_data" [18446744073709551615N 1048575 300 1 1 1 1] 18446744073709551615N]
           ["lean_expr_mk_data" [0 0 0 0 0 0 0] 0]
           ["lean_expr_mk_data" [4294967297N 7 9 1 0 1 0] 128681515155457N]
           ["lean_expr_mk_app_data" [0 0] 4973039801N]
           ["lean_expr_mk_app_data" [18446744073709551615N 0] 18446744071490995634N]
           ["lean_expr_mk_app_data" [4294967297N 987654321012345N] 987660324716846N]
           ["lean_level_mk_data" [18446744073709551615N 16777215 1 1] 18446742991377793023N]
           ["lean_level_mk_data" [4294967297N 2 0 1] 2207613190145N]]]
    (is (= [{} expected] (evaluate {} symbol args))))
  (doseq [[symbol args]
          [["lean_expr_mk_data" [0 1048576 0 0 0 0 0]]
           ["lean_expr_mk_data" [0 -1 0 0 0 0 0]]
           ["lean_expr_mk_data" [0 0 4294967296N 0 0 0 0]]
           ["lean_expr_mk_data" [0 0 0 2 0 0 0]]
           ["lean_level_mk_data" [0 16777216 0 0]]
           ["lean_level_mk_data" [18446744073709551616N 0 0 0]]]]
    (is (thrown? clojure.lang.ExceptionInfo (evaluate {} symbol args)))))

(deftest structural-level-equality-includes-every-constructor-and-caches
  (let [[world u] (name-node (m/world {}) "u")
        [world v] (name-node world "v")
        [world p] (level world 4 [u] 0)
        [world p2] (level world 4 [u] 0)
        [world q] (level world 4 [v] 0)
        [world mv] (level world 5 [u] 0)
        [world s] (level world 1 [p] 1)
        [world s2] (level world 1 [p2] 1)
        [world maxuv] (level world 2 [p q] 1)
        [world maxvu] (level world 2 [q p] 1)
        [world imaxuv] (level world 3 [p q] 1)]
    (doseq [[left right expected] [[0 (m/->Tag 0) 1] [p p2 1] [p q 0] [p mv 0]
                                  [s s2 1] [s p 0] [maxuv maxvu 0] [maxuv imaxuv 0]]]
      (is (= [world expected] (evaluate world "lean_level_eq" [left right]))))
    (let [changed-depth (first (cache-node world 1 [p2] 123))]
      ;; A same-structure node with an inconsistent cached depth is rejected by
      ;; native structural equality before comparing its child.
      (is (= 0 (second (evaluate changed-depth "lean_level_eq" [s (m/->Ref (dec (:next-id changed-depth)))])))))))

(deftest native-expression-equality-rules-on-real-constructor-layouts
  ;; Native 4.33.1 oracle: changed lambda name/info→true,false;
  ;; changed let nondep→false,false; fvar x/y→false,false;
  ;; mvar x/x→true,true; sort(mvar u)/sort(param u)→false,false.
  ;; Intentional identical cache hashes force collision-safe structural checks.
  (let [[world x] (name-node (m/world {}) "x")
        [world y] (name-node world "y")
        [world p] (level world 4 [x] 0)
        [world mv] (level world 5 [x] 0)
        [world t] (expr world 3 [0])
        [world b] (expr world 0 [0])
        [world b1] (expr world 0 [1])
        [world fx] (expr world 1 [x]) [world fy] (expr world 1 [y])
        [world mx] (expr world 2 [x]) [world mx2] (expr world 2 [x])
        [world sp] (expr world 3 [p]) [world sm] (expr world 3 [mv])
        [world us] (m/guest-list world [p mv]) [world vs] (m/guest-list world [mv p])
        [world c] (expr world 4 [x us]) [world c2] (expr world 4 [x us]) [world c3] (expr world 4 [x vs])
        [world app] (expr world 5 [fx b]) [world app2] (expr world 5 [fx b1])
        [world lam] (expr world 6 [x t b] 0) [world lam2] (expr world 6 [y t b] 1)
        [world pi] (expr world 7 [x t b] 0)
        [world let0] (expr world 8 [x t t b] 0) [world let1] (expr world 8 [y t t b] 1)
        [world let2] (expr world 8 [y t t b] 0)
        [world ln] (m/allocate world :ctor 0 [18446744073709551617N])
        [world ls] (m/allocate world :ctor 1 ["é😀"])
        [world en] (expr world 9 [ln]) [world es] (expr world 9 [ls])
        [world pr] (expr world 11 [x 0 t]) [world pr2] (expr world 11 [x 1 t])]
    (doseq [[left right expected] [[b b1 [0 0]] [fx fy [0 0]] [fx mx [0 0]] [mx mx2 [1 1]]
                                  [sp sm [0 0]] [c c2 [1 1]] [c c3 [0 0]] [app app2 [0 0]]
                                  [lam lam2 [1 0]] [lam pi [0 0]] [let0 let1 [0 0]] [let0 let2 [1 0]]
                                  [en en [1 1]] [es es [1 1]] [en es [0 0]] [pr pr2 [0 0]]]]
      (compare-both world left right expected))))

(defn- kv [world name data-value]
  (let [[world pair] (m/allocate world :ctor 0 [name data-value])]
    (m/guest-list world [pair])))
(defn- metadata-expr [world metadata child] (expr world 10 [metadata child]))

(deftest metadata-values-and-syntax-equality-ignore-only-source-info
  (let [[world x] (name-node (m/world {}) "x")
        [world y] (name-node world "y")
        [world t] (expr world 3 [0])
        [world synthetic] (byte-node world 1 [3 4] 1)
        [world s1] (m/allocate world :ctor 2 [(m/->Tag 2) "é"])
        [world s2] (m/allocate world :ctor 2 [synthetic "é"])
        [world s3] (m/allocate world :ctor 2 [(m/->Tag 2) "different"])
        [world a1] (m/allocate world :array 246 [s1])
        [world a2] (m/allocate world :array 246 [s2])
        [world n1] (m/allocate world :ctor 1 [(m/->Tag 2) x a1])
        [world n2] (m/allocate world :ctor 1 [synthetic x a2])
        [world sub1] (m/allocate world :ctor 0 ["xxéyy" 2 4])
        [world sub2] (m/allocate world :ctor 0 ["é" 0 2])
        [world pre1] (m/allocate world :ctor 0 [x])
        [world fields] (m/guest-list world ["field"])
        [world pre2] (m/allocate world :ctor 1 [y fields])
        [world pres] (m/guest-list world [pre1 pre2])
        [world ident1] (m/allocate world :ctor 3 [(m/->Tag 2) sub1 x pres])
        [world ident2] (m/allocate world :ctor 3 [synthetic sub2 x pres])
        [world bool0] (byte-node world 1 [] 0)
        [world bool1] (byte-node world 1 [] 1)
        [world missing1] (m/allocate world :ctor 5 [0])
        [world missing2] (m/allocate world :ctor 5 [(m/->Tag 0)])]
    (doseq [[left right expected] [[s1 s2 [1 1]] [s1 s3 [0 0]] [n1 n2 [1 1]] [ident1 ident2 [1 1]]
                                  [0 (m/->Tag 0) [1 1]]]]
      (let [[w d1] (m/allocate world :ctor 5 [left]) [w d2] (m/allocate w :ctor 5 [right])
            [w k1] (kv w x d1) [w k2] (kv w x d2)
            [w e1] (metadata-expr w k1 t) [w e2] (metadata-expr w k2 t)]
        (compare-both w e1 e2 expected)))
    (doseq [[tag a b expected] [[0 "str" "str" [1 1]] [2 x y [0 0]]
                              [3 12345678901234567890N 12345678901234567890N [1 1]]
                              [4 -12345678901234567890N -12345678901234567890N [1 1]]]]
      (let [[w d1] (m/allocate world :ctor tag [a]) [w d2] (m/allocate w :ctor tag [b])
            [w k1] (kv w x d1) [w k2] (kv w x d2)
            [w e1] (metadata-expr w k1 t) [w e2] (metadata-expr w k2 t)]
        (compare-both w e1 e2 expected)))
    (let [[w k1] (kv world x bool0) [w k2] (kv w x bool1)
          [w e1] (metadata-expr w k1 t) [w e2] (metadata-expr w k2 t)]
      (compare-both w e1 e2 [0 0]))
    ;; Native Expr equality compares ordered underlying KVMap lists, even
    ;; though Lean's KVMap BEq separately compares maps without order.
    (let [[w p1] (m/allocate world :ctor 0 [x missing1]) [w p2] (m/allocate w :ctor 0 [y missing2])
          [w l1] (m/guest-list w [p1 p2]) [w l2] (m/guest-list w [p2 p1])
          [w e1] (metadata-expr w l1 t) [w e2] (metadata-expr w l2 t)]
      (compare-both w e1 e2 [0 0]))))

(deftest deep-level-and-expression-equality-use-explicit-worklists
  (let [[world a] (expr (m/world {}) 0 [0])
        [world b] (expr world 0 [0])
        [world left right level-left level-right]
        (loop [i 0 world world left a right b ll 0 lr (m/->Tag 0)]
          (if (= i 4001) [world left right ll lr]
            (let [[w left] (expr world 5 [left a]) [w right] (expr w 5 [right b])
                  [w ll] (level w 1 [ll] (inc i)) [w lr] (level w 1 [lr] (inc i))]
              (recur (inc i) w left right ll lr))))]
    (compare-both world left right [1 1])
    (is (= [world 1] (evaluate world "lean_level_eq" [level-left level-right])))))

(deftest malformed-input-and-cycles-fail-without-mutating-world
  (let [[world a] (expr (m/world {}) 5 [0 0])
        [world b] (expr world 5 [0 0])
        world (-> world (assoc-in [:heap (:id a) :fields] [a a]) (assoc-in [:heap (:id b) :fields] [b b]))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Cyclic"
                         (evaluate world "lean_expr_eqv" [a b]))))
  (is (thrown? clojure.lang.ExceptionInfo (evaluate (m/world {}) "lean_expr_equal" [0 0])))
  (is (thrown? clojure.lang.ExceptionInfo (evaluate (m/world {}) "lean_level_eq" [42 42])))
  (is (thrown? clojure.lang.ExceptionInfo (evaluate {} "lean_expr_mk_data" []))))

(deftest borrowed-equality-reads-real-mutable-field-arrays-without-rc-changes
  (let [[world name] (name-node (m/world {}) "binder")
        [world t] (expr world 3 [0])
        [world b] (expr world 0 [0])
        [world e1] (expr world 6 [name t b] 0)
        [world e2] (expr world 6 [name t b] 0)
        world (m/mark-persistent world e1)
        machine (u/thaw world) before (u/freeze machine)
        mutable-ops {:ref? m/ref?
                     :node (fn [machine value] (.get ^java.util.Map (:heap machine) (:id value)))}]
    (doseq [symbol ["lean_expr_eqv" "lean_expr_equal"]]
      (let [[returned result] (runtime/evaluate mutable-ops machine symbol [e1 e2])]
        (is (identical? returned machine))
        (is (= 1 result))))
    (is (= before (u/freeze machine)))))

(deftest borrowed-expression-data-accessor
  (let [[world value] (cache-node (m/world {}) 0 [0] 18446744073709551615N)]
    (is (= [world 18446744073709551615N] (evaluate world "lean_expr_data" [value])))
    (let [persistent (m/mark-persistent world value)]
      (is (= [persistent 18446744073709551615N] (evaluate persistent "lean_expr_data" [value])))))
  (is (thrown? clojure.lang.ExceptionInfo (evaluate (m/world {}) "lean_expr_data" [0]))))
