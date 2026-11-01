(ns prototype.runtime-expr
  "Lean 4.33.1 cached Expr/Level data, borrowed equality and ordering.
   Sources: kernel/{expr,level,expr_eq_fn}.cpp at release commit
   819816b2e0a3bf405af45ae5c7af2491d8f5bee6; installed Lean/{Expr,Level}.lean.
   Constructor layouts were checked against the producer's actual _override IR.
   Ordering also follows pinned library/expr_lt.cpp and util/{name,kvmap}.cpp.
   Equality is structural, not kernel definitional equality or Level.eqv
   normalization. No native kernel objects or host round trips are involved."
  (:require [prototype.scalar :as scalar]
            [prototype.native-scalar :as native]
            [prototype.runtime-string :as string]
            [prototype.runtime-object :as object]))

(def supported-symbols
  {"lean_expr_data" {:arity 1}
   "lean_expr_mk_data" {:arity 7} "lean_expr_mk_app_data" {:arity 2}
   "lean_level_mk_data" {:arity 4} "lean_level_eq" {:arity 2}
   "lean_expr_quick_lt" {:arity 2} "lean_expr_lt" {:arity 2}
   "lean_expr_eqv" {:arity 2} "lean_expr_equal" {:arity 2}})

(defn- fail [message data] (throw (ex-info message data)))
(defn- power2 [n] #?(:clj (bigint (.shiftLeft java.math.BigInteger/ONE n)) :cljs (js/Math.pow 2 n)))
(defn- add [a b] #?(:clj (+' a b) :cljs (+ a b)))
(defn- multiply [a b] #?(:clj (*' a b) :cljs (* a b)))
(defn- bool! [x]
  (let [x (scalar/integer! "uint8" x)]
    (when-not (contains? #{0 1} x) (fail "Invalid guest Bool" {:value x})) x))
(defn- at-bit [data n] (mod (quot data (power2 n)) 2))
(defn- field [data offset width] (mod (quot data (power2 offset)) (power2 width)))
(defn- pack [parts]
  (scalar/integer! "uint64" (reduce (fn [data [value offset]] (add data (multiply value (power2 offset)))) 0 parts)))

(defn- expr-data [ops world [hash range depth fvar mvar lmvar lparam]]
  (when (and (:ref? ops) ((:ref? ops) range))
    (fail "Too many bound variables: expected native small Nat" {}))
  (let [hash (scalar/integer! "uint64" hash)
        range (native/nat-value ops world range)
        depth (scalar/integer! "uint32" depth)
        [fvar mvar lmvar lparam] (mapv bool! [fvar mvar lmvar lparam])]
    (when (> range 1048575) (fail "Too many bound variables" {:range range}))
    (pack [[(mod hash (power2 32)) 0] [(min depth 255) 32]
           [fvar 40] [mvar 41] [lmvar 42] [lparam 43] [range 44]])))

(defn- level-data [ops world [hash depth mvar param]]
  (when (and (:ref? ops) ((:ref? ops) depth))
    (fail "Universe level depth is too big: expected native small Nat" {}))
  (let [hash (scalar/integer! "uint64" hash)
        depth (native/nat-value ops world depth)
        mvar (bool! mvar) param (bool! param)]
    (when (> depth 16777215) (fail "Universe level depth is too big" {:depth depth}))
    (pack [[(mod hash (power2 32)) 0] [mvar 32] [param 33] [depth 40]])))

(defn- app-data [ops world [fdata adata]]
  (let [fdata (scalar/integer! "uint64" fdata) adata (scalar/integer! "uint64" adata)
        hash (second (string/evaluate ops world "lean_uint64_mix_hash" [fdata adata]))]
    (pack (into [[(mod hash (power2 32)) 0]
                 [(min 255 (inc (max (field fdata 32 8) (field adata 32 8)))) 32]
                 [(max (field fdata 44 20) (field adata 44 20)) 44]]
                (map (fn [i] [(max (at-bit fdata i) (at-bit adata i)) i]) (range 40 44))))))

(defn- zero-value? [ops value]
  (and (not ((:ref? ops) value))
       (or (= value 0)
           (and (native/native-scalar? value) (zero? (native/payload value)))
           (and (map? value) (= 0 (:tag value))))))
(defn- node! [ops world value counts label]
  (when-not ((:ref? ops) value) (fail "Expected guest constructor reference" {:type label :value value}))
  (let [node ((:node ops) world value) expected (get counts (:tag node))]
    (when-not (and (= :ctor (:kind node)) (some? expected) (= expected (count (:fields node))))
      (fail "Malformed guest constructor" {:type label :tag (:tag node) :fields (count (:fields node))}))
    (update node :fields vec)))
(defn- scalar-field [node offset type]
  (scalar/read-bytes (:layout node) (:scalar-bytes node)
                     {:index (count (:fields node)) :offset offset :type type :region :scalar}))
(defn- cache-data [node] (scalar-field node 0 "uint64"))
(defn- identical-ref? [ops left right]
  (and ((:ref? ops) left) ((:ref? ops) right) (= left right)))

(def ^:private expr-counts {0 1, 1 1, 2 1, 3 1, 4 2, 5 2, 6 3, 7 3, 8 4, 9 1, 10 2, 11 3})
(def ^:private level-counts {1 1, 2 2, 3 2, 4 1, 5 1})
(defn- name-equal? [ops world left right]
  (= 1 (second (object/evaluate ops world "lean_name_eq" [left right]))))
(defn- string-equal? [ops world left right]
  (= 1 (second (string/evaluate ops world "lean_string_dec_eq" [left right]))))

(defn- list-children [ops world kind left right]
  (let [lz (zero-value? ops left) rz (zero-value? ops right)]
    (if (or lz rz) (when (and lz rz) [])
      (let [l (:fields (node! ops world left {1 2} :list))
            r (:fields (node! ops world right {1 2} :list))]
        [[(second kind) (l 0) (r 0)] [kind (l 1) (r 1)]]))))

(defn- expr-children [ops world left right binder-info?]
  (let [l (node! ops world left expr-counts :expr) r (node! ops world right expr-counts :expr)
        lf (:fields l) rf (:fields r) tag (:tag l)]
    (when (and (= tag (:tag r)) (= (mod (cache-data l) (power2 32)) (mod (cache-data r) (power2 32))))
      (if (identical-ref? ops left right) []
        (case tag
          0 [[:nat (lf 0) (rf 0)]]
          (1 2) [[:name (lf 0) (rf 0)]] ; FVarId/MVarId wrappers are erased.
          3 [[:level (lf 0) (rf 0)]]
          4 [[:name (lf 0) (rf 0)] [[:list :level] (lf 1) (rf 1)]]
          5 [[:expr (lf 1) (rf 1)] [:expr (lf 0) (rf 0)]]
          (6 7) (when (or (not binder-info?) (= (scalar-field l 8 "uint8") (scalar-field r 8 "uint8")))
                  (cond-> [[:expr (lf 1) (rf 1)] [:expr (lf 2) (rf 2)]]
                    binder-info? (conj [:name (lf 0) (rf 0)])))
          8 (when (= (scalar-field l 8 "uint8") (scalar-field r 8 "uint8"))
              (cond-> [[:expr (lf 1) (rf 1)] [:expr (lf 2) (rf 2)] [:expr (lf 3) (rf 3)]]
                binder-info? (conj [:name (lf 0) (rf 0)])))
          9 [[:literal (lf 0) (rf 0)]]
          10 [[:expr (lf 1) (rf 1)] [[:list :kv-entry] (lf 0) (rf 0)]]
          11 [[:expr (lf 2) (rf 2)] [:name (lf 0) (rf 0)] [:nat (lf 1) (rf 1)]])))))

(defn- level-children [ops world left right]
  (let [lz (zero-value? ops left) rz (zero-value? ops right)]
    (if (or lz rz) (when (and lz rz) [])
      (let [l (node! ops world left level-counts :level) r (node! ops world right level-counts :level)
            tag (:tag l) ld (cache-data l) rd (cache-data r)
            lf (:fields l) rf (:fields r)]
        (when (and (= tag (:tag r)) (= (mod ld (power2 32)) (mod rd (power2 32))))
          (cond
            (identical-ref? ops left right) []
            (contains? #{4 5} tag) [[:name (lf 0) (rf 0)]]
            (not= (field ld 40 24) (field rd 40 24)) nil
            (= 1 tag) [[:level (lf 0) (rf 0)]]
            :else [[:level (lf 0) (rf 0)] [:level (lf 1) (rf 1)]]))))))

(defn- children [ops world kind left right binder-info?]
  (if (and (vector? kind) (= :list (first kind)))
    (list-children ops world kind left right)
    (case kind
      :expr (expr-children ops world left right binder-info?)
      :level (level-children ops world left right)
      :name (when (name-equal? ops world left right) [])
      :string (when (string-equal? ops world left right) [])
      :nat (when (= (native/nat-value ops world left) (native/nat-value ops world right)) [])
      :int (when (= (native/int-value ops world left) (native/int-value ops world right)) [])
      :kv-entry (let [l (:fields (node! ops world left {0 2} :kv-entry))
                      r (:fields (node! ops world right {0 2} :kv-entry))]
                  [[:name (l 0) (r 0)] [:data-value (l 1) (r 1)]])
      :literal (let [l (node! ops world left {0 1, 1 1} :literal)
                     r (node! ops world right {0 1, 1 1} :literal)]
                 (when (= (:tag l) (:tag r))
                   [[(if (= 0 (:tag l)) :nat :string) (first (:fields l)) (first (:fields r))]]))
      :data-value (let [counts {0 1, 1 0, 2 1, 3 1, 4 1, 5 1}
                        l (node! ops world left counts :data-value) r (node! ops world right counts :data-value)
                        tag (:tag l)]
                    (when (= tag (:tag r))
                      (if (= 1 tag)
                        (when (= (bool! (scalar-field l 0 "uint8")) (bool! (scalar-field r 0 "uint8"))) [])
                        [[(get {0 :string, 2 :name, 3 :nat, 4 :int, 5 :syntax} tag)
                          (first (:fields l)) (first (:fields r))]])))
      :syntax (let [lz (zero-value? ops left) rz (zero-value? ops right)]
                (if (or lz rz) (when (and lz rz) [])
                  (let [counts {1 3, 2 2, 3 4}
                        l (node! ops world left counts :syntax) r (node! ops world right counts :syntax)
                        lf (:fields l) rf (:fields r)]
                    (when (= (:tag l) (:tag r))
                      (case (:tag l)
                        1 [[:name (lf 1) (rf 1)] [:syntax-array (lf 2) (rf 2)]]
                        2 [[:string (lf 1) (rf 1)]]
                        3 [[:substring (lf 1) (rf 1)] [:name (lf 2) (rf 2)]
                           [[:list :preresolved] (lf 3) (rf 3)]])))))
      :syntax-array (let [l ((:node ops) world left) r ((:node ops) world right)]
                      (when-not (and (= :array (:kind l)) (= :array (:kind r)))
                        (fail "Malformed guest Syntax array" {}))
                      (when (= (count (:fields l)) (count (:fields r)))
                        (mapv (fn [x y] [:syntax x y]) (:fields l) (:fields r))))
      :substring (when (= 1 (second (string/evaluate
                                     ;; structEq borrows its syntax subobjects.
                                     ;; Reuse the raw byte comparison without
                                     ;; transferring ownership of substrings.
                                     (assoc ops :release (fn [w _ _] w)) world "lean_substring_beq" [left right]))) [])
      :preresolved (let [l (node! ops world left {0 1, 1 2} :preresolved)
                         r (node! ops world right {0 1, 1 2} :preresolved)
                         lf (:fields l) rf (:fields r)]
                     (when (= (:tag l) (:tag r))
                       (cond-> [[:name (lf 0) (rf 0)]]
                         (= 1 (:tag l)) (conj [[:list :string] (lf 1) (rf 1)])))))))

(defn- equal? [ops world kind left right binder-info?]
  (loop [pending [[kind left right]] active #{} complete #{}]
    (if (empty? pending) true
      (let [[kind left right :as entry] (peek pending) pending (pop pending)]
        (if (= :exit kind)
          (recur pending (disj active left) (conj complete left))
          (cond
            (contains? complete entry) (recur pending active complete)
            (contains? active entry) (fail "Cyclic guest Expr/Level value" {:kind kind})
            :else
            (if-let [next (children ops world kind left right binder-info?)]
              (recur (into (conj pending [:exit entry]) (rseq next)) (conj active entry) complete)
              false)))))))

;; Pinned library/expr_lt.cpp, kernel/level.cpp, util/name.cpp and kvmap.cpp.
;; Keep equality separate from ordering: metadata Int/Syntax values deliberately
;; have neither direction less-than in pinned C++, despite unequal values.
(defn- comparison-equal? [ops world memo kind left right]
  (let [root [kind left right]]
    (loop [pending [root] active #{}]
      (if (empty? pending) true
        (let [[kind left right :as entry] (peek pending) pending (pop pending)]
          (cond
            (= :exit kind)
            (do (vswap! memo assoc left true) (recur pending (disj active left)))
            (contains? @memo entry)
            (if (get @memo entry) (recur pending active)
              (do (vswap! memo #(reduce (fn [m key] (assoc m key false)) % active)) false))
            (contains? active entry) (fail "Cyclic guest Expr/Level value" {:kind kind})
            :else
            (if-let [next (children ops world kind left right false)]
              (recur (into (conj pending [:exit entry]) (rseq next)) (conj active entry))
              (do (vswap! memo #(reduce (fn [m key] (assoc m key false)) (assoc % entry false) active)) false))))))))

(defn- string-order [ops world left right]
  (dec (second (string/evaluate ops world "lean_string_compare" [left right]))))

(defn- name-parts [ops world value]
  (loop [value value parts [] seen #{}]
    (if (zero-value? ops value) parts
      (do
        (when (contains? seen value) (fail "Cyclic guest Name" {}))
        (let [node (node! ops world value {1 2, 2 2} :name)
              [parent payload] (:fields node)]
          (recur parent (conj parts [(:tag node) payload]) (conj seen value)))))))

(defn- name-order [ops world left right]
  ;; Prefix-first lexicographic limbs; numeric segments precede string segments.
  ;; Cached Name hashes do not participate in name::cmp_core.
  (loop [left (rseq (name-parts ops world left)) right (rseq (name-parts ops world right))]
    (cond
      (nil? left) (if (nil? right) 0 -1)
      (nil? right) 1
      :else
      (let [[lt lv] (first left) [rt rv] (first right)
            c (if (not= lt rt) (if (= lt 2) -1 1)
                (if (= lt 1) (string-order ops world lv rv)
                  (compare (native/nat-value ops world lv) (native/nat-value ops world rv))))]
        (if (zero? c) (recur (next left) (next right)) c)))))

(defn- level-view [ops world value]
  (if (zero-value? ops value) {:tag 0 :fields [] :data 2221}
    (let [node (node! ops world value level-counts :level)]
      (assoc node :data (cache-data node)))))

(defn- expr-order-tasks [ops world memo left right use-hash?]
  (let [l (node! ops world left expr-counts :expr) r (node! ops world right expr-counts :expr)
        tag (:tag l) lf (:fields l) rf (:fields r)
        hash-order (when (and use-hash? (= tag (:tag r)) (not (identical-ref? ops left right)))
                     (compare (field (cache-data l) 0 32) (field (cache-data r) 0 32)))
        same? (fn [kind a b] (comparison-equal? ops world memo kind a b))
        child (fn [kind i] [[kind (lf i) (rf i)]])]
    (cond
      (identical-ref? ops left right) 0
      (not= tag (:tag r)) (compare tag (:tag r))
      (and use-hash? (not (zero? hash-order))) hash-order
      (same? :expr left right) 0
      :else
      (case tag
        0 (child :nat 0)
        (1 2) (child :name 0)
        3 (child :level 0)
        4 (if (name-equal? ops world (lf 0) (rf 0))
            [[ :levels (lf 1) (rf 1)]] (child :name 0))
        5 (child :expr (if (same? :expr (lf 0) (rf 0)) 1 0))
        (6 7) (child :expr (if (same? :expr (lf 1) (rf 1)) 2 1))
        8 (let [c (compare (scalar-field l 8 "uint8") (scalar-field r 8 "uint8"))]
            (if (not (zero? c)) c
              (child :expr (cond (not (same? :expr (lf 1) (rf 1))) 1
                                (not (same? :expr (lf 2) (rf 2))) 2 :else 3))))
        9 (child :literal 0)
        10 (if (same? :expr (lf 1) (rf 1)) (child :kv-list 0) (child :expr 1))
        11 (cond (not (same? :expr (lf 2) (rf 2))) (child :expr 2)
                 (not (name-equal? ops world (lf 0) (rf 0))) (child :name 0)
                 :else (child :nat 1))))))

(defn- level-order-tasks [ops world memo left right use-hash?]
  (let [l (level-view ops world left) r (level-view ops world right)
        ld (:data l) rd (:data r) tag (:tag l) lf (:fields l) rf (:fields r)
        depth-order (compare (field ld 40 24) (field rd 40 24))
        hash-order (when use-hash? (compare (field ld 0 32) (field rd 0 32)))]
    (cond
      (or (= left right) (identical-ref? ops left right)) 0
      (not (zero? depth-order)) depth-order
      (not= tag (:tag r)) (compare tag (:tag r))
      (and use-hash? (not (zero? hash-order))) hash-order
      (comparison-equal? ops world memo :level left right) 0
      :else
      (case tag
        0 0
        (4 5) [[:name (lf 0) (rf 0)]]
        1 [[:level (lf 0) (rf 0)]]
        (2 3) (let [i (if (comparison-equal? ops world memo :level (lf 0) (rf 0)) 1 0)]
                [[:level (lf i) (rf i)]])))))

(defn- order-tasks [ops world memo kind left right use-hash?]
  (case kind
    :expr (expr-order-tasks ops world memo left right use-hash?)
    :level (level-order-tasks ops world memo left right use-hash?)
    :name (name-order ops world left right)
    :nat (compare (native/nat-value ops world left) (native/nat-value ops world right))
    :string (string-order ops world left right)
    :literal (let [l (node! ops world left {0 1, 1 1} :literal)
                   r (node! ops world right {0 1, 1 1} :literal)]
               (if (not= (:tag l) (:tag r)) (compare (:tag l) (:tag r))
                 [[(if (= 0 (:tag l)) :nat :string) (first (:fields l)) (first (:fields r))]]))
    :levels (let [lz (zero-value? ops left) rz (zero-value? ops right)]
              (cond lz (if rz 0 -1) rz 1
                    :else
                    (let [lf (:fields (node! ops world left {1 2} :list))
                          rf (:fields (node! ops world right {1 2} :list))]
                      (if (comparison-equal? ops world memo :level (lf 0) (rf 0))
                        [[:levels (lf 1) (rf 1)]] [[:level (lf 0) (rf 0)]]))))
    :kv-list (let [lz (zero-value? ops left) rz (zero-value? ops right)]
               (cond lz (if rz 0 -1) rz 1
                     :else
                     (let [lf (:fields (node! ops world left {1 2} :list))
                           rf (:fields (node! ops world right {1 2} :list))]
                       [[:kv-entry (lf 0) (rf 0)] [:kv-list (lf 1) (rf 1)]])))
    :kv-entry (let [lf (:fields (node! ops world left {0 2} :kv-entry))
                    rf (:fields (node! ops world right {0 2} :kv-entry))]
                (if (name-equal? ops world (lf 0) (rf 0))
                  [[:data-value (lf 1) (rf 1)]] [[:name (lf 0) (rf 0)]]))
    :data-value (let [counts {0 1, 1 0, 2 1, 3 1, 4 1, 5 1}
                      l (node! ops world left counts :data-value)
                      r (node! ops world right counts :data-value) tag (:tag l)]
                  (cond (not= tag (:tag r)) (compare tag (:tag r))
                        (= tag 1) (compare (bool! (scalar-field l 0 "uint8"))
                                           (bool! (scalar-field r 0 "uint8")))
                        (contains? #{4 5} tag) 0 ; Pinned C++ TODO: Int/Syntax comparison.
                        :else [[(get {0 :string, 2 :name, 3 :nat} tag)
                                (first (:fields l)) (first (:fields r))]]))))

(defn- expression-lt? [ops world left right use-hash?]
  (let [memo (volatile! {})]
    (loop [pending [[:expr left right]] active #{}]
      (if (empty? pending) false
        (let [[kind left right :as entry] (peek pending) pending (pop pending)]
          (if (= :exit kind)
            (recur pending (disj active left))
            (do
              (when (contains? active entry) (fail "Cyclic guest Expr/Level ordering" {:kind kind}))
              (let [result (order-tasks ops world memo kind left right use-hash?)]
                (if (number? result)
                  (if (zero? result) (recur pending active) (neg? result))
                  (recur (into (conj pending [:exit entry]) (rseq result)) (conj active entry)))))))))))

(defn evaluate
  "Evaluate raw arguments. All arguments are borrowed (cache packers' Nat
   range/depth included); world/RC is unchanged. Bool results are uint8 0/1.
   CLJS rejects cache values beyond exact Number range, as scalar.cljc does.
   Structural equality covers all Expr/Level constructors, ordered metadata,
   all DataValue cases and Syntax.structEq (which ignores source info).
   quickLt compares kind, then low32 cached hash, then structural tie-breaks;
   lt omits the hash comparison. Levels compare depth before kind/hash. Binder
   names/info are ignored; let nondep and ordered metadata participate. Pinned
   metadata Int/Syntax ordering is intentionally incomparable, not invented.
   All traversal is iterative with invocation-local equality memoization.
   Heartbeat charging is not modeled; malformed layouts and traversed cycles fail."
  [ops world symbol args]
  (let [spec (get supported-symbols symbol)]
    (when-not spec (fail "Unsupported Expr/Level runtime extern" {:symbol symbol}))
    (when-not (= (:arity spec) (count args)) (fail "Expr/Level runtime arity mismatch" {:symbol symbol})))
  [world (case symbol
           "lean_expr_quick_lt" (if (expression-lt? ops world (first args) (second args) true) 1 0)
           "lean_expr_lt" (if (expression-lt? ops world (first args) (second args) false) 1 0)
           "lean_expr_data" (cache-data (node! ops world (first args) expr-counts :expr))
           "lean_expr_mk_data" (expr-data ops world args)
           "lean_level_mk_data" (level-data ops world args)
           "lean_expr_mk_app_data" (app-data ops world args)
           "lean_level_eq" (if (equal? ops world :level (first args) (second args) false) 1 0)
           ("lean_expr_eqv" "lean_expr_equal")
           (if (equal? ops world :expr (first args) (second args) (= symbol "lean_expr_equal")) 1 0))])
