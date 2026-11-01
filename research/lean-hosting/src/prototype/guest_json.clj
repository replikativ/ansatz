(ns prototype.guest-json
  "Borrow a pinned Lean4.33.1 Json value without guest execution or serialization.
   Layout sources: Lean/Data/Json/Basic.lean25,180 and
   Std/Data/DTreeMap/Internal/Def.lean27. Single-field Raw wrappers erase.
   JsonNumber is exact mantissa:Int *10^-exponent:Nat. Nonzero exponents above
   Integer/MAX_VALUE fail explicitly (outside JVM BigDecimal scale). Tree objects
   must have consistent sizes and strictly ordered unique Unicode keys."
  (:require [prototype.machine :as m]
            [prototype.native-scalar :as native]
            [prototype.constructor-layout :as layout]
            [prototype.runtime-string :as string])
  (:import [java.math BigDecimal]))

(def ^:private ops {:ref? m/ref? :node m/node})
(defn- fail [message data] (throw (ex-info message data)))
(defn- immediate [value]
  (cond (native/native-scalar? value) (native/payload value)
        (instance? prototype.machine.Tag value) (:tag value)
        (integer? value) value
        :else nil))
(defn- ctor! [world value tag objects scalar-size]
  (when-not (m/ref? value) (fail "Expected guest Json constructor reference" {:tag tag}))
  (let [node (m/node world value)]
    (when-not (and (= tag (:tag node)) (vector? (:fields node))
                   (layout/constructor-layout? node objects scalar-size))
      (fail "Invalid guest Json constructor layout" {:value value :tag tag}))
    node))
(defn- text! [world value]
  (when (m/ref? value)
    (let [node (m/node world value)]
      (when-not (and (= :string (:kind node)) (= 249 (:tag node))
                     (vector? (:fields node)) (empty? (:fields node))
                     (nil? (:layout node)) (empty? (:scalar-bytes node)))
        (fail "Invalid guest Json String layout" {:value value}))))
  (let [s (string/string-value ops world value)]
    ;; Validate Unicode even for immutable host strings; native imported strings
    ;; were validated by the receiver, but this API also accepts local values.
    (string/evaluate {} nil "lean_string_utf8_byte_size" [s]) s))
(defn- number! [world value]
  (let [[mantissa exponent] (:fields (ctor! world value 0 2 0))
        n (native/int-value ops world mantissa)
        scale (native/nat-value ops world exponent)]
    (cond
      (zero? n) 0
      (zero? scale) n
      (> scale Integer/MAX_VALUE)
      (fail "Guest Json decimal exponent exceeds exact JVM scale" {:exponent scale})
      :else
      (let [decimal (.stripTrailingZeros (BigDecimal. (biginteger n) (int scale)))]
        (if (<= (.scale decimal) 0) (bigint (.toBigIntegerExact decimal)) decimal)))))
(defn- string-compare [^String a ^String b]
  ;; Valid UTF8 lexical ordering equals Unicode scalar ordering, whereas Java's
  ;; UTF16 compareTo reverses supplementary characters relative to U+E000.
  (loop [i 0 j 0]
    (cond (= i (.length a)) (if (= j (.length b)) 0 -1)
          (= j (.length b)) 1
          :else (let [x (.codePointAt a i) y (.codePointAt b j)]
                  (if (= x y) (recur (+ i (Character/charCount x)) (+ j (Character/charCount y)))
                    (compare x y))))))
(defn- object-entries! [world root]
  (loop [todo [[:tree root]] sizes [] entries [] seen #{} previous nil]
    (if (empty? todo)
      (do (when-not (= 1 (count sizes)) (fail "Invalid guest Json object tree" {})) entries)
      (let [[op a b] (peek todo) todo (pop todo)]
        (case op
          :tree
          (if (= 1 (immediate a))
            (recur todo (conj sizes 0) entries seen previous)
            (let [[size key value left right] (:fields (ctor! world a 0 5 0))
                  size (native/nat-value ops world size)
                  key (text! world key)]
              (when (contains? seen (:id a)) (fail "Cyclic or shared guest Json object tree" {}))
              (recur (conj todo [:finish size] [:tree right] [:entry key value] [:tree left])
                     sizes entries (conj seen (:id a)) previous)))
          :entry
          (do (when (and previous (not (neg? (string-compare previous a))))
                (fail "Unordered or duplicate guest Json object key" {:key a}))
              (recur todo sizes (conj entries [a b]) seen a))
          :finish
          (let [right (peek sizes) sizes (pop sizes) left (peek sizes) sizes (pop sizes)
                size (+ 1 left right)]
            (when-not (= a size) (fail "Guest Json object size mismatch" {:expected a :actual size}))
            (recur todo (conj sizes size) entries seen previous)))))))
(defn- array-fields! [world value]
  (when-not (m/ref? value) (fail "Expected guest Json array reference" {}))
  (let [node (m/node world value)]
    (when-not (and (= :array (:kind node)) (= 246 (:tag node)) (vector? (:fields node))
                   (nil? (:layout node)) (empty? (:scalar-bytes node)))
      (fail "Invalid guest Json array layout" {:value value}))
    (:fields node)))

(defn project
  "Return a host Json value, borrowing all guest ownership. Objects default to
   string keys; optional :key-fn (e.g.keyword) transforms keys after validation.
   Exact integers/BigDecimals avoid floating rounding. Cyclic/malformed layouts,
   duplicate/transformed-colliding keys and unsupported decimal scales fail closed.
   No retain/release, guest writes, IO, or initialization occurs."
  ([world value] (project world value {}))
  ([world value {:keys [key-fn] :or {key-fn identity} :as options}]
   (when-not (and (map? options) (every? #{:key-fn} (keys options)) (ifn? key-fn))
     (fail "Invalid guest Json projection options" {}))
   (loop [todo [[:visit value]] results [] active #{} memo {}]
     (if (empty? todo)
       (do (when-not (= 1 (count results)) (fail "Invalid guest Json projection stack" {})) (peek results))
       (let [[op a b c] (peek todo) todo (pop todo)]
         (case op
           :visit
           (cond
             (= 0 (immediate a)) (recur todo (conj results nil) active memo)
             (not (m/ref? a)) (fail "Invalid guest Json immediate" {:value a})
             (contains? active (:id a)) (fail "Cyclic guest Json value" {:value a})
             (contains? memo (:id a)) (recur todo (conj results (get memo (:id a))) active memo)
             :else
             (let [node (m/node world a) tag (:tag node)
                   _ (when-not (and (= :ctor (:kind node)) (integer? tag) (<= 0 tag 5))
                       (fail "Invalid guest Json constructor tag" {:value a :tag tag}))
]
               (case tag
                 0 (do (ctor! world a 0 0 0) (recur todo (conj results nil) active (assoc memo (:id a) nil)))
                 1 (let [node (ctor! world a 1 0 1) b (get (:scalar-bytes node) 0)]
                     (when-not (contains? #{0 1} b) (fail "Invalid guest Json Bool" {:value b}))
                     (recur todo (conj results (= 1 b)) active (assoc memo (:id a) (= 1 b))))
                 2 (let [[number] (:fields (ctor! world a 2 1 0)) result (number! world number)]
                     (recur todo (conj results result) active (assoc memo (:id a) result)))
                 3 (let [[text] (:fields (ctor! world a 3 1 0)) result (text! world text)]
                     (recur todo (conj results result) active (assoc memo (:id a) result)))
                 4 (let [[array] (:fields (ctor! world a 4 1 0)) fields (array-fields! world array)]
                     (recur (into (conj todo [:array (:id a) (count fields)])
                                  (map #(vector :visit %) (rseq fields)))
                            results (conj active (:id a)) memo))
                 5 (let [[tree] (:fields (ctor! world a 5 1 0)) entries (object-entries! world tree)]
                     (recur (into (conj todo [:object (:id a) (mapv first entries)])
                                  (map #(vector :visit (second %)) (rseq entries)))
                            results (conj active (:id a)) memo)))))
           :array
           (let [start (- (count results) b) value (into [] (subvec results start)) results (subvec results 0 start)]
             (recur todo (conj results value) (disj active a) (assoc memo a value)))
           :object
           (let [start (- (count results) (count b)) values (subvec results start)
                 value (reduce (fn [result [key v]]
                                 (let [key (key-fn key)]
                                   (when (contains? result key) (fail "Colliding transformed guest Json object key" {}))
                                   (assoc result key v))) {} (map vector b values))]
             (recur todo (conj (subvec results 0 start) value) (disj active a) (assoc memo a value)))))))))
