(ns prototype.heap-overlay-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.heap-overlay :as overlay]
            [prototype.mutable :as u] [prototype.machine :as m])
  (:import [java.util Map HashMap HashSet AbstractMap$SimpleImmutableEntry]
           [java.util.function Function BiFunction]))

(defn- contents [^Map map] (HashMap. map))
(defn- entry [k v] (AbstractMap$SimpleImmutableEntry. k v))
(defn- binary [f] (reify BiFunction (apply [_ a b] (f a b))))
(defn- unary [f] (reify Function (apply [_ a] (f a))))

(deftest map-abstract-contract-null-and-independent-overlays
  (let [base {"a" 1 "nil" nil nil "nil-key"}
        dirty (HashSet.) ^Map left (overlay/overlay base dirty)
        ^Map right (overlay/overlay base) expected (HashMap. ^Map base)]
    (is (= 3 (.size left)))
    (is (.containsKey left "nil"))
    (is (nil? (.get left "nil")))
    (is (.containsValue left nil))
    (is (= "nil-key" (.get left nil)))
    (doseq [[k v] [["a" 2] ["b" nil] [nil 3]]]
      (is (= (.put expected k v) (.put left k v))))
    (is (= (.remove expected "a") (.remove left "a")))
    (is (nil? (.remove left "missing")))
    (is (= (.put expected "a" 7) (.put left "a" 7)))
    (.putAll left {"c" 9 "d" nil}) (.putAll expected {"c" 9 "d" nil})
    (is (.equals expected left))
    (is (.equals left expected))
    (is (= (.hashCode expected) (.hashCode left)))
    (is (= (.size expected) (.size left) (.size (.entrySet left))))
    (is (= (set (.keySet expected)) (set (.keySet left))))
    (is (= {"a" 1 "nil" nil nil "nil-key"} (into {} right) base))
    (is (.containsAll dirty ["a" "b" nil "c" "d"]))
    (.clear left)
    (is (.isEmpty left))
    (is (empty? (.entrySet left)))
    (.put left "a" 8)
    (is (= {"a" 8} (into {} left)))
    (is (= base (into {} right)))))

(deftest views-stay-live-and-removals-mark-dirty-with-immutable-entries
  (let [dirty (HashSet.) ^Map map (overlay/overlay {"a" 1 "b" nil} dirty)
        entries (.entrySet map) keys (.keySet map) values (.values map)]
    (.put map "c" 3)
    (is (= 3 (.size entries) (.size keys) (.size values)))
    (is (.contains entries (entry "b" nil)))
    (is (not (.contains entries (entry "absent" nil))))
    (is (.remove keys "a"))
    (is (not (.containsKey map "a")))
    (is (.remove values 3))
    (is (.contains dirty "c"))
    (let [it (.iterator entries) e (.next it)]
      (is (thrown? UnsupportedOperationException (.setValue ^java.util.Map$Entry e 10)))
      (.remove it)
      (is (thrown? IllegalStateException (.remove it))))
    (is (.isEmpty map))
    (.put map "z" 4)
    (is (.contains keys "z"))
    (.clear values)
    (is (.isEmpty map))
    (is (.contains dirty "z"))))

(deftest java-default-mutators-use-the-effective-map-and-dirty-set
  (let [dirty (HashSet.) ^Map map (overlay/overlay {"a" 1 "nil" nil} dirty)]
    (is (= 9 (.getOrDefault map "absent" 9)))
    (is (nil? (.getOrDefault map "nil" 9)))
    (is (= 1 (.putIfAbsent map "a" 2)))
    (is (nil? (.putIfAbsent map "nil" 3)))
    (is (= 4 (.computeIfAbsent map "b" (unary (constantly 4)))))
    (is (= 5 (.computeIfPresent map "b" (binary (fn [_ v] (inc v))))))
    (is (= 6 (.compute map "b" (binary (fn [_ v] (inc v))))))
    (is (= 7 (.merge map "b" 1 (binary +))))
    (is (.replace map "b" 7 8))
    (is (= 8 (.replace map "b" 9)))
    (is (not (.remove map "b" 8)))
    (is (.remove map "b" 9))
    (is (nil? (.compute map "a" (binary (fn [_ _] nil)))))
    (.replaceAll map (binary (fn [_ v] (inc v))))
    (is (= {"nil" 4} (into {} map)))
    (is (.containsAll dirty ["a" "nil" "b"]))
    (is (thrown? NullPointerException (.replaceAll map nil)))))

(deftest java-key-equality-is-consistent-with-eager-hashmap
  (doseq [canonical? [false true]]
    (let [base {(long 1) "long"}
          ^Map map (overlay/overlay base (HashSet.) canonical?)
          expected (HashMap. ^Map base)]
      (doseq [key [(int 1) (bigint 1) (double 1) nil "x"]]
        (is (= (.get expected key) (.get map key)))
        (is (= (.put expected key key) (.put map key key))))
      (is (= (.size expected) (.size map) (.size (.entrySet map))))
      (is (.equals expected map))
      (is (.equals map expected))
      (is (= (.hashCode expected) (.hashCode map)))
      (doseq [key [(int 1) (long 1) (bigint 1) nil]]
        (is (= (.remove expected key) (.remove map key))))
      (is (.equals expected map))))
  (let [base {(int 1) :integer} ^Map map (overlay/overlay base)]
    (is (nil? (.get map (long 1))))
    (is (= :integer (.get map (int 1))))))

(deftest overlay-mutations-participate-in-delta-and-full-freezes
  (let [[world a] (m/allocate (m/world {}) :ctor 0 [1])
        [world b] (m/allocate world :ctor 0 [2])
        [world c] (m/allocate world :ctor 0 [3])
        state (u/thaw world) ^Map heap (:heap state)]
    (is (instance? ansatz.runtime.HeapOverlay heap))
    (is (identical? (:heap world) (:heap (u/freeze state))))
    ;; Direct Java mutation, including a default method, must mark dirty too.
    (.compute heap (:id a) (binary (fn [_ n] (assoc n :tag 1))))
    (is (= (assoc-in world [:heap (:id a) :tag] 1)
           (select-keys (u/freeze state) (keys world))))
    (is (= 0 (:tag (m/node world a))))
    (.remove heap (:id b)) (.remove heap (:id c))
    (is (= #{(:id a)} (set (keys (:heap (u/freeze state))))))
    (.clear heap)
    (is (empty? (:heap (u/freeze state))))))

(deftest mutable-external-map-falls-back-to-private-hashmap
  (let [[world ref] (m/allocate (m/world {}) :ctor 0 [1])
        heap (HashMap. ^Map (:heap world)) state (u/thaw (assoc world :heap heap))]
    (is (instance? HashMap (:heap state)))
    (.clear heap)
    (is (= 1 (u/project state ref 0)))
    (is (= [1] (:fields (m/node (u/freeze state) ref))))))

(deftest comparator-based-persistent-map-cannot-use-long-key-fast-proof
  (let [base (assoc (sorted-map-by (fn [_ _] 0)) (long 1) :stored)
        ^Map map (overlay/overlay base (HashSet.) true)]
    (is (= :stored (.get map (long 1))))
    (is (nil? (.get map (long 3))))
    (is (nil? (.put map (long 3) :new)))
    (is (= 2 (.size map) (.size (.entrySet map))))
    (is (= {(long 1) :stored (long 3) :new} (into {} map)))))
