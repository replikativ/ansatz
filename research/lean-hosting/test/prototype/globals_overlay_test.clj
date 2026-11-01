(ns prototype.globals-overlay-test
  "Differential globals boundary tests against the original eager HashMap path.
   No archived frontend/checkpoint compatibility or actual frontend speed claim."
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m] [prototype.mutable :as u]
            [prototype.global-test :as global])
  (:import [ansatz.runtime GlobalsOverlay]
           [java.util Map HashMap AbstractMap AbstractMap$SimpleImmutableEntry ConcurrentModificationException]
           [java.util.function Function BiFunction]))

(def global-name ["str" ["anonymous"] "snapshotGlobal"])
(def io-name [:prototype.initialization/io global-name])
(defn snapshot [globals] (assoc (m/world {}) :globals globals))
(defn frozen [state] (:globals (u/freeze state)))
(defn binary [f] (reify BiFunction (apply [_ a b] (f a b))))
(defn unary [f] (reify Function (apply [_ a] (f a))))

(deftest read-only-boundaries-reuse-canonical-base-and-forks-stay-independent
  (let [value {:status :ready :value 42}
        base {global-name value io-name {:status :initializing} "name" nil (long 7) value}
        original (snapshot base) left (u/thaw original) right (u/thaw original)
        ^Map globals (:globals left)]
    (is (instance? GlobalsOverlay globals))
    (is (= (.get (HashMap. ^Map base) global-name) (.get globals global-name)))
    (is (.containsKey globals "name")) (is (nil? (.get globals "name")))
    (is (= 4 (.size globals)))
    (is (identical? base (frozen left)))
    (is (identical? base (frozen right)))
    (.put globals global-name {:status :ready :value 43})
    (let [first (frozen left)]
      (is (= 43 (get-in first [global-name :value])))
      (is (= 42 (get-in base [global-name :value])))
      (is (identical? base (frozen right)))
      (.put globals global-name {:status :ready :value 44})
      (is (= 43 (get-in first [global-name :value])))
      (is (= 44 (get-in (frozen left) [global-name :value])))
      (is (identical? first (frozen (u/thaw (snapshot first))))))))

(deftest first-write-and-unsupported-keys-match-eager-java-equality-and-freeze
  (doseq [[base operations]
          [[{(long 1) :long} [[(int 1) :integer] [(bigint 1) :bigint] [nil :nil]]]
           [{["num" ["anonymous"] (long 1)] :long}
            [[["num" ["anonymous"] (int 1)] :integer]]]
           [{(long 8589934597) :long :other :base}
            [[:third :canonical-write] [(biginteger 8589934597) :big-integer]]]
           [{io-name :io global-name :name} [[[:prototype.initialization/io ["num" ["anonymous"] (int 1)]] :unsupported]]]]]
    (let [state (u/thaw (snapshot base)) ^Map actual (:globals state) expected (HashMap. ^Map base)]
      (doseq [[key value] operations]
        (is (= (.get expected key) (.get actual key)))
        (is (= (.containsKey expected key) (.containsKey actual key)))
        (is (= (.put expected key value) (.put actual key value))))
      (is (.equals expected actual))
      (is (.equals actual expected))
      (is (= (.hashCode expected) (.hashCode actual)))
      (is (= (into {} expected) (frozen state)))))
  (let [base {(long 1) :long} state (u/thaw (snapshot base)) ^Map actual (:globals state)]
    (is (nil? (.get actual (int 1))))
    (is (false? (.containsKey actual (int 1))))
    (is (= :long (.get actual (long 1))))
    (is (= base (frozen state)))))

(deftest exotic-maps-mutable-keys-and-metadata-conservatively-use-eager-copy
  (let [mutable-key (doto (java.util.ArrayList.) (.add "key"))]
    (doseq [base [{(int 1) :integer} {nil :nil} {mutable-key :mutable}
                  (assoc (sorted-map-by (fn [_ _] 0)) (long 1) :first (long 2) :last)
                  (with-meta {global-name :ready} {:caller :metadata})
                  (HashMap. ^Map {global-name :ready})]]
      (let [state (u/thaw (snapshot base)) ^Map actual (:globals state) expected (HashMap. ^Map base)]
        (is (instance? HashMap actual))
        (is (.equals expected actual))
        (is (= (into {} expected) (frozen state)))
        (is (nil? (meta (frozen state)))))))
  (let [base (HashMap. ^Map {global-name :owned}) state (u/thaw (snapshot base))]
    (.clear base)
    (is (= {global-name :owned} (frozen state)))))

(deftest values-remain-borrowed-without-new-deep-validation
  (let [value (object-array [42]) base {global-name value} state (u/thaw (snapshot base))]
    (is (instance? GlobalsOverlay (:globals state)))
    (is (identical? value (.get ^Map (:globals state) global-name)))
    (is (identical? base (frozen state)))
    (aset value 0 43)
    (is (= 43 (aget ^objects (get (frozen state) global-name) 0)))))

(deftest views-materialize-once-and-remain-live-through-default-mutators
  (let [base {"a" 1 "b" nil} state (u/thaw (snapshot base)) ^Map actual (:globals state)
        expected (HashMap. ^Map base)
        entries (.entrySet actual) keys (.keySet actual) values (.values actual)]
    (is (nil? (GlobalsOverlay/unchangedBase actual)))
    (.put actual "c" 3) (.put expected "c" 3)
    (is (.contains keys "c")) (is (.contains values 3))
    (let [entry (first (filter #(= "a" (.getKey ^java.util.Map$Entry %)) entries))]
      (.setValue ^java.util.Map$Entry entry 2) (.put expected "a" 2))
    (let [iterator (.iterator keys)]
      (loop [] (when (.hasNext iterator)
                 (let [key (.next iterator)]
                   (when (= key "b") (.remove iterator) (.remove expected "b")))
                 (recur))))
    (is (= (.putIfAbsent expected "d" 4) (.putIfAbsent actual "d" 4)))
    (is (= (.computeIfAbsent expected "e" (unary (constantly 5)))
           (.computeIfAbsent actual "e" (unary (constantly 5)))))
    (is (= (.compute expected "e" (binary (fn [_ v] (inc v))))
           (.compute actual "e" (binary (fn [_ v] (inc v))))))
    (is (= (.merge expected "e" 2 (binary +)) (.merge actual "e" 2 (binary +))))
    (.replaceAll actual (binary (fn [_ v] (inc v))))
    (.replaceAll expected (binary (fn [_ v] (inc v))))
    (is (= (.remove expected "c" 4) (.remove actual "c" 4)))
    (is (.equals expected actual))
    (is (= (into {} expected) (frozen state)))
    (.clear values) (.clear expected)
    (is (.isEmpty entries)) (is (= {} (frozen state))))
  (doseq [make-map [#(HashMap. ^Map {"a" 1}) #(GlobalsOverlay/open {"a" 1})]]
    (let [^Map map (make-map)]
      (is (thrown? ConcurrentModificationException
                   (.computeIfAbsent map "new" (unary (fn [_] (.put map "side" 2) 3))))))))

(deftest put-all-does-not-attest-a-separately-observed-source-keyset
  (let [base {(long 1) :one} state (u/thaw (snapshot base)) ^Map actual (:globals state)
        ; Deterministic boundary model for a weakly consistent source changing
        ; between key and entry traversals. The delegate observes Integer(2).
        source (proxy [AbstractMap] []
                 (size [] 1)
                 (keySet [] #{(long 2)})
                 (entrySet [] #{(AbstractMap$SimpleImmutableEntry. (int 2) :two)}))
        expected (HashMap. ^Map base)]
    (.putAll actual source) (.putAll expected source)
    (is (.equals expected actual))
    (let [result (frozen state)]
      (is (= (into {} expected) result))
      (is (instance? HashMap (:globals (u/thaw (snapshot result))))))))

(deftest initialization-pauses-forks-and-persistent-reference-counts-stay-differential
  (let [functions {:read {:params [] :body [:global global-name :initialize]}
                   :initialize {:params [] :body [:let 1 [:ctor 0 [[:imm 42]]]
                                                  [:let 2 [:ctor 1 [[:var 1]]] [:return [:var 2]]]]}}
        start (m/start (m/world functions) :read []) expected (m/run start)]
    (doseq [run (global/runners functions) fuel (range 12)]
      (is (= (m/run start fuel) (run start fuel))))
    (is (every? #(zero? (:rc %)) (vals (:heap expected))))
    (let [left (u/thaw start) right (u/thaw start)]
      (u/run! left 100)
      (is (= expected (u/freeze left)))
      (is (= (:globals start) (frozen right)))
      (let [ready (u/freeze left) again (u/thaw (m/start ready :read []))]
        (u/run! again 100)
        (is (identical? (:globals ready) (frozen again)))
        (is (= (:heap ready) (:heap (u/freeze again))))))))

(deftest io-error-retains-initializing-state-and-error-owner-without-replay
  (let [functions {:entry {:params [] :body [:begin-init io-name :initialize [] "object"]}
                   :initialize {:params [] :body [:let 1 [:ctor 1 [[:imm "failure"]]] [:return [:var 1]]]}}
        initial (m/start (m/world functions) :entry []) state (u/thaw initial)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"IO success" (u/run! state 100)))
    (let [failed (u/freeze state)]
      (is (= :initializing (get-in failed [:globals io-name :status])))
      (is (= {} (:globals initial)))
      (is (= 1 (count (:heap failed))))
      (is (= 1 (:rc (first (vals (:heap failed))))))
      (is (= 1 (:tag (first (vals (:heap failed))))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Recursive global"
            (u/run! (u/thaw (m/start failed :entry [])) 100))))))

(deftest shared-key-dags-have-bounded-eligibility-and-use-eager-fallback
  (let [key (reduce (fn [child _]
                      (let [value [child child]]
                        ; Warm BOTH Java hashCode and Clojure hasheq bottom-up:
                        ; old HashMap(base) does not traverse an exponential tree.
                        (.hashCode value) (hash value) value)) "leaf" (range 30))
        base {key :shared} state (u/thaw (snapshot base))]
    (is (instance? HashMap (:globals state)))
    (is (= :shared (.get ^Map (:globals state) key)))
    (is (= base (frozen state)))))
