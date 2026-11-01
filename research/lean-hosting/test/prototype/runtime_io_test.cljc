(ns prototype.runtime-io-test
  (:require [prototype.runtime-io :as runtime]
            [prototype.entropy :as entropy]
            [prototype.machine :as m]
            #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])))

(def ops
  {:allocate m/allocate :node m/node :ref? m/ref?
   :replace-node (fn [world value node] (assoc-in world [:heap (:id value)] node))
   :take-entropy entropy/take-bytes})

(defn run [ops world n]
  (runtime/evaluate ops world "lean_io_get_random_bytes" [n m/erased]))
(defn result-bytes [world result]
  (:bytes (m/node world (first (:fields (m/node world result))))))

(defn getenv [ops world name]
  (runtime/evaluate ops world "lean_io_getenv" [name m/erased]))

(deftest environment-returns-option-directly-and-threads-world
  (let [before (assoc (m/world {}) :environment {"LEAN_MANUAL_ROOT" "" "名😀" "éλ😀"})
        provider (fn [world name]
                   [(update world :lookups (fnil conj []) name)
                    (get (:environment world) name)])
        ops (assoc ops :get-env provider)]
    (doseq [[name expected] [["LEAN_MANUAL_ROOT" ""] ["名😀" "éλ😀"]]]
      (let [[world result] (getenv ops before name)]
        ;; BaseIO returns Some itself; no IO.Result.ok wrapper around it.
        (is (= {:kind :ctor :tag 1 :fields [expected] :rc 1} (m/node world result)))
        (is (= [name] (:lookups world)))
        (is (= (:environment before) (:environment world)))
        (is (empty? (:heap (m/release world result 1))))))
    (let [[world result] (getenv ops before "missing")]
      (is (= 0 result))
      (is (= ["missing"] (:lookups world)))
      (is (empty? (:heap world))))
    (is (not (contains? before :lookups)))
    (is (empty? (:heap before)))
    (is (= (getenv ops before "名😀") (getenv ops before "名😀"))))
  ;; NUL names cannot be silently truncated to a different environment variable.
  (doseq [name ["\u0000" "LEAN_MANUAL_ROOT\u0000suffix"]]
    (let [before (m/world {})]
      (is (= [before 0] (getenv (dissoc ops :get-env) before name)))
      (is (= [before 0] (getenv (assoc ops :get-env
                                      (fn [& _] (throw (ex-info "must not look up" {}))))
                               before name))))))

(deftest environment-borrows-native-string-reference
  (let [[before name] (m/allocate (m/world {}) :string 249 [])
        before (assoc-in before [:heap (:id name) :text] "名😀")
        provider (fn [world host-name]
                   (is (= "名😀" host-name))
                   [(assoc world :seen host-name) "éλ😀"])
        [world result] (getenv (assoc ops :get-env provider) before name)]
    (is (= ["éλ😀"] (:fields (m/node world result))))
    (is (= (:heap before) (dissoc (:heap world) (:id result))))
    (is (= 1 (:rc (m/node world name))))
    (is (not (contains? before :seen))))
  (let [[world name] (m/allocate (m/world {}) :string 249 [])
        world (assoc-in world [:heap (:id name) :text] "NAME\u0000suffix")]
    (is (= [world 0] (getenv (dissoc ops :get-env) world name)))))

(deftest environment-capability-and-unicode-preconditions
  (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"capability"
        (getenv ops (m/world {}) "LEAN_MANUAL_ROOT")))
  (let [bad-unicode #?(:clj (str (char 55296)) :cljs (js/String.fromCharCode 55296))
        allocations (atom 0)
        lookups (atom 0)
        base (assoc ops :allocate (fn [& _] (swap! allocations inc)
                                    (throw (ex-info "must not allocate" {}))))]
    (doseq [name [42 nil bad-unicode (str "\u0000" bad-unicode)]]
      (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
            (getenv (assoc base :get-env (fn [& _] (swap! lookups inc))) (m/world {}) name))))
    (is (zero? @lookups))
    (doseq [provider [(fn [& _] nil) (fn [& _] [{}])
                      (fn [world _] [world 42])
                      (fn [world _] [world bad-unicode])
                      (fn [world _] [world "bad\u0000value"])]]
      (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
            (getenv (assoc base :get-env provider) (m/world {}) "NAME"))))
    (is (zero? @allocations)))
  (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"arity"
        (runtime/evaluate ops (m/world {}) "lean_io_getenv" ["NAME"]))))

(deftest random-bytes-layout-ownership-and-world-threading
  (let [before (assoc (m/world {}) :entropy {:bytes [0 127 128 255 42] :position 1})
        [world result] (run ops before 3)
        array (first (:fields (m/node world result)))]
    (is (= {:kind :ctor :tag 0 :fields [array] :rc 1} (m/node world result)))
    (is (= {:kind :byte-array :tag 248 :fields [] :rc 1 :bytes [127 128 255]}
           (m/node world array)))
    (is (= 4 (get-in world [:entropy :position])))
    (is (= 1 (get-in before [:entropy :position])))
    (is (empty? (:heap before)))
    (is (empty? (:heap (m/release world result 1))))
    (let [[later next-result] (run ops world 1)]
      (is (= [42] (result-bytes later next-result)))
      (is (= 5 (get-in later [:entropy :position]))))))

(deftest snapshots-and-forks-replay-recorded-entropy
  (let [snapshot (assoc (m/world {}) :entropy {:bytes [1 2 3] :position 0})
        [left lr] (run ops snapshot 2)
        [right rr] (run ops snapshot 2)]
    (is (= [1 2] (result-bytes left lr)))
    (is (= [1 2] (result-bytes right rr)))
    (is (= left right))
    (is (= 0 (get-in snapshot [:entropy :position])))))

(deftest zero-bypasses-entropy-input-entirely
  (doseq [provider [nil (fn [& _] (throw (ex-info "must not run" {})))]]
    (let [before (assoc (m/world {}) :entropy {:bytes [] :position 0})
          [world result] (run (assoc ops :take-entropy provider) before 0)]
      (is (= [] (result-bytes world result)))
      (is (= (:entropy before) (:entropy world)))))
  (let [[world result] (run (dissoc ops :take-entropy) (m/world {}) 0)]
    (is (= [] (result-bytes world result)))
    (is (not (contains? world :entropy)))))

(deftest invalid-entropy-fails-before-allocation
  (let [before (assoc (m/world {}) :entropy {:bytes [1] :position 0})]
    (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"exhausted"
          (run ops before 2)))
    (is (= {:bytes [1] :position 0} (:entropy before)))
    (is (empty? (:heap before)))
    (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"capability"
          (run (dissoc ops :take-entropy) before 1)))
    (doseq [provider [(fn [_ _] nil)
                      (fn [world _] [world nil])
                      (fn [world _] [world []])
                      (fn [world _] [world [1 2]])
                      (fn [world _] [world (repeat 1)])
                      (fn [world _] [world [256]])
                      (fn [world _] [world [-1]])
                      (fn [world _] [world [0.5]])]]
      (testing "Invalid capability output must never allocate"
        (let [allocations (atom 0)]
          (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
                (run (assoc ops :take-entropy provider
                           :allocate (fn [& _]
                                       (swap! allocations inc)
                                       (throw (ex-info "unexpected allocation" {}))))
                     before 1)))
          (is (zero? @allocations)))))
    (is (empty? (:heap before))))
  (let [before (assoc (m/world {}) :entropy {:bytes [256] :position 0})]
    (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) (run ops before 1)))
    (is (= 0 (get-in before [:entropy :position])))))

(deftest scalar-and-abi-preconditions
  (let [called? (atom false)
        ops (assoc ops :take-entropy (fn [& _] (reset! called? true)))]
    (doseq [n [-1 0.5 2147483648
               #?(:clj 18446744073709551616N :cljs 9007199254740992)]]
      (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
            (run ops (m/world {}) n))))
    (is (false? @called?)))
  (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"arity"
        (runtime/evaluate ops (m/world {}) "lean_io_get_random_bytes" [1])))
  (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"Unsupported"
        (runtime/evaluate ops (m/world {}) "lean_io_fake" [1 m/erased]))))
