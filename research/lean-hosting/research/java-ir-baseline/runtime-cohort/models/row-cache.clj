(ns authenticated-raw-row-cache-checks-v1
  "Bounded policy/data models with explicit fake source authority. No catalogue,
   VM, Header, guest execution or actual CodeReceipt issuance."
  (:require [clojure.test :refer [deftest is run-tests]]
            [authenticated-raw-row-cache-v1 :as cache]
            [ansatz.research.ir.source-setup :as source]))
(defn- name-of [s] ["str" ["anonymous"] s])
(defn- entry [name value]
  {:row {"name" name "payload" value} :sha256 (apply str (repeat 64 "a"))})
(defn- model [f]
  (let [receipt (Object.) binding (Object.) driver {:source binding}
        lease (atom true) guards (atom 0) reads (atom 0) rows (atom {})]
    (with-redefs [source/guard-source! (fn [actual src]
                                       (swap! guards inc)
                                       (when-not (and @lease (identical? actual receipt) (identical? src binding))
                                         (throw (ex-info "Model source closed or foreign" {}))))
                  source/lookup-entry (fn [actual name]
                                         (is (identical? actual receipt)) (swap! reads inc) (get @rows name))]
      (f {:receipt receipt :driver driver :lease lease :guards guards :reads reads :rows rows}))))
(deftest cache-hit-still-checks-actual-receipt-source-before-and-after
  (model
    (fn [{:keys [receipt driver lease guards reads rows]}]
      (let [name (name-of "a") _ (swap! rows assoc name (entry name "a")) p (cache/open-policy receipt)]
        (is (= "a" (get-in ((:resolve-row! p) driver name) [:row "payload"])))
        (is (= "a" (get-in ((:resolve-row! p) driver name) [:row "payload"])))
        (is (= 1 @reads)) (is (= 4 @guards)) (is (= 1 (:hits ((:stats p)))))
        (let [other (assoc driver :source (Object.))]
          (is (thrown? Exception ((:resolve-row! p) other name))))
        (reset! lease false)
        (is (thrown? Exception ((:resolve-row! p) driver name)))
        (is (= 1 @reads))
        ((:close! p))
        (is (true? (:closed ((:stats p)))))
        (is (zero? (:entries ((:stats p)))))
        (is (thrown? Exception ((:resolve-row! p) driver name)))))))
(deftest lru-count-bound-keeps-the-most-recent-entry
  (model
    (fn [{:keys [receipt driver reads rows]}]
      (let [[a b c] (mapv name-of ["a" "b" "c"])
            _ (doseq [name [a b c]] (swap! rows assoc name (entry name "small")))
            p (cache/open-policy receipt {:entry-limit 2})]
        (doseq [name [a b a c a b]] ((:resolve-row! p) driver name))
        (is (= 4 @reads))
        (is (= {:entries 2 :hits 2 :misses 4 :evictions 2}
               (select-keys ((:stats p)) [:entries :hits :misses :evictions])))
        (is (<= (:bytes ((:stats p))) cache/max-charged-bytes))
        ((:close! p))))))
(deftest only-recursively-immutable-owner-free-rows-qualify
  (model
    (fn [{:keys [receipt driver reads rows]}]
      (doseq [payload [(Object.) (java.util.ArrayList. ["mutable"])
                       (proxy [Object clojure.lang.IMeta] [] (meta [] (throw (AssertionError. "Must not invoke opaque IMeta"))))
                       (with-meta ["value"] {:engine (Object.)})
                       (sorted-map-by #(compare %1 %2) "x" "value")
                       (subvec ["unobserved" "visible"] 1)
                       (lazy-seq (throw (AssertionError. "Must not realize lazy sequence")))]]
        (let [name (name-of "uncached") p (cache/open-policy receipt) before @reads]
          (reset! rows {name (entry name payload)})
          (dotimes [_ 2] ((:resolve-row! p) driver name))
          (is (= (+ before 2) @reads))
          (is (= 0 (:entries ((:stats p)))))
          ((:close! p)))))))
(deftest charged-byte-bound-and-oversize-rows-fall-back-without-semantic-rejection
  (model
    (fn [{:keys [receipt driver rows]}]
      (let [p (cache/open-policy receipt {:byte-limit 12000})]
        (doseq [i (range 20) :let [name (name-of (str i))]]
          (swap! rows assoc name (entry name (apply str (repeat 128 "x"))))
          ((:resolve-row! p) driver name)
          (is (<= (:bytes ((:stats p))) 12000)))
        (is (pos? (:insertions ((:stats p)))))
        (is (< (:entries ((:stats p))) 20))
        (is (pos? (:evictions ((:stats p)))))
        (let [name (name-of "oversize") payload (apply str (repeat 10000 "x"))]
          (swap! rows assoc name (entry name payload))
          (is (= payload (get-in ((:resolve-row! p) driver name) [:row "payload"])))
          (is (pos? (:uncached ((:stats p))))))
        ((:close! p))))))
(deftest unknown-name-never-becomes-a-negative-cache-entry
  (model
    (fn [{:keys [receipt driver reads rows]}]
      (let [p (cache/open-policy receipt) name (name-of "unknown")]
        (dotimes [_ 2] (is (thrown? AssertionError ((:resolve-row! p) driver name))))
        (is (= 2 @reads)) (is (zero? (:entries ((:stats p)))))
        (swap! rows assoc name (entry name "now present"))
        (is (= "now present" (get-in ((:resolve-row! p) driver name) [:row "payload"])))
        ((:close! p))))))
(deftest post-access-guard-can-revoke-a-hit-and-cache-scopes-never-mix-receipts
  (let [name (name-of "shared") a (Object.) b (Object.) sa (Object.) sb (Object.) guards (atom 0)
        reads (atom 0) revoke-at (atom nil)]
    (with-redefs [source/guard-source! (fn [receipt binding]
                                       (swap! guards inc)
                                       (when (= @guards @revoke-at) (throw (ex-info "Revoked after cached hit" {})))
                                       (is (or (and (identical? receipt a) (identical? binding sa))
                                               (and (identical? receipt b) (identical? binding sb)))))
                  source/lookup-entry (fn [receipt n] (swap! reads inc) (entry n (if (identical? receipt a) "A" "B")))]
      (let [pa (cache/open-policy a) pb (cache/open-policy b)]
        (is (= "A" (get-in ((:resolve-row! pa) {:source sa} name) [:row "payload"])))
        (is (= "B" (get-in ((:resolve-row! pb) {:source sb} name) [:row "payload"])))
        (is (= 2 @reads))
        (reset! revoke-at (+ @guards 2))
        (is (thrown? Exception ((:resolve-row! pa) {:source sa} name)))
        (is (= 2 @reads))
        ((:close! pa)) ((:close! pb))))))
(defn check! [] (run-tests 'authenticated-raw-row-cache-checks-v1))
