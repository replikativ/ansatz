(ns prototype.runtime-string-construction-ownership-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]
            [prototype.runtime-string :as string])
  (:import [java.lang.ref WeakReference]))

(deftest validity-hints-use-weak-identity-without-content-hashing
  (string/clear-validation-cache!)
  (try
    (let [a (String. (char-array "A😀")) b (String. (char-array "A😀"))
          ops {:ref? (constantly false)}]
      (is (= a b)) (is (not (identical? a b)))
      (string/evaluate ops {} "lean_string_push" [a 65])
      (string/evaluate ops {} "lean_string_push" [b 66])
      (is (= 2 (:scans (string/validation-cache-stats))))
      ;; Structural weak-retention check, without nondeterministic GC timing.
      (let [state @(var-get (ns-resolve 'prototype.runtime-string 'summary-cache))]
        (is (every? #(instance? WeakReference (:reference %)) (:entries state)))
        (is (not-any? #(contains? % :string) (:entries state)))
        (is (some #(identical? a (.get ^WeakReference (:reference %))) (:entries state)))
        (is (some #(identical? b (.get ^WeakReference (:reference %))) (:entries state)))))
    (finally (string/clear-validation-cache!))))

(deftest append-and-push-preserve-forks-and-consume-only-the-owned-first-input
  (doseq [backend [:reference :mutable :jvm]
          [symbol tail expected] [["lean_string_append" "😀" "é😀"]
                                  ["lean_string_push" 128512 "é😀"]]
          ownership [:unique :shared :persistent]]
    (let [name ["construct"]
          functions {name {:params [0 1]
                           :body [:let 2 [:runtime symbol [[:var 0] [:var 1]]]
                                  [:return [:var 2]]]}}
          [world source] (m/allocate (m/world functions) :string 249 [])
          world (assoc-in world [:heap (:id source) :text] "é")
          world (case ownership :shared (m/retain world source 1)
                  :persistent (m/mark-persistent world source) world)
          before world
          session (raw/open-functions functions {} {:backend backend :fuel 100})
          result (raw/call session world name [source tail])
          after (:state result)]
      (is (= expected (:value result)))
      (is (= "é" (:text (m/node before source))))
      (case ownership
        :unique (is (not (contains? (:heap after) (:id source))))
        :shared (is (= 1 (:rc (m/node after source))))
        :persistent (is (= 0 (:rc (m/node after source)))))
      (is (= before world)))))

(deftest old-weak-validity-entries-survive-source-hotreload-without-invented-counts
  (let [cache (var-get (ns-resolve 'prototype.runtime-string 'summary-cache))
        s (String. (char-array "é😀\u0000"))]
    (try
      ;; The running prototype may contain the former WeakReference-only
      ;; validity hints when this namespace is refreshed in place.
      (reset! cache {:entries [(WeakReference. s)] :hits 0 :scans 0 :input-code-units 0})
      (is (= 7 (second (string/evaluate {:ref? (constantly false)} {} "lean_string_utf8_byte_size" [s]))))
      (is (= 3 (second (string/evaluate {:ref? (constantly false)} {} "lean_string_length" [s]))))
      (is (= 1 (:scans (string/validation-cache-stats))))
      (is (= {:byte-size 7 :length 3} (:summary (first (:entries @cache)))))
      (finally (string/clear-validation-cache!)))))

(deftest captured-old-cache-reader-can-run-while-new-code-writes-summaries
  (let [legacy (var-get (ns-resolve 'prototype.runtime-string 'validation-cache))
        modern (var-get (ns-resolve 'prototype.runtime-string 'summary-cache))
        seed (String. (char-array "old-reader😀"))
        ;; Capture the original atom and exact v1 WeakReference-only reader and
        ;; writer contract, as a running pre-reload function does.
        old-read (fn [s] (some #(identical? s (.get ^WeakReference %)) (:entries @legacy)))
        old-write (fn [s] (swap! legacy update :entries
                           #(into [(WeakReference. s)] (take 63 %))))]
    (try
      (reset! legacy {:entries [(WeakReference. seed)] :hits 0 :scans 0 :input-code-units 0})
      (string/clear-validation-cache!)
      (is (not (identical? legacy modern)))
      (let [ready (promise) start (promise)
            reader (future (deliver ready true) @start
                           (dotimes [_ 1000] (assert (old-read seed))) true)]
        @ready (deliver start true)
        (dotimes [i 1000]
          (string/evaluate {:ref? (constantly false)} {} "lean_string_push" ["new😀" 65])
          (when (zero? (mod i 20)) (old-write seed)))
        (is (true? @reader)))
      (is (every? #(instance? WeakReference %) (:entries @legacy)))
      (is (every? #(instance? WeakReference (:reference %)) (:entries @modern)))
      (finally (reset! legacy {:entries [] :hits 0 :scans 0 :input-code-units 0})
               (string/clear-validation-cache!)))))
