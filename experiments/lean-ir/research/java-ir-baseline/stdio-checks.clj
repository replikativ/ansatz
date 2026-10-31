(ns java-ir-stdio-checks
  "Opt-in branch-thread stdio, original Buffer closures and exact owner transitions."
  (:refer-clojure :exclude [swap!])
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-host-checks :as host]
            [java-ir-generation-checks :as g] [java-ir-ref-checks :as ref]
            [java-ir-array-checks :as array] [java-ir-byte-array-checks :as bytes]
            [java-ir-sync-task-checks :as sync] [java-ir-release-order-checks :as order]
            [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-stdio-runtime/")
(defn records [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn original-fap [label arguments]
  (let [record (first (filter #(= label (get % "label")) (records)))
        name (get-in record ["row" "name"])]
    (assert name "Original qualified stdio Name absent from fixture")
    {:fap {:c name :ys arguments}}))
(defn helper-rows []
  [(c/decl "stdio-apply0" [(c/p 1 "object")] "object"
     (c/let-ir 2 "object" {:ap {:x {:idx 1} :ys ["erased"]}} (c/ret 2)))
   (c/decl "stdio-apply1" [(c/p 1 "object") (c/p 2 "object")] "object"
     (c/let-ir 3 "object" {:ap {:x {:idx 1} :ys [(c/v 2) "erased"]}} (c/ret 3)))
   (c/decl "stdio-observe-install" [(c/p 1 "object") (c/p 2 "object") (c/p 3 "object")] "object"
     (c/let-ir 4 "object" (original-fap "IO.getStdout" ["erased"])
       (c/let-ir 5 "object" (original-fap "IO.setStdout" [(c/v 1) "erased"])
         ["dec" {:idx 5} 1 true false ["dec" {:idx 2} 1 true false (c/ret 4)]])))
   (c/decl "stdio-recreate" [(c/p 1 "object") (c/p 2 "object")] "object"
     ["dec" {:idx 1} 1 true false
      (c/let-ir 3 "object" (original-fap "IO.getStdin" ["erased"])
        ["dec" {:idx 3} 1 true false
         (c/let-ir 4 "object" (original-fap "IO.getStdout" ["erased"])
           ["dec" {:idx 4} 1 true false
            (c/let-ir 5 "object" (original-fap "IO.getStderr" ["erased"])
              ["dec" {:idx 5} 1 true false
               (c/let-ir 6 "object" (c/lit 0) (c/ret 6))])])])])
   (c/decl "stdio-hold-promise" [(c/p 1 "object") (c/p 2 "object")] "object"
     ["dec" {:idx 1} 1 true false
      (c/let-ir 3 "object" (c/ctor 0 ["erased"] 0) (c/ret 3))])])
(defn context [mode]
  (let [rs (records) base (j/prepare-host-program *basis* [] [])
        source (j/source-binding base (Object.))
        hs (into {} (map (fn [r] [(get r "label") (j/declaration-header source (get r "row") (get r "sha256"))]) rs))
        by-name (into {} (map (fn [[_ h]] [(json/write-str (j/lean-name-data (j/request-value h "name"))) h]) hs))
        registered (j/register-headers base (mapv #(get hs (get % "label")) rs))
        ready (reduce (fn [ctx r]
                        (if (and (get-in r ["row" "ir" "fdecl"])
                                 (not (.contains ^String (get r "label") "._lam_")))
                          (j/materialize-body ctx (get hs (get r "label")) (get r "row")
                            (mapv #(get by-name (json/write-str %)) (distinct (get-in r ["row" "dependencies"])))) ctx)) registered rs)
        extra (concat (map #(get % "row") (json/read-str (slurp "test/fixtures/java-task-sync-runtime/original-rows.json")))
                      (map #(get % "row") (ref/originals)) (map #(get % "row") (array/originals))
                      (x/raw (helper-rows)))
        table (java.util.LinkedHashMap.)
        _ (doseq [row extra]
            (when-let [old (.putIfAbsent table (get row "name") row)]
              (assert (= old row) "Original fixture duplicate differs")))
        ctx (assoc (j/extend-program ready (vec (.values table))) :explicit (not= mode :control)
                   :stdio-source source :stdio-headers hs)]
    (if (= mode :active) (assoc ctx :task-runtime (j/logical-sync-task-runtime ctx)) ctx)))
(defn fields [ctx value] (.get ^java.lang.reflect.Field (:fields ctx) value))
(defn counters [e] (mapv #(host/private-value e %) ["allocations" "stores" "retains" "releases"]))
(defn release! [ctx e value]
  (if (:task-runtime ctx) (sync/release! ctx e value) (j/release! ctx e value)))
(defn close! [ctx e]
  (if (:task-runtime ctx) (sync/close! ctx e) (j/close! ctx e)))
(defn streams! [ctx e]
  ;; Data-only factory follows the pinned Buffer layout (data:ByteArray,pos:Nat)
  ;; and Ref layout. The actual original ofBuffer executes to create all6 methods.
  (let [r #(j/graph-ref ctx %) source (:stdio-source ctx)
        nodes (mapcat (fn [base]
                        [(bytes/raw-descriptor ctx base 99 (byte-array 0))
                         (j/graph-node ctx {:kind :ctor :id (inc base) :rc 99 :tag 0 :fields [(r base) 0]})
                         (j/graph-node ctx {:kind :ref :id (+ base 2) :rc 99 :fields [(r (inc base))]})]) [1 4 7])
        refs (j/install-graph! ctx e (j/selected-owner-graph ctx source (Object.) nodes [] [] [(r 3) (r 6) (r 9)]))]
    (mapv #(j/call ctx e "IO.FS.Stream.ofBuffer" [%]) refs)))
(defn install! [ctx e stdin]
  (j/install-stdio-defaults! ctx e (get-in ctx [:stdio-headers "IO.FS.Stream.ofBuffer"]) stdin))
(defn get! [ctx e channel] (j/call ctx e (str "IO.getStd" channel "._boxed") [0]))
(defn swap! [ctx e channel value] (j/call ctx e (str "IO.setStd" channel "._boxed") [value 0]))
(defn current [e i] (aget ^objects (host/private-value (host/private-value e "stdioContext") "current") i))
(defn put! [ctx e stream text]
  (let [method (aget ^objects (fields ctx stream) 4)]
    (j/retain! ctx e method)
    (let [ok (j/call ctx e "stdio-apply1" [method text])]
      (is (= 0 (.getInt ^java.lang.reflect.Field (:tag ctx) ok)))
      (release! ctx e ok))))
(defn cleanup! [ctx e streams]
  (doseq [s streams] (release! ctx e s)) (close! ctx e))

(deftest original-source-fixture-and-all-six-exact-raw-abis
  (let [rs (records) p (json/read-str (slurp (str directory "provenance.json")))
        method (.getMethod ^Class (:class *basis*) "validateExternAbi" (into-array Class [java.util.Map]))]
    (is (= 21 (count rs))) (is (= 375258 (get p "source-index-declarations")))
    (is (= (get p "fixture-sha256") (corpus/sha256 (str directory "original-rows.json"))))
    (doseq [r rs :when (get-in r ["row" "ir" "extern"])]
      (is (string? (j/invoke-static method [(get r "row")])))
      (is (every? false? (map #(get % "borrow") (get-in r ["row" "ir" "extern" "xs"]))))
      (is (= "object" (get-in r ["row" "ir" "extern" "type"]))))))

(deftest unconfigured-profile-preserves-legacy-stdout-and-new-channels-refuse
  (let [ctx (context :control) e (j/machine ctx) out (j/call ctx e "IO.getStdout" [0])]
    (try
      (is (= 2 (c/rc ctx out)))
      (let [before (counters e)]
        (is (g/bad? #(j/call ctx e "IO.getStdin" [0])))
        (is (g/bad? #(j/call ctx e "IO.getStderr" [0])))
        (is (= before (counters e)))
        (is (nil? (host/private-value e "stdioContext")))
        (is (nil? (host/private-value e "stdinDefaultRoot")))
        (is (nil? (host/private-value e "stderrRoot"))))
      (finally (release! ctx e out) (close! ctx e)))
    (is (order/dead? out))))

(deftest callback-bearing-default-graph-rejects-before-any-install-owner-acquisition
  (let [ctx (context :active) e (j/machine ctx) [a b c :as ss] (streams! ctx e)
        method (aget ^objects (fields ctx a) 1)
        buffer-ref (aget ^objects (fields ctx method) 0)
        payloads ^objects (fields ctx buffer-ref) buffer (aget payloads 0)
        p (sync/promise! ctx e)]
    ;; Move owning edges explicitly; do not release borrowed aliases.
    (aset payloads 0 p) ; old buffer owner moves to this test, p owner into Ref
    (try
      (let [before (counters e)]
        (is (g/bad? #(install! ctx e a)))
        (is (= before (counters e))) (is (= 1 (c/rc ctx a)))
        (is (nil? (host/private-value e "stdioContext")))
        (is (nil? (host/private-value e "stdinDefaultRoot"))))
      (finally
        (aset payloads 0 buffer) ; return buffer edge, move p owner back out
        (release! ctx e p)
        (cleanup! ctx e ss)))))

(deftest opt-in-defaults-lazy-slots-and-owned-noop-swaps
  (doseq [mode [:control :explicit :active]]
    (let [ctx (context mode) e (j/machine ctx) [a b c :as ss] (streams! ctx e)]
      (try
        (is (= 1 (c/rc ctx a))) (install! ctx e a) (is (= 2 (c/rc ctx a)))
        (is (every? nil? (map #(current e %) (range 3))))
        (let [got (get! ctx e "in")]
          (is (identical? a got)) (is (= 4 (c/rc ctx a)))
          (is (= 6 (alength ^objects (fields ctx got)))) ; direct Stream, not IO.Result
          (release! ctx e got))
        (is (= 3 (c/rc ctx a)))
        (j/retain! ctx e a)
        (let [old (swap! ctx e "in" a)]
          (is (identical? a old)) (is (= 4 (c/rc ctx a))) (release! ctx e old))
        (is (= 3 (c/rc ctx a)))
        (j/retain! ctx e b)
        (let [old (swap! ctx e "out" b)]
          (is (identical? old (host/private-value e "stdoutRoot")))
          (is (= 2 (c/rc ctx old))) (release! ctx e old))
        (is (identical? b (current e 1))) (is (= 2 (c/rc ctx b)))
        (j/retain! ctx e b)
        (let [old (swap! ctx e "err" b)]
          (is (identical? old (host/private-value e "stderrRoot"))) (release! ctx e old))
        (is (identical? (current e 1) (current e 2))) (is (= 3 (c/rc ctx b)))
        (finally (cleanup! ctx e ss))))))

(deftest separate-default-sinks-and-current-redirects-do-not-mirror-capture
  (doseq [mode [:control :explicit :active]]
    (let [ctx (context mode) e (j/machine ctx) [a b c :as ss] (streams! ctx e)]
      (try
        (install! ctx e a)
        (let [out (get! ctx e "out") err (get! ctx e "err")]
          (is (not (identical? out err)))
          (put! ctx e out "out✓") (put! ctx e err "err✓")
          (is (= "out✓" (j/request-value e "capturedStdout")))
          (is (= "err✓" (j/request-value e "capturedStderr")))
          (j/retain! ctx e b)
          (release! ctx e (swap! ctx e "out" b))
          ;; The genuine buffer method remains its original guest closure. We
          ;; do not execute its unadmitted UTF8/copySlice dependency frontier.
          (is (identical? b (current e 1)))
          (is (= "out✓" (j/request-value e "capturedStdout")))
          (release! ctx e out) (release! ctx e err))
        (finally (cleanup! ctx e ss))))))

(deftest default-install-is-readonly-before-retain-and-rejects-wrong-source-or-layout
  (let [ctx (context :active) e (j/machine ctx) [a b c :as ss] (streams! ctx e)]
    (try
      (let [before (counters e) old-tag (.getInt ^java.lang.reflect.Field (:tag ctx) a)]
        (.setInt ^java.lang.reflect.Field (:tag ctx) a 1)
        (try
          (is (g/bad? #(install! ctx e a)))
          (is (= before (counters e)))
          (is (nil? (host/private-value e "stdioContext"))) (is (nil? (host/private-value e "stdinDefaultRoot")))
          (finally (.setInt ^java.lang.reflect.Field (:tag ctx) a old-tag))))
      (let [record (first (filter #(= "IO.FS.Stream.ofBuffer" (get % "label")) (records)))
            foreign (j/declaration-header (j/source-binding ctx (Object.)) (get record "row") (get record "sha256"))
            before (counters e)]
        (is (g/bad? #(j/install-stdio-defaults! ctx e foreign a)))
        (is (= before (counters e))) (is (= 1 (c/rc ctx a))))
      (let [before (counters e)]
        (.setInt ^java.lang.reflect.Field (:rc ctx) a Integer/MAX_VALUE)
        (try (is (g/bad? #(install! ctx e a))) (is (= before (counters e)))
             (is (nil? (host/private-value e "stdioContext")))
             (finally (.setInt ^java.lang.reflect.Field (:rc ctx) a 1))))
      (install! ctx e a)
      (is (g/bad? #(install! ctx e a))) (is (= 2 (c/rc ctx a)))
      (finally (cleanup! ctx e ss)))))

(deftest malformed-swap-world-and-getter-overflow-do-not-publish-native-owner-changes
  ;; Control-mode guest failures can return without claiming argument owners.
  ;; Explicit terminal failures are tested separately without fake unwinding.
  (let [ctx (context :control) e (j/machine ctx) [a b c :as ss] (streams! ctx e)]
    (try
      (install! ctx e a)
      (let [before (counters e)]
        (is (g/bad? #(j/call ctx e "IO.setStdout" [b 1])))
        (is (= before (counters e))) (is (nil? (current e 1)))
        (is (= 1 (c/rc ctx b))))
      (.setInt ^java.lang.reflect.Field (:tag ctx) b 1)
      (try (let [before (counters e)]
             (is (g/bad? #(swap! ctx e "out" b)))
             (is (= before (counters e))) (is (nil? (current e 1))))
           (finally (.setInt ^java.lang.reflect.Field (:tag ctx) b 0)))
      (let [out (get! ctx e "out") rc (c/rc ctx out) before (counters e)]
        (.setInt ^java.lang.reflect.Field (:rc ctx) out Integer/MAX_VALUE)
        (try (is (g/bad? #(get! ctx e "out")))
             (is (= before (counters e))) (is (identical? out (current e 1)))
             (finally (.setInt ^java.lang.reflect.Field (:rc ctx) out rc)))
        (release! ctx e out))
      (finally (cleanup! ctx e ss)))))

(deftest fork-remaps-default-current-external-and-saved-old-stream-aliases
  (let [ctx (context :active) parent (j/machine ctx) [a b c :as ss] (streams! ctx parent)]
    (install! ctx parent a)
    (j/retain! ctx parent b)
    (let [saved (swap! ctx parent "out" b)
          fork (j/fork! ctx parent [a b c saved]) child (:engine fork) [aa bb cc old] (:roots fork)]
      (try
        (is (identical? b (current parent 1))) (is (identical? bb (current child 1)))
        (is (not (identical? b bb)))
        (is (identical? a (host/private-value parent "stdinDefaultRoot")))
        (is (identical? aa (host/private-value child "stdinDefaultRoot")))
        (is (identical? saved (host/private-value parent "stdoutRoot")))
        (is (identical? old (host/private-value child "stdoutRoot")))
        ;; Transfer the actual saved previous owner back to each branch's slot.
        (release! ctx parent (swap! ctx parent "out" saved))
        (release! ctx child (swap! ctx child "out" old))
        (let [out (get! ctx child "out")]
          (put! ctx child out "child") (release! ctx child out))
        (is (= "" (j/request-value parent "capturedStdout")))
        (is (= "child" (j/request-value child "capturedStdout")))
        (finally (cleanup! ctx parent ss) (cleanup! ctx child [aa bb cc]))))))

(deftest pending-sync-callback-observes-resolver-time-stream-and-leaves-unbalanced-swap
  (let [ctx (context :active) e (j/machine ctx) [a b c :as ss] (streams! ctx e)]
    (try
      (install! ctx e a)
      (j/retain! ctx e a) (release! ctx e (swap! ctx e "out" a))
      (let [p (sync/promise! ctx e)
            _ (j/retain! ctx e c)
            callback (j/make-closure! ctx e "stdio-observe-install" [c])
            result (sync/io-map! ctx e callback (sync/result-task! ctx e p))]
        (j/retain! ctx e b) (release! ctx e (swap! ctx e "out" b))
        (is (= 0 (sync/resolve! ctx e p 7)))
        (j/retain! ctx e result)
        (let [seen (sync/get! ctx e result)]
          (is (identical? b seen)) (release! ctx e seen))
        (is (identical? c (current e 1)))
        (is (nil? (host/private-value e "currentTask")))
        (let [outer (get! ctx e "out")] (is (identical? c outer)) (release! ctx e outer))
        (release! ctx e result) (release! ctx e p))
      (finally (cleanup! ctx e ss)))))

(deftest callback-created-earlier-current-slots-are-retired-before-defaults-and-fork-during-disposal
  (let [ctx (context :active) parent (j/machine ctx) [a b c :as ss] (streams! ctx parent)]
    (install! ctx parent a)
    (let [p (sync/promise! ctx parent)
          callback (j/make-closure! ctx parent "stdio-recreate" [])
          result (sync/io-map! ctx parent callback (sync/result-task! ctx parent p))
          holder (j/make-closure! ctx parent "stdio-hold-promise" [p])
          fs ^objects (fields ctx b) old-flush (aget fs 0)]
      (aset fs 0 nil) ; take the old method owning edge before releasing it
      (release! ctx parent old-flush) (aset fs 0 holder)
      (j/retain! ctx parent b) (release! ctx parent (swap! ctx parent "out" b))
      (release! ctx parent result)
      (doseq [s ss] (release! ctx parent s))
      (j/start-dispose! ctx parent)
      (j/advance! ctx parent 1)
      (let [fork (j/fork! ctx parent []) child (:engine fork)]
        (doseq [e [parent child]]
          (is (= 0 (sync/finish! ctx e)))
          (is (every? nil? (map #(current e %) (range 3))))
          (is (nil? (host/private-value e "stdinDefaultRoot")))
          (is (nil? (host/private-value e "stdoutRoot")))
          (is (nil? (host/private-value e "stderrRoot")))
          (is (true? (host/private-value e "disposed")))
          (j/close! ctx e))))))

(deftest mutated-default-ref-to-promise-is-detected-before-any-default-root-claim
  ;; Deliberately violate the typed Buffer field invariant after installation.
  ;; The failed engine retains exact owners; this test does not pretend cleanup.
  (let [ctx (context :active) e (j/machine ctx) [a b c :as ss] (streams! ctx e)]
    (install! ctx e a)
    (let [method (aget ^objects (fields ctx a) 1)
          buffer-ref (aget ^objects (fields ctx method) 0)
          payloads ^objects (fields ctx buffer-ref) old-buffer (aget payloads 0)
          p (sync/promise! ctx e)]
      (aset payloads 0 nil) ; take the actual Ref payload owner, not a borrowed alias
      (release! ctx e old-buffer) (aset payloads 0 p) ; transfer p owner into Ref
      (doseq [s ss] (release! ctx e s))
      (j/start-dispose! ctx e)
      (is (re-find #"Stdio defaults reject Task/Promise lifecycle" (c/failure #(sync/finish! ctx e))))
      (is (= "failed" (j/phase ctx e)))
      (is (identical? a (host/private-value e "stdinDefaultRoot")))
      (is (= 1 (c/rc ctx a))) (is (false? (order/dead? a)))
      (let [action (or (host/private-value e "failedRuntimeAction") (host/private-value e "runtimeAction"))]
        (is (some? action)) (is (= 1 (host/private-value action "stage")))
        (is (= 0 (host/private-value action "cursor"))))
      (is (g/bad? #(j/close! ctx e))))))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-stdio-checks)))
