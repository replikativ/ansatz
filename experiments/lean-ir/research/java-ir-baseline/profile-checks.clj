(ns java-ir-profile-checks
  "Checked-disabled native profiling: authentic getter/options, resumable callback."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as h] [java-ir-code-checks :as code]
            [java-ir-sync-task-checks :as sync] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-profile-runtime/")
(def getter-label "_private.Lean.Util.Profile.0.Lean.get_profiler._boxed")
(defn originals [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn exact [name] (json/write-str name))
(defn direct [row]
  (let [self (get row "name")]
    (vals (into {} (for [n (tree-seq coll? seq (get-in row ["ir" "fdecl" "body"]))
                        :when (map? n) :let [call (or (get n "fap") (get n "pap"))]
                        :when call :let [name (get call "c")] :when (not= self name)] [(exact name) name])))))
(def helpers
  [(second g/common)
   (c/decl "capture" [(c/p 1 "object") (c/p 2 "object")] "object" (c/ret 1))
   (c/decl "cons" [(c/p 1 "object")] "object" (c/let-ir 2 "object" (c/ctor 0 [(c/v 1)] 0) (c/ret 2)))
   (c/decl "float-unbox" [(c/p 1 "object")] "float"
     (c/let-ir 2 "float" {:unbox {:x {:idx 1}}} ["dec" {:idx 1} 1 false false (c/ret 2)]))])
(defn context
  ([] (context {}))
  ([{:keys [defer-getter skip-global extra-rows host-specs]}]
   (let [base (j/prepare-host-program *basis* (x/raw (into helpers extra-rows)) (or host-specs []))
         source (j/source-binding base {:profile-fixture (corpus/sha256 (str directory "provenance.json"))})
         records (originals)
         hs (into {} (for [r records] [(exact (get-in r ["row" "name"]))
                                      (j/declaration-header source (get r "row") (get r "sha256"))]))
         by-label (into {} (for [r records] [(get r "label") (hs (exact (get-in r ["row" "name"])))]))
         registered (j/register-headers base (vec (vals hs)))
         ctx (reduce (fn [ctx r]
                       (if (and (get-in r ["row" "ir" "fdecl"])
                                (not= "initialized" (get-in r ["row" "runtime" "role"]))
                                (not (and defer-getter (= getter-label (get r "label")))))
                         (j/materialize-body ctx (by-label (get r "label")) (get r "row")
                           (mapv #(hs (exact %)) (direct (get r "row")))) ctx)) registered records)
         ctx (assoc ctx :explicit true :task-runtime (j/logical-sync-task-runtime ctx)
                        :profiling-policy (j/require-disabled-profiling ctx (by-label getter-label)))
         engine (j/machine ctx)]
     (when-not skip-global
       (j/install-graph! ctx engine
         (j/prepared-graph ctx source {:captured-option (corpus/sha256 (str directory "captured-profiler-option.json"))}
           [(j/graph-node ctx {:kind :ctor :id 5709 :tag 0 :fields [(j/graph-ref ctx 5698) 0]})
            (j/graph-node ctx {:kind :ctor :id 5698 :tag 1 :fields [0 "profiler"]
                              :scalars [55 -57 104 -109 -96 34 -127 33]})]
           [(by-label "Lean.profiler")] [(j/graph-ref ctx 5709)] [])))
     {:ctx ctx :engine engine :source source :headers by-label :records records})))
(defn invoke [ctx engine label args]
  (j/start! ctx engine label args) (sync/finish! ctx engine))
(defn options [ctx engine flag]
  (let [empty (invoke ctx engine "Lean.Options.empty" [])]
    (if (nil? flag) empty
      (let [key (invoke ctx engine "Lean.Name.mkStr1" ["profiler"])]
        (invoke ctx engine "Lean.Options.setBool" [empty key (if flag 1 0)])))))
(defn decl [ctx engine] (invoke ctx engine "Lean.Name.mkStr1" ["observedDecl"]))
(defn dead? [value] (h/private-value value "dead"))
(defn profile-start! [ctx engine opts callback decl]
  (j/start! ctx engine "Lean.profileit._boxed" [0 "category" opts callback decl]))
(defn until! [ctx engine predicate]
  (loop [left 10000]
    (when (zero? left) (throw (ex-info "Profile test boundary absent" {})))
    (when-not (predicate) (j/advance! ctx engine 1) (recur (dec left)))))

(deftest authentic-source-capture-and-exact-extern-abi
  (let [manifest (json/read-str (slurp (str directory "provenance.json")))]
    (is (= 43 (count (originals))))
    (is (= (get manifest "fixture-sha256") (corpus/sha256 (str directory "original-rows.json"))))
    (is (= (get manifest "captured-option-sha256") (corpus/sha256 (str directory "captured-profiler-option.json"))))
    (let [{:keys [ctx engine headers]} (context)]
      (is (= "697f802be49ca83e350147ca7a564a73e3162beb454ca78d2990455df96796ed"
             (j/request-value (headers getter-label) "originalSha256")))
      (sync/close! ctx engine))))

(deftest actual-getter-honors-default-false-and-explicit-options
  (let [{:keys [ctx engine]} (context)]
    (try
      (doseq [flag [nil false true]]
        (is (= (if flag 1 0) (invoke ctx engine getter-label [(options ctx engine flag)]))))
      (doseq [flag [nil false]]
        (let [value (invoke ctx engine "cons" [42]) callback (j/make-closure! ctx engine "capture" [value])
              name (decl ctx engine)]
          (profile-start! ctx engine (options ctx engine flag) callback name)
          (is (identical? value (sync/finish! ctx engine)))
          (is (dead? name)) (is (dead? callback))
          (sync/release! ctx engine value)))
      (finally (sync/close! ctx engine)))))

(deftest enabled-profile-rejects-before-owned-decl-or-callback-consumption
  (let [{:keys [ctx engine]} (context) opts (options ctx engine true)
        value (invoke ctx engine "cons" [7]) callback (j/make-closure! ctx engine "capture" [value])
        name (decl ctx engine)]
    (profile-start! ctx engine opts callback name)
    (is (re-find #"Enabled native profiling" (c/failure #(sync/finish! ctx engine))))
    (is (= 1 (c/rc ctx opts) (c/rc ctx callback) (c/rc ctx name) (c/rc ctx value)))
    (is (not (dead? name))) (is (not (dead? callback)))
    ;; Terminal failure is not automatically cleaned up or replayed.
    (is (= 1 (h/private-value (sync/action engine) "stage")))))

(deftest original-getter-code-pause-retains-one-copy-and-forks
  (let [{:keys [ctx engine headers records]} (context {:defer-getter true})
        opts (options ctx engine false) name (decl ctx engine)
        callback (j/make-closure! ctx engine "capture" [77])]
    (profile-start! ctx engine opts callback name)
    (until! ctx engine #(some? (j/code-request ctx engine)))
    (let [request (j/code-request ctx engine) fork (j/fork! ctx engine [opts name callback]) child (:engine fork)
          [co cn cf] (:roots fork) child-request (j/code-request ctx child)
          row (get (first (filter #(= getter-label (get % "label")) records)) "row")
          ready (j/materialize-body ctx (headers getter-label) row
                  [(headers "_private.Lean.Util.Profile.0.Lean.get_profiler")])]
      (try
        (is (identical? (headers getter-label) (j/request-value request "header")))
        (is (= 2 (c/rc ctx opts) (c/rc ctx co)))
        (is (= 1 (c/rc ctx name) (c/rc ctx cn) (c/rc ctx callback) (c/rc ctx cf)))
        (is (identical? (h/private-value engine "profilingPolicy") (h/private-value child "profilingPolicy")))
        (is (g/bad? #(j/resume-code! ready child request)))
        (j/resume-code! ready engine request) (j/resume-code! ready child child-request)
        (is (= 77 (sync/finish! ready engine) (sync/finish! ready child)))
        (is (every? dead? [opts co name cn callback cf]))
        (finally (sync/close! ready engine) (sync/close! ready child))))))

(deftest missing-real-initialized-option-preserves-native-packet
  (let [{:keys [ctx engine]} (context {:skip-global true}) opts (options ctx engine false)
        callback (j/make-closure! ctx engine "capture" [11]) name (decl ctx engine)]
    (profile-start! ctx engine opts callback name)
    (is (re-find #"Initialized global is unavailable: Lean.profiler" (c/failure #(sync/finish! ctx engine))))
    (is (= 2 (c/rc ctx opts))) (is (= 1 (c/rc ctx callback) (c/rc ctx name)))
    (is (not (dead? name))) (is (not (dead? callback)))))

(deftest callback-host-pause-observes-decl-release-and-forks-full-float-result
  (let [spec (h/spec "research_profile_float" ["object"] [false] "float")
        callback-row (c/decl "host-callback" [(c/p 1 "object")] "object"
                       (c/let-ir 2 "float" (c/fap "profile-host" [(c/v 1)])
                         (c/let-ir 3 "object" {:box {:ty "float" :x {:idx 2}}} (c/ret 3))))
        {:keys [ctx engine]} (context {:host-specs [spec] :extra-rows [(h/ext "profile-host" spec) callback-row]})
        opts (options ctx engine false) name (decl ctx engine) callback (j/make-closure! ctx engine "host-callback" [])]
    (profile-start! ctx engine opts callback name)
    (until! ctx engine #(some? (j/host-request ctx engine)))
    (let [request (j/host-request ctx engine) fork (j/fork! ctx engine [opts name callback]) child (:engine fork)
          [co cn cf] (:roots fork) child-request (j/host-request ctx child)]
      (try
        (is (dead? name)) (is (dead? cn))
        (is (= 1 (c/rc ctx opts) (c/rc ctx co)))
        (is (= [0] (h/args request) (h/args child-request)))
        (is (= "float" (j/request-value request "resultType")))
        (is (g/bad? #(j/resume-host! ctx child request 1.25)))
        (j/resume-host! ctx engine request 1.25) (j/resume-host! ctx child child-request -0.0)
        (let [a (sync/finish! ctx engine) b (sync/finish! ctx child)]
          (is (= 1.25 (invoke ctx engine "float-unbox" [a])))
          (is (= Long/MIN_VALUE (Double/doubleToRawLongBits (invoke ctx child "float-unbox" [b])))))
        (is (every? dead? [opts co callback cf]))
        (finally (sync/close! ctx engine) (sync/close! ctx child))))))

(deftest callback-code-pause-and-owned-profile-wrapper-pap
  (let [{:keys [ctx engine source]} (context)
        row (c/decl "late-callback" [(c/p 7 "object")] "object"
              (c/let-ir 19 "object" (c/lit 99) (c/ret 19)))
        header (j/declaration-header source (first (x/raw [row])) (apply str (repeat 64 "a")))
        linked (j/register-headers ctx [header])
        _ (j/install-program! linked engine)
        ready (j/materialize-body linked header (first (x/raw [row])) [])
        opts (options linked engine false) name (decl linked engine)
        callback (j/make-closure! linked engine "late-callback" [])]
    (profile-start! linked engine opts callback name)
    (until! linked engine #(some? (j/code-request linked engine)))
    (let [request (j/code-request linked engine) fork (j/fork! linked engine [opts name]) child (:engine fork)]
      (try
        (is (identical? header (j/request-value request "header")))
        (is (= [0] (vec (j/request-value request "arguments"))))
        (is (dead? name)) (is (dead? (second (:roots fork))))
        (j/resume-code! ready engine request)
        (j/resume-code! ready child (j/code-request linked child))
        (is (= 99 (sync/finish! ready engine) (sync/finish! ready child)))
        (let [opts (options ready engine false) name (decl ready engine)
              callback (j/make-closure! ready engine "capture" [123])
              pap (j/make-closure! ready engine "Lean.profileit._boxed" [0 "pap" opts callback])]
          (is (= 123 (invoke ready engine "apply" [pap name])))
          (is (every? dead? [pap opts name callback])))
        (finally (sync/close! ready engine) (sync/close! ready child))))))

(deftest missing-policy-and-borrowed-root-closure-pap-fences
  (let [{:keys [ctx engine headers]} (context)]
    (try
      (is (re-find #"Borrowed profiling primitive" (c/failure #(j/start! ctx engine "Lean.profileit" []))))
      (is (re-find #"Borrowed profiling primitive" (c/failure #(j/make-closure! ctx engine "Lean.profileit" []))))
      (let [fresh (j/machine ctx)]
        (try
          (is (re-find #"Borrowed profiling primitive"
                (c/failure #(j/install-graph! ctx fresh
                  (j/prepared-graph ctx (.source (headers getter-label)) (Object.)
                    [(j/graph-node ctx {:kind :closure :id 1 :target (headers "Lean.profileit")})] [] [] [])))))
          (is (false? (h/private-value fresh "graphInstalled")))
          (finally (sync/close! ctx fresh))))
      (let [pap (c/decl "bad-profile-pap" [] "object"
                  (c/let-ir 1 "object" {:pap {:c (j/request-value (headers "Lean.profileit") "name") :ys []}} (c/ret 1)))]
        (is (re-find #"Borrowed profiling primitive" (c/failure #(j/extend-program ctx (x/raw [pap]))))))
      (let [no-policy (dissoc ctx :profiling-policy) other (j/machine no-policy)
            callback (j/make-closure! no-policy other "capture" [33]) name (decl no-policy other)]
        (profile-start! no-policy other (options no-policy other false) callback name)
        (is (re-find #"checked-disabled policy" (c/failure #(sync/finish! no-policy other))))
        (is (= 1 (c/rc ctx callback) (c/rc ctx name))))
      (is (g/bad? #(j/machine (assoc ctx :explicit false))))
      (finally (sync/close! ctx engine)))))

(deftest policy-rejects-source-header-name-hash-abi-and-kind-drift
  (let [{:keys [ctx engine source records]} (context)
        original (get (first (filter #(= getter-label (get % "label")) records)) "row")
        digest "697f802be49ca83e350147ca7a564a73e3162beb454ca78d2990455df96796ed"]
    (try
      (doseq [row [(assoc original "name" ["str" ["anonymous"] "other"])
                   (assoc-in original ["ir" "fdecl" "xs" 0 "borrow"] true)
                   (assoc-in original ["ir" "fdecl" "xs" 0 "ty"] "tobject")
                   (assoc-in original ["ir" "fdecl" "type"] "object")]]
        (is (g/bad? #(j/require-disabled-profiling ctx (j/declaration-header source row digest)))))
      (is (g/bad? #(j/require-disabled-profiling ctx (j/declaration-header source original (apply str (repeat 64 "b"))))))
      ;; A valid pinned Header from another source cannot govern this Program.
      (let [foreign (j/declaration-header (j/source-binding ctx (Object.)) original digest)
            foreign-ctx (assoc ctx :profiling-policy (j/require-disabled-profiling ctx foreign))
            other (j/machine foreign-ctx) callback (j/make-closure! foreign-ctx other "capture" [44])
            name (decl foreign-ctx other)]
        (profile-start! foreign-ctx other (options foreign-ctx other false) callback name)
        (is (re-find #"Profiling getter source binding differs" (c/failure #(sync/finish! foreign-ctx other))))
        (is (= 1 (c/rc ctx callback) (c/rc ctx name))))
      (finally (sync/close! ctx engine)))))

(deftest invalid-callback-and-category-reject-before-getter-credit-or-decl-release
  (doseq [invalid-category? [false true]]
    (let [{:keys [ctx engine]} (context) opts (options ctx engine false) name (decl ctx engine)
          value (invoke ctx engine "cons" [8])
          fn-value (if invalid-category? (j/make-closure! ctx engine "capture" [value]) value)
          counts (into {} (for [key ["allocations" "retains" "releases" "stores"]]
                            [key (h/private-value engine key)]))]
      (j/start! ctx engine "Lean.profileit._boxed" [0 (if invalid-category? 7 "category") opts fn-value name])
      (is (g/bad? #(sync/finish! ctx engine)))
      (is (= counts (into {} (for [key (keys counts)] [key (h/private-value engine key)]))))
      (is (= 1 (c/rc ctx opts) (c/rc ctx name) (c/rc ctx fn-value)))
      (is (not (dead? name))))))

(deftest getter-result-must-be-an-actual-bool
  (let [{:keys [ctx engine]} (context)
        empty (invoke ctx engine "Lean.Options.empty" []) key (invoke ctx engine "Lean.Name.mkStr1" ["profiler"])
        ;; Deliberately malformed low-level Bool outside Lean source typing. The
        ;; original getter still runs; its result cannot become silent false.
        opts (invoke ctx engine "Lean.Options.setBool" [empty key 2])
        callback (j/make-closure! ctx engine "capture" [9]) name (decl ctx engine)]
    (profile-start! ctx engine opts callback name)
    (is (re-find #"Profiling getter did not return Bool" (c/failure #(sync/finish! ctx engine))))
    (is (= 1 (c/rc ctx opts) (c/rc ctx name) (c/rc ctx callback)))
    (is (not (dead? name))) (is (not (dead? callback)))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-profile-checks)))
