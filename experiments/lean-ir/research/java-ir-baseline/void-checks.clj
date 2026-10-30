(ns java-ir-void-checks
  "Exact Void.mk ownership and resumable active release, without new world carriers."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-host-checks :as h]
            [java-ir-header-checks :as headers] [java-ir-code-checks :as code]
            [java-ir-generation-checks :as g] [java-ir-continuation-checks :as k]
            [java-ir-sync-task-checks :as sync] [java-ir-array-checks :as array]
            [java-ir-logical-sharing-checks :as sharing] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-void-runtime/")
(defn records [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn record [label] (first (filter #(= label (get % "label")) (records))))
(defn actual-name [label] (get-in (record label) ["row" "name"]))
(defn void-fap [args] {:fap {:c (actual-name "Void.mk") :ys args}})
(defn helpers []
  (concat g/common
    [(c/decl "void-value" [(c/p 1 "object")] "object"
       (c/let-ir 2 "object" (c/ctor 0 [(c/v 1)] 0) (c/ret 2)))
     (c/decl "void-pair" [(c/p 1 "object") (c/p 2 "object")] "object"
       (c/let-ir 3 "object" (c/ctor 0 [(c/v 1) (c/v 2)] 0) (c/ret 3)))
     (c/decl "void-fap" [(c/p 1 "object")] "void"
       (c/let-ir 2 "void" (void-fap ["erased" (c/v 1)]) (c/ret 2)))
     (c/object-constant "void-cache")]))
(defn direct [row]
  (let [self (get row "name")]
    (vals (into {} (for [x (tree-seq coll? seq (get-in row ["ir" "fdecl" "body"]))
                        :when (map? x) :let [call (or (get x "fap") (get x "pap"))]
                        :when call :let [n (get call "c")] :when (not= n self)] [(json/write-str n) n])))))
(defn context
  ([] (context {}))
  ([{:keys [rows host-specs defer active arrays]}]
   (let [originals (concat (records) (when arrays (array/originals))
                           (when active (json/read-str (slurp "test/fixtures/java-task-sync-runtime/original-rows.json"))))
         entries (concat originals (for [row (x/raw (concat (helpers) rows))]
                                     {"label" (last (get row "name")) "row" row "sha256" headers/digest}))
         entries (vals (reduce (fn [m row]
                                (let [n (get-in row ["row" "name"]) old (get m n)]
                                  (when old (assert (= (get old "row") (get row "row")))) (assoc m n row))) {} entries))
         base (j/prepare-host-program *basis* [] [])
         source (j/source-binding base {:void-fixture (corpus/sha256 (str directory "provenance.json")) :models true})
         hm (into {} (for [r entries] [(get-in r ["row" "name"]) (j/declaration-header source (get r "row") (get r "sha256"))]))
         ctx (j/register-headers base (vec (vals hm)) (or host-specs []))
         ctx (reduce (fn [ctx r]
                       (if (and (get-in r ["row" "ir" "fdecl"]) (not (contains? (set defer) (get r "label"))))
                         (j/materialize-body ctx (hm (get-in r ["row" "name"])) (get r "row")
                                             (mapv hm (direct (get r "row")))) ctx)) ctx entries)]
     {:ctx (if active (sync/active ctx) ctx) :source source
      :headers (into {} (for [r entries] [(get r "label") (hm (get-in r ["row" "name"]))]))
      :rows (into {} (for [r entries] [(get r "label") (get r "row")]))})))
(defn fresh [ctx e value] (j/call ctx e "void-value" [value]))
(defn void-action [e]
  (loop [a (sync/action e)]
    (when a (let [f (h/private-value a "function")]
              (if (and f (= 516 (h/private-value f "intrinsic"))) a (recur (h/private-value a "parent")))))))
(defn cleanup-lab []
  (let [event (h/spec "research_void_finalizer" ["object"] [true] "object")
        row (c/decl "void-finalizer" [(c/p 1 "object")] "object"
              (c/let-ir 2 "object" (c/fap "void-finalizer-event" [(c/v 1)])
                ["dec" {:idx 1} 1 false false (c/ret 2)]))]
    (context {:active true :host-specs [event] :defer #{"void-finalizer"}
              :rows [(h/ext "void-finalizer-event" event) row]})))
(defn cleanup-values [ctx e]
  (let [promise (sync/promise! ctx e) source (sync/result-task! ctx e promise)
        mapped (sync/map! ctx e (j/make-closure! ctx e "void-finalizer" []) source)
        leaf (fresh ctx e 7) outer (j/call ctx e "void-pair" [promise leaf])]
    {:promise promise :mapped mapped :leaf leaf :outer outer}))

(deftest exact-original-void-and-owned-boxed-abis
  (let [proof (json/read-str (slurp (str directory "provenance.json")))
        row (get (record "Void.mk") "row") d (get-in row ["ir" "extern"])]
    (is (= 2 (count (records)))) (is (= [] (get proof "initialized-dependencies")))
    (is (= (get proof "original-rows-sha256") (corpus/sha256 (str directory "original-rows.json"))))
    (is (= "d2b000fd149cb88f53641b2510e9a82394dd812443bd668093d2ee7d1f2ebbb4" (get (record "Void.mk") "sha256")))
    (is (= [["erased" "tobject"] [false false] "void"]
           [(mapv #(get % "ty") (get d "xs")) (mapv #(get % "borrow") (get d "xs")) (get d "type")]))
    (is (= "lean_void_mk" (x/abi row)))
    (doseq [bad [(assoc-in row ["ir" "extern" "type"] "tobject")
                 (assoc-in row ["ir" "extern" "xs" 0 "ty"] "tobject")
                 (assoc-in row ["ir" "extern" "xs" 1 "borrow"] true)]]
      (is (g/bad? #(x/abi bad))))
    (is (= "tagged" (get-in (record "Void.mk._boxed") ["row" "ir" "fdecl" "type"])))))

(deftest root-fap-and-genuine-boxed-wrapper-consume-one-owner-and-return-zero
  (let [{:keys [ctx]} (context) e (j/machine ctx)]
    (doseq [label ["Void.mk" "Void.mk._boxed" "void-fap"]]
      (doseq [value [0 17 (biginteger "18446744073709551616") "payload"]]
        (let [before (k/counters ctx e)]
          (is (= 0 (j/call ctx e label (if (= label "void-fap") [value] [0 value]))))
          (is (= before (k/counters ctx e)))))
      (let [leaf (fresh ctx e 42) outer (fresh ctx e leaf) before (h/private-value e "releases")]
        (is (= 0 (j/call ctx e label (if (= label "void-fap") [outer] [0 outer]))))
        (is (= 2 (- (h/private-value e "releases") before)))
        (is (every? sharing/dead? [leaf outer]))))
    (j/close! ctx e)))

(deftest surviving-aliases-cache-owners-and-persistent-payloads-are-not-overreleased
  (let [{:keys [ctx source]} (context) e (j/machine ctx) value (fresh ctx e 0)]
    (j/retain! ctx e value)
    (is (= 0 (j/call ctx e "Void.mk" [0 value]))) (is (= 1 (c/rc ctx value)))
    (is (not (sharing/dead? value))) (j/release! ctx e value)
    (let [cached (j/call ctx e "void-cache" [])]
      (is (= 2 (c/rc ctx cached))) (is (= 0 (j/call ctx e "Void.mk" [0 cached])))
      (is (= 1 (c/rc ctx cached)))
      (let [[persistent] (j/install-graph! ctx e
                           (j/prepared-graph ctx source (Object.)
                             [(j/graph-node ctx {:kind :ctor :id 1 :tag 0 :fields [0]})] [] [] [(j/graph-ref ctx 1)]))
            before (k/counters ctx e)]
        (is (= 0 (j/call ctx e "Void.mk" [0 persistent])))
        (is (= before (k/counters ctx e))) (is (= 0 (c/rc ctx persistent))) (is (not (sharing/dead? persistent))))
      (j/close! ctx e) (is (sharing/dead? cached)))))

(deftest raw-and-boxed-partial-applications-consume-closure-and-transferred-payload
  (let [{:keys [ctx]} (context) e (j/machine ctx)]
    (doseq [label ["Void.mk" "Void.mk._boxed"]]
      (let [p (j/make-closure! ctx e label [0]) value (fresh ctx e 42)]
        (is (= 0 (j/call ctx e "apply" [p value])))
        (is (every? sharing/dead? [p value]))))
    (j/close! ctx e)))

(deftest erased-payload-and-direct-native-ap-reject-before-owner-effects
  (doseq [mode [:root :ap]]
    (let [{:keys [ctx]} (context) e (j/machine ctx) value (fresh ctx e 0)
          p (when (= mode :ap) (j/make-closure! ctx e "Void.mk" [1])) before (k/counters ctx e)]
      (is (re-find #"erased parameter" (c/failure #(if p (j/call ctx e "apply" [p value]) (j/call ctx e "Void.mk" [1 value])))))
      (is (= before (k/counters ctx e))) (is (= 1 (c/rc ctx value))) (is (not (sharing/dead? value)))
      (when p (is (= 1 (c/rc ctx p))) (is (not (sharing/dead? p))))))
  (let [{:keys [ctx]} (context) e (j/machine ctx)]
    (doseq [bad [nil (Object.) 0.5]]
      (is (g/bad? #(j/call ctx e "Void.mk" [0 bad]))))
    (is (= [0 0 0 0 0] (sharing/counters e)))))

(deftest inactive-quiet-domain-rejects-nested-foreign-runtime-task-before-root-or-ap-claim
  (let [{active :ctx} (context {:active true}) owner (j/machine active)]
    (doseq [mode [:root :ap]]
      (let [{:keys [ctx]} (context) e (j/machine ctx) promise (sync/promise! active owner)
            outer (fresh active owner promise) p (when (= mode :ap) (j/make-closure! ctx e "Void.mk" [0]))
            before (k/counters ctx e)]
        (is (re-find #"Task/Promise|another interpreter" (c/failure #(if p (j/call ctx e "apply" [p outer]) (j/call ctx e "Void.mk" [0 outer])))))
        (is (= before (k/counters ctx e))) (is (= 1 (c/rc active outer) (c/rc active promise)))
        (is (not (sharing/dead? outer)))
        (when p (is (not (sharing/dead? p))) (is (= 1 (c/rc ctx p))))
        ;; The rejected foreign-owner packet was never transferred. Its real owner retires it.
        (sync/release! active owner outer)))
    (sync/close! active owner)))

(deftest active-void-result-is-not-published-before-release-and-forks-consume-once
  (let [{:keys [ctx]} (context {:active true}) parent (j/machine ctx) leaf (fresh ctx parent 1) value (fresh ctx parent leaf)]
    (j/start! ctx parent "Void.mk" [0 value])
    (is (= "running" (j/phase ctx parent))) (is (= 1 (c/rc ctx value)))
    (is (g/bad? #(j/take-result! ctx parent)))
    (let [{:keys [engine roots]} (j/fork! ctx parent [value leaf]) child engine [cv cl] roots]
      (doseq [[e v l] [[parent value leaf] [child cv cl]]]
        (let [before (h/private-value e "releases")]
          (is (= 0 (sync/finish! ctx e))) (is (= 2 (- (h/private-value e "releases") before)))
          (is (every? sharing/dead? [v l]))
          (is (g/bad? #(j/take-result! ctx e))) (is (nil? (sync/action e))))
        (sync/close! ctx e)))))

(deftest active-void-finalizer-code-host-and-fork-drain-before-canonical-zero-result
  (let [{:keys [ctx headers rows]} (cleanup-lab) parent (j/machine ctx)
        {:keys [outer promise mapped leaf]} (cleanup-values ctx parent)]
    (j/start! ctx parent "Void.mk" [0 outer])
    (let [request (code/request! ctx parent) action (void-action parent)
          {:keys [engine roots]} (j/fork! ctx parent [outer promise mapped leaf]) child engine [co cp cm cl] roots
          ready (j/materialize-body ctx (headers "void-finalizer") (rows "void-finalizer") [(headers "void-finalizer-event")])]
      (is (identical? (headers "void-finalizer") (.header request)))
      (is (= 2 (h/private-value action "stage"))) (is (true? (h/private-value action "releaseClaimed")))
      (is (identical? outer (h/private-value action "retiring"))) (is (= 0 (h/private-value action "output")))
      (is (every? sharing/dead? [outer promise leaf co cp cl]))
      (doseq [[e v p m l answer] [[parent outer promise mapped leaf 83] [child co cp cm cl 99]]]
        (j/resume-code! ready e (j/code-request ready e))
        (let [r (h/request! ready e)]
          (is (= "research_void_finalizer" (j/request-value r "symbol"))) (is (= [0] (h/args r)))
          (is (g/bad? #(j/take-result! ready e))) (j/resume-host! ready e r answer))
        (is (= 0 (sync/finish! ready e)))
        (is (= answer (sync/get! ready e m))) ; callback result is Task's value, never Void's result
        (is (every? sharing/dead? [v p m l])) (is (nil? (void-action e)))
        (is (sync/quiescent? ready e)) (sync/close! ready e)))))

(deftest active-finalizer-failure-keeps-claimed-native-release-without-replay
  (let [{:keys [ctx headers rows]} (cleanup-lab) e (j/machine ctx)
        {:keys [outer promise mapped]} (cleanup-values ctx e)]
    (j/start! ctx e "Void.mk" [0 outer])
    (let [request (code/request! ctx e)
          ready (j/materialize-body ctx (headers "void-finalizer") (rows "void-finalizer") [(headers "void-finalizer-event")])]
      (j/resume-code! ready e request)
      (let [r (h/request! ready e) action (void-action e) before (k/counters ready e)]
        (j/fail-host! ready e r (ex-info "model Void finalizer failure" {}))
        (is (= "failed" (j/phase ready e))) (is (= before (k/counters ready e)))
        (is (true? (h/private-value action "releaseClaimed"))) (is (= 2 (h/private-value action "stage")))
        (is (identical? outer (h/private-value action "retiring")))
        (is (every? sharing/dead? [outer promise])) (is (not (sharing/dead? mapped)))
        (is (g/bad? #(j/resume-host! ready e r 0))) (is (g/bad? #(j/take-result! ready e)))
        (is (g/bad? #(j/fork! ready e []))) (is (g/bad? #(j/start-dispose! ready e)))
        (is (g/bad? #(j/close! ready e)))))))

(deftest quiet-domain-boundaries-check-persistent-owners-but-ignore-nonowning-spare-slots
  (let [{active :ctx source :source} (context {:active true}) owner (j/machine active)]
    ;; Private pointer observation models a foreign persistent child. The quiet
    ;; walk must check its shallow owner before stopping at RC0, just as DEC does.
    (let [[persistent] (j/install-graph! active owner
                         (j/prepared-graph active source (Object.)
                           [(j/graph-node active {:kind :ctor :id 1 :tag 0 :fields [0]})] [] [] [(j/graph-ref active 1)]))
          _ (sharing/private-call active owner "pointerWord" [Object] [persistent])
          outer (fresh active owner persistent) {ctx :ctx} (context) e (j/machine ctx)
          before (k/counters ctx e)]
      (is (re-find #"Pointer-observed.*another interpreter" (c/failure #(j/call ctx e "Void.mk" [0 outer]))))
      (is (= before (k/counters ctx e))) (is (= 1 (c/rc active outer)))
      (is (not (sharing/dead? outer))) (is (= 0 (c/rc active persistent)))
      (sync/release! active owner outer) (j/close! ctx e))
    ;; A nonfinal root DEC cannot reach its child: the quiet guard deliberately
    ;; permits that constant-time operation without inspecting a foreign Task.
    (let [promise (sync/promise! active owner) outer (fresh active owner promise)
          {ctx :ctx} (context) e (j/machine ctx)]
      (j/retain! active owner outer)
      (is (= 0 (j/call ctx e "Void.mk" [0 outer])))
      (is (= 1 (c/rc active outer) (c/rc active promise)))
      (is (= 1 (h/private-value e "releases")))
      (sync/release! active owner outer) (j/close! ctx e))
    ;; The foreign Promise in spare capacity is a private borrowed sentinel,
    ;; never an owning edge; clear it after the check even if an assertion fails.
    (let [promise (sync/promise! active owner) {ctx :ctx} (context {:arrays true}) e (j/machine ctx)
          leaf (fresh ctx e 7) a (array/push! ctx e (array/empty! ctx e 4) leaf)
          slots ^objects (array/fields ctx a)]
      (aset slots 3 promise)
      (try
        (is (= 0 (j/call ctx e "Void.mk" [0 a])))
        (is (every? sharing/dead? [a leaf])) (is (= 1 (c/rc active promise)))
        (finally (aset slots 3 nil)))
      (sync/release! active owner promise) (j/close! ctx e))
    (sync/close! active owner)))

(defn check! [basis] (binding [*basis* basis x/*basis* basis] (run-tests 'java-ir-void-checks)))
