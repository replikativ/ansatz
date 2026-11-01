(ns java-ir-expr-machinery-checks
  "PRIVATE stage-one research jobs, not a registered Lean native or frontend capability."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-host-checks :as h]
            [java-ir-header-checks :as header] [java-ir-generation-checks :as g]
            [java-ir-code-checks :as code] [java-ir-expr-equality-checks :as eq]
            [java-ir-expr-find-checks :as find] [java-ir-sync-task-checks :as sync]
            [java-ir-logical-sharing-checks :as sharing] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-expr-machinery-runtime/")
(def roles ["Lean.Expr.bvar._override" "Lean.Expr.sort._override" "Lean.Expr.const._override"
            "Lean.Expr.app._override" "Lean.Expr.lam._override._boxed" "Lean.Expr.forallE._override._boxed"
            "Lean.Expr.letE._override._boxed" "Lean.Expr.mdata._override" "Lean.Expr.proj._override"])
(defn private-value [value field]
  ;; Typed job fields live partly on their private common superclass.
  (let [f (loop [cls (class value)]
            (when-not cls (throw (NoSuchFieldException. field)))
            (let [f (try (.getDeclaredField ^Class cls field) (catch NoSuchFieldException _ nil))]
              (if f f (recur (.getSuperclass ^Class cls)))))]
    (.setAccessible ^java.lang.reflect.Field f true) (.get ^java.lang.reflect.Field f value)))
(defn records [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn native-row [] (first (filter #(= "Lean.instantiateExprMVarsImp" (get % "label")) (records))))
(defn setup-copy [entry]
  ;; Input preparation model: same original constructor algorithm, distinct Name.
  (let [label (str "model-setup-" (get entry "label")) n ["str" ["anonymous"] label]]
    {"label" label "sha256" header/digest
     "row" (-> (get entry "row") (assoc "name" n) (assoc-in ["ir" "fdecl" "f"] n))}))
(defn context
  ([] (context {}))
  ([{:keys [defer replacements rows host-specs inactive tasks extra-originals]}]
   (let [originals (filter #(not= "Lean.instantiateExprMVarsImp" (get % "label")) (records))
         entries (concat originals (eq/records) extra-originals (map setup-copy originals)
                   (when tasks (json/read-str (slurp "test/fixtures/java-task-sync-runtime/original-rows.json")))
                   (for [r (x/raw rows)] {"label" (last (get r "name")) "row" r "sha256" header/digest}))
         entries (vals (reduce (fn [m r] (let [n (get-in r ["row" "name"])]
                               (when-let [old (m n)] (assert (= (get old "row") (get r "row"))))
                               (assoc m n r))) {} entries))
         entries (mapv (fn [r] (if-let [body (get replacements (get r "label"))]
                                  (assoc-in r ["row" "ir" "fdecl" "body"] (json/read-str (json/write-str body))) r)) entries)
         base (j/prepare-host-program *basis* [] []) source (j/source-binding base {:expr-machinery-models true :fixture (corpus/sha256 (str directory "provenance.json"))})
         hm (into {} (for [r entries] [(get-in r ["row" "name"]) (j/declaration-header source (get r "row") (get r "sha256"))]))
         registered (j/register-headers base (vec (vals hm)) (or host-specs []))
         ctx (reduce (fn [ctx r] (if (and (get-in r ["row" "ir" "fdecl"]) (not (contains? (set defer) (get r "label"))))
                                   (j/materialize-body ctx (hm (get-in r ["row" "name"])) (get r "row") (mapv hm (find/direct (get r "row")))) ctx)) registered entries)
         ctx (if inactive (assoc ctx :explicit true) (sync/active ctx))]
     {:ctx ctx :source source :rows (into {} (map (juxt #(get % "label") #(get % "row")) entries))
      :headers (into {} (for [r entries] [(get r "label") (hm (get-in r ["row" "name"]))]))})))
(defn call [ctx e label args] (j/start! ctx e label args) (sync/finish! ctx e))
(defn setup! [ctx e role args] (call ctx e (str "model-setup-" (roles role)) args))
(defn fields [ctx value] (mapv identity (.get ^java.lang.reflect.Field (:fields ctx) value)))
(defn scalar-bytes [ctx value] (vec (.get ^java.lang.reflect.Field (:scalars ctx) value)))
(defn retain [ctx e value] (j/retain! ctx e value) value)
(defn bvar! [ctx e index] (setup! ctx e 0 [index]))
(defn sort! [ctx e] (setup! ctx e 1 [0]))
(defn app! [ctx e f a] (setup! ctx e 3 [f a]))
(defn lam! [ctx e body] (setup! ctx e 4 [0 (sort! ctx e) body 0]))
(defn fvar! [ctx e text]
  (call ctx e "Lean.Expr.fvar._override" [(call ctx e "Lean.Name.str._override" [0 text])]))
(defn start! [{:keys [ctx headers]} e mode input args cutoff amount]
  (let [hs (into-array (Class/forName "ansatz.research.ir.Interpreter$Header" true (:loader ctx)) (mapv headers roles))
        m (.getDeclaredMethod ^Class (:class ctx) "startExprMachineryResearch"
            (into-array Class [(class hs) Integer/TYPE Object (class (object-array 0)) Long/TYPE Long/TYPE]))]
    (.setAccessible m true)
    (.invoke m e (object-array [hs (int mode) input (object-array args) (long cutoff) (long amount)]))))
(defn finish-research! [ctx e]
  ;; Bound actual dispatches, not the number of single-step host round trips.
  ;; Dedicated pause/fork checks continue to advance exactly one instruction.
  (let [start (j/instructions ctx e) deadline (+ (System/nanoTime) 30000000000)]
    (loop []
      (let [phase (j/phase ctx e) elapsed (- (j/instructions ctx e) start)]
        (cond
          (= phase "complete") (j/take-result! ctx e)
          (or (not= phase "running") (>= elapsed 2000000) (> (System/nanoTime) deadline))
          (throw (ex-info "Bounded private Expr job reached a boundary"
                   {:phase phase :dispatches elapsed :instructions (j/instructions ctx e)
                    :code-header (some-> (j/code-request ctx e) (.header) (.name))
                    :host-symbol (some-> (j/host-request ctx e) (j/request-value "symbol"))}))
          :else (do (j/advance! ctx e (min 64 (- 2000000 elapsed))) (recur)))))))
(defn run! [lab e mode input args cutoff amount]
  (start! lab e mode input args cutoff amount) (finish-research! (:ctx lab) e))
(defn lift! [lab e input cutoff amount] (run! lab e 0 input [] cutoff amount))
(defn substitute! [lab e input args] (run! lab e 1 input args 0 0))
(defn beta! [lab e input reverse-args] (run! lab e 2 input reverse-args 0 0))
(defn state [e] (some-> (sync/action e) (private-value "exprMachinery")))
(defn current-job [e] (.peekLast ^java.util.Deque (private-value (state e) "jobs")))
(defn materialize [{:keys [ctx headers rows]} label]
  (let [row (rows label) by-name (into {} (for [[label h] headers] [(get (rows label) "name") h]))]
    (j/materialize-body ctx (headers label) row (mapv by-name (find/direct row)))))
(deftest exact-original-constructor-fixture-and-native-metadata-recognized
  (let [rs (records) native (native-row) p (json/read-str (slurp (str directory "provenance.json")))]
    (is (= 10 (count rs))) (is (= (get p "original-rows-sha256") (corpus/sha256 (str directory "original-rows.json"))))
    (is (= "7e53092b477181a60a5e66f6cf2e2f33827b9f05411b294359b860431fc8a9ef" (get native "sha256")))
    (is (some? (:program (j/prepare-host-program *basis* [(get native "row")] []))))))
(deftest identity-fast-paths-preserve-exact-input-and-data
  (doseq [mode [:lift-zero :lift-cutoff :sub-empty :beta-empty]]
    (let [{:keys [ctx] :as lab} (context {:defer (set roles)}) e (j/machine ctx)
          input (bvar! ctx e 0) before (scalar-bytes ctx input)
          output (case mode :lift-zero (lift! lab e input 0 0) :lift-cutoff (lift! lab e input 1 2)
                       :sub-empty (substitute! lab e input []) :beta-empty (beta! lab e input []))]
      (is (identical? input output)) (is (= before (scalar-bytes ctx output))) (is (= 1 (c/rc ctx output)))
      (sync/release! ctx e output) (sync/close! ctx e))))
(deftest lift-cutoff-and-binder-depth-use-original-bvar-and-binder-constructors
  (doseq [[index cutoff amount expected] [[0 0 2 2] [0 1 3 0] [2 1 2 4]]]
    (let [{:keys [ctx] :as lab} (context) e (j/machine ctx) input (bvar! ctx e index)
          result (lift! lab e input cutoff amount) expected-node (bvar! ctx e expected)]
      (is (= [expected] (fields ctx result))) (is (= (scalar-bytes ctx expected-node) (scalar-bytes ctx result)))
      (sync/release! ctx e expected-node) (sync/release! ctx e result) (sync/close! ctx e)))
  (doseq [[index expected] [[0 0] [1 3]]]
    (let [{:keys [ctx] :as lab} (context) e (j/machine ctx) input (lam! ctx e (bvar! ctx e index))
          result (lift! lab e input 0 2)]
      (is (= [expected] (fields ctx (nth (fields ctx result) 2))))
      (when (zero? index) (is (identical? input result)))
      (sync/release! ctx e result) (sync/close! ctx e))))
(deftest substitution-is-nonreverse-and-lifts-open-arguments-under-binders
  (doseq [index [0 1 3]]
    (let [{:keys [ctx] :as lab} (context) e (j/machine ctx) p (fvar! ctx e "p") q (fvar! ctx e "q")
          result (substitute! lab e (bvar! ctx e index) [(retain ctx e p) (retain ctx e q)])]
      (case index 0 (is (identical? p result)) 1 (is (identical? q result)) 3 (is (= [1] (fields ctx result))))
      (doseq [value [p q result]] (sync/release! ctx e value)) (sync/close! ctx e)))
  (let [{:keys [ctx] :as lab} (context) e (j/machine ctx)
        input (lam! ctx e (bvar! ctx e 1)) result (substitute! lab e input [(bvar! ctx e 0)])]
    (is (= [1] (fields ctx (nth (fields ctx result) 2))))
    (is (not (identical? input result))) (sync/release! ctx e result) (sync/close! ctx e)))
(deftest beta-exact-partial-and-overapplication-use-reverse-argument-order
  (doseq [mode [:identity :two :over :partial]]
    (let [{:keys [ctx] :as lab} (context) e (j/machine ctx) p (fvar! ctx e "p") q (fvar! ctx e "q")
          function (case mode :identity (lam! ctx e (bvar! ctx e 0)) :over (lam! ctx e (bvar! ctx e 0))
                         (lam! ctx e (lam! ctx e (app! ctx e (bvar! ctx e 1) (bvar! ctx e 0)))))
          args (case mode :identity [(retain ctx e p)] :partial [(retain ctx e p)] [(retain ctx e q) (retain ctx e p)])
          result (beta! lab e function args)]
      (case mode
        :identity (is (identical? p result))
        (:two :over) (is (every? true? (map identical? [p q] (fields ctx result))))
        :partial (let [body (nth (fields ctx result) 2)]
                   (is (identical? p (first (fields ctx body))))
                   (is (= [0] (fields ctx (second (fields ctx body)))))))
      (doseq [value [p q result]] (sync/release! ctx e value)) (sync/close! ctx e))))
(deftest beta-zeta-and-metadata-apply-only-on-the-applied-head-path
  (let [{:keys [ctx] :as lab} (context) e (j/machine ctx) p (fvar! ctx e "p") q (fvar! ctx e "q")
        function (setup! ctx e 6 [0 (sort! ctx e) (retain ctx e p)
                                  (lam! ctx e (app! ctx e (bvar! ctx e 1) (bvar! ctx e 0))) 1])
        wrapped (setup! ctx e 7 [0 function]) result (beta! lab e wrapped [(retain ctx e q)])]
    (is (every? true? (map identical? [p q] (fields ctx result))))
    (doseq [value [p q result]] (sync/release! ctx e value)) (sync/close! ctx e))
  (let [{:keys [ctx] :as lab} (context) e (j/machine ctx) p (fvar! ctx e "inner")
        function (lam! ctx e (setup! ctx e 7 [0 (bvar! ctx e 0)])) result (beta! lab e function [(retain ctx e p)])]
    (is (= 10 (.getInt ^java.lang.reflect.Field (:tag ctx) result)))
    (is (identical? p (second (fields ctx result))))
    (sync/release! ctx e p) (sync/release! ctx e result) (sync/close! ctx e)))
(defn constructor-request! [ctx e]
  (loop [left 20000]
    (assert (pos? left) "No constructor CodeRequest within bounded progress")
    (or (j/code-request ctx e)
        (do (assert (not (j/advance! ctx e 1)) "Unexpected completion before constructor request")
            (recur (dec left))))))
(defn until! [ctx e predicate]
  (loop [left 20000]
    (assert (pos? left) "Private machinery test exceeded bounded progress")
    (when-not (predicate) (assert (not (j/advance! ctx e 1)) "Unexpected completion before target") (recur (dec left)))))
(deftest complete-null-entry-forks-and-scalar-root-take-result-remains-correct
  (let [{:keys [ctx] :as lab} (context) parent (j/machine ctx) input (bvar! ctx parent 1)]
    (start! lab parent 0 input [] 0 1)
    (loop [left 1000]
      (assert (pos? left)) (when-not (j/advance! ctx parent 1) (recur (dec left))))
    (is (nil? (private-value parent "entry")))
    (let [child (:engine (j/fork! ctx parent []))
          answer (j/take-result! ctx parent) copied (j/take-result! ctx child)]
      (is (= [2] (fields ctx answer) (fields ctx copied))) (is (not (identical? answer copied)))
      (is (= 1 (c/rc ctx answer) (c/rc ctx copied)))
      (sync/release! ctx parent answer) (sync/release! ctx child copied) (sync/close! ctx child))
    (is (= 4294967296 (call ctx parent "Lean.Expr.mkData" [0 0 1 0 0 0 0])))
    (sync/close! ctx parent)))
(deftest constructor-code-request-and-fork-preserve-borrowed-original-and-owned-packet
  (let [label (roles 3) {:keys [ctx headers] :as lab} (context {:defer #{label}})
        parent (j/machine ctx) input (app! ctx parent (bvar! ctx parent 0) (fvar! ctx parent "code"))]
    (start! lab parent 0 input [] 0 1)
    (let [request (constructor-request! ctx parent) packet (private-value (state parent) "call")
          {:keys [engine roots]} (j/fork! ctx parent [input]) child engine ci (first roots)
          ready (materialize lab label)]
      (is (identical? (headers label) (.header request)))
      (is (true? (private-value packet "entered")))
      (is (= [false false] (vec (private-value packet "owned"))))
      (is (identical? ci (private-value (private-value (state child) "input") "value")))
      (doseq [[e old] [[parent input] [child ci]]]
        (j/resume-code! ready e (j/code-request ready e))
        (let [result (sync/finish! ready e)]
          (is (= [1] (fields ready (first (fields ready result)))))
          (is (true? (private-value old "dead")))
          (sync/release! ready e result) (sync/close! ready e))))))
(deftest zeta-result-stays-owned-when-next-beta-frame-cap-rejects
  (let [{:keys [ctx] :as lab} (context) e (j/machine ctx) p (fvar! ctx e "cap-p") q (fvar! ctx e "cap-q")
        function (setup! ctx e 6 [0 (sort! ctx e) (retain ctx e p) (retain ctx e q) 0])]
    (start! lab e 2 function [(retain ctx e p)] 0 0)
    (until! ctx e #(let [job (current-job e)] (and (= "BetaJob" (.getSimpleName (class job)))
                       (= 2 (private-value job "stage")) (some? (private-value job "childResult")))))
    (let [job (current-job e) credit (private-value job "childResult") before (c/rc ctx q)]
      (sync/private-set! (state e) "liveFrames" (int 100000))
      (is (re-find #"frame limit" (c/failure #(j/advance! ctx e 1))))
      (is (identical? credit (private-value job "childResult")))
      (is (true? (private-value credit "owned")))
      (is (identical? q (private-value credit "value")))
      (is (= before (c/rc ctx q))) (is (= "failed" (j/phase ctx e))))))
(deftest replacement-cache-uses-rc-heuristic-including-mt-and-binder-offset
  (let [{:keys [ctx] :as lab} (context) e (j/machine ctx) shared (bvar! ctx e 0)
        input (app! ctx e (retain ctx e shared) shared) result (lift! lab e input 0 1)]
    (is (identical? (first (fields ctx result)) (second (fields ctx result))))
    (sync/release! ctx e result) (sync/close! ctx e))
  (doseq [mt? [false true]]
    (let [{:keys [ctx] :as lab} (context) e (j/machine ctx) input (bvar! ctx e 0)]
      (when mt? (sharing/mark! ctx e input))
      (start! lab e 0 input [] 0 1)
      (until! ctx e #(= 2 (private-value (current-job e) "stage")))
      (is (zero? (.size ^java.util.List (private-value (current-job e) "cacheValues"))))
      (let [result (sync/finish! ctx e)] (sync/release! ctx e result) (sync/close! ctx e))))
  (let [{:keys [ctx] :as lab} (context) e (j/machine ctx) p (fvar! ctx e "offset") shared (bvar! ctx e 0)
        input (setup! ctx e 4 [0 (retain ctx e shared) shared 0])
        result (substitute! lab e input [(retain ctx e p)]) [name domain body] (fields ctx result)]
    (is (identical? p domain)) (is (identical? shared body))
    (is (= [0] (fields ctx body)))
    (sync/release! ctx e p) (sync/release! ctx e result) (sync/close! ctx e)))
(deftest constructor-frame-entry-failure-distinguishes-unentered-packet-and-owned-frame
  (doseq [[field value entered] [["continuationDepth" (int 65536) false] ["callsLeft" (long 0) true]]]
    (let [{:keys [ctx] :as lab} (context) e (j/machine ctx)
          input (app! ctx e (bvar! ctx e 0) (fvar! ctx e "entry"))]
      (start! lab e 0 input [] 0 1)
      (until! ctx e #(let [job (current-job e) frame (.peekLast ^java.util.Deque (private-value job "frames"))]
                      (and frame (= 5 (.getInt ^java.lang.reflect.Field (:tag ctx) (private-value frame "original")))
                           (= 1 (private-value frame "stage")) (= 2 (private-value frame "cursor")))))
      (sync/private-set! e field value)
      (is (g/bad? #(j/advance! ctx e 1)))
      (let [packet (private-value (state e) "call")]
        (is (= entered (private-value packet "entered")))
        (is (= [(not entered) (not entered)] (vec (private-value packet "owned"))))
        (is (= "failed" (j/phase ctx e)))))))
(deftest constructor-code-then-host-reply-fork-never-reclaims-the-packet
  (let [label (roles 3) original (get-in (first (filter #(= label (get % "label")) (records))) ["row" "ir" "fdecl" "body"])
        spec (h/spec "research_expr_constructor_event" ["object" "object"] [true true] "object")
        body (c/let-ir 100 "object" (c/fap "model-constructor-event" [(c/v 1) (c/v 2)]) original)
        {:keys [ctx] :as lab} (context {:defer #{label} :replacements {label body}
                                      :rows [(h/ext "model-constructor-event" spec)] :host-specs [spec]})
        parent (j/machine ctx) input (app! ctx parent (bvar! ctx parent 0) (fvar! ctx parent "host"))]
    (start! lab parent 0 input [] 0 1)
    (constructor-request! ctx parent)
    (let [ready (materialize lab label)]
      (j/resume-code! ready parent (j/code-request ready parent))
      (let [request (h/request! ready parent) args (h/args request)
            {:keys [engine]} (j/fork! ready parent []) child engine]
        (is (= "research_expr_constructor_event" (j/request-value request "symbol")))
        (is (= [2 3] (mapv #(c/rc ready %) args)))
        (is (g/bad? #(j/resume-host! ready child request 0)))
        (doseq [e [parent child]]
          (is (= [false false] (vec (private-value (private-value (state e) "call") "owned"))))
          (j/resume-host! ready e (j/host-request ready e) 0)
          (let [result (sync/finish! ready e)]
            (is (= [1] (fields ready (first (fields ready result)))))
            (is (nil? (state e)))
            (sync/release! ready e result) (sync/close! ready e)))))))
(deftest malformed-constructor-result-remains-owned-in-receiver
  (let [label (roles 0) body (c/let-ir 2 "object" (c/ctor 3 [(c/v 1)] 8) (c/ret 2))
        {:keys [ctx] :as lab} (context {:replacements {label body}})
        e (j/machine ctx) input (bvar! ctx e 0)]
    (start! lab e 0 input [] 0 1)
    (is (re-find #"unexpected head" (c/failure #(sync/finish! ctx e))))
    (let [action (sync/action e) slot (private-value action "slot")
          receiver (aget ^objects (private-value e "objects") slot)
          packet (private-value (state e) "call")]
      (is (= 3 (.getInt ^java.lang.reflect.Field (:tag ctx) receiver)))
      (is (= 1 (c/rc ctx receiver))) (is (= 1 (c/rc ctx input)))
      (is (true? (private-value packet "entered")))
      (is (= [false] (vec (private-value packet "owned")))))))
(deftest all-updated-binders-let-and-payload-wrappers-preserve-source-fields-and-flags
  (doseq [role [4 5 6 7 8]]
    (let [{:keys [ctx] :as lab} (context) e (j/machine ctx)
          p (fvar! ctx e "payload") n (call ctx e "Lean.Name.str._override" [0 "binder"])
          input (case role
                  (4 5) (setup! ctx e role [n (bvar! ctx e 0) (bvar! ctx e 1) 3])
                  6 (setup! ctx e role [n (bvar! ctx e 0) (bvar! ctx e 0) (bvar! ctx e 1) 1])
                  7 (do (sync/release! ctx e n) (setup! ctx e role [0 (bvar! ctx e 0)]))
                  8 (setup! ctx e role [n 2 (bvar! ctx e 0)]))
          result (substitute! lab e input [(retain ctx e p)]) result-fields (fields ctx result)]
      (case role
        (4 5) (do (is (identical? n (first result-fields)))
                  (is (identical? p (nth result-fields 1))) (is (identical? p (nth result-fields 2)))
                  (is (= 3 (nth (scalar-bytes ctx result) 8))))
        6 (do (is (identical? n (first result-fields)))
              (is (every? #(identical? p %) (rest result-fields)))
              (is (= 1 (nth (scalar-bytes ctx result) 8))))
        7 (do (is (= 0 (first result-fields))) (is (identical? p (second result-fields))))
        8 (do (is (identical? n (first result-fields))) (is (= 2 (second result-fields)))
              (is (identical? p (nth result-fields 2)))))
      (sync/release! ctx e p) (sync/release! ctx e result) (sync/close! ctx e))))
(deftest private-entry-preclaim-rejects-inactive-bounds-aliases-and-source-mismatch
  (let [{:keys [ctx headers] :as lab} (context) e (j/machine ctx) input (bvar! ctx e 0)
        before [(c/rc ctx input) (private-value e "allocations") (private-value e "retains")]]
    (doseq [[mode args cutoff amount] [[0 [] -1 1] [0 [] 0 1048576] [0 [input] 0 1]
                                      [1 [] 1 0] [2 [] 0 1] [3 [] 0 0]]]
      (is (g/bad? #(start! lab e mode input args cutoff amount)))
      (is (= "idle" (j/phase ctx e))))
    (is (g/bad? #(start! lab e 1 input [input] 0 0)))
    (is (= before [(c/rc ctx input) (private-value e "allocations") (private-value e "retains")]))
    (let [row (get-in (first (records)) ["row"])
          foreign (j/declaration-header (j/source-binding ctx (Object.)) row (get (first (records)) "sha256"))]
      (is (g/bad? #(start! (assoc lab :headers (assoc headers (first roles) foreign)) e 0 input [] 0 1)))
      (is (= 1 (c/rc ctx input))))
    (sync/release! ctx e input) (sync/close! ctx e))
  (let [{:keys [ctx] :as lab} (context {:inactive true}) e (j/machine ctx)]
    (is (g/bad? #(start! lab e 0 0 [] 0 1)))
    (is (= "idle" (j/phase ctx e))) (j/close! ctx e)))

(deftest named-work-and-interruption-limits-preserve-owned-input
  (doseq [kind [:work :interrupt]]
    (let [{:keys [ctx] :as lab} (context) e (j/machine ctx) input (bvar! ctx e 0) outcome (atom nil)]
      (start! lab e 0 input [] 0 1)
      (sync/private-set! (private-value (state e) "budget") "work" (long (if (= kind :work) 1000000 1023)))
      (if (= kind :work)
        (reset! outcome (c/failure #(j/advance! ctx e 1)))
        (let [worker (Thread. ^Runnable (fn []
                         (.interrupt (Thread/currentThread))
                         (try (reset! outcome (c/failure #(j/advance! ctx e 1)))
                              (finally (Thread/interrupted)))))]
          ;; Only this worker accesses the engine during its bounded call.
          (.start worker) (.join worker 1000) (is (not (.isAlive worker)))))
      (is (re-find (if (= kind :work) #"work outside bounded" #"interrupted") (or @outcome "")))
      (is (= 1 (c/rc ctx input))) (is (= "failed" (j/phase ctx e))))))
(deftest forged-big-nat-and-encountered-cycle-reject-without-truncating-or-recursing
  (doseq [mode [:big-nat :cycle]]
    (let [{:keys [ctx] :as lab} (context) e (j/machine ctx)
          bytes (eq/bytes64 (bit-shift-left 1 44)) r #(j/graph-ref ctx %)
          nodes (if (= mode :big-nat)
                  [(j/graph-node ctx {:kind :ctor :id 1 :rc 99 :tag 0
                                     :fields [(.shiftLeft java.math.BigInteger/ONE 80)] :scalars bytes})]
                  [(j/graph-node ctx {:kind :ctor :id 1 :rc 99 :tag 5 :fields [(r 1) (r 2)] :scalars bytes})
                   (j/graph-node ctx {:kind :ctor :id 2 :rc 99 :tag 0 :fields [0] :scalars bytes})])
          [input] (j/install-graph! ctx e (j/selected-owner-graph ctx (j/source-binding ctx (Object.)) (Object.) nodes [] [] [(r 1)]))
          before (c/rc ctx input)]
      ;; Deliberately forged cache/cycle models, not source-produced Exprs.
      (start! lab e 0 input [] 0 1)
      (is (re-find (if (= mode :big-nat) #"bvar constructor range" #"structural cycle")
                   (c/failure #(sync/finish! ctx e))))
      (is (= before (c/rc ctx input))) (is (= "failed" (j/phase ctx e))))))

(deftest beta-ancestor-parameters-zeta-move-and-application-temporary-survive-code-fork
  (let [label (roles 3) {:keys [ctx headers] :as lab} (context {:defer #{label}}) parent (j/machine ctx)
        p (fvar! ctx parent "beta-p") q (fvar! ctx parent "beta-q")
        old-body (setup! ctx parent 7 [0 (bvar! ctx parent 1)])
        old-let (setup! ctx parent 6 [0 (sort! ctx parent) (bvar! ctx parent 0) old-body 0])
        lambda (lam! ctx parent old-let) input (setup! ctx parent 7 [0 lambda])]
    (start! lab parent 2 input [(retain ctx parent q) (retain ctx parent p)] 0 0)
    (let [request (constructor-request! ctx parent) beta (current-job parent)
          frames (mapv #(private-value % "expression") (private-value beta "frames"))
          zeta (private-value (nth frames 3) "value")
          temporary (private-value beta "temporary") accumulator (private-value beta "accumulator")
          {:keys [engine roots]} (j/fork! ctx parent [input p q]) child engine [ci cp cq] roots
          ready (materialize lab label)]
      (is (identical? (headers label) (.header request)))
      (is (= 5 (count frames)))
      (is (identical? input (private-value (private-value beta "function") "value")))
      (is (not (identical? (private-value beta "function") (first frames))))
      (is (every? #(private-value % "owned") frames))
      (is (= [2 2 2] (mapv #(c/rc ctx %) [input lambda old-let])))
      (is (= 1 (c/rc ctx zeta)))
      (is (identical? (second (fields ctx zeta)) (private-value (last frames) "value")))
      (is (= 2 (c/rc ctx (second (fields ctx zeta)))))
      (is (not (identical? temporary accumulator)))
      (is (true? (private-value temporary "owned"))) (is (true? (private-value accumulator "owned")))
      (is (identical? p (private-value temporary "value"))) (is (identical? p (private-value accumulator "value")))
      (is (= [5 3] (mapv #(c/rc ctx %) [p q])))
      (doseq [[e root ep eq] [[parent input p q] [child ci cp cq]]]
        (let [job (current-job e)]
          (is (identical? ep (private-value (private-value job "temporary") "value")))
          (is (identical? ep (private-value (private-value job "accumulator") "value"))))
        (j/resume-code! ready e (j/code-request ready e))
        (let [result (sync/finish! ready e)]
          (is (every? true? (map identical? [ep eq] (fields ready result))))
          (is (true? (private-value root "dead")))
          (is (= [2 2] (mapv #(c/rc ready %) [ep eq])))
          (doseq [value [ep eq result]] (sync/release! ready e value)) (sync/close! ready e))))))
(deftest aggregate-live-cache-cap-preserves-the-unpublished-result-owner
  (let [{:keys [ctx] :as lab} (context) e (j/machine ctx) input (bvar! ctx e 0)]
    (retain ctx e input)
    (start! lab e 0 input [] 0 1)
    (until! ctx e #(let [job (current-job e) frame (.peekLast ^java.util.Deque (private-value job "frames"))]
                    (and frame (= 5 (private-value frame "stage")))))
    (let [job (current-job e) frame (.peekLast ^java.util.Deque (private-value job "frames"))
          result (private-value frame "result")]
      (sync/private-set! (state e) "liveCacheEntries" (int 100000))
      (is (re-find #"live cache entries outside bounded" (c/failure #(j/advance! ctx e 1))))
      (is (true? (private-value result "owned")))
      (is (= 1 (c/rc ctx (private-value result "value"))))
      (is (= 2 (c/rc ctx input)))
      (is (zero? (private-value job "reservedCacheEntries"))))))
(deftest deep-binder-rebuild-uses-iterative-frames-and-resumable-cleanup
  (let [{:keys [ctx] :as lab} (context) e (j/machine ctx) depth 1000 domain (sort! ctx e)
        input (loop [left depth body (bvar! ctx e depth)]
                (if (zero? left) body
                  (recur (dec left) (setup! ctx e 4 [0 (retain ctx e domain) body 0]))))]
    (sync/release! ctx e domain)
    (let [result (lift! lab e input 0 1)
          body (loop [left depth node result]
                 (if (zero? left) node (recur (dec left) (nth (fields ctx node) 2))))]
      (is (= [(inc depth)] (fields ctx body)))
      (is (true? (private-value input "dead")))
      (sync/release! ctx e result) (sync/close! ctx e))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-machinery-checks)))
