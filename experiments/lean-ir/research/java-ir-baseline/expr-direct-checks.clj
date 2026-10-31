(ns java-ir-expr-direct-checks
  "PRIVATE complete direct pass report; original two-pass native remains unavailable."
  (:refer-clojure :exclude [run!])
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-host-checks :as h] [java-ir-generation-checks :as g]
            [java-ir-header-checks :as header] [java-ir-sync-task-checks :as sync]
            [java-ir-expr-machinery-checks :as expr] [java-ir-level-mvars-checks :as level]
            [java-ir-logical-sharing-checks :as sharing] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-expr-direct-runtime/")
(def pv expr/private-value)
(def helpers ["Lean.MetavarContext.getExprAssignmentExp" "Lean.MetavarContext.getDelayedMVarAssignmentExp"
              "Lean.DelayedMetavarAssignment.fvarsExp" "Lean.DelayedMetavarAssignment.mvarIdPendingExp" "Lean.assignExp"])
(defn originals [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn records [] (json/read-str (slurp (str directory "execution-rows.json"))))
(defn copy-role [entry]
  (let [label (str "model-setup-" (get entry "label")) n ["str" ["anonymous"] label]]
    {"label" label "sha256" header/digest
     "row" (-> (get entry "row") (assoc "name" n) (assoc-in ["ir" "fdecl" "f"] n))}))
(defn context
  ([] (context {}))
  ([options]
   (let [extra (concat (records) (level/records) (map copy-role (take 19 (originals))))
         lab (binding [expr/*basis* *basis*]
               (expr/context (merge options {:extra-originals extra :rows (concat [(level/fresh-context-row)] (:rows options))})))
         policy (apply j/level-instantiation-policy (:ctx lab) (map (:headers lab) level/roles))]
     (assoc lab :level-policy policy))))
(defn engine [{:keys [ctx level-policy]}]
  (let [e (j/machine ctx)] (j/configure-level-instantiation! ctx e level-policy) e))
(defn state [e]
  (loop [a (sync/action e)] (when a (if (pv a "exprDirect") (pv a "exprDirect") (recur (pv a "parent"))))))
(defn session [e] (some-> (state e) (pv "session")))
(defn task [e] (.peekLast ^java.util.Deque (pv (session e) "tasks")))
(defn start! [{:keys [ctx headers]} e m input]
  (let [cls (Class/forName "ansatz.research.ir.Interpreter$Header" true (:loader ctx))
        hs (into-array cls (mapv headers helpers)) cs (into-array cls (mapv headers expr/roles))
        method (.getDeclaredMethod ^Class (:class ctx) "startExprDirectResearch" (into-array Class [(class hs) (class cs) Object Object]))]
    (.setAccessible method true) (.invoke method e (object-array [hs cs m input]))))
(defn run! [lab e m input] (start! lab e m input) (expr/finish-research! (:ctx lab) e))
(defn mvar! [ctx e n] (expr/call ctx e "Lean.Expr.mvar._override" [n]))
(defn assign! [ctx e m n value] (expr/call ctx e "Lean.assignExp" [m n value]))
(defn fields [ctx value] (expr/fields ctx value))
(defn close! [ctx e report] (sync/release! ctx e report) (sync/close! ctx e))
(deftest nineteen-authentic-roles-closed-helper-fixture-and-native-stays-off
  (let [m (json/read-str (slurp (str directory "provenance.json")))]
    (is (= 20 (count (originals)))) (is (= 111 (count (records))))
    (is (= [] (get m "execution-initialized-dependencies")))
    (is (= (get m "original-rows-sha256") (corpus/sha256 (str directory "original-rows.json"))))
    (is (= (get m "execution-rows-sha256") (corpus/sha256 (str directory "execution-rows.json"))))
    (let [native (last (originals))]
      (is (re-find #"Unsupported baseline extern" (c/failure #(j/prepare-host-program *basis* [(get native "row")] [])))))))
(deftest no-mvars-fast-path-preserves-input-with-all-helper-bodies-unprepared
  (let [{:keys [ctx] :as lab} (context {:defer (set (concat helpers expr/roles level/roles))}) e (engine lab)
        m (level/fresh! ctx e) input (expr/bvar! ctx e 0) report (run! lab e m input) values (fields ctx report)]
    (is (identical? m (values 0))) (is (identical? input (values 1))) (is (= 0 (values 2)))
    (is (= 1 (c/rc ctx input))) (is (nil? (state e))) (close! ctx e report)))
(deftest unassigned-mvar-is-unchanged-without-claiming-full-instantiation
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
        input (mvar! ctx e (level/name! ctx e "unassigned")) report (run! lab e m input) values (fields ctx report)]
    (is (identical? input (values 1))) (is (= 0 (values 2))) (is (= 1 (c/rc ctx input))) (close! ctx e report)))
(deftest direct-assignment-chain-compresses-and-reads-back-through-original-getter
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
        a (level/name! ctx e "expr-a") b (level/name! ctx e "expr-b")
        input (mvar! ctx e (expr/retain ctx e a)) bv (mvar! ctx e (expr/retain ctx e b)) value (expr/sort! ctx e)
        m (assign! ctx e m b (expr/retain ctx e value)) m (assign! ctx e m (expr/retain ctx e a) bv)
        report (run! lab e m input) values (fields ctx report)
        assignment (expr/call ctx e (helpers 0) [(expr/retain ctx e (values 0)) a])]
    (is (identical? value (values 1))) (is (= 0 (values 2)))
    (is (identical? value (first (fields ctx assignment)))) (is (true? (pv bv "dead")))
    (sync/release! ctx e assignment) (sync/release! ctx e value) (close! ctx e report)))
(deftest sort-and-const-level-jobs-preserve-latest-context-and-list-suffix
  (let [{:keys [ctx] :as lab} (context {:rows [(c/decl "model-level-cons" [(c/p 1 "object") (c/p 2 "object")] "object"
                                                            (c/let-ir 3 "object" (c/ctor 1 [(c/v 1) (c/v 2)] 0) (c/ret 3)))]})
        e (engine lab) m (level/fresh! ctx e) n (level/name! ctx e "universe")
        variable (level/mvar! ctx e (expr/retain ctx e n)) one (level/succ! ctx e 0)
        m (level/assign! ctx e m n (expr/retain ctx e one))
        tail (expr/call ctx e "model-level-cons" [(expr/retain ctx e one) 0])
        ls (expr/call ctx e "model-level-cons" [variable (expr/retain ctx e tail)])
        input (expr/setup! ctx e 2 [(level/name! ctx e "C") ls]) report (run! lab e m input)
        result (second (fields ctx report)) new-list (second (fields ctx result))]
    (is (not (identical? input result))) (is (identical? one (first (fields ctx new-list))))
    (is (identical? tail (second (fields ctx new-list))))
    (sync/release! ctx e one) (sync/release! ctx e tail) (close! ctx e report)))
(deftest assigned-mvar-head-runs-original-beta-machinery
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
        n (level/name! ctx e "fn") fn (expr/lam! ctx e (expr/bvar! ctx e 0))
        head (mvar! ctx e (expr/retain ctx e n)) p (expr/fvar! ctx e "p")
        m (assign! ctx e m n fn) input (expr/app! ctx e head (expr/retain ctx e p))
        report (run! lab e m input)]
    (is (identical? p (second (fields ctx report)))) (is (= 0 (nth (fields ctx report) 2)))
    (sync/release! ctx e p) (close! ctx e report)))
(defn until! [ctx e pred] (expr/until! ctx e pred))
(defn current-context [e] (some-> (session e) (pv "context") (pv "current") (pv "value")))
(defn all-tasks [e] (vec (pv (session e) "tasks")))
(defn task-kind? [kind t] (= kind (.getSimpleName (class t))))
(defn task-of [e kind] (first (filter #(task-kind? kind %) (all-tasks e))))
(defn materialize [lab label] (expr/materialize lab label))
(deftest semantic-equal-distinct-names-stop-self-and-mutual-assignment-cycles
  (doseq [mutual? [false true]]
    (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
          a (level/name! ctx e "semantic-cycle-a") a2 (level/name! ctx e "semantic-cycle-a")
          b (level/name! ctx e "semantic-cycle-b") input (mvar! ctx e a2)
          av (mvar! ctx e (expr/retain ctx e a)) bv (mvar! ctx e (expr/retain ctx e b))
          m (if mutual? (assign! ctx e m b av) (do (sync/release! ctx e b) (sync/release! ctx e av) m))
          m (assign! ctx e m a (if mutual? bv (do (sync/release! ctx e bv) (mvar! ctx e (level/name! ctx e "semantic-cycle-a")))))
          report (run! lab e m input) result (second (fields ctx report))]
      (is (= 2 (.getInt ^java.lang.reflect.Field (:tag ctx) result)))
      (is (= 0 (nth (fields ctx report) 2))) (is (< (j/instructions ctx e) 10000))
      (close! ctx e report))))
(deftest reentrant-shared-composite-keeps-first-cache-entry-and-returns-outer-result
  ;; Actual context contains a semantic assignment cycle; no forged Node graph.
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
        a (level/name! ctx e "reentry") mv (mvar! ctx e (expr/retain ctx e a))
        input (expr/app! ctx e mv (expr/fvar! ctx e "arg"))
        m (assign! ctx e m a (expr/retain ctx e input))]
    (start! lab e m input)
    (until! ctx e #(some (fn [f] (and (task-kind? "DirectVisitFrame" f) (pv f "cacheTemporary"))) (all-tasks e)))
    (let [frame (first (filter #(and (task-kind? "DirectVisitFrame" %) (pv % "cacheTemporary")) (all-tasks e)))
          original (pv frame "original") cache (pv (session e) "cache")
          first-value (pv (.get ^java.util.Map cache original) "value") outer (pv (pv frame "result") "value")]
      (is (not (identical? first-value outer)))
      (is (identical? input original))
      (let [report (expr/finish-research! ctx e)]
        (is (identical? outer (second (fields ctx report)))) (close! ctx e report)))))
(deftest shared-dag-cache-hit-preserves-output-alias-and-logical-mt-uses-exclusive-rule
  (doseq [mt? [false true]]
    (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
          name (level/name! ctx e "dag") mv (mvar! ctx e (expr/retain ctx e name))
          sub (expr/app! ctx e (expr/fvar! ctx e "f") mv)
          input (expr/setup! ctx e 4 [0 (expr/retain ctx e sub) sub 0]) val (expr/sort! ctx e)
          m (assign! ctx e m name val)]
      (when mt? (sharing/mark! ctx e input))
      (start! lab e m input)
      (until! ctx e #(some (fn [f] (and (task-kind? "DirectVisitFrame" f) (= 91 (pv f "stage"))
                            (identical? sub (pv f "original")) (false? (pv f "shared"))
                            (some? (.get ^java.util.Map (pv (session e) "cache") sub)))) (all-tasks e)))
      (let [report (expr/finish-research! ctx e) out (second (fields ctx report))]
        (is (identical? (second (fields ctx out)) (nth (fields ctx out) 2)))
        (close! ctx e report)))))
(deftest getter-and-setter-code-forks-preserve-context-packet-transfer-and-budget
  (doseq [label [(helpers 0) (helpers 4)]]
    (let [{:keys [ctx headers] :as lab} (context {:defer #{label}}) parent (engine lab)
          a (level/name! ctx parent "outer") b (level/name! ctx parent "inner")
          input (mvar! ctx parent (expr/retain ctx parent a)) bv (mvar! ctx parent (expr/retain ctx parent b))
          m (level/fresh! ctx parent) m (expr/call ctx parent (str "model-setup-" (helpers 4)) [m b (expr/sort! ctx parent)])
          ;; Setter under test remains unprepared: use its explicitly model-labeled copy for setup.
          m (expr/call ctx parent (str "model-setup-" (helpers 4)) [m a bv])]
      (start! lab parent m input)
      (until! ctx parent #(some? (j/code-request ctx parent)))
      (let [packet (pv (session parent) "call") request (j/code-request ctx parent)
            {:keys [engine roots]} (j/fork! ctx parent [m input]) child engine ready (materialize lab label)]
        (is (identical? (headers label) (.header request)))
        (is (true? (pv packet "entered"))) (is (every? false? (vec (pv packet "owned"))))
        (is (= (if (= label (helpers 4)) nil m) (current-context parent)))
        (is (identical? (pv (state child) "budget") (pv (session child) "budget")))
        (is (identical? (pv (state child) "context") (pv (pv (session child) "levels") "context")))
        (doseq [e [parent child]]
          (j/resume-code! ready e (j/code-request ready e))
          (let [report (expr/finish-research! ready e)] (is (= 3 (.getInt ^java.lang.reflect.Field (:tag ready) (second (fields ready report)))))
            (close! ready e report)))))))

(defn delayed-model-rows []
  ;; Explicit test adapter: copy the authenticated ten-field context and swap the
  ;; compiled assignment-map fields 8/9. Actual map operations/getters stay guest IR.
  ;; This is not claimed to be original assignDelayedMVar's monad implementation.
  [(let [order [0 1 2 3 4 5 6 7 9 8]
         tail (c/let-ir 12 "object" (c/ctor 0 (mapv #(c/v (+ 2 %)) order) 0)
                       ["dec" {:idx 1} 1 false false (c/ret 12)])]
     (c/decl "model-swap-expr-delayed-maps" [(c/p 1 "object")] "object"
       (reduce (fn [body i] (c/let-ir (+ i 2) "object" {:proj {:i i :x {:idx 1}}}
                             ["inc" {:idx (+ i 2)} 1 false false body])) tail (reverse (range 10)))))
   (c/decl "model-delayed-record" [(c/p 1 "object") (c/p 2 "object")] "object"
     (c/let-ir 3 "object" (c/ctor 0 [(c/v 1) (c/v 2)] 0) (c/ret 3)))])
(defn delayed! [ctx e m name pending]
  (let [array (expr/call ctx e "Array.mkEmpty" [0 0])
        record (expr/call ctx e "model-delayed-record" [array pending])
        m (expr/call ctx e "model-swap-expr-delayed-maps" [m])
        m (assign! ctx e m name record)]
    [(expr/call ctx e "model-swap-expr-delayed-maps" [m]) record]))
(deftest delayed-probe-reports-flag-only-for-assigned-pending-name-and-never-reads-fvars
  (doseq [pending-assigned? [false true]]
    (let [{:keys [ctx] :as lab} (context {:rows (delayed-model-rows) :defer #{(helpers 2)}}) e (engine lab)
          m (level/fresh! ctx e) pending (level/name! ctx e "pending") n (level/name! ctx e "delayed")
          input (mvar! ctx e (expr/retain ctx e n))
          m (if pending-assigned? (assign! ctx e m (expr/retain ctx e pending) (expr/sort! ctx e)) m)
          [m record] (delayed! ctx e m n pending) report (run! lab e m input)]
      (is (identical? input (second (fields ctx report))))
      (is (= (if pending-assigned? 1 0) (nth (fields ctx report) 2)))
      (is (= 1 (c/rc ctx record))) (close! ctx e report))))
(deftest delayed-accessor-code-pause-keeps-option-record-temporary-and-packet-occurrences
  (let [label (helpers 3) {:keys [ctx headers] :as lab} (context {:rows (delayed-model-rows) :defer #{label}})
        parent (engine lab) m (level/fresh! ctx parent) n (level/name! ctx parent "delayed-code")
        input (mvar! ctx parent (expr/retain ctx parent n))
        [m record] (delayed! ctx parent m n (level/name! ctx parent "pending-code"))]
    (start! lab parent m input) (until! ctx parent #(some? (j/code-request ctx parent)))
    (let [frame (task-of parent "DirectDelayedFrame") option (pv (pv frame "option") "value")
          temp (pv frame "recordTemporary") packet (pv (session parent) "call")
          {:keys [engine roots]} (j/fork! ctx parent [m input record]) child engine ready (materialize lab label)]
      (is (identical? (headers label) (.header (j/code-request ctx parent))))
      (is (identical? record (first (fields ctx option)))) (is (identical? record (pv temp "value")))
      (is (true? (pv temp "owned"))) (is (= 4 (c/rc ctx record)))
      (is (= [false] (vec (pv packet "owned"))))
      (is (not (identical? temp (pv (task-of child "DirectDelayedFrame") "recordTemporary"))))
      (doseq [e [parent child]]
        (j/resume-code! ready e (j/code-request ready e))
        (let [report (expr/finish-research! ready e)] (is (= 0 (nth (fields ready report) 2))) (close! ready e report))))))
(deftest unresolved-app-keeps-delayed-option-through-structural-fallback-and-reprobe
  (let [{:keys [ctx] :as lab} (context {:rows (delayed-model-rows)}) e (engine lab)
        m (level/fresh! ctx e) n (level/name! ctx e "fallback")
        head (mvar! ctx e (expr/retain ctx e n)) input (expr/app! ctx e head (expr/fvar! ctx e "argument"))
        [m record] (delayed! ctx e m n (level/name! ctx e "unresolved"))]
    (start! lab e m input)
    (until! ctx e #(let [f (task-of e "DirectAppFrame")]
                    (and f (= 5 (pv f "stage")) (some? (pv f "delayed")) (some? (task-of e "DirectDelayedFrame")))))
    (let [outer (task-of e "DirectAppFrame") option (pv (pv outer "delayed") "value")]
      (is (identical? record (first (fields ctx option))))
      ;; Outer Option plus captured context record remain owners while the leaf
      ;; probes the same delayed assignment again; pending/condition locals retired.
      (is (>= (c/rc ctx record) 2)))
    (let [report (expr/finish-research! ctx e)]
      (is (identical? input (second (fields ctx report)))) (is (= 0 (nth (fields ctx report) 2)))
      (is (= 1 (c/rc ctx record))) (close! ctx e report))))

(deftest all-composite-constructors-preserve-payloads-flags-and-unchanged-child-identities
  (doseq [[role expected-tag] [[3 5] [4 6] [5 7] [6 8] [7 10] [8 11]]]
    (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
          n (level/name! ctx e "composite") mv (mvar! ctx e (expr/retain ctx e n))
          fixed (expr/sort! ctx e) replacement (expr/fvar! ctx e "replacement")
          args (case role 3 [(expr/retain ctx e fixed) mv]
                    (4 5) [0 (expr/retain ctx e fixed) mv 2]
                    6 [0 (expr/retain ctx e fixed) (expr/retain ctx e fixed) mv 1]
                    7 [0 mv] 8 [(level/name! ctx e "Struct") 3 mv])
          input (expr/setup! ctx e role args) m (assign! ctx e m n (expr/retain ctx e replacement))
          report (run! lab e m input) out (second (fields ctx report)) fs (fields ctx out)]
      (is (= expected-tag (.getInt ^java.lang.reflect.Field (:tag ctx) out)))
      (is (identical? replacement (last fs)))
      (when (#{3 4 5 6} role) (is (identical? fixed (fs (if (= role 3) 0 1)))))
      (when (#{4 5 6} role) (is (= (if (= role 6) 1 2) (nth (expr/scalar-bytes ctx out) 8))))
      (when (= role 8) (is (= 3 (second fs))))
      (is (true? (pv input "dead")))
      (sync/release! ctx e fixed) (sync/release! ctx e replacement) (close! ctx e report))))
(deftest nested-level-and-expr-constructor-code-forks-share-one-context-cell-and-budget
  (doseq [label [(level/roles 2) (expr/roles 1)]]
    (let [{:keys [ctx headers] :as lab} (context {:defer #{label}}) parent (engine lab)
          n (level/name! ctx parent "constructor-level") l (level/mvar! ctx parent (expr/retain ctx parent n))
          l (expr/call ctx parent (str "model-setup-" (level/roles 2)) [l])
          input (expr/setup! ctx parent 1 [l]) m (level/fresh! ctx parent) m (level/assign! ctx parent m n 0)]
      (start! lab parent m input) (until! ctx parent #(some? (j/code-request ctx parent)))
      (let [request (j/code-request ctx parent) {:keys [engine roots]} (j/fork! ctx parent [m input])
            child engine ready (materialize lab label)]
        (is (identical? (headers label) (.header request)))
        (doseq [e [parent child]]
          (let [s (session e) levels (pv s "levels")]
            (is (identical? (pv s "context") (pv levels "context")))
            (is (identical? (pv s "budget") (pv levels "budget"))))
          (j/resume-code! ready e (j/code-request ready e))
          (let [report (expr/finish-research! ready e) result (second (fields ready report))]
            (is (= [0] (fields ready (first (fields ready result))))) (close! ready e report)))))))
(deftest assigned-beta-buffer-and-recursive-ancestors-survive-constructor-code-fork
  (let [label (expr/roles 3) {:keys [ctx headers] :as lab} (context {:defer #{label}}) parent (engine lab)
        p (expr/fvar! ctx parent "buffer-p") q (expr/fvar! ctx parent "buffer-q")
        body (expr/setup! ctx parent 7 [0 (expr/bvar! ctx parent 1)])
        let-expr (expr/setup! ctx parent 6 [0 (expr/sort! ctx parent) (expr/bvar! ctx parent 0) body 0])
        lambda (expr/lam! ctx parent let-expr) function (expr/setup! ctx parent 7 [0 lambda])
        n (level/name! ctx parent "beta-head") head (mvar! ctx parent (expr/retain ctx parent n))
        input (expr/app! ctx parent (expr/app! ctx parent head (expr/retain ctx parent p)) (expr/retain ctx parent q))
        m (assign! ctx parent (level/fresh! ctx parent) n function)]
    (start! lab parent m input) (expr/constructor-request! ctx parent)
    (let [worker (expr/state parent) beta (expr/current-job parent) frame (task-of parent "DirectAppBetaFrame")
          ancestors (mapv #(pv % "expression") (pv beta "frames")) args (vec (pv frame "arguments"))
          {:keys [engine roots]} (j/fork! ctx parent [p q]) child engine [cp cq] roots ready (materialize lab label)]
      (is (= 5 (count ancestors))) (is (every? #(true? (pv % "owned")) ancestors))
      (is (= 2 (count args))) (is (every? #(true? (pv % "owned")) args))
      (is (identical? q (pv (args 0) "value"))) (is (identical? p (pv (args 1) "value")))
      (is (empty? (pv worker "arguments")))
      (is (nil? (pv frame "betaParameter")))
      (is (true? (pv (pv beta "function") "owned")))
      (is (not (identical? (pv beta "temporary") (pv beta "accumulator"))))
      (is (identical? (pv (session parent) "budget") (pv worker "budget")))
      (doseq [[e ep eq] [[parent p q] [child cp cq]]]
        (is (identical? (pv (session e) "budget") (pv (expr/state e) "budget")))
        (j/resume-code! ready e (j/code-request ready e))
        (let [report (expr/finish-research! ready e) result (second (fields ready report))]
          (is (every? true? (map identical? [ep eq] (fields ready result))))
          (sync/release! ready e ep) (sync/release! ready e eq) (close! ready e report))))))
(deftest modeled-getter-host-pause-invalid-reply-and-fork-preserve-option-protocol
  (let [label (helpers 0) entry (first (filter #(= label (get % "label")) (originals)))
        body (get-in entry ["row" "ir" "fdecl" "body"])
        spec (h/spec "research_expr_direct_event" ["object"] [true] "object")
        replacement (c/let-ir 100 "object" (c/fap "model-direct-event" [(c/v 1)]) body)
        {:keys [ctx] :as lab} (context {:replacements {label replacement}
                                       :rows [(h/ext "model-direct-event" spec)] :host-specs [spec]})
        parent (engine lab) m (level/fresh! ctx parent) input (mvar! ctx parent (level/name! ctx parent "host"))]
    (start! lab parent m input)
    (let [request (h/request! ctx parent) packet (pv (session parent) "call")
          {:keys [engine roots]} (j/fork! ctx parent [m input]) child engine]
      (is (true? (pv packet "entered"))) (is (every? false? (vec (pv packet "owned"))))
      (is (g/bad? #(j/resume-host! ctx parent request (Double/valueOf 1))))
      (is (identical? request (j/host-request ctx parent)))
      (doseq [e [parent child]]
        (j/resume-host! ctx e (j/host-request ctx e) 0)
        (let [report (expr/finish-research! ctx e)] (is (= 0 (nth (fields ctx report) 2))) (close! ctx e report))))))
(deftest malformed-getter-result-retains-the-owned-receiver-and-inputs
  (let [body ["dec" {:idx 1} 1 false false ["dec" {:idx 2} 1 false false
                         (c/let-ir 3 "object" (c/lit 0)
                           (c/let-ir 4 "object" (c/ctor 2 [(c/v 3)] 0) (c/ret 4)))]]
        {:keys [ctx] :as lab} (context {:replacements {(helpers 0) body}}) e (engine lab)
        m (level/fresh! ctx e) input (mvar! ctx e (level/name! ctx e "invalid-result"))]
    (start! lab e m input)
    (is (re-find #"malformed Option" (c/failure #(expr/finish-research! ctx e))))
    (let [action (sync/action e) receiver (aget ^objects (pv e "objects") (pv action "slot"))]
      (is (= 2 (.getInt ^java.lang.reflect.Field (:tag ctx) receiver))) (is (= 1 (c/rc ctx receiver)))
      (is (some? (pv (session e) "call"))) (is (= 1 (c/rc ctx m) (c/rc ctx input))))))

(defn level-cons-row []
  (c/decl "model-direct-level-cons" [(c/p 1 "object") (c/p 2 "object")] "object"
    (c/let-ir 3 "object" (c/ctor 1 [(c/v 1) (c/v 2)] 0) (c/ret 3))))
(deftest const-level-list-visits-tail-first-and-retains-first-changed-head-through-prefix
  (doseq [pause-getter? [false true]]
    (let [label (level/roles 0) {:keys [ctx headers] :as lab}
          (context {:rows [(level-cons-row)] :defer (if pause-getter? #{label} #{})})
          parent (engine lab) m (level/fresh! ctx parent)
          head-name (level/name! ctx parent "head-level") tail-name (level/name! ctx parent "tail-level")
          head (level/mvar! ctx parent (expr/retain ctx parent head-name))
          tail (level/mvar! ctx parent (expr/retain ctx parent tail-name)) one (level/succ! ctx parent 0)
          m (level/assign! ctx parent m (expr/retain ctx parent tail-name) (expr/retain ctx parent one))
          tail-list (expr/call ctx parent "model-direct-level-cons" [tail 0])
          list (expr/call ctx parent "model-direct-level-cons" [head tail-list])
          input (expr/setup! ctx parent 2 [(level/name! ctx parent "C") list])]
      (start! lab parent m input)
      (if pause-getter?
        (do (until! ctx parent #(some? (j/code-request ctx parent)))
            (let [request (j/code-request ctx parent) args (vec (j/request-value request "arguments")) ready (materialize lab label)]
              (is (identical? (headers label) (.header request))) (is (identical? tail-name (args 1)))
              (is (= 1 (c/rc ctx tail))) ;; The borrowed Level job does not retain list elements.
              (j/resume-code! ready parent request)
              (let [report (expr/finish-research! ready parent)]
                (doseq [value [head-name tail-name one]] (sync/release! ready parent value)) (close! ready parent report))))
        (do (until! ctx parent #(let [f (task-of parent "DirectLevelsFrame")]
                                (and f (= 1 (pv f "stage")) (= 0 (pv f "index")) (some? (pv f "firstChanged")))))
            (let [frame (task-of parent "DirectLevelsFrame") credit (pv frame "firstChanged")
                  {:keys [engine roots]} (j/fork! ctx parent [head-name tail-name one]) child engine [chn ctn co] roots]
              (is (true? (pv credit "owned"))) (is (identical? one (pv credit "value")))
              (is (= 4 (c/rc ctx one)))
              (is (identical? co (pv (pv (task-of child "DirectLevelsFrame") "firstChanged") "value")))
              (doseq [[e hn tn o] [[parent head-name tail-name one] [child chn ctn co]]]
                (let [report (expr/finish-research! ctx e)]
                  (is (= 3 (c/rc ctx o)))
                  (doseq [value [hn tn o]] (sync/release! ctx e value)) (close! ctx e report)))))))))
(deftest private-entry-rejects-mixed-source-inactive-and-undercredited-alias-before-claims
  (let [{:keys [ctx headers] :as lab} (context) e (engine lab)
        m (level/fresh! ctx e) input (expr/bvar! ctx e 0)
        getter (first (filter #(= (helpers 0) (get % "label")) (originals)))
        foreign (j/declaration-header (j/source-binding ctx (Object.)) (get getter "row") (get getter "sha256"))
        counters #(mapv (fn [n] (pv e n)) ["allocations" "stores" "retains" "releases"])
        before (counters)]
    (doseq [thunk [#(start! (assoc lab :headers (assoc headers (helpers 0) foreign)) e m input)
                   #(start! lab e input input)]]
      (is (g/bad? thunk)) (is (= "idle" (j/phase ctx e))) (is (nil? (state e)))
      (is (= before (counters))) (is (= 1 (c/rc ctx m) (c/rc ctx input))))
    (sync/release! ctx e m) (sync/release! ctx e input) (sync/close! ctx e))
  (let [{:keys [ctx] :as lab} (context {:inactive true}) e (j/machine ctx) input (expr/bvar! ctx e 0)]
    (is (g/bad? #(start! lab e 0 input))) (is (= "idle" (j/phase ctx e)))
    (is (= 1 (c/rc ctx input))) (j/release! ctx e input) (j/close! ctx e)))
(deftest named-shared-work-and-worker-interruption-bounds-preserve-input-ledger
  (doseq [kind [:work :interrupt]]
    (let [{:keys [ctx] :as lab} (context) e (engine lab) input (expr/bvar! ctx e 0)
          m (level/fresh! ctx e) outcome (atom nil)]
      (start! lab e m input)
      (sync/private-set! (pv (state e) "budget") "work" (long (if (= kind :work) 1000000 1023)))
      (if (= kind :work)
        (reset! outcome (c/failure #(j/advance! ctx e 1)))
        (let [worker (Thread. ^Runnable (fn [] (.interrupt (Thread/currentThread))
                            (try (reset! outcome (c/failure #(j/advance! ctx e 1)))
                                 (finally (Thread/interrupted)))))]
          (.start worker) (.join worker 1000) (is (not (.isAlive worker)))))
      (is (re-find (if (= kind :work) #"work outside bounded" #"interrupted") (or @outcome "")))
      (is (= 1 (c/rc ctx input) (c/rc ctx m))) (is (= "failed" (j/phase ctx e)))
      (is (true? (pv (pv (state e) "input") "owned")))
      (is (true? (pv (pv (pv (state e) "context") "current") "owned"))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-direct-checks)))
