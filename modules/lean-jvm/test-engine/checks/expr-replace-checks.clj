(ns java-ir-expr-replace-checks
  "Original callback replace: native cache, owned Options and resumable AP."
  (:refer-clojure :exclude [run!])
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [engine-support.expr :as expr] [java-ir-expr-find-checks :as find]
            [java-ir-extern-checks :as x] [java-ir-host-checks :as h]
            [java-ir-generation-checks :as g] [java-ir-code-checks :as code]
            [java-ir-sync-task-checks :as sync] [java-ir-logical-sharing-checks :as sharing]
            [java-ir-continuation-checks :as k] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-expr-replace-runtime/")
(defn records [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn native-fap [args] {:fap {:c (get-in (first (records)) ["row" "name"]) :ys args}})
(defn helpers []
  [(c/decl "replace-none" [(c/p 1 "object")] "object"
     ["dec" {:idx 1} 1 false false (c/let-ir 2 "object" (c/lit 0) (c/ret 2))])
   (c/decl "replace-self" [(c/p 1 "object")] "object"
     (c/let-ir 2 "object" (c/ctor 1 [(c/v 1)] 0) (c/ret 2)))
   (c/decl "replace-some" [(c/p 1 "object")] "object"
     (c/let-ir 2 "object" (c/ctor 1 [(c/v 1)] 0) (c/ret 2)))
   (c/decl "replace-captured" [(c/p 1 "object") (c/p 2 "object")] "object"
     ["dec" {:idx 2} 1 false false (c/let-ir 3 "object" (c/ctor 1 [(c/v 1)] 0) (c/ret 3))])
   (c/decl "replace-apply" (mapv #(c/p % "object") [1 2 3]) "object"
     (c/let-ir 4 "object" {:ap {:x {:idx 1} :ys [(c/v 2) (c/v 3)]}} (c/ret 4)))
   (c/decl "replace-nested" [(c/p 1 "object")] "object"
     (c/let-ir 2 "object" {:pap {:c (c/name-ir "replace-none") :ys []}}
       (c/let-ir 3 "object" (native-fap [(c/v 2) (c/v 1)])
         ["dec" {:idx 2} 1 false false ["dec" {:idx 1} 1 false false
          (c/let-ir 4 "object" (c/ctor 1 [(c/v 3)] 0) (c/ret 4))]])))])
(defn context
  ([] (context {}))
  ([options]
   (binding [expr/*basis* *basis*]
     (expr/context (-> options
                      (update :extra-originals #(concat (records) %))
                      (update :rows #(concat (helpers) %)))))))
(defn machine [{:keys [ctx headers]}]
  (let [e (j/machine ctx)]
    (j/configure-expr-transforms! ctx e (j/expr-transform-policy ctx (mapv headers expr/roles))) e))
(defn pred! [ctx e label] (j/make-closure! ctx e label []))
(defn run! [ctx e p root] (expr/call ctx e "Lean.Expr.replaceImpl._boxed" [p root]))
(defn state [e]
  (loop [action (sync/action e)]
    (when action (if (= 15 (h/private-value action "operation")) (h/private-value action "exprMachinery")
                  (recur (h/private-value action "parent"))))))
(defn job [e] (some-> (state e) (h/private-value "jobs") (.peekLast)))
(defn frame [e] (some-> (job e) (h/private-value "frames") (.peekLast)))
(defn until! [ctx e condition]
  (loop [left 100000]
    (assert (pos? left) "Bounded replace test did not reach checkpoint")
    (when-not (condition) (j/advance! ctx e 1) (recur (dec left)))))
(def host-predicate (h/spec "research_replace_predicate" ["object"] [true] "object"))
(defn host-lab [] (context {:rows [(h/ext "replace-host" host-predicate)] :host-specs [host-predicate]}))
(defn drive! [ctx e handler]
  (loop [left 100000]
    (assert (pos? left) "Bounded replace test did not finish")
    (case (j/phase ctx e)
      "complete" (j/take-result! ctx e)
      "running" (do (j/advance! ctx e 1) (recur (dec left)))
      "host-call" (do (handler (j/host-request ctx e)) (recur (dec left)))
      (throw (ex-info "Unexpected replace boundary" {:phase (j/phase ctx e)})))))

(deftest exact-original-abi-and-owning-wrapper-provenance
  (let [rs (records) p (json/read-str (slurp (str directory "provenance.json"))) raw (get-in (first rs) ["row" "ir" "extern"])]
    (is (= 2 (count rs)))
    (is (= (get p "original-rows-sha256") (corpus/sha256 (str directory "original-rows.json"))))
    (is (= [] (get p "initialized-dependencies")))
    (is (= [["object" "object"] [true true] "object"]
           [(mapv #(get % "ty") (get raw "xs")) (mapv #(get % "borrow") (get raw "xs")) (get raw "type")]))
    (is (= [false false] (mapv #(get % "borrow") (get-in (second rs) ["row" "ir" "fdecl" "xs"]))))))

(deftest no-policy-inactive-and-raw-first-class-entry-reject-before-loans
  (let [{:keys [ctx source headers] :as lab} (context) e (machine lab) root (expr/bvar! ctx e 0) p (pred! ctx e "replace-none")
        before (k/counters ctx e)]
    (is (g/bad? #(j/start! ctx e "Lean.Expr.replaceImpl" [p root])))
    (is (= before (k/counters ctx e))) (is (= "idle" (j/phase ctx e)))
    (is (g/bad? #(j/make-closure! ctx e "Lean.Expr.replaceImpl" [])))
    (is (g/bad? #(context {:rows [(c/decl "bad-replace-pap" [] "object"
                       (c/let-ir 1 "object" {:pap {:c (get-in (first (records)) ["row" "name"]) :ys []}} (c/ret 1)))]})))
    (is (g/bad? #(j/install-graph! ctx e (j/prepared-graph ctx source (Object.)
                  [(j/graph-node ctx {:kind :closure :id 1 :target (headers "Lean.Expr.replaceImpl")})] [] [] [(j/graph-ref ctx 1)]))))
    (sync/release! ctx e p) (sync/release! ctx e root) (sync/close! ctx e))
  (doseq [inactive? [false true]]
    (let [{:keys [ctx]} (context (when inactive? {:inactive true})) e (j/machine ctx)
          root (expr/bvar! ctx e 0) p (pred! ctx e "replace-none") before (k/counters ctx e)]
      (j/start! ctx e "Lean.Expr.replaceImpl._boxed" [p root])
      (is (re-find #"Expr transforms require" (c/failure #(sync/finish! ctx e))))
      (is (= before (k/counters ctx e))) (is (= 1 (c/rc ctx p) (c/rc ctx root))))))

(deftest none-and-some-self-preserve-source-identity-with-exact-one-result-owner
  (doseq [label ["replace-none" "replace-self"] route [:root :ap]]
    (let [{:keys [ctx] :as lab} (context) e (machine lab) root (expr/app! ctx e (expr/bvar! ctx e 0) (expr/bvar! ctx e 1))
          p (pred! ctx e label) before (expr/scalar-bytes ctx root)
          output (if (= route :root) (run! ctx e p root)
                   (expr/call ctx e "replace-apply" [(j/make-closure! ctx e "Lean.Expr.replaceImpl._boxed" []) p root]))]
      (is (identical? root output)) (is (= before (expr/scalar-bytes ctx output)))
      (is (= 1 (c/rc ctx output))) (is (h/private-value p "dead"))
      (is (nil? (state e))) (sync/release! ctx e output) (sync/close! ctx e))))

(deftest some-replacement-stops-children-and-transfers-captured-result
  (let [{:keys [ctx] :as lab} (context) e (machine lab)
        root (expr/app! ctx e (expr/bvar! ctx e 0) (expr/bvar! ctx e 1)) replacement (expr/bvar! ctx e 42)
        p (j/make-closure! ctx e "replace-captured" [replacement]) output (run! ctx e p root)]
    (is (identical? replacement output)) (is (= 1 (c/rc ctx output)))
    (is (= [42] (expr/fields ctx output))) (is (h/private-value root "dead"))
    (is (h/private-value p "dead")) (sync/release! ctx e output) (sync/close! ctx e)))

(deftest all-child-orders-including-partial-apps-ignore-range-flags-for-arbitrary-callback
  (let [extra (remove #(= (c/name-ir "model-captured-root-search") (:name %)) (find/helpers)) {:keys [ctx] :as lab} (context {:rows (concat extra [(h/ext "replace-host" host-predicate)]) :host-specs [host-predicate]})
        e (machine lab) mk #(apply find/mk ctx e %&)
        bf (mk 0 11) br (mk 0 12) fv (mk 1 0) mv (mk 2 0) sort (mk 3 0) con (mk 4 0 0)
        literal (expr/call ctx e "model-literal" [17]) lit (mk 9 literal)
        proj (mk 11 0 0 bf) md (mk 10 0 proj) forall (mk 7 0 mv md)
        app (mk 5 con sort) lam (mk 6 0 app forall) let-node (mk 8 0 fv lit lam) root (mk 5 let-node br)
        expected [root let-node fv lit lam app con sort forall mv md proj bf br]
        seen (atom []) p (pred! ctx e "replace-host") _ (j/start! ctx e "Lean.Expr.replaceImpl._boxed" [p root])
        output (drive! ctx e #(do (swap! seen conj (first (h/args %))) (j/resume-host! ctx e % 0)))]
    ;; These structural Expr models have zero range/cache flags deliberately.
    (is (= (count expected) (count @seen))) (is (every? true? (map identical? expected @seen)))
    (is (identical? root output)) (sync/release! ctx e output) (sync/close! ctx e)))

(deftest shared-cache-includes-leaf-kinds-and-mt-count-one-differs-from-likely-unshared
  (doseq [mode [:st :mt :shared :persistent]]
    (let [{:keys [ctx source] :as lab} (host-lab) e (machine lab)
          root (if (= mode :persistent)
                 (first (j/install-graph! ctx e (j/prepared-graph ctx source (Object.)
                   [(j/graph-node ctx {:kind :ctor :id 1 :tag 0 :fields [0] :scalars (repeat 8 0)})] [] [] [(j/graph-ref ctx 1)])))
                 (expr/bvar! ctx e 0))
          _ (when (= mode :mt) (sharing/mark! ctx e root)) _ (when (= mode :shared) (j/retain! ctx e root))
          p (pred! ctx e "replace-host") _ (j/start! ctx e "Lean.Expr.replaceImpl._boxed" [p root]) request (h/request! ctx e)]
      (is (= (not= mode :st) (h/private-value (frame e) "shared")))
      (is (= (case mode :st 2 :mt 2 :shared 3 :persistent 0) (c/rc ctx root)))
      (j/resume-host! ctx e request 0)
      (let [output (sync/finish! ctx e)]
        (is (identical? root output)) (is (= (case mode :shared 2 :persistent 0 1) (c/rc ctx output)))
        (sync/release! ctx e output))
      (when (= mode :shared) (sync/release! ctx e root)) (sync/close! ctx e)))
  (doseq [tag [:bvar :sort :const]]
    (let [{:keys [ctx] :as lab} (host-lab) e (machine lab)
          leaf (case tag :bvar (expr/bvar! ctx e 0) :sort (expr/sort! ctx e)
                     :const (expr/setup! ctx e 2 [0 0]))
          _ (j/retain! ctx e leaf) root (expr/app! ctx e leaf leaf)
          p (pred! ctx e "replace-host") seen (atom []) _ (j/start! ctx e "Lean.Expr.replaceImpl._boxed" [p root])
          output (drive! ctx e #(do (swap! seen conj (first (h/args %))) (j/resume-host! ctx e % 0)))]
      (is (= 2 (count @seen))) (is (every? true? (map identical? [root leaf] @seen)))
      (is (= 2 (c/rc ctx leaf))) (sync/release! ctx e output) (sync/close! ctx e))))

(deftest nested-native-call-uses-independent-visitor-state-without-consuming-borrowed-input
  (let [{:keys [ctx] :as lab} (context) e (machine lab) root (expr/bvar! ctx e 7)
        p (pred! ctx e "replace-nested") output (run! ctx e p root)]
    (is (identical? root output)) (is (= 1 (c/rc ctx output)))
    (is (h/private-value p "dead")) (is (nil? (state e)))
    (sync/release! ctx e output) (sync/close! ctx e)))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-replace-checks)))

(deftest some-input-alias-is-retained-before-the-owned-option-is-released
  (let [{:keys [ctx] :as lab} (host-lab) e (machine lab) root (expr/bvar! ctx e 7)
        _ (j/retain! ctx e root) option (expr/call ctx e "replace-some" [root]) p (pred! ctx e "replace-host")]
    (j/start! ctx e "Lean.Expr.replaceImpl._boxed" [p root])
    (let [request (h/request! ctx e)]
      (is (= 3 (c/rc ctx root)))
      (j/resume-host! ctx e request option)
      (let [output (sync/finish! ctx e)]
        (is (identical? root output)) (is (= 1 (c/rc ctx output)))
        (is (h/private-value option "dead")) (is (h/private-value p "dead"))
        (sync/release! ctx e output)))
    (sync/close! ctx e)))

(deftest malformed-option-or-expression-keeps-the-owned-receiver-on-terminal-failure
  (doseq [kind [:immediate :big-integer :expr :some-immediate]]
    (let [{:keys [ctx] :as lab} (host-lab) e (machine lab) root (expr/bvar! ctx e 0)
          invalid (case kind :immediate 1 :big-integer (java.math.BigInteger. "0")
                    :expr (expr/bvar! ctx e 9) :some-immediate (expr/call ctx e "replace-some" [0]))
          p (pred! ctx e "replace-host")]
      (j/start! ctx e "Lean.Expr.replaceImpl._boxed" [p root])
      (j/resume-host! ctx e (h/request! ctx e) invalid)
      (is (g/bad? #(sync/finish! ctx e)))
      (let [s (state e) packet (h/private-value s "callback") action (sync/action e)
            slot (h/private-value action "slot") receiver (aget ^objects (h/private-value e "objects") slot)]
        (is (identical? invalid receiver)) (is (h/private-value packet "receiverOwned"))
        (when (instance? (class root) invalid) (is (= 1 (c/rc ctx invalid))))
        (is (= 1 (c/rc ctx root) (c/rc ctx p))) (is (= "failed" (j/phase ctx e)))
        (is (g/bad? #(j/fork! ctx e []))) (is (g/bad? #(j/close! ctx e)))))))

(deftest callback-inc-order-preserves-first-credit-if-the-second-increment-overflows
  (doseq [which [:expression :predicate]]
    (let [{:keys [ctx] :as lab} (context) e (machine lab) root (expr/bvar! ctx e 0)
          p (pred! ctx e "replace-none") value (if (= which :expression) root p)]
      ;; Forged overflow counts are an owner-ledger failure model only.
      (.setInt ^java.lang.reflect.Field (:rc ctx) value Integer/MAX_VALUE)
      (j/start! ctx e "Lean.Expr.replaceImpl._boxed" [p root])
      (is (g/bad? #(sync/finish! ctx e)))
      (let [packet (h/private-value (state e) "callback") current (h/private-value packet "current")
            predicate (h/private-value packet "predicate")]
        (is (= (= which :predicate) (h/private-value current "owned")))
        (is (false? (h/private-value predicate "owned"))) (is (false? (h/private-value packet "started")))
        (is (= (if (= which :expression) Integer/MAX_VALUE 2) (c/rc ctx root)))
        (is (= (if (= which :predicate) Integer/MAX_VALUE 1) (c/rc ctx p)))
        (is (= "failed" (j/phase ctx e)))))))

(deftest callback-code-then-host-fork-preserves-single-acquisition-and-divergent-results
  (let [callback (c/decl "replace-code" [(c/p 1 "object")] "object"
                   (c/let-ir 2 "object" (c/fap "replace-host" [(c/v 1)])
                     ["dec" {:idx 1} 1 false false (c/ret 2)]))
        {:keys [ctx headers] :as lab} (context {:rows [(h/ext "replace-host" host-predicate) callback]
                                             :host-specs [host-predicate] :defer #{"replace-code"}})
        parent (machine lab) root (expr/bvar! ctx parent 0) replacement (expr/bvar! ctx parent 42)
        option (expr/call ctx parent "replace-some" [replacement]) p (pred! ctx parent "replace-code")]
    (j/start! ctx parent "Lean.Expr.replaceImpl._boxed" [p root])
    (let [_ (code/request! ctx parent) packet (h/private-value (state parent) "callback")
          {:keys [engine roots]} (j/fork! ctx parent [root option]) child engine [cr co] roots
          ready (expr/materialize lab "replace-code")]
      (is (h/private-value packet "started"))
      (is (false? (h/private-value (h/private-value packet "current") "owned")))
      (is (= 2 (c/rc ctx root) (c/rc ctx cr)))
      (doseq [[e input reply] [[parent root 0] [child cr co]]]
        (j/resume-code! ready e (j/code-request ready e))
        (let [request (h/request! ready e)]
          (is (identical? input (first (h/args request))))
          (j/resume-host! ready e request reply))
        (let [output (sync/finish! ready e)]
          (if (zero? (if (number? reply) reply 1)) (is (identical? input output))
            (do (is (= [42] (expr/fields ready output))) (is (h/private-value input "dead"))))
          (is (= 1 (c/rc ready output))) (sync/release! ready e output))
        ;; The parent never transferred its separately owned Option reply.
        (when (identical? e parent) (sync/release! ready e option))
        (sync/close! ready e)))))

(deftest changed-child-rebuild-demands-the-authorized-constructor-and-forks-its-packet
  (let [{:keys [ctx headers] :as lab} (context {:rows [(h/ext "replace-host" host-predicate)]
                                             :host-specs [host-predicate] :defer #{"Lean.Expr.app._override"}})
        parent (machine lab) a (expr/bvar! ctx parent 0) b (expr/bvar! ctx parent 1) root (expr/app! ctx parent a b)
        replacement (expr/bvar! ctx parent 42) option (expr/call ctx parent "replace-some" [replacement])
        p (pred! ctx parent "replace-host")]
    (j/start! ctx parent "Lean.Expr.replaceImpl._boxed" [p root])
    (doseq [reply [0 option 0]] (j/resume-host! ctx parent (h/request! ctx parent) reply))
    (let [request (code/request! ctx parent) s (state parent) call (h/private-value s "call")
          {:keys [engine roots]} (j/fork! ctx parent [root replacement]) child engine [cr cv] roots
          ready (expr/materialize lab "Lean.Expr.app._override")]
      (is (identical? (headers "Lean.Expr.app._override") (.header request)))
      (is (h/private-value call "entered"))
      (doseq [[e old value] [[parent root replacement] [child cr cv]]]
        (j/resume-code! ready e (j/code-request ready e))
        (let [output (sync/finish! ready e)]
          (is (not (identical? old output))) (is (h/private-value old "dead"))
          (is (identical? value (first (expr/fields ready output))))
          (is (= [42] (expr/fields ready value))) (is (= 1 (c/rc ready output) (c/rc ready value)))
          (sync/release! ready e output)) (sync/close! ready e)))))

(deftest fork-with-owning-result-cache-drains-the-same-credit-objects-once
  (let [{:keys [ctx] :as lab} (context) parent (machine lab) leaf (expr/bvar! ctx parent 0)
        _ (j/retain! ctx parent leaf) root (expr/app! ctx parent leaf leaf) p (pred! ctx parent "replace-none")]
    (j/start! ctx parent "Lean.Expr.replaceImpl._boxed" [p root])
    (until! ctx parent #(let [j (job parent)] (and j (= 2 (h/private-value j "stage"))
                                                (pos? (.size ^java.util.List (h/private-value j "cacheValues"))))))
    (let [j (job parent) credits (h/private-value j "cacheValues")
          {:keys [engine roots]} (j/fork! ctx parent [root leaf]) child engine [cr cl] roots
          cj (job child) copied (h/private-value cj "cacheValues")]
      (is (= 1 (.size ^java.util.List credits) (.size ^java.util.List copied)))
      (is (not (identical? (.get ^java.util.List credits 0) (.get ^java.util.List copied 0))))
      (is (h/private-value (.get ^java.util.List copied 0) "owned"))
      (is (identical? cl (h/private-value (.get ^java.util.List copied 0) "value")))
      (doseq [[e old l] [[parent root leaf] [child cr cl]]]
        (let [output (sync/finish! ctx e)]
          (is (identical? old output)) (is (= 2 (c/rc ctx l)))
          (sync/release! ctx e output)) (sync/close! ctx e)))))

(deftest changed-composite-children-use-original-constructors-and-preserve-all-other-fields
  (doseq [role [3 4 5 6 7 8]]
    (let [{:keys [ctx] :as lab} (host-lab) e (machine lab) target (expr/bvar! ctx e 1)
          root (case role
                 3 (expr/app! ctx e (expr/sort! ctx e) target)
                 4 (expr/setup! ctx e 4 [0 (expr/sort! ctx e) target 2])
                 5 (expr/setup! ctx e 5 [0 (expr/sort! ctx e) target 3])
                 6 (expr/setup! ctx e 6 [0 (expr/sort! ctx e) (expr/bvar! ctx e 0) target 0])
                 7 (expr/setup! ctx e 7 [0 target])
                 8 (expr/setup! ctx e 8 [0 2 target]))
          old-fields (expr/fields ctx root) replacement (expr/bvar! ctx e 42)
          option (expr/call ctx e "replace-some" [replacement]) p (pred! ctx e "replace-host")]
      (j/start! ctx e "Lean.Expr.replaceImpl._boxed" [p root])
      (let [output (drive! ctx e #(let [current (first (h/args %))]
                                  (j/resume-host! ctx e % (if (identical? target current) option 0))))
            at (.indexOf ^java.util.List old-fields target) new-fields (expr/fields ctx output)
            args (if (<= 4 role 6) (conj new-fields (case role 4 2 5 3 6 0)) new-fields)]
        (is (not (identical? root output))) (is (h/private-value root "dead"))
        (is (identical? replacement (nth new-fields at)))
        (doseq [i (range (count new-fields)) :when (not= i at)]
          (is (or (identical? (nth old-fields i) (nth new-fields i))
                  (and (not (instance? (class root) (nth old-fields i))) (= (nth old-fields i) (nth new-fields i))))))
        (doseq [value args] (j/retain! ctx e value))
        (let [expected (expr/setup! ctx e role args)]
          (is (= (expr/scalar-bytes ctx expected) (expr/scalar-bytes ctx output)))
          (sync/release! ctx e expected))
        (is (= 1 (c/rc ctx replacement))) (sync/release! ctx e output))
      (sync/close! ctx e))))

(deftest raw-runtime-closure-host-reply-is-rejected-before-reply-claim
  (let [spec (h/spec "research_replace_return_closure" [] [] "object")
        {:keys [ctx] :as lab} (context {:rows [(h/ext "replace-return-closure" spec)] :host-specs [spec]})
        e (machine lab) closure (j/make-closure! ctx e "Lean.Expr.replaceImpl._boxed" [])
        original (h/private-value closure "closure") functions ^objects (h/private-value (:program ctx) "functions")
        raw (aget functions (j/function-id ctx "Lean.Expr.replaceImpl"))]
    ;; Reflectively forged borrowed closure models a hostile reply; this is not
    ;; a legal importer/construction path or an ownership certificate.
    (sync/private-set! closure "closure" raw)
    (j/start! ctx e "replace-return-closure" [])
    (let [request (h/request! ctx e) before (k/counters ctx e)]
      (try
        (is (re-find #"Borrowed Expr.replace" (c/failure #(j/resume-host! ctx e request closure))))
        (is (identical? request (j/host-request ctx e)))
        (is (= 1 (c/rc ctx closure))) (is (= before (k/counters ctx e)))
        (finally (sync/private-set! closure "closure" original)))
      (j/resume-host! ctx e request 0) (is (= 0 (sync/finish! ctx e))))
    (sync/release! ctx e closure) (sync/close! ctx e)))

(deftest callback-failure-and-changed-helper-program-retain-exact-loans-without-retry
  (let [{:keys [ctx] :as lab} (host-lab) e (machine lab) input (expr/bvar! ctx e 0) p (pred! ctx e "replace-host")]
    (j/start! ctx e "Lean.Expr.replaceImpl._boxed" [p input])
    (let [request (h/request! ctx e) saved (state e) packet (h/private-value saved "callback")]
      (j/fail-host! ctx e request (ex-info "replace callback model failure" {}))
      (is (= "failed" (j/phase ctx e))) (is (identical? saved (state e)))
      (is (h/private-value packet "started")) (is (= 2 (c/rc ctx input)))
      (is (g/bad? #(j/resume-host! ctx e request 0))) (is (g/bad? #(j/fork! ctx e [])))
      (is (g/bad? #(j/start-dispose! ctx e)))))
  (let [{:keys [ctx] :as lab} (context) e (machine lab) input (expr/bvar! ctx e 0) p (pred! ctx e "replace-self")
        exports ^objects (h/private-value (:program ctx) "guestExports")
        functions ^objects (h/private-value (:program ctx) "functions")
        id (j/function-id ctx "Lean.Expr.bvar._override") other (aget functions (j/function-id ctx "Lean.Expr.sort._override"))
        before (k/counters ctx e)]
    (aset exports id other)
    (try
      (is (re-find #"current exact ordinary" (c/failure #(run! ctx e p input))))
      (is (= before (k/counters ctx e))) (is (= 1 (c/rc ctx input) (c/rc ctx p)))
      (finally (aset exports id nil)))))

(deftest claimed-host-cleanup-can-demand-code-host-and-fork-inside-callback
  (let [consume (h/spec "research_replace_consume_promise" ["object"] [true] "object")
        event (h/spec "research_replace_finalizer_event" ["object"] [true] "object")
        finalizer (c/decl "replace-finalizer" [(c/p 1 "object")] "object"
                    (c/let-ir 2 "object" (c/fap "replace-finalizer-event" [(c/v 1)])
                      ["dec" {:idx 1} 1 false false (c/ret 2)]))
        callback (c/decl "replace-cleanup-predicate" [(c/p 1 "object")] "object"
                   (c/let-ir 10 "object" (c/lit 1)
                     (c/let-ir 2 "object" (sync/sfap "IO.Promise.new._boxed" ["erased" "erased" "erased"])
                       ["inc" {:idx 2} 1 false false
                        (c/let-ir 3 "object" (sync/sfap "IO.Promise.result?._boxed" ["erased" (c/v 2)])
                          (c/let-ir 4 "object" {:pap {:c (c/name-ir "replace-finalizer") :ys []}}
                            (c/let-ir 5 "object" (sync/sfap "Task.map._boxed" ["erased" "erased" (c/v 4) (c/v 3) "erased" (c/v 10)])
                              (c/let-ir 6 "object" {:pap {:c (c/name-ir "replace-consume-promise") :ys []}}
                                (c/let-ir 7 "object" {:ap {:x {:idx 6} :ys [(c/v 2)]}}
                                  ["dec" {:idx 5} 1 false false
                                   ["dec" {:idx 1} 1 false false
                                    (c/let-ir 8 "object" (c/lit 0) (c/ret 8))]])))))])))
        {:keys [ctx headers] :as lab}
        (context {:tasks true :host-specs [consume event] :defer #{"replace-finalizer"}
                  :rows [(h/ext "replace-consume-promise" consume) (h/ext "replace-finalizer-event" event) finalizer callback]})
        parent (machine lab) root (expr/bvar! ctx parent 0) p (pred! ctx parent "replace-cleanup-predicate")]
    (j/start! ctx parent "Lean.Expr.replaceImpl._boxed" [p root])
    (let [request (h/request! ctx parent) promise (first (h/args request))]
      (is (= "research_replace_consume_promise" (j/request-value request "symbol")))
      (j/resume-host! ctx parent request 0)
      (let [request (code/request! ctx parent) completion (h/private-value parent "hostCompletion")
            {:keys [engine roots]} (j/fork! ctx parent [root promise]) child engine [cr cp] roots
            ready (expr/materialize lab "replace-finalizer")]
        (is (identical? (headers "replace-finalizer") (.header request)))
        (is (h/private-value completion "replyClaimed"))
        (is (h/private-value (h/private-value child "hostCompletion") "replyClaimed"))
        (is (h/private-value (h/private-value (state parent) "callback") "started"))
        (is (= 2 (c/rc ctx root) (c/rc ctx cr)))
        (doseq [[e er dead-promise reply] [[parent root promise 0] [child cr cp 77]]]
          (j/resume-code! ready e (j/code-request ready e))
          (let [request (h/request! ready e)]
            (is (= "research_replace_finalizer_event" (j/request-value request "symbol")))
            (is (= [0] (h/args request))) (j/resume-host! ready e request reply))
          (let [output (sync/finish! ready e)]
            (is (identical? er output)) (is (= 1 (c/rc ready output)))
            (is (h/private-value dead-promise "dead"))
            (is (nil? (h/private-value e "hostCompletion"))) (is (nil? (state e)))
            (sync/release! ready e output))
          (is (sync/quiescent? ready e)) (sync/close! ready e))))))

(deftest callback-work-bound-and-structural-cycle-fail-with-owned-progress-preserved
  (let [{:keys [ctx] :as lab} (context) e (machine lab) input (expr/bvar! ctx e 0) p (pred! ctx e "replace-none")]
    (j/start! ctx e "Lean.Expr.replaceImpl._boxed" [p input])
    (until! ctx e #(some? (state e)))
    (let [s (state e) budget (h/private-value s "budget")]
      ;; Forged work cursor only; no admission of new guest owners is implied.
      (sync/private-set! budget "work" (long 1000000))
      (is (re-find #"work outside" (c/failure #(j/advance! ctx e 1))))
      (is (= 1 (c/rc ctx input) (c/rc ctx p)))
      (is (nil? (h/private-value s "callback"))) (is (= "failed" (j/phase ctx e)))))
  (let [{:keys [ctx source] :as lab} (context) e (machine lab)
        [input] (j/install-graph! ctx e (j/selected-owner-graph ctx source (Object.)
          [(j/graph-node ctx {:kind :ctor :id 1 :rc 99 :tag 5 :fields [(j/graph-ref ctx 1) (j/graph-ref ctx 2)] :scalars (repeat 8 0)})
           (j/graph-node ctx {:kind :ctor :id 2 :rc 99 :tag 0 :fields [0] :scalars (repeat 8 0)})] [] [] [(j/graph-ref ctx 1)]))
        p (pred! ctx e "replace-none")]
    (j/start! ctx e "Lean.Expr.replaceImpl._boxed" [p input])
    (is (re-find #"structural cycle" (c/failure #(sync/finish! ctx e))))
    (is (= "failed" (j/phase ctx e))) (is (false? (h/private-value input "dead")))
    (is (= 2 (c/rc ctx input))) (is (g/bad? #(j/fork! ctx e [])))))
