(ns java-ir-expr-full-native-control-checks
 "Public native wrappers/control; source mutation and Host prefixes are explicit models."
 (:require [clojure.test :refer [deftest is run-tests]]
  [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
  [java-ir-expr-full-native-checks :as native] [java-ir-expr-full-checks :as full]
  [java-ir-expr-full-control-checks :as control] [engine-support.expr-context :as direct]
  [engine-support.expr :as expr] [java-ir-level-mvars-checks :as level]
  [java-ir-sync-task-checks :as sync] [java-ir-host-checks :as h]
  [java-ir-host-guest-checks :as hg] [java-ir-generation-checks :as g]
  [java-ir-continuation-checks :as k]))
(def ^:dynamic *basis* nil)
(defn context [options] (binding [native/*basis* *basis*] (native/context options)))

(deftest wrong-current-helper-rejects-before-raw-and-saturated-ap-claims
 ;; Unsafe Program export-table mutation MODEL. No public API replaces an ordinary
 ;; helper this way; the guard must still refuse this current-function mismatch.
 (doseq [ap? [false true]]
  (let [{:keys [ctx] :as lab} (context {}) e (native/engine lab)
        m (level/fresh! ctx e) input (expr/bvar! ctx e 0)
        closure (when ap? (j/make-closure! ctx e native/raw []))
        program (expr/private-value e "program") exports (expr/private-value program "guestExports")
        functions (expr/private-value program "functions") id (j/function-id ctx (direct/helpers 0))
        before (k/counters ctx e)]
   (aset ^objects exports id (aget ^objects functions id))
   (try
    (if ap?
     (do (is (g/bad? #(native/call ctx e "model-native-ap" [closure m input])))
         (is (= 1 (c/rc ctx closure))) (is (not (true? (expr/private-value closure "dead")))))
     (do (is (g/bad? #(j/start! ctx e native/raw [m input])))
         (is (= "idle" (j/phase ctx e))) (is (= before (k/counters ctx e)))))
    (is (= 1 (c/rc ctx m) (c/rc ctx input)))
    (finally (aset ^objects exports id nil)))
   (when-not ap? (sync/release! ctx e m) (sync/release! ctx e input) (sync/close! ctx e)))))

(deftest genuine-helper-code-entry-fork-through-owned-native
 (let [target (direct/helpers 2) {:keys [ctx] :as lab} (context {:defer #{target}})
       parent (native/engine lab) {:keys [m input]} (control/simple-case! ctx parent)]
  (j/start! ctx parent native/boxed [m input])
  (expr/until! ctx parent #(some? (j/code-request ctx parent)))
  (let [before (j/instructions ctx parent) {child :engine} (j/fork! ctx parent [])
        ready (expr/materialize lab target)]
   (doseq [e [parent child]]
    (is (= before (j/instructions ready e)))
    (j/resume-code! ready e (j/code-request ready e))
    (let [pair (sync/finish! ready e)]
     (is (= [3] (expr/fields ready (full/full-result ready pair))))
     (is (> (j/instructions ready e) before)) (full/close! ready e pair))))))

(deftest native-getter-host-suspension-fork-and-terminal-child-preserve-source-packet
 ;; MODEL observational Host prefix in an otherwise authentic fvars accessor.
 (let [target (direct/helpers 2)
       entry (first (filter #(= target (get % "label")) (direct/originals)))
       original (get-in entry ["row" "ir" "fdecl" "body"])
       spec (h/spec "native_expr_event" ["object"] [true] "object")
       replacement (c/let-ir 100 "object" (c/fap "native-expr-event" [(c/v 1)]) original)
       {:keys [ctx] :as lab} (context {:rows [(h/ext "native-expr-event" spec)]
                       :host-specs [spec] :replacements {target replacement}})
       parent (native/engine lab) {:keys [m input]} (control/simple-case! ctx parent)]
  (j/start! ctx parent native/raw [m input])
  (let [request (h/request! ctx parent) {child :engine} (j/fork! ctx parent [])]
   (is (= "native_expr_event" (.symbol request)))
   (is (g/bad? #(j/resume-host! ctx child request 0)))
   (j/fail-host! ctx child (j/host-request ctx child) (ex-info "deliberate native helper failure" {}))
   (is (= "failed" (j/phase ctx child)))
   (is (some? (full/state child)))
   (j/resume-host! ctx parent request 0)
   (let [pair (sync/finish! ctx parent)]
    (is (= [3] (expr/fields ctx (full/full-result ctx pair)))) (full/close! ctx parent pair)))))

(deftest native-owned-wrapper-runs-inside-parked-hostguest-with-code-fork
 (let [target (direct/helpers 2)
       outer (h/spec "native_expr_outer" ["object" "object"] [false false] "object")
       {:keys [ctx headers] :as lab} (context {:rows [(h/ext "native-outer" outer)] :host-specs [outer] :defer #{target}})
       parent (native/engine lab) {:keys [m input]} (control/simple-case! ctx parent)]
  (j/configure-host-guest! ctx parent (j/host-guest-policy ctx [(headers "native-outer")] [(headers native/boxed)]))
  (j/start! ctx parent "native-outer" [m input])
  (let [outer-request (j/host-request ctx parent) before (j/instructions ctx parent)
        op (j/start-host-guest! ctx parent outer-request (headers native/boxed)
              [(j/host-transferred-argument ctx outer-request 0) (j/host-transferred-argument ctx outer-request 1)])]
   (expr/until! ctx parent #(some? (j/code-request ctx parent)))
   (let [{child :engine} (j/fork! ctx parent []) child-op (j/host-guest-operation ctx child)
         child-outer (.outerRequest child-op) ready (expr/materialize lab target)]
    (doseq [[e request operation] [[parent outer-request op] [child child-outer child-op]]]
     (j/resume-code! ready e (j/code-request ready e))
     (is (identical? operation (hg/result! ready e)))
     (is (= "host-guest-result" (j/phase ready e)))
     (is (g/bad? #(j/take-result! ready e)))
     (let [pair (j/take-host-guest-result! ready e request operation)]
      (is (= [3] (expr/fields ready (full/full-result ready pair))))
      (is (identical? request (j/host-request ready e)))
      (is (> (j/instructions ready e) before))
      (j/resume-host! ready e request pair)
      (let [result (sync/finish! ready e)]
       (is (identical? pair result)) (full/close! ready e result))))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-full-native-control-checks)))

(deftest native-delayed-writeback-reads-all-known-assignment-keys-and-other-context-fields
 (let [{:keys [ctx] :as lab} (context {}) e (native/engine lab)
       {:keys [m input name value old]} (control/writeback-case! ctx e)
       original-fields (expr/fields ctx m)
       pair (native/call ctx e native/raw [m input]) [updated out] (expr/fields ctx pair)
       q (expr/call ctx e (direct/helpers 0) [(expr/retain ctx e updated) name])
       pn (level/name! ctx e "ready-pending")
       p (expr/call ctx e (direct/helpers 0) [(expr/retain ctx e updated) pn])
       unknown (expr/call ctx e (direct/helpers 0) [(expr/retain ctx e updated) (level/name! ctx e "absent")])
       q-value (first (expr/fields ctx q)) prefix (first (expr/fields ctx q-value))]
  (is (identical? input out)) (is (identical? value (first (expr/fields ctx prefix))))
  (is (identical? value (first (expr/fields ctx p)))) (is (= 0 unknown))
  ;; Only eAssignment field8 can change; the native oracle additionally verifies
  ;; exact eAssignment domain size. Ten-field context layout is fixture-pinned.
  (doseq [i [0 1 2 3 4 5 6 7 9]]
   (is (identical? (original-fields i) ((expr/fields ctx updated) i))))
  (is (true? (expr/private-value old "dead")))
  (sync/release! ctx e q) (sync/release! ctx e p) (sync/release! ctx e value) (full/close! ctx e pair)))

(deftest imported-original-owned-native-closure-is-callable-with-the-configured-policy
 (let [{:keys [ctx source headers] :as lab} (context {}) e (native/engine lab)
       graph (j/prepared-graph ctx source (Object.)
          [(j/graph-node ctx {:kind :closure :id 1 :target (headers native/raw)})] [] [] [(j/graph-ref ctx 1)])
       closure (first (j/install-graph! ctx e graph))
       pair (native/call ctx e "model-native-ap" [closure (level/fresh! ctx e) (expr/bvar! ctx e 2)])]
  (is (= [2] (expr/fields ctx (full/full-result ctx pair))))
  ;; Default graph imports sourceRC0; the original closure remains persistent.
  (is (= 0 (c/rc ctx closure))) (full/close! ctx e pair)))

(deftest mismatched-native-origin-hash-source-and-name-reject-before-claims
 ;; Explicit fabricated Header metadata models. They are NOT accepted catalogue
 ;; rows; this proves the runtime cannot turn ABI recognition into source policy.
 (doseq [bad [:hash :source :name]]
  (let [lab (binding [full/*basis* *basis*] (full/base-context {}))
        base (:ctx lab) source (:source lab)
        original (first (native/records))
        n (c/name-ir "fabricatedExprNative")
        row (if (= bad :name) (-> (get original "row") (assoc "name" n) (assoc-in ["ir" "extern" "f"] n)) (get original "row"))
        source (if (= bad :source) (j/source-binding base (Object.)) source)
        header (j/declaration-header source row (if (= bad :hash) (apply str (repeat 64 "0")) (get original "sha256")))
        ctx (j/register-headers base [header]) lab (assoc lab :ctx ctx) e (native/engine lab)
        m (level/fresh! ctx e) input (expr/bvar! ctx e 0) before (k/counters ctx e)
        label (if (= bad :name) "fabricatedExprNative" native/raw)]
   (is (g/bad? #(j/start! ctx e label [m input])))
   (is (= "idle" (j/phase ctx e))) (is (= before (k/counters ctx e)))
   (is (= 1 (c/rc ctx m) (c/rc ctx input)))
   (sync/release! ctx e m) (sync/release! ctx e input) (sync/close! ctx e))))
